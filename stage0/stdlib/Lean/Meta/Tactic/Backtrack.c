// Lean compiler output
// Module: Lean.Meta.Tactic.Backtrack
// Imports: public import Lean.Meta.Iterator public import Lean.Meta.Tactic.IndependentOf import Init.Data.Nat.Linear import Init.Omega
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isIndependentOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Meta_Iterator_firstM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__2(lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 45, .m_data = "⏸️ suspending search and returning as subgoal"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "success!"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 42, .m_data = "⏭️ deemed acceptable, returning as subgoal"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 35, .m_data = "⏬ discharger generated new subgoals"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "BacktrackConfig.proc failed: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "discarding already assigned goal "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "working on: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Backtrack exceeded the recursion limit"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2;
static const lean_closure_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "independent goals "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = " working on them before "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "failed: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", new: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1;
static const lean_array_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(lean_object* v_g_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_MVarId_getType(v_g_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_9_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_a_8_);
lean_dec_ref(v___x_7_);
v___x_9_ = l_Lean_Meta_ppExpr(v_a_8_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
return v___x_9_;
}
else
{
lean_object* v_a_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_17_; 
v_a_10_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_17_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_17_ == 0)
{
v___x_12_ = v___x_7_;
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_a_10_);
lean_dec(v___x_7_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_15_; 
if (v_isShared_13_ == 0)
{
v___x_15_ = v___x_12_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_a_10_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId___boxed(lean_object* v_g_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(v_g_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(lean_object* v_x_25_, lean_object* v_x_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
if (lean_obj_tag(v_x_25_) == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = l_List_reverse___redArg(v_x_26_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
else
{
lean_object* v_head_34_; lean_object* v_tail_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_53_; 
v_head_34_ = lean_ctor_get(v_x_25_, 0);
v_tail_35_ = lean_ctor_get(v_x_25_, 1);
v_isSharedCheck_53_ = !lean_is_exclusive(v_x_25_);
if (v_isSharedCheck_53_ == 0)
{
v___x_37_ = v_x_25_;
v_isShared_38_ = v_isSharedCheck_53_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_tail_35_);
lean_inc(v_head_34_);
lean_dec(v_x_25_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_53_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; 
v___x_39_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(v_head_34_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; lean_object* v___x_42_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_a_40_);
lean_dec_ref(v___x_39_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 1, v_x_26_);
lean_ctor_set(v___x_37_, 0, v_a_40_);
v___x_42_ = v___x_37_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_40_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_x_26_);
v___x_42_ = v_reuseFailAlloc_44_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
v_x_25_ = v_tail_35_;
v_x_26_ = v___x_42_;
goto _start;
}
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
lean_del_object(v___x_37_);
lean_dec(v_tail_35_);
lean_dec(v_x_26_);
v_a_45_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_39_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_39_);
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
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0___boxed(lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(v_x_54_, v_x_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(lean_object* v_gs_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_box(0);
v___x_69_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(v_gs_62_, v___x_68_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds___boxed(lean_object* v_gs_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_gs_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__0(lean_object* v_s_77_){
_start:
{
if (lean_obj_tag(v_s_77_) == 1)
{
lean_object* v_val_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v_val_78_ = lean_ctor_get(v_s_77_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v_s_77_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v_s_77_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_val_78_);
lean_dec(v_s_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_val_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
else
{
lean_object* v___x_86_; 
lean_dec_ref(v_s_77_);
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__1(lean_object* v_s_87_){
_start:
{
if (lean_obj_tag(v_s_87_) == 0)
{
lean_object* v_val_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_val_88_ = lean_ctor_get(v_s_87_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v_s_87_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v_s_87_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_val_88_);
lean_dec(v_s_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set_tag(v___x_90_, 1);
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_val_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v___x_96_; 
lean_dec_ref(v_s_87_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__2(lean_object* v_val_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v_val_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3(lean_object* v___f_101_, lean_object* v___f_102_, lean_object* v_toPure_103_, lean_object* v_R_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_105_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_R_104_);
v___x_106_ = l_List_filterMapTR_go___redArg(v___f_101_, v_R_104_, v___x_105_);
v___x_107_ = l_List_filterMapTR_go___redArg(v___f_102_, v_R_104_, v___x_105_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_apply_2(v_toPure_103_, lean_box(0), v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__4(lean_object* v_a_110_, lean_object* v_toPure_111_, lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v_a_110_);
v___x_114_ = lean_apply_2(v_toPure_111_, lean_box(0), v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__5(lean_object* v_toFunctor_115_, lean_object* v_toPure_116_, lean_object* v_f_117_, lean_object* v___f_118_, lean_object* v_orElse_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_map_121_; lean_object* v___f_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_map_121_ = lean_ctor_get(v_toFunctor_115_, 0);
lean_inc(v_map_121_);
lean_dec_ref(v_toFunctor_115_);
lean_inc(v_a_120_);
v___f_122_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_122_, 0, v_a_120_);
lean_closure_set(v___f_122_, 1, v_toPure_116_);
v___x_123_ = lean_apply_1(v_f_117_, v_a_120_);
v___x_124_ = lean_apply_4(v_map_121_, lean_box(0), lean_box(0), v___f_118_, v___x_123_);
v___x_125_ = lean_apply_3(v_orElse_119_, lean_box(0), v___x_124_, v___f_122_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg(lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_L_131_, lean_object* v_f_132_){
_start:
{
lean_object* v_toApplicative_133_; lean_object* v_toBind_134_; lean_object* v_orElse_135_; lean_object* v_toFunctor_136_; lean_object* v_toPure_137_; lean_object* v___f_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_toApplicative_133_ = lean_ctor_get(v_inst_130_, 0);
lean_inc_ref(v_toApplicative_133_);
v_toBind_134_ = lean_ctor_get(v_inst_129_, 1);
lean_inc(v_toBind_134_);
v_orElse_135_ = lean_ctor_get(v_inst_130_, 2);
lean_inc(v_orElse_135_);
lean_dec_ref(v_inst_130_);
v_toFunctor_136_ = lean_ctor_get(v_toApplicative_133_, 0);
lean_inc_ref(v_toFunctor_136_);
v_toPure_137_ = lean_ctor_get(v_toApplicative_133_, 1);
lean_inc(v_toPure_137_);
lean_dec_ref(v_toApplicative_133_);
v___f_138_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__0));
v___f_139_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__1));
v___f_140_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__2));
lean_inc(v_toPure_137_);
v___f_141_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3), 4, 3);
lean_closure_set(v___f_141_, 0, v___f_139_);
lean_closure_set(v___f_141_, 1, v___f_138_);
lean_closure_set(v___f_141_, 2, v_toPure_137_);
v___f_142_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_142_, 0, v_toFunctor_136_);
lean_closure_set(v___f_142_, 1, v_toPure_137_);
lean_closure_set(v___f_142_, 2, v_f_132_);
lean_closure_set(v___f_142_, 3, v___f_140_);
lean_closure_set(v___f_142_, 4, v_orElse_135_);
v___x_143_ = lean_box(0);
v___x_144_ = l_List_mapM_loop___redArg(v_inst_129_, v___f_142_, v_L_131_, v___x_143_);
v___x_145_ = lean_apply_4(v_toBind_134_, lean_box(0), lean_box(0), v___x_144_, v___f_141_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM(lean_object* v_m_146_, lean_object* v_00_u03b1_147_, lean_object* v_00_u03b2_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_L_151_, lean_object* v_f_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg(v_inst_149_, v_inst_150_, v_L_151_, v_f_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(lean_object* v_cls_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_options_160_; uint8_t v_hasTrace_161_; 
v_options_160_ = lean_ctor_get(v___y_158_, 2);
v_hasTrace_161_ = lean_ctor_get_uint8(v_options_160_, sizeof(void*)*1);
if (v_hasTrace_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v_cls_157_);
v___x_162_ = lean_box(v_hasTrace_161_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
else
{
lean_object* v_inheritedTraceOptions_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_inheritedTraceOptions_164_ = lean_ctor_get(v___y_158_, 13);
v___x_165_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1));
v___x_166_ = l_Lean_Name_append(v___x_165_, v_cls_157_);
v___x_167_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_164_, v_options_160_, v___x_166_);
lean_dec(v___x_166_);
v___x_168_ = lean_box(v___x_167_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___boxed(lean_object* v_cls_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_cls_170_, v___y_171_);
lean_dec_ref(v___y_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(lean_object* v_cls_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_cls_174_, v___y_177_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___boxed(lean_object* v_cls_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(v_cls_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_187_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_unsigned_to_nat(32u);
v___x_189_ = lean_mk_empty_array_with_capacity(v___x_188_);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_191_ = ((size_t)5ULL);
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_unsigned_to_nat(32u);
v___x_194_ = lean_mk_empty_array_with_capacity(v___x_193_);
v___x_195_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0);
v___x_196_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
lean_ctor_set(v___x_196_, 2, v___x_192_);
lean_ctor_set(v___x_196_, 3, v___x_192_);
lean_ctor_set_usize(v___x_196_, 4, v___x_191_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v_traceState_200_; lean_object* v_traces_201_; lean_object* v___x_202_; lean_object* v_traceState_203_; lean_object* v_env_204_; lean_object* v_nextMacroScope_205_; lean_object* v_ngen_206_; lean_object* v_auxDeclNGen_207_; lean_object* v_cache_208_; lean_object* v_messages_209_; lean_object* v_infoState_210_; lean_object* v_snapshotTasks_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_230_; 
v___x_199_ = lean_st_ref_get(v___y_197_);
v_traceState_200_ = lean_ctor_get(v___x_199_, 4);
lean_inc_ref(v_traceState_200_);
lean_dec(v___x_199_);
v_traces_201_ = lean_ctor_get(v_traceState_200_, 0);
lean_inc_ref(v_traces_201_);
lean_dec_ref(v_traceState_200_);
v___x_202_ = lean_st_ref_take(v___y_197_);
v_traceState_203_ = lean_ctor_get(v___x_202_, 4);
v_env_204_ = lean_ctor_get(v___x_202_, 0);
v_nextMacroScope_205_ = lean_ctor_get(v___x_202_, 1);
v_ngen_206_ = lean_ctor_get(v___x_202_, 2);
v_auxDeclNGen_207_ = lean_ctor_get(v___x_202_, 3);
v_cache_208_ = lean_ctor_get(v___x_202_, 5);
v_messages_209_ = lean_ctor_get(v___x_202_, 6);
v_infoState_210_ = lean_ctor_get(v___x_202_, 7);
v_snapshotTasks_211_ = lean_ctor_get(v___x_202_, 8);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_230_ == 0)
{
v___x_213_ = v___x_202_;
v_isShared_214_ = v_isSharedCheck_230_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_snapshotTasks_211_);
lean_inc(v_infoState_210_);
lean_inc(v_messages_209_);
lean_inc(v_cache_208_);
lean_inc(v_traceState_203_);
lean_inc(v_auxDeclNGen_207_);
lean_inc(v_ngen_206_);
lean_inc(v_nextMacroScope_205_);
lean_inc(v_env_204_);
lean_dec(v___x_202_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_230_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
uint64_t v_tid_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_228_; 
v_tid_215_ = lean_ctor_get_uint64(v_traceState_203_, sizeof(void*)*1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_traceState_203_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v_traceState_203_, 0);
lean_dec(v_unused_229_);
v___x_217_ = v_traceState_203_;
v_isShared_218_ = v_isSharedCheck_228_;
goto v_resetjp_216_;
}
else
{
lean_dec(v_traceState_203_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_228_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_219_);
lean_ctor_set_uint64(v_reuseFailAlloc_227_, sizeof(void*)*1, v_tid_215_);
v___x_221_ = v_reuseFailAlloc_227_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_223_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 4, v___x_221_);
v___x_223_ = v___x_213_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_env_204_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_nextMacroScope_205_);
lean_ctor_set(v_reuseFailAlloc_226_, 2, v_ngen_206_);
lean_ctor_set(v_reuseFailAlloc_226_, 3, v_auxDeclNGen_207_);
lean_ctor_set(v_reuseFailAlloc_226_, 4, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_226_, 5, v_cache_208_);
lean_ctor_set(v_reuseFailAlloc_226_, 6, v_messages_209_);
lean_ctor_set(v_reuseFailAlloc_226_, 7, v_infoState_210_);
lean_ctor_set(v_reuseFailAlloc_226_, 8, v_snapshotTasks_211_);
v___x_223_ = v_reuseFailAlloc_226_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_st_ref_set(v___y_197_, v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v_traces_201_);
return v___x_225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___boxed(lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v___y_231_);
lean_dec(v___y_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v___y_237_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___boxed(lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_245_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_opts_246_, lean_object* v_opt_247_){
_start:
{
lean_object* v_name_248_; lean_object* v_defValue_249_; lean_object* v_map_250_; lean_object* v___x_251_; 
v_name_248_ = lean_ctor_get(v_opt_247_, 0);
v_defValue_249_ = lean_ctor_get(v_opt_247_, 1);
v_map_250_ = lean_ctor_get(v_opts_246_, 0);
v___x_251_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_250_, v_name_248_);
if (lean_obj_tag(v___x_251_) == 0)
{
uint8_t v___x_252_; 
v___x_252_ = lean_unbox(v_defValue_249_);
return v___x_252_;
}
else
{
lean_object* v_val_253_; 
v_val_253_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_val_253_);
lean_dec_ref(v___x_251_);
if (lean_obj_tag(v_val_253_) == 1)
{
uint8_t v_v_254_; 
v_v_254_ = lean_ctor_get_uint8(v_val_253_, 0);
lean_dec_ref(v_val_253_);
return v_v_254_;
}
else
{
uint8_t v___x_255_; 
lean_dec(v_val_253_);
v___x_255_ = lean_unbox(v_defValue_249_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_opts_256_, lean_object* v_opt_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_opts_256_, v_opt_257_);
lean_dec_ref(v_opt_257_);
lean_dec_ref(v_opts_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg(lean_object* v_x_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Meta_saveState___redArg(v___y_262_, v___y_264_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_268_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref(v___x_266_);
lean_inc(v___y_264_);
lean_inc_ref(v___y_263_);
lean_inc(v___y_262_);
lean_inc_ref(v___y_261_);
v___x_268_ = lean_apply_5(v_x_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, lean_box(0));
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_a_267_);
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v_a_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_307_; 
v_a_278_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_307_ == 0)
{
v___x_280_ = v___x_268_;
v_isShared_281_ = v_isSharedCheck_307_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_268_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_307_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
uint8_t v___y_283_; uint8_t v___x_305_; 
v___x_305_ = l_Lean_Exception_isInterrupt(v_a_278_);
if (v___x_305_ == 0)
{
uint8_t v___x_306_; 
lean_inc(v_a_278_);
v___x_306_ = l_Lean_Exception_isRuntime(v_a_278_);
v___y_283_ = v___x_306_;
goto v___jp_282_;
}
else
{
v___y_283_ = v___x_305_;
goto v___jp_282_;
}
v___jp_282_:
{
if (v___y_283_ == 0)
{
lean_object* v___x_284_; 
lean_del_object(v___x_280_);
lean_dec(v_a_278_);
v___x_284_ = l_Lean_Meta_SavedState_restore___redArg(v_a_267_, v___y_262_, v___y_264_);
lean_dec(v_a_267_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_292_; 
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_292_ == 0)
{
lean_object* v_unused_293_; 
v_unused_293_ = lean_ctor_get(v___x_284_, 0);
lean_dec(v_unused_293_);
v___x_286_ = v___x_284_;
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
else
{
lean_dec(v___x_284_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_box(0);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_288_);
v___x_290_ = v___x_286_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
v_a_294_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_284_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_284_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v___x_303_; 
lean_dec(v_a_267_);
if (v_isShared_281_ == 0)
{
v___x_303_ = v___x_280_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_278_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v_x_260_);
v_a_308_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_266_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_266_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg___boxed(lean_object* v_x_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg(v_x_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(lean_object* v_00_u03b1_323_, lean_object* v_x_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg(v_x_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___boxed(lean_object* v_00_u03b1_331_, lean_object* v_x_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_00_u03b1_331_, v_x_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* v_msgData_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v_env_346_; lean_object* v___x_347_; lean_object* v_mctx_348_; lean_object* v_lctx_349_; lean_object* v_options_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v_env_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_346_);
lean_dec(v___x_345_);
v___x_347_ = lean_st_ref_get(v___y_341_);
v_mctx_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc_ref(v_mctx_348_);
lean_dec(v___x_347_);
v_lctx_349_ = lean_ctor_get(v___y_340_, 2);
v_options_350_ = lean_ctor_get(v___y_342_, 2);
lean_inc_ref(v_options_350_);
lean_inc_ref(v_lctx_349_);
v___x_351_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_351_, 0, v_env_346_);
lean_ctor_set(v___x_351_, 1, v_mctx_348_);
lean_ctor_set(v___x_351_, 2, v_lctx_349_);
lean_ctor_set(v___x_351_, 3, v_options_350_);
v___x_352_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v_msgData_339_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* v_msgData_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_msgData_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_360_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object* v_x_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object* v_x_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(v_x_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec_ref(v_x_372_);
return v_res_378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0));
v___x_381_ = l_Lean_stringToMessageData(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object* v_x_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1);
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object* v_x_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(v_x_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec_ref(v_x_390_);
return v_res_396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0));
v___x_399_ = l_Lean_stringToMessageData(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object* v_x_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object* v_x_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(v_x_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec_ref(v_x_408_);
return v_res_414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0));
v___x_417_ = l_Lean_stringToMessageData(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object* v_x_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object* v_x_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(v_x_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec_ref(v_x_426_);
return v_res_432_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0));
v___x_435_ = l_Lean_stringToMessageData(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* v_a_436_, lean_object* v_x_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
v___x_444_ = l_Lean_Exception_toMessageData(v_a_436_);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* v_a_447_, lean_object* v_x_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_a_447_, v_x_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec_ref(v_x_448_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(lean_object* v_opts_455_, lean_object* v_opt_456_){
_start:
{
lean_object* v_name_457_; lean_object* v_defValue_458_; lean_object* v_map_459_; lean_object* v___x_460_; 
v_name_457_ = lean_ctor_get(v_opt_456_, 0);
v_defValue_458_ = lean_ctor_get(v_opt_456_, 1);
v_map_459_ = lean_ctor_get(v_opts_455_, 0);
v___x_460_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_459_, v_name_457_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_inc(v_defValue_458_);
return v_defValue_458_;
}
else
{
lean_object* v_val_461_; 
v_val_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_val_461_);
lean_dec_ref(v___x_460_);
if (lean_obj_tag(v_val_461_) == 3)
{
lean_object* v_v_462_; 
v_v_462_ = lean_ctor_get(v_val_461_, 0);
lean_inc(v_v_462_);
lean_dec_ref(v_val_461_);
return v_v_462_;
}
else
{
lean_dec(v_val_461_);
lean_inc(v_defValue_458_);
return v_defValue_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7___boxed(lean_object* v_opts_463_, lean_object* v_opt_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(v_opts_463_, v_opt_464_);
lean_dec_ref(v_opt_464_);
lean_dec_ref(v_opts_463_);
return v_res_465_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13(lean_object* v_e_466_){
_start:
{
if (lean_obj_tag(v_e_466_) == 0)
{
uint8_t v___x_467_; 
v___x_467_ = 2;
return v___x_467_;
}
else
{
lean_object* v_a_468_; 
v_a_468_ = lean_ctor_get(v_e_466_, 0);
if (lean_obj_tag(v_a_468_) == 0)
{
uint8_t v___x_469_; 
v___x_469_ = 1;
return v___x_469_;
}
else
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13___boxed(lean_object* v_e_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13(v_e_471_);
lean_dec_ref(v_e_471_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8(size_t v_sz_474_, size_t v_i_475_, lean_object* v_bs_476_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = lean_usize_dec_lt(v_i_475_, v_sz_474_);
if (v___x_477_ == 0)
{
return v_bs_476_;
}
else
{
lean_object* v_v_478_; lean_object* v_msg_479_; lean_object* v___x_480_; lean_object* v_bs_x27_481_; size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v_v_478_ = lean_array_uget_borrowed(v_bs_476_, v_i_475_);
v_msg_479_ = lean_ctor_get(v_v_478_, 1);
lean_inc_ref(v_msg_479_);
v___x_480_ = lean_unsigned_to_nat(0u);
v_bs_x27_481_ = lean_array_uset(v_bs_476_, v_i_475_, v___x_480_);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_add(v_i_475_, v___x_482_);
v___x_484_ = lean_array_uset(v_bs_x27_481_, v_i_475_, v_msg_479_);
v_i_475_ = v___x_483_;
v_bs_476_ = v___x_484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8___boxed(lean_object* v_sz_486_, lean_object* v_i_487_, lean_object* v_bs_488_){
_start:
{
size_t v_sz_boxed_489_; size_t v_i_boxed_490_; lean_object* v_res_491_; 
v_sz_boxed_489_ = lean_unbox_usize(v_sz_486_);
lean_dec(v_sz_486_);
v_i_boxed_490_ = lean_unbox_usize(v_i_487_);
lean_dec(v_i_487_);
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8(v_sz_boxed_489_, v_i_boxed_490_, v_bs_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(lean_object* v_oldTraces_492_, lean_object* v_data_493_, lean_object* v_ref_494_, lean_object* v_msg_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_fileName_501_; lean_object* v_fileMap_502_; lean_object* v_options_503_; lean_object* v_currRecDepth_504_; lean_object* v_maxRecDepth_505_; lean_object* v_ref_506_; lean_object* v_currNamespace_507_; lean_object* v_openDecls_508_; lean_object* v_initHeartbeats_509_; lean_object* v_maxHeartbeats_510_; lean_object* v_quotContext_511_; lean_object* v_currMacroScope_512_; uint8_t v_diag_513_; lean_object* v_cancelTk_x3f_514_; uint8_t v_suppressElabErrors_515_; lean_object* v_inheritedTraceOptions_516_; lean_object* v___x_517_; lean_object* v_traceState_518_; lean_object* v_traces_519_; lean_object* v_ref_520_; lean_object* v___x_521_; lean_object* v___x_522_; size_t v_sz_523_; size_t v___x_524_; lean_object* v___x_525_; lean_object* v_msg_526_; lean_object* v___x_527_; lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_565_; 
v_fileName_501_ = lean_ctor_get(v___y_498_, 0);
v_fileMap_502_ = lean_ctor_get(v___y_498_, 1);
v_options_503_ = lean_ctor_get(v___y_498_, 2);
v_currRecDepth_504_ = lean_ctor_get(v___y_498_, 3);
v_maxRecDepth_505_ = lean_ctor_get(v___y_498_, 4);
v_ref_506_ = lean_ctor_get(v___y_498_, 5);
v_currNamespace_507_ = lean_ctor_get(v___y_498_, 6);
v_openDecls_508_ = lean_ctor_get(v___y_498_, 7);
v_initHeartbeats_509_ = lean_ctor_get(v___y_498_, 8);
v_maxHeartbeats_510_ = lean_ctor_get(v___y_498_, 9);
v_quotContext_511_ = lean_ctor_get(v___y_498_, 10);
v_currMacroScope_512_ = lean_ctor_get(v___y_498_, 11);
v_diag_513_ = lean_ctor_get_uint8(v___y_498_, sizeof(void*)*14);
v_cancelTk_x3f_514_ = lean_ctor_get(v___y_498_, 12);
v_suppressElabErrors_515_ = lean_ctor_get_uint8(v___y_498_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_516_ = lean_ctor_get(v___y_498_, 13);
v___x_517_ = lean_st_ref_get(v___y_499_);
v_traceState_518_ = lean_ctor_get(v___x_517_, 4);
lean_inc_ref(v_traceState_518_);
lean_dec(v___x_517_);
v_traces_519_ = lean_ctor_get(v_traceState_518_, 0);
lean_inc_ref(v_traces_519_);
lean_dec_ref(v_traceState_518_);
v_ref_520_ = l_Lean_replaceRef(v_ref_494_, v_ref_506_);
lean_inc_ref(v_inheritedTraceOptions_516_);
lean_inc(v_cancelTk_x3f_514_);
lean_inc(v_currMacroScope_512_);
lean_inc(v_quotContext_511_);
lean_inc(v_maxHeartbeats_510_);
lean_inc(v_initHeartbeats_509_);
lean_inc(v_openDecls_508_);
lean_inc(v_currNamespace_507_);
lean_inc(v_maxRecDepth_505_);
lean_inc(v_currRecDepth_504_);
lean_inc_ref(v_options_503_);
lean_inc_ref(v_fileMap_502_);
lean_inc_ref(v_fileName_501_);
v___x_521_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_521_, 0, v_fileName_501_);
lean_ctor_set(v___x_521_, 1, v_fileMap_502_);
lean_ctor_set(v___x_521_, 2, v_options_503_);
lean_ctor_set(v___x_521_, 3, v_currRecDepth_504_);
lean_ctor_set(v___x_521_, 4, v_maxRecDepth_505_);
lean_ctor_set(v___x_521_, 5, v_ref_520_);
lean_ctor_set(v___x_521_, 6, v_currNamespace_507_);
lean_ctor_set(v___x_521_, 7, v_openDecls_508_);
lean_ctor_set(v___x_521_, 8, v_initHeartbeats_509_);
lean_ctor_set(v___x_521_, 9, v_maxHeartbeats_510_);
lean_ctor_set(v___x_521_, 10, v_quotContext_511_);
lean_ctor_set(v___x_521_, 11, v_currMacroScope_512_);
lean_ctor_set(v___x_521_, 12, v_cancelTk_x3f_514_);
lean_ctor_set(v___x_521_, 13, v_inheritedTraceOptions_516_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*14, v_diag_513_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*14 + 1, v_suppressElabErrors_515_);
v___x_522_ = l_Lean_PersistentArray_toArray___redArg(v_traces_519_);
lean_dec_ref(v_traces_519_);
v_sz_523_ = lean_array_size(v___x_522_);
v___x_524_ = ((size_t)0ULL);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8(v_sz_523_, v___x_524_, v___x_522_);
v_msg_526_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_526_, 0, v_data_493_);
lean_ctor_set(v_msg_526_, 1, v_msg_495_);
lean_ctor_set(v_msg_526_, 2, v___x_525_);
v___x_527_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_msg_526_, v___y_496_, v___y_497_, v___x_521_, v___y_499_);
lean_dec_ref(v___x_521_);
v_a_528_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_565_ == 0)
{
v___x_530_ = v___x_527_;
v_isShared_531_ = v_isSharedCheck_565_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_527_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_565_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v_traceState_533_; lean_object* v_env_534_; lean_object* v_nextMacroScope_535_; lean_object* v_ngen_536_; lean_object* v_auxDeclNGen_537_; lean_object* v_cache_538_; lean_object* v_messages_539_; lean_object* v_infoState_540_; lean_object* v_snapshotTasks_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_564_; 
v___x_532_ = lean_st_ref_take(v___y_499_);
v_traceState_533_ = lean_ctor_get(v___x_532_, 4);
v_env_534_ = lean_ctor_get(v___x_532_, 0);
v_nextMacroScope_535_ = lean_ctor_get(v___x_532_, 1);
v_ngen_536_ = lean_ctor_get(v___x_532_, 2);
v_auxDeclNGen_537_ = lean_ctor_get(v___x_532_, 3);
v_cache_538_ = lean_ctor_get(v___x_532_, 5);
v_messages_539_ = lean_ctor_get(v___x_532_, 6);
v_infoState_540_ = lean_ctor_get(v___x_532_, 7);
v_snapshotTasks_541_ = lean_ctor_get(v___x_532_, 8);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_564_ == 0)
{
v___x_543_ = v___x_532_;
v_isShared_544_ = v_isSharedCheck_564_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_snapshotTasks_541_);
lean_inc(v_infoState_540_);
lean_inc(v_messages_539_);
lean_inc(v_cache_538_);
lean_inc(v_traceState_533_);
lean_inc(v_auxDeclNGen_537_);
lean_inc(v_ngen_536_);
lean_inc(v_nextMacroScope_535_);
lean_inc(v_env_534_);
lean_dec(v___x_532_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_564_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
uint64_t v_tid_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_562_; 
v_tid_545_ = lean_ctor_get_uint64(v_traceState_533_, sizeof(void*)*1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_traceState_533_);
if (v_isSharedCheck_562_ == 0)
{
lean_object* v_unused_563_; 
v_unused_563_ = lean_ctor_get(v_traceState_533_, 0);
lean_dec(v_unused_563_);
v___x_547_ = v_traceState_533_;
v_isShared_548_ = v_isSharedCheck_562_;
goto v_resetjp_546_;
}
else
{
lean_dec(v_traceState_533_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_562_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_ref_494_);
lean_ctor_set(v___x_549_, 1, v_a_528_);
v___x_550_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_492_, v___x_549_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_550_);
v___x_552_ = v___x_547_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_550_);
lean_ctor_set_uint64(v_reuseFailAlloc_561_, sizeof(void*)*1, v_tid_545_);
v___x_552_ = v_reuseFailAlloc_561_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_554_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 4, v___x_552_);
v___x_554_ = v___x_543_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_env_534_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_nextMacroScope_535_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v_ngen_536_);
lean_ctor_set(v_reuseFailAlloc_560_, 3, v_auxDeclNGen_537_);
lean_ctor_set(v_reuseFailAlloc_560_, 4, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_560_, 5, v_cache_538_);
lean_ctor_set(v_reuseFailAlloc_560_, 6, v_messages_539_);
lean_ctor_set(v_reuseFailAlloc_560_, 7, v_infoState_540_);
lean_ctor_set(v_reuseFailAlloc_560_, 8, v_snapshotTasks_541_);
v___x_554_ = v_reuseFailAlloc_560_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_555_ = lean_st_ref_set(v___y_499_, v___x_554_);
v___x_556_ = lean_box(0);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 0, v___x_556_);
v___x_558_ = v___x_530_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___boxed(lean_object* v_oldTraces_566_, lean_object* v_data_567_, lean_object* v_ref_568_, lean_object* v_msg_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(v_oldTraces_566_, v_data_567_, v_ref_568_, v_msg_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(lean_object* v_x_576_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v_x_576_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v_x_576_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v_x_576_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v_x_576_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 1);
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
v_a_586_ = lean_ctor_get(v_x_576_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v_x_576_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v_x_576_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v_x_576_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 0);
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg___boxed(lean_object* v_x_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_x_594_);
return v_res_596_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__0));
v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
return v___x_599_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2(void){
_start:
{
lean_object* v___x_600_; double v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_float_of_nat(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__3));
v___x_604_ = l_Lean_stringToMessageData(v___x_603_);
return v___x_604_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5(void){
_start:
{
lean_object* v___x_605_; double v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(1000u);
v___x_606_ = lean_float_of_nat(v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(lean_object* v_cls_607_, uint8_t v_collapsed_608_, lean_object* v_tag_609_, lean_object* v_opts_610_, uint8_t v_clsEnabled_611_, lean_object* v_oldTraces_612_, lean_object* v_msg_613_, lean_object* v_resStartStop_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_fst_620_; lean_object* v_snd_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_719_; 
v_fst_620_ = lean_ctor_get(v_resStartStop_614_, 0);
v_snd_621_ = lean_ctor_get(v_resStartStop_614_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_resStartStop_614_);
if (v_isSharedCheck_719_ == 0)
{
v___x_623_ = v_resStartStop_614_;
v_isShared_624_ = v_isSharedCheck_719_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_snd_621_);
lean_inc(v_fst_620_);
lean_dec(v_resStartStop_614_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_719_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v_data_628_; lean_object* v_fst_639_; lean_object* v_snd_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_718_; 
v_fst_639_ = lean_ctor_get(v_snd_621_, 0);
v_snd_640_ = lean_ctor_get(v_snd_621_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_snd_621_);
if (v_isSharedCheck_718_ == 0)
{
v___x_642_ = v_snd_621_;
v_isShared_643_ = v_isSharedCheck_718_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_snd_640_);
lean_inc(v_fst_639_);
lean_dec(v_snd_621_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_718_;
goto v_resetjp_641_;
}
v___jp_625_:
{
lean_object* v___x_629_; 
lean_inc(v___y_627_);
v___x_629_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(v_oldTraces_612_, v_data_628_, v___y_627_, v___y_626_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v___x_630_; 
lean_dec_ref(v___x_629_);
v___x_630_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_fst_620_);
return v___x_630_;
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_fst_620_);
v_a_631_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_629_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_629_);
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
v_resetjp_641_:
{
lean_object* v___x_644_; uint8_t v___x_645_; lean_object* v___y_647_; lean_object* v_a_648_; uint8_t v___y_672_; double v___y_703_; 
v___x_644_ = l_Lean_trace_profiler;
v___x_645_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_opts_610_, v___x_644_);
if (v___x_645_ == 0)
{
v___y_672_ = v___x_645_;
goto v___jp_671_;
}
else
{
lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = l_Lean_trace_profiler_useHeartbeats;
v___x_709_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_opts_610_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; double v___x_712_; double v___x_713_; double v___x_714_; 
v___x_710_ = l_Lean_trace_profiler_threshold;
v___x_711_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(v_opts_610_, v___x_710_);
v___x_712_ = lean_float_of_nat(v___x_711_);
v___x_713_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5);
v___x_714_ = lean_float_div(v___x_712_, v___x_713_);
v___y_703_ = v___x_714_;
goto v___jp_702_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; double v___x_717_; 
v___x_715_ = l_Lean_trace_profiler_threshold;
v___x_716_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(v_opts_610_, v___x_715_);
v___x_717_ = lean_float_of_nat(v___x_716_);
v___y_703_ = v___x_717_;
goto v___jp_702_;
}
}
v___jp_646_:
{
uint8_t v_result_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v_result_649_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13(v_fst_620_);
v___x_650_ = l_Lean_TraceResult_toEmoji(v_result_649_);
v___x_651_ = l_Lean_stringToMessageData(v___x_650_);
v___x_652_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1);
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 7);
lean_ctor_set(v___x_642_, 1, v___x_652_);
lean_ctor_set(v___x_642_, 0, v___x_651_);
v___x_654_ = v___x_642_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_652_);
v___x_654_ = v_reuseFailAlloc_665_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v_m_656_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set_tag(v___x_623_, 7);
lean_ctor_set(v___x_623_, 1, v_a_648_);
lean_ctor_set(v___x_623_, 0, v___x_654_);
v_m_656_ = v___x_623_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_a_648_);
v_m_656_ = v_reuseFailAlloc_664_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; double v___x_659_; lean_object* v_data_660_; 
v___x_657_ = lean_box(v_result_649_);
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
v___x_659_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2);
lean_inc_ref(v_tag_609_);
lean_inc_ref(v___x_658_);
lean_inc(v_cls_607_);
v_data_660_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_660_, 0, v_cls_607_);
lean_ctor_set(v_data_660_, 1, v___x_658_);
lean_ctor_set(v_data_660_, 2, v_tag_609_);
lean_ctor_set_float(v_data_660_, sizeof(void*)*3, v___x_659_);
lean_ctor_set_float(v_data_660_, sizeof(void*)*3 + 8, v___x_659_);
lean_ctor_set_uint8(v_data_660_, sizeof(void*)*3 + 16, v_collapsed_608_);
if (v___x_645_ == 0)
{
lean_dec_ref(v___x_658_);
lean_dec(v_snd_640_);
lean_dec(v_fst_639_);
lean_dec_ref(v_tag_609_);
lean_dec(v_cls_607_);
v___y_626_ = v_m_656_;
v___y_627_ = v___y_647_;
v_data_628_ = v_data_660_;
goto v___jp_625_;
}
else
{
lean_object* v_data_661_; double v___x_662_; double v___x_663_; 
lean_dec_ref(v_data_660_);
v_data_661_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_661_, 0, v_cls_607_);
lean_ctor_set(v_data_661_, 1, v___x_658_);
lean_ctor_set(v_data_661_, 2, v_tag_609_);
v___x_662_ = lean_unbox_float(v_fst_639_);
lean_dec(v_fst_639_);
lean_ctor_set_float(v_data_661_, sizeof(void*)*3, v___x_662_);
v___x_663_ = lean_unbox_float(v_snd_640_);
lean_dec(v_snd_640_);
lean_ctor_set_float(v_data_661_, sizeof(void*)*3 + 8, v___x_663_);
lean_ctor_set_uint8(v_data_661_, sizeof(void*)*3 + 16, v_collapsed_608_);
v___y_626_ = v_m_656_;
v___y_627_ = v___y_647_;
v_data_628_ = v_data_661_;
goto v___jp_625_;
}
}
}
}
v___jp_666_:
{
lean_object* v_ref_667_; lean_object* v___x_668_; 
v_ref_667_ = lean_ctor_get(v___y_617_, 5);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
lean_inc(v_fst_620_);
v___x_668_ = lean_apply_6(v_msg_613_, v_fst_620_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, lean_box(0));
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref(v___x_668_);
v___y_647_ = v_ref_667_;
v_a_648_ = v_a_669_;
goto v___jp_646_;
}
else
{
lean_object* v___x_670_; 
lean_dec_ref(v___x_668_);
v___x_670_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4);
v___y_647_ = v_ref_667_;
v_a_648_ = v___x_670_;
goto v___jp_646_;
}
}
v___jp_671_:
{
if (v_clsEnabled_611_ == 0)
{
if (v___y_672_ == 0)
{
lean_object* v___x_673_; lean_object* v_traceState_674_; lean_object* v_env_675_; lean_object* v_nextMacroScope_676_; lean_object* v_ngen_677_; lean_object* v_auxDeclNGen_678_; lean_object* v_cache_679_; lean_object* v_messages_680_; lean_object* v_infoState_681_; lean_object* v_snapshotTasks_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_701_; 
lean_del_object(v___x_642_);
lean_dec(v_snd_640_);
lean_dec(v_fst_639_);
lean_del_object(v___x_623_);
lean_dec_ref(v_msg_613_);
lean_dec_ref(v_tag_609_);
lean_dec(v_cls_607_);
v___x_673_ = lean_st_ref_take(v___y_618_);
v_traceState_674_ = lean_ctor_get(v___x_673_, 4);
v_env_675_ = lean_ctor_get(v___x_673_, 0);
v_nextMacroScope_676_ = lean_ctor_get(v___x_673_, 1);
v_ngen_677_ = lean_ctor_get(v___x_673_, 2);
v_auxDeclNGen_678_ = lean_ctor_get(v___x_673_, 3);
v_cache_679_ = lean_ctor_get(v___x_673_, 5);
v_messages_680_ = lean_ctor_get(v___x_673_, 6);
v_infoState_681_ = lean_ctor_get(v___x_673_, 7);
v_snapshotTasks_682_ = lean_ctor_get(v___x_673_, 8);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_701_ == 0)
{
v___x_684_ = v___x_673_;
v_isShared_685_ = v_isSharedCheck_701_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_snapshotTasks_682_);
lean_inc(v_infoState_681_);
lean_inc(v_messages_680_);
lean_inc(v_cache_679_);
lean_inc(v_traceState_674_);
lean_inc(v_auxDeclNGen_678_);
lean_inc(v_ngen_677_);
lean_inc(v_nextMacroScope_676_);
lean_inc(v_env_675_);
lean_dec(v___x_673_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_701_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint64_t v_tid_686_; lean_object* v_traces_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_700_; 
v_tid_686_ = lean_ctor_get_uint64(v_traceState_674_, sizeof(void*)*1);
v_traces_687_ = lean_ctor_get(v_traceState_674_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v_traceState_674_);
if (v_isSharedCheck_700_ == 0)
{
v___x_689_ = v_traceState_674_;
v_isShared_690_ = v_isSharedCheck_700_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_traces_687_);
lean_dec(v_traceState_674_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_700_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_612_, v_traces_687_);
lean_dec_ref(v_traces_687_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_691_);
lean_ctor_set_uint64(v_reuseFailAlloc_699_, sizeof(void*)*1, v_tid_686_);
v___x_693_ = v_reuseFailAlloc_699_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 4, v___x_693_);
v___x_695_ = v___x_684_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_env_675_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_nextMacroScope_676_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_ngen_677_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_auxDeclNGen_678_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_698_, 5, v_cache_679_);
lean_ctor_set(v_reuseFailAlloc_698_, 6, v_messages_680_);
lean_ctor_set(v_reuseFailAlloc_698_, 7, v_infoState_681_);
lean_ctor_set(v_reuseFailAlloc_698_, 8, v_snapshotTasks_682_);
v___x_695_ = v_reuseFailAlloc_698_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_st_ref_set(v___y_618_, v___x_695_);
v___x_697_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_fst_620_);
return v___x_697_;
}
}
}
}
}
else
{
goto v___jp_666_;
}
}
else
{
goto v___jp_666_;
}
}
v___jp_702_:
{
double v___x_704_; double v___x_705_; double v___x_706_; uint8_t v___x_707_; 
v___x_704_ = lean_unbox_float(v_snd_640_);
v___x_705_ = lean_unbox_float(v_fst_639_);
v___x_706_ = lean_float_sub(v___x_704_, v___x_705_);
v___x_707_ = lean_float_decLt(v___y_703_, v___x_706_);
v___y_672_ = v___x_707_;
goto v___jp_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___boxed(lean_object* v_cls_720_, lean_object* v_collapsed_721_, lean_object* v_tag_722_, lean_object* v_opts_723_, lean_object* v_clsEnabled_724_, lean_object* v_oldTraces_725_, lean_object* v_msg_726_, lean_object* v_resStartStop_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
uint8_t v_collapsed_boxed_733_; uint8_t v_clsEnabled_boxed_734_; lean_object* v_res_735_; 
v_collapsed_boxed_733_ = lean_unbox(v_collapsed_721_);
v_clsEnabled_boxed_734_ = lean_unbox(v_clsEnabled_724_);
v_res_735_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(v_cls_720_, v_collapsed_boxed_733_, v_tag_722_, v_opts_723_, v_clsEnabled_boxed_734_, v_oldTraces_725_, v_msg_726_, v_resStartStop_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec_ref(v_opts_723_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_ref_742_; lean_object* v___x_743_; lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_ref_742_ = lean_ctor_get(v___y_739_, 5);
v___x_743_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_msg_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_752_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
lean_inc(v_ref_742_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v_ref_742_);
lean_ctor_set(v___x_748_, 1, v_a_744_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 1);
lean_ctor_set(v___x_746_, 0, v___x_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_759_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(lean_object* v_keys_760_, lean_object* v_i_761_, lean_object* v_k_762_){
_start:
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = lean_array_get_size(v_keys_760_);
v___x_764_ = lean_nat_dec_lt(v_i_761_, v___x_763_);
if (v___x_764_ == 0)
{
lean_dec(v_i_761_);
return v___x_764_;
}
else
{
lean_object* v_k_x27_765_; uint8_t v___x_766_; 
v_k_x27_765_ = lean_array_fget_borrowed(v_keys_760_, v_i_761_);
v___x_766_ = l_Lean_instBEqMVarId_beq(v_k_762_, v_k_x27_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(1u);
v___x_768_ = lean_nat_add(v_i_761_, v___x_767_);
lean_dec(v_i_761_);
v_i_761_ = v___x_768_;
goto _start;
}
else
{
lean_dec(v_i_761_);
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg___boxed(lean_object* v_keys_770_, lean_object* v_i_771_, lean_object* v_k_772_){
_start:
{
uint8_t v_res_773_; lean_object* v_r_774_; 
v_res_773_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(v_keys_770_, v_i_771_, v_k_772_);
lean_dec(v_k_772_);
lean_dec_ref(v_keys_770_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0(void){
_start:
{
size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; 
v___x_775_ = ((size_t)5ULL);
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_shift_left(v___x_776_, v___x_775_);
return v___x_777_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1(void){
_start:
{
size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; 
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0);
v___x_780_ = lean_usize_sub(v___x_779_, v___x_778_);
return v___x_780_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(lean_object* v_x_781_, size_t v_x_782_, lean_object* v_x_783_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
lean_object* v_es_784_; lean_object* v___x_785_; size_t v___x_786_; size_t v___x_787_; size_t v___x_788_; lean_object* v_j_789_; lean_object* v___x_790_; 
v_es_784_ = lean_ctor_get(v_x_781_, 0);
lean_inc_ref(v_es_784_);
lean_dec_ref(v_x_781_);
v___x_785_ = lean_box(2);
v___x_786_ = ((size_t)5ULL);
v___x_787_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1);
v___x_788_ = lean_usize_land(v_x_782_, v___x_787_);
v_j_789_ = lean_usize_to_nat(v___x_788_);
v___x_790_ = lean_array_get(v___x_785_, v_es_784_, v_j_789_);
lean_dec(v_j_789_);
lean_dec_ref(v_es_784_);
switch(lean_obj_tag(v___x_790_))
{
case 0:
{
lean_object* v_key_791_; uint8_t v___x_792_; 
v_key_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_key_791_);
lean_dec_ref(v___x_790_);
v___x_792_ = l_Lean_instBEqMVarId_beq(v_x_783_, v_key_791_);
lean_dec(v_key_791_);
return v___x_792_;
}
case 1:
{
lean_object* v_node_793_; size_t v___x_794_; 
v_node_793_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_node_793_);
lean_dec_ref(v___x_790_);
v___x_794_ = lean_usize_shift_right(v_x_782_, v___x_786_);
v_x_781_ = v_node_793_;
v_x_782_ = v___x_794_;
goto _start;
}
default: 
{
uint8_t v___x_796_; 
v___x_796_ = 0;
return v___x_796_;
}
}
}
else
{
lean_object* v_ks_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_ks_797_ = lean_ctor_get(v_x_781_, 0);
lean_inc_ref(v_ks_797_);
lean_dec_ref(v_x_781_);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(v_ks_797_, v___x_798_, v_x_783_);
lean_dec_ref(v_ks_797_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
size_t v_x_71750__boxed_803_; uint8_t v_res_804_; lean_object* v_r_805_; 
v_x_71750__boxed_803_ = lean_unbox_usize(v_x_801_);
lean_dec(v_x_801_);
v_res_804_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(v_x_800_, v_x_71750__boxed_803_, v_x_802_);
lean_dec(v_x_802_);
v_r_805_ = lean_box(v_res_804_);
return v_r_805_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(lean_object* v_x_806_, lean_object* v_x_807_){
_start:
{
uint64_t v___x_808_; size_t v___x_809_; uint8_t v___x_810_; 
v___x_808_ = l_Lean_instHashableMVarId_hash(v_x_807_);
v___x_809_ = lean_uint64_to_usize(v___x_808_);
v___x_810_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(v_x_806_, v___x_809_, v_x_807_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg___boxed(lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(v_x_811_, v_x_812_);
lean_dec(v_x_812_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(lean_object* v_mvarId_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; lean_object* v_mctx_819_; lean_object* v_eAssignment_820_; uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_818_ = lean_st_ref_get(v___y_816_);
v_mctx_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc_ref(v_mctx_819_);
lean_dec(v___x_818_);
v_eAssignment_820_ = lean_ctor_get(v_mctx_819_, 7);
lean_inc_ref(v_eAssignment_820_);
lean_dec_ref(v_mctx_819_);
v___x_821_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(v_eAssignment_820_, v_mvarId_815_);
v___x_822_ = lean_box(v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg___boxed(lean_object* v_mvarId_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(v_mvarId_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec(v_mvarId_824_);
return v_res_827_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_830_ = l_Lean_stringToMessageData(v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_head_831_, lean_object* v_x_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_838_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v_head_831_);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_head_842_, lean_object* v_x_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_head_842_, v_x_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v_x_843_);
return v_res_849_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(lean_object* v_e_850_){
_start:
{
if (lean_obj_tag(v_e_850_) == 0)
{
uint8_t v___x_851_; 
v___x_851_ = 2;
return v___x_851_;
}
else
{
uint8_t v___x_852_; 
v___x_852_ = 0;
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4___boxed(lean_object* v_e_853_){
_start:
{
uint8_t v_res_854_; lean_object* v_r_855_; 
v_res_854_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(v_e_853_);
lean_dec_ref(v_e_853_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object* v_cls_856_, uint8_t v_collapsed_857_, lean_object* v_tag_858_, lean_object* v_opts_859_, uint8_t v_clsEnabled_860_, lean_object* v_oldTraces_861_, lean_object* v_msg_862_, lean_object* v_resStartStop_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_fst_869_; lean_object* v_snd_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_968_; 
v_fst_869_ = lean_ctor_get(v_resStartStop_863_, 0);
v_snd_870_ = lean_ctor_get(v_resStartStop_863_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v_resStartStop_863_);
if (v_isSharedCheck_968_ == 0)
{
v___x_872_ = v_resStartStop_863_;
v_isShared_873_ = v_isSharedCheck_968_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_snd_870_);
lean_inc(v_fst_869_);
lean_dec(v_resStartStop_863_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_968_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v_data_877_; lean_object* v_fst_888_; lean_object* v_snd_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_967_; 
v_fst_888_ = lean_ctor_get(v_snd_870_, 0);
v_snd_889_ = lean_ctor_get(v_snd_870_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v_snd_870_);
if (v_isSharedCheck_967_ == 0)
{
v___x_891_ = v_snd_870_;
v_isShared_892_ = v_isSharedCheck_967_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_snd_889_);
lean_inc(v_fst_888_);
lean_dec(v_snd_870_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_967_;
goto v_resetjp_890_;
}
v___jp_874_:
{
lean_object* v___x_878_; 
lean_inc(v___y_876_);
v___x_878_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(v_oldTraces_861_, v_data_877_, v___y_876_, v___y_875_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_879_; 
lean_dec_ref(v___x_878_);
v___x_879_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_fst_869_);
return v___x_879_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec(v_fst_869_);
v_a_880_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_878_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_878_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
v_resetjp_890_:
{
lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___y_896_; lean_object* v_a_897_; uint8_t v___y_921_; double v___y_952_; 
v___x_893_ = l_Lean_trace_profiler;
v___x_894_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_opts_859_, v___x_893_);
if (v___x_894_ == 0)
{
v___y_921_ = v___x_894_;
goto v___jp_920_;
}
else
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = l_Lean_trace_profiler_useHeartbeats;
v___x_958_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_opts_859_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; double v___x_961_; double v___x_962_; double v___x_963_; 
v___x_959_ = l_Lean_trace_profiler_threshold;
v___x_960_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(v_opts_859_, v___x_959_);
v___x_961_ = lean_float_of_nat(v___x_960_);
v___x_962_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5);
v___x_963_ = lean_float_div(v___x_961_, v___x_962_);
v___y_952_ = v___x_963_;
goto v___jp_951_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; double v___x_966_; 
v___x_964_ = l_Lean_trace_profiler_threshold;
v___x_965_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(v_opts_859_, v___x_964_);
v___x_966_ = lean_float_of_nat(v___x_965_);
v___y_952_ = v___x_966_;
goto v___jp_951_;
}
}
v___jp_895_:
{
uint8_t v_result_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v_result_898_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(v_fst_869_);
v___x_899_ = l_Lean_TraceResult_toEmoji(v_result_898_);
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
v___x_901_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 7);
lean_ctor_set(v___x_891_, 1, v___x_901_);
lean_ctor_set(v___x_891_, 0, v___x_900_);
v___x_903_ = v___x_891_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_914_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v_m_905_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set_tag(v___x_872_, 7);
lean_ctor_set(v___x_872_, 1, v_a_897_);
lean_ctor_set(v___x_872_, 0, v___x_903_);
v_m_905_ = v___x_872_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_a_897_);
v_m_905_ = v_reuseFailAlloc_913_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; lean_object* v___x_907_; double v___x_908_; lean_object* v_data_909_; 
v___x_906_ = lean_box(v_result_898_);
v___x_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
v___x_908_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2);
lean_inc_ref(v_tag_858_);
lean_inc_ref(v___x_907_);
lean_inc(v_cls_856_);
v_data_909_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_909_, 0, v_cls_856_);
lean_ctor_set(v_data_909_, 1, v___x_907_);
lean_ctor_set(v_data_909_, 2, v_tag_858_);
lean_ctor_set_float(v_data_909_, sizeof(void*)*3, v___x_908_);
lean_ctor_set_float(v_data_909_, sizeof(void*)*3 + 8, v___x_908_);
lean_ctor_set_uint8(v_data_909_, sizeof(void*)*3 + 16, v_collapsed_857_);
if (v___x_894_ == 0)
{
lean_dec_ref(v___x_907_);
lean_dec(v_snd_889_);
lean_dec(v_fst_888_);
lean_dec_ref(v_tag_858_);
lean_dec(v_cls_856_);
v___y_875_ = v_m_905_;
v___y_876_ = v___y_896_;
v_data_877_ = v_data_909_;
goto v___jp_874_;
}
else
{
lean_object* v_data_910_; double v___x_911_; double v___x_912_; 
lean_dec_ref(v_data_909_);
v_data_910_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_910_, 0, v_cls_856_);
lean_ctor_set(v_data_910_, 1, v___x_907_);
lean_ctor_set(v_data_910_, 2, v_tag_858_);
v___x_911_ = lean_unbox_float(v_fst_888_);
lean_dec(v_fst_888_);
lean_ctor_set_float(v_data_910_, sizeof(void*)*3, v___x_911_);
v___x_912_ = lean_unbox_float(v_snd_889_);
lean_dec(v_snd_889_);
lean_ctor_set_float(v_data_910_, sizeof(void*)*3 + 8, v___x_912_);
lean_ctor_set_uint8(v_data_910_, sizeof(void*)*3 + 16, v_collapsed_857_);
v___y_875_ = v_m_905_;
v___y_876_ = v___y_896_;
v_data_877_ = v_data_910_;
goto v___jp_874_;
}
}
}
}
v___jp_915_:
{
lean_object* v_ref_916_; lean_object* v___x_917_; 
v_ref_916_ = lean_ctor_get(v___y_866_, 5);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc_ref(v___y_864_);
lean_inc(v_fst_869_);
v___x_917_ = lean_apply_6(v_msg_862_, v_fst_869_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref(v___x_917_);
v___y_896_ = v_ref_916_;
v_a_897_ = v_a_918_;
goto v___jp_895_;
}
else
{
lean_object* v___x_919_; 
lean_dec_ref(v___x_917_);
v___x_919_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4);
v___y_896_ = v_ref_916_;
v_a_897_ = v___x_919_;
goto v___jp_895_;
}
}
v___jp_920_:
{
if (v_clsEnabled_860_ == 0)
{
if (v___y_921_ == 0)
{
lean_object* v___x_922_; lean_object* v_traceState_923_; lean_object* v_env_924_; lean_object* v_nextMacroScope_925_; lean_object* v_ngen_926_; lean_object* v_auxDeclNGen_927_; lean_object* v_cache_928_; lean_object* v_messages_929_; lean_object* v_infoState_930_; lean_object* v_snapshotTasks_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_950_; 
lean_del_object(v___x_891_);
lean_dec(v_snd_889_);
lean_dec(v_fst_888_);
lean_del_object(v___x_872_);
lean_dec_ref(v_msg_862_);
lean_dec_ref(v_tag_858_);
lean_dec(v_cls_856_);
v___x_922_ = lean_st_ref_take(v___y_867_);
v_traceState_923_ = lean_ctor_get(v___x_922_, 4);
v_env_924_ = lean_ctor_get(v___x_922_, 0);
v_nextMacroScope_925_ = lean_ctor_get(v___x_922_, 1);
v_ngen_926_ = lean_ctor_get(v___x_922_, 2);
v_auxDeclNGen_927_ = lean_ctor_get(v___x_922_, 3);
v_cache_928_ = lean_ctor_get(v___x_922_, 5);
v_messages_929_ = lean_ctor_get(v___x_922_, 6);
v_infoState_930_ = lean_ctor_get(v___x_922_, 7);
v_snapshotTasks_931_ = lean_ctor_get(v___x_922_, 8);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_950_ == 0)
{
v___x_933_ = v___x_922_;
v_isShared_934_ = v_isSharedCheck_950_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_snapshotTasks_931_);
lean_inc(v_infoState_930_);
lean_inc(v_messages_929_);
lean_inc(v_cache_928_);
lean_inc(v_traceState_923_);
lean_inc(v_auxDeclNGen_927_);
lean_inc(v_ngen_926_);
lean_inc(v_nextMacroScope_925_);
lean_inc(v_env_924_);
lean_dec(v___x_922_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_950_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
uint64_t v_tid_935_; lean_object* v_traces_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_949_; 
v_tid_935_ = lean_ctor_get_uint64(v_traceState_923_, sizeof(void*)*1);
v_traces_936_ = lean_ctor_get(v_traceState_923_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_traceState_923_);
if (v_isSharedCheck_949_ == 0)
{
v___x_938_ = v_traceState_923_;
v_isShared_939_ = v_isSharedCheck_949_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_traces_936_);
lean_dec(v_traceState_923_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_949_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_940_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_861_, v_traces_936_);
lean_dec_ref(v_traces_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_940_);
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_940_);
lean_ctor_set_uint64(v_reuseFailAlloc_948_, sizeof(void*)*1, v_tid_935_);
v___x_942_ = v_reuseFailAlloc_948_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 4, v___x_942_);
v___x_944_ = v___x_933_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_env_924_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_nextMacroScope_925_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_ngen_926_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_auxDeclNGen_927_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_947_, 5, v_cache_928_);
lean_ctor_set(v_reuseFailAlloc_947_, 6, v_messages_929_);
lean_ctor_set(v_reuseFailAlloc_947_, 7, v_infoState_930_);
lean_ctor_set(v_reuseFailAlloc_947_, 8, v_snapshotTasks_931_);
v___x_944_ = v_reuseFailAlloc_947_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_st_ref_set(v___y_867_, v___x_944_);
v___x_946_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_fst_869_);
return v___x_946_;
}
}
}
}
}
else
{
goto v___jp_915_;
}
}
else
{
goto v___jp_915_;
}
}
v___jp_951_:
{
double v___x_953_; double v___x_954_; double v___x_955_; uint8_t v___x_956_; 
v___x_953_ = lean_unbox_float(v_snd_889_);
v___x_954_ = lean_unbox_float(v_fst_888_);
v___x_955_ = lean_float_sub(v___x_953_, v___x_954_);
v___x_956_ = lean_float_decLt(v___y_952_, v___x_955_);
v___y_921_ = v___x_956_;
goto v___jp_920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object* v_cls_969_, lean_object* v_collapsed_970_, lean_object* v_tag_971_, lean_object* v_opts_972_, lean_object* v_clsEnabled_973_, lean_object* v_oldTraces_974_, lean_object* v_msg_975_, lean_object* v_resStartStop_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
uint8_t v_collapsed_boxed_982_; uint8_t v_clsEnabled_boxed_983_; lean_object* v_res_984_; 
v_collapsed_boxed_982_ = lean_unbox(v_collapsed_970_);
v_clsEnabled_boxed_983_ = lean_unbox(v_clsEnabled_973_);
v_res_984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_cls_969_, v_collapsed_boxed_982_, v_tag_971_, v_opts_972_, v_clsEnabled_boxed_983_, v_oldTraces_974_, v_msg_975_, v_resStartStop_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec_ref(v_opts_972_);
return v_res_984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object* v_head_988_, lean_object* v_x_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1006_; 
v___x_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_995_, 0, v_head_988_);
v___x_996_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v___x_995_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1006_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1006_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1001_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v_a_997_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1002_);
v___x_1004_ = v___x_999_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object* v_head_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(v_head_1007_, v_x_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec_ref(v_x_1008_);
return v_res_1014_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_1015_; double v___x_1016_; 
v___x_1015_ = lean_unsigned_to_nat(1000000000u);
v___x_1016_ = lean_float_of_nat(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* v_tail_1025_, lean_object* v_cfg_1026_, lean_object* v_trace_1027_, lean_object* v_next_1028_, lean_object* v_goals_1029_, lean_object* v_n_1030_, lean_object* v_acc_1031_, lean_object* v_r_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_1025_, v_cfg_1026_, v_trace_1027_, v_next_1028_, v_goals_1029_, v_n_1030_, v_acc_1031_, v_r_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_1039_, lean_object* v_trace_1040_, lean_object* v_next_1041_, lean_object* v_goals_1042_, lean_object* v_n_1043_, lean_object* v_curr_1044_, lean_object* v_acc_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___y_1052_; uint8_t v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; uint8_t v___y_1058_; lean_object* v_a_1059_; lean_object* v___y_1069_; uint8_t v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; uint8_t v___y_1075_; lean_object* v_a_1076_; lean_object* v___y_1089_; uint8_t v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; uint8_t v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; uint8_t v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; uint8_t v___y_1143_; lean_object* v_a_1144_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; uint8_t v___y_1158_; uint8_t v___y_1159_; lean_object* v___y_1160_; lean_object* v_a_1161_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; uint8_t v___y_1168_; uint8_t v___y_1169_; lean_object* v___y_1170_; lean_object* v_a_1171_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; uint8_t v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; uint8_t v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; uint8_t v___y_1188_; lean_object* v___y_1189_; uint8_t v___y_1190_; lean_object* v___y_1191_; lean_object* v_a_1192_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; uint8_t v___y_1208_; lean_object* v___y_1209_; uint8_t v___y_1210_; lean_object* v___y_1211_; lean_object* v_a_1212_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; uint8_t v___y_1218_; lean_object* v___y_1219_; uint8_t v___y_1220_; lean_object* v___y_1221_; lean_object* v_a_1222_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; uint8_t v___y_1228_; lean_object* v___y_1229_; uint8_t v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v_zero_1235_; uint8_t v_isZero_1236_; 
v_zero_1235_ = lean_unsigned_to_nat(0u);
v_isZero_1236_ = lean_nat_dec_eq(v_n_1043_, v_zero_1235_);
if (v_isZero_1236_ == 1)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_acc_1045_);
lean_dec(v_curr_1044_);
lean_dec(v_n_1043_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
v___x_1237_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1238_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1237_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1238_;
}
else
{
lean_object* v_proc_1239_; lean_object* v_suspend_1240_; lean_object* v_discharge_1241_; lean_object* v___f_1242_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; uint8_t v___y_1247_; lean_object* v___y_1248_; uint8_t v___y_1249_; lean_object* v_a_1250_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; uint8_t v___y_1266_; lean_object* v___y_1267_; uint8_t v___y_1268_; lean_object* v_a_1269_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; uint8_t v___y_1282_; lean_object* v___y_1283_; uint8_t v___y_1284_; lean_object* v___y_1285_; lean_object* v___f_1326_; uint8_t v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; uint8_t v___y_1332_; lean_object* v___f_1368_; lean_object* v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; uint8_t v___y_1376_; lean_object* v___y_1377_; uint8_t v___y_1378_; lean_object* v___y_1379_; lean_object* v_a_1380_; lean_object* v___y_1390_; uint8_t v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; uint8_t v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1398_; lean_object* v___y_1399_; lean_object* v_a_1400_; uint8_t v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; uint8_t v___y_1418_; uint8_t v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; uint8_t v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___f_1464_; uint8_t v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; uint8_t v___y_1473_; lean_object* v___y_1474_; uint8_t v___y_1475_; lean_object* v_a_1476_; uint8_t v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; uint8_t v___y_1496_; lean_object* v___y_1497_; uint8_t v___y_1498_; lean_object* v_a_1499_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; uint8_t v___y_1514_; uint8_t v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; uint8_t v___y_1518_; lean_object* v_a_1519_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; uint8_t v___y_1536_; uint8_t v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; uint8_t v___y_1540_; lean_object* v___y_1541_; lean_object* v_a_1542_; uint8_t v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; uint8_t v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; uint8_t v___y_1558_; uint8_t v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1604_; lean_object* v___y_1605_; uint8_t v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; uint8_t v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; uint8_t v___y_1613_; lean_object* v_a_1614_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; uint8_t v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; uint8_t v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; uint8_t v___y_1633_; lean_object* v_a_1634_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; uint8_t v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; uint8_t v___y_1655_; uint8_t v___y_1656_; lean_object* v_a_1657_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; uint8_t v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; uint8_t v___y_1675_; uint8_t v___y_1676_; lean_object* v_a_1677_; uint8_t v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; uint8_t v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; uint8_t v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; uint8_t v___y_1700_; lean_object* v___y_1701_; uint8_t v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; uint8_t v___y_1749_; lean_object* v___y_1750_; uint8_t v___y_1751_; lean_object* v_a_1752_; uint8_t v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; uint8_t v___y_1769_; lean_object* v___y_1770_; uint8_t v___y_1771_; lean_object* v_a_1772_; uint8_t v___y_1785_; uint8_t v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; uint8_t v___y_1792_; lean_object* v___y_1793_; uint8_t v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1837_; uint8_t v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; uint8_t v___y_1842_; lean_object* v_a_1843_; lean_object* v___y_1856_; uint8_t v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; uint8_t v___y_1861_; lean_object* v_a_1862_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; uint8_t v___y_1875_; lean_object* v___y_1876_; uint8_t v___y_1877_; lean_object* v_a_1878_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; uint8_t v___y_1894_; lean_object* v___y_1895_; uint8_t v___y_1896_; lean_object* v_a_1897_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; lean_object* v___y_1911_; uint8_t v___y_1912_; lean_object* v___y_1913_; lean_object* v_one_1954_; lean_object* v_n_1955_; uint8_t v___y_1957_; lean_object* v___y_1958_; uint8_t v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; uint8_t v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; uint8_t v___y_2009_; lean_object* v___y_2010_; uint8_t v___y_2011_; uint8_t v___y_2039_; uint8_t v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; uint8_t v___y_2045_; lean_object* v___y_2046_; uint8_t v___y_2047_; lean_object* v___y_2048_; uint8_t v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; uint8_t v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; uint8_t v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; uint8_t v___y_2101_; uint8_t v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; uint8_t v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; uint8_t v___y_2132_; uint8_t v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; uint8_t v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; uint8_t v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; uint8_t v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; uint8_t v___y_2188_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; uint8_t v___y_2220_; uint8_t v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; uint8_t v___y_2273_; lean_object* v_a_2291_; lean_object* v___y_2396_; lean_object* v___x_2406_; 
v_proc_1239_ = lean_ctor_get(v_cfg_1039_, 1);
v_suspend_1240_ = lean_ctor_get(v_cfg_1039_, 2);
v_discharge_1241_ = lean_ctor_get(v_cfg_1039_, 3);
v___f_1242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1954_ = lean_unsigned_to_nat(1u);
v_n_1955_ = lean_nat_sub(v_n_1043_, v_one_1954_);
lean_dec(v_n_1043_);
lean_inc_ref(v_proc_1239_);
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v_curr_1044_);
lean_inc(v_goals_1042_);
v___x_2406_ = lean_apply_7(v_proc_1239_, v_goals_1042_, v_curr_1044_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___x_2406_);
v_a_2291_ = v_a_2407_;
goto v___jp_2290_;
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2480_; 
v_a_2408_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2410_ = v___x_2406_;
v_isShared_2411_ = v_isSharedCheck_2480_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2406_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2480_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___f_2412_; lean_object* v___y_2414_; lean_object* v___y_2415_; uint8_t v___y_2416_; uint8_t v___y_2417_; uint8_t v___y_2454_; uint8_t v___x_2478_; 
lean_inc(v_a_2408_);
v___f_2412_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(v___f_2412_, 0, v_a_2408_);
v___x_2478_ = l_Lean_Exception_isInterrupt(v_a_2408_);
if (v___x_2478_ == 0)
{
uint8_t v___x_2479_; 
lean_inc(v_a_2408_);
v___x_2479_ = l_Lean_Exception_isRuntime(v_a_2408_);
v___y_2454_ = v___x_2479_;
goto v___jp_2453_;
}
else
{
v___y_2454_ = v___x_2478_;
goto v___jp_2453_;
}
v___jp_2413_:
{
lean_object* v___x_2418_; lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2452_; 
v___x_2418_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2452_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2452_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2424_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2414_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2425_ = lean_io_mono_nanos_now();
v___x_2426_ = lean_io_mono_nanos_now();
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v_a_2408_);
v___x_2428_ = v___x_2421_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2408_);
v___x_2428_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
double v___x_2429_; double v___x_2430_; double v___x_2431_; double v___x_2432_; double v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2429_ = lean_float_of_nat(v___x_2425_);
v___x_2430_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2431_ = lean_float_div(v___x_2429_, v___x_2430_);
v___x_2432_ = lean_float_of_nat(v___x_2426_);
v___x_2433_ = lean_float_div(v___x_2432_, v___x_2430_);
v___x_2434_ = lean_box_float(v___x_2431_);
v___x_2435_ = lean_box_float(v___x_2433_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2428_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
lean_inc(v_trace_1040_);
v___x_2438_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(v_trace_1040_, v___y_2417_, v___y_2415_, v___y_2414_, v___y_2416_, v_a_2419_, v___f_2412_, v___x_2437_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_2396_ = v___x_2438_;
goto v___jp_2395_;
}
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2440_ = lean_io_get_num_heartbeats();
v___x_2441_ = lean_io_get_num_heartbeats();
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v_a_2408_);
v___x_2443_ = v___x_2421_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2408_);
v___x_2443_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
double v___x_2444_; double v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2444_ = lean_float_of_nat(v___x_2440_);
v___x_2445_ = lean_float_of_nat(v___x_2441_);
v___x_2446_ = lean_box_float(v___x_2444_);
v___x_2447_ = lean_box_float(v___x_2445_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2443_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
lean_inc(v_trace_1040_);
v___x_2450_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(v_trace_1040_, v___y_2417_, v___y_2415_, v___y_2414_, v___y_2416_, v_a_2419_, v___f_2412_, v___x_2449_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_2396_ = v___x_2450_;
goto v___jp_2395_;
}
}
}
}
v___jp_2453_:
{
if (v___y_2454_ == 0)
{
lean_object* v_options_2455_; uint8_t v_hasTrace_2456_; 
v_options_2455_ = lean_ctor_get(v_a_1048_, 2);
v_hasTrace_2456_ = lean_ctor_get_uint8(v_options_2455_, sizeof(void*)*1);
if (v_hasTrace_2456_ == 0)
{
lean_object* v___x_2458_; 
lean_dec_ref(v___f_2412_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_curr_1044_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
if (v_isShared_2411_ == 0)
{
v___x_2458_ = v___x_2410_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2408_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
else
{
lean_object* v___x_2460_; lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2474_; 
lean_del_object(v___x_2410_);
lean_inc(v_trace_1040_);
v___x_2460_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2474_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2474_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
v___x_2466_ = lean_unbox(v_a_2461_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; uint8_t v___x_2468_; 
v___x_2467_ = l_Lean_trace_profiler;
v___x_2468_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_2455_, v___x_2467_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2470_; 
lean_dec(v_a_2461_);
lean_dec_ref(v___f_2412_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_curr_1044_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set_tag(v___x_2463_, 1);
lean_ctor_set(v___x_2463_, 0, v_a_2408_);
v___x_2470_ = v___x_2463_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2408_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
else
{
uint8_t v___x_2472_; 
lean_del_object(v___x_2463_);
v___x_2472_ = lean_unbox(v_a_2461_);
lean_dec(v_a_2461_);
v___y_2414_ = v_options_2455_;
v___y_2415_ = v___x_2465_;
v___y_2416_ = v___x_2472_;
v___y_2417_ = v_hasTrace_2456_;
goto v___jp_2413_;
}
}
else
{
uint8_t v___x_2473_; 
lean_del_object(v___x_2463_);
v___x_2473_ = lean_unbox(v_a_2461_);
lean_dec(v_a_2461_);
v___y_2414_ = v_options_2455_;
v___y_2415_ = v___x_2465_;
v___y_2416_ = v___x_2473_;
v___y_2417_ = v_hasTrace_2456_;
goto v___jp_2413_;
}
}
}
}
else
{
lean_object* v___x_2476_; 
lean_dec_ref(v___f_2412_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_curr_1044_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
if (v_isShared_2411_ == 0)
{
v___x_2476_ = v___x_2410_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2408_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
v___jp_1243_:
{
lean_object* v___x_1251_; double v___x_1252_; double v___x_1253_; double v___x_1254_; double v___x_1255_; double v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1251_ = lean_io_mono_nanos_now();
v___x_1252_ = lean_float_of_nat(v___y_1246_);
v___x_1253_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1254_ = lean_float_div(v___x_1252_, v___x_1253_);
v___x_1255_ = lean_float_of_nat(v___x_1251_);
v___x_1256_ = lean_float_div(v___x_1255_, v___x_1253_);
v___x_1257_ = lean_box_float(v___x_1254_);
v___x_1258_ = lean_box_float(v___x_1256_);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_a_1250_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1249_, v___y_1248_, v___y_1245_, v___y_1247_, v___y_1244_, v___f_1242_, v___x_1260_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1261_;
}
v___jp_1262_:
{
lean_object* v___x_1270_; double v___x_1271_; double v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1270_ = lean_io_get_num_heartbeats();
v___x_1271_ = lean_float_of_nat(v___y_1265_);
v___x_1272_ = lean_float_of_nat(v___x_1270_);
v___x_1273_ = lean_box_float(v___x_1271_);
v___x_1274_ = lean_box_float(v___x_1272_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_a_1269_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1268_, v___y_1267_, v___y_1264_, v___y_1266_, v___y_1263_, v___f_1242_, v___x_1276_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1277_;
}
v___jp_1278_:
{
lean_object* v___x_1286_; lean_object* v_a_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1286_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref(v___x_1286_);
v___x_1288_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1289_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_1281_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1040_);
v___x_1291_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1280_, v___y_1285_, v___y_1279_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set_tag(v___x_1294_, 1);
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
v___y_1244_ = v_a_1287_;
v___y_1245_ = v___y_1281_;
v___y_1246_ = v___x_1290_;
v___y_1247_ = v___y_1284_;
v___y_1248_ = v___y_1283_;
v___y_1249_ = v___y_1282_;
v_a_1250_ = v___x_1297_;
goto v___jp_1243_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v_a_1300_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1291_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1291_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 0);
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
v___y_1244_ = v_a_1287_;
v___y_1245_ = v___y_1281_;
v___y_1246_ = v___x_1290_;
v___y_1247_ = v___y_1284_;
v___y_1248_ = v___y_1283_;
v___y_1249_ = v___y_1282_;
v_a_1250_ = v___x_1305_;
goto v___jp_1243_;
}
}
}
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1040_);
v___x_1309_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1280_, v___y_1285_, v___y_1279_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set_tag(v___x_1312_, 1);
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
v___y_1263_ = v_a_1287_;
v___y_1264_ = v___y_1281_;
v___y_1265_ = v___x_1308_;
v___y_1266_ = v___y_1284_;
v___y_1267_ = v___y_1283_;
v___y_1268_ = v___y_1282_;
v_a_1269_ = v___x_1315_;
goto v___jp_1262_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_a_1318_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1309_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1309_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 0);
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
v___y_1263_ = v_a_1287_;
v___y_1264_ = v___y_1281_;
v___y_1265_ = v___x_1308_;
v___y_1266_ = v___y_1284_;
v___y_1267_ = v___y_1283_;
v___y_1268_ = v___y_1282_;
v_a_1269_ = v___x_1323_;
goto v___jp_1262_;
}
}
}
}
}
v___jp_1327_:
{
lean_object* v___x_1333_; lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1367_; 
v___x_1333_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1367_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1367_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1339_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_1330_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1340_ = lean_io_mono_nanos_now();
v___x_1341_ = lean_io_mono_nanos_now();
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 1);
lean_ctor_set(v___x_1336_, 0, v___y_1329_);
v___x_1343_ = v___x_1336_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___y_1329_);
v___x_1343_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
double v___x_1344_; double v___x_1345_; double v___x_1346_; double v___x_1347_; double v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1344_ = lean_float_of_nat(v___x_1340_);
v___x_1345_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1346_ = lean_float_div(v___x_1344_, v___x_1345_);
v___x_1347_ = lean_float_of_nat(v___x_1341_);
v___x_1348_ = lean_float_div(v___x_1347_, v___x_1345_);
v___x_1349_ = lean_box_float(v___x_1346_);
v___x_1350_ = lean_box_float(v___x_1348_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1349_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1343_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1328_, v___y_1331_, v___y_1330_, v___y_1332_, v_a_1334_, v___f_1326_, v___x_1352_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1353_;
}
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1355_ = lean_io_get_num_heartbeats();
v___x_1356_ = lean_io_get_num_heartbeats();
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 1);
lean_ctor_set(v___x_1336_, 0, v___y_1329_);
v___x_1358_ = v___x_1336_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___y_1329_);
v___x_1358_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
double v___x_1359_; double v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1359_ = lean_float_of_nat(v___x_1355_);
v___x_1360_ = lean_float_of_nat(v___x_1356_);
v___x_1361_ = lean_box_float(v___x_1359_);
v___x_1362_ = lean_box_float(v___x_1360_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1358_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1328_, v___y_1331_, v___y_1330_, v___y_1332_, v_a_1334_, v___f_1326_, v___x_1364_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1365_;
}
}
}
}
v___jp_1369_:
{
lean_object* v___x_1381_; double v___x_1382_; double v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1381_ = lean_io_get_num_heartbeats();
v___x_1382_ = lean_float_of_nat(v___y_1371_);
v___x_1383_ = lean_float_of_nat(v___x_1381_);
v___x_1384_ = lean_box_float(v___x_1382_);
v___x_1385_ = lean_box_float(v___x_1383_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_a_1380_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
lean_inc_ref(v___y_1377_);
lean_inc(v_trace_1040_);
v___x_1388_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1378_, v___y_1377_, v___y_1370_, v___y_1372_, v___y_1379_, v___f_1368_, v___x_1387_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1174_ = v___y_1370_;
v___y_1175_ = v___y_1373_;
v___y_1176_ = v___y_1374_;
v___y_1177_ = v___y_1376_;
v___y_1178_ = v___y_1375_;
v___y_1179_ = v___y_1377_;
v___y_1180_ = v___y_1378_;
v___y_1181_ = v___x_1388_;
goto v___jp_1173_;
}
v___jp_1389_:
{
lean_object* v___x_1401_; double v___x_1402_; double v___x_1403_; double v___x_1404_; double v___x_1405_; double v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1401_ = lean_io_mono_nanos_now();
v___x_1402_ = lean_float_of_nat(v___y_1393_);
v___x_1403_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1404_ = lean_float_div(v___x_1402_, v___x_1403_);
v___x_1405_ = lean_float_of_nat(v___x_1401_);
v___x_1406_ = lean_float_div(v___x_1405_, v___x_1403_);
v___x_1407_ = lean_box_float(v___x_1404_);
v___x_1408_ = lean_box_float(v___x_1406_);
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v_a_1400_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
lean_inc_ref(v___y_1397_);
lean_inc(v_trace_1040_);
v___x_1411_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1398_, v___y_1397_, v___y_1390_, v___y_1391_, v___y_1399_, v___f_1368_, v___x_1410_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1174_ = v___y_1390_;
v___y_1175_ = v___y_1392_;
v___y_1176_ = v___y_1394_;
v___y_1177_ = v___y_1396_;
v___y_1178_ = v___y_1395_;
v___y_1179_ = v___y_1397_;
v___y_1180_ = v___y_1398_;
v___y_1181_ = v___x_1411_;
goto v___jp_1173_;
}
v___jp_1412_:
{
lean_object* v___x_1425_; 
v___x_1425_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
if (v___y_1413_ == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1040_);
v___x_1428_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1416_, v___y_1424_, v___y_1420_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 1);
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
v___y_1390_ = v___y_1414_;
v___y_1391_ = v___y_1419_;
v___y_1392_ = v___y_1415_;
v___y_1393_ = v___x_1427_;
v___y_1394_ = v___y_1421_;
v___y_1395_ = v___y_1417_;
v___y_1396_ = v___y_1422_;
v___y_1397_ = v___y_1423_;
v___y_1398_ = v___y_1418_;
v___y_1399_ = v_a_1426_;
v_a_1400_ = v___x_1434_;
goto v___jp_1389_;
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
v_a_1437_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1428_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1428_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set_tag(v___x_1439_, 0);
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
v___y_1390_ = v___y_1414_;
v___y_1391_ = v___y_1419_;
v___y_1392_ = v___y_1415_;
v___y_1393_ = v___x_1427_;
v___y_1394_ = v___y_1421_;
v___y_1395_ = v___y_1417_;
v___y_1396_ = v___y_1422_;
v___y_1397_ = v___y_1423_;
v___y_1398_ = v___y_1418_;
v___y_1399_ = v_a_1426_;
v_a_1400_ = v___x_1442_;
goto v___jp_1389_;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v_a_1445_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1445_);
lean_dec_ref(v___x_1425_);
v___x_1446_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1040_);
v___x_1447_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1416_, v___y_1424_, v___y_1420_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set_tag(v___x_1450_, 1);
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
v___y_1370_ = v___y_1414_;
v___y_1371_ = v___x_1446_;
v___y_1372_ = v___y_1419_;
v___y_1373_ = v___y_1415_;
v___y_1374_ = v___y_1421_;
v___y_1375_ = v___y_1417_;
v___y_1376_ = v___y_1422_;
v___y_1377_ = v___y_1423_;
v___y_1378_ = v___y_1418_;
v___y_1379_ = v_a_1445_;
v_a_1380_ = v___x_1453_;
goto v___jp_1369_;
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
v_a_1456_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1447_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1447_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
lean_ctor_set_tag(v___x_1458_, 0);
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
v___y_1370_ = v___y_1414_;
v___y_1371_ = v___x_1446_;
v___y_1372_ = v___y_1419_;
v___y_1373_ = v___y_1415_;
v___y_1374_ = v___y_1421_;
v___y_1375_ = v___y_1417_;
v___y_1376_ = v___y_1422_;
v___y_1377_ = v___y_1423_;
v___y_1378_ = v___y_1418_;
v___y_1379_ = v_a_1445_;
v_a_1380_ = v___x_1461_;
goto v___jp_1369_;
}
}
}
}
}
v___jp_1465_:
{
lean_object* v___x_1477_; double v___x_1478_; double v___x_1479_; double v___x_1480_; double v___x_1481_; double v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1477_ = lean_io_mono_nanos_now();
v___x_1478_ = lean_float_of_nat(v___y_1467_);
v___x_1479_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1480_ = lean_float_div(v___x_1478_, v___x_1479_);
v___x_1481_ = lean_float_of_nat(v___x_1477_);
v___x_1482_ = lean_float_div(v___x_1481_, v___x_1479_);
v___x_1483_ = lean_box_float(v___x_1480_);
v___x_1484_ = lean_box_float(v___x_1482_);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v_a_1476_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
lean_inc_ref(v___y_1474_);
lean_inc(v_trace_1040_);
v___x_1487_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1475_, v___y_1474_, v___y_1469_, v___y_1466_, v___y_1468_, v___f_1464_, v___x_1486_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1174_ = v___y_1469_;
v___y_1175_ = v___y_1470_;
v___y_1176_ = v___y_1471_;
v___y_1177_ = v___y_1473_;
v___y_1178_ = v___y_1472_;
v___y_1179_ = v___y_1474_;
v___y_1180_ = v___y_1475_;
v___y_1181_ = v___x_1487_;
goto v___jp_1173_;
}
v___jp_1488_:
{
lean_object* v___x_1500_; double v___x_1501_; double v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1500_ = lean_io_get_num_heartbeats();
v___x_1501_ = lean_float_of_nat(v___y_1490_);
v___x_1502_ = lean_float_of_nat(v___x_1500_);
v___x_1503_ = lean_box_float(v___x_1501_);
v___x_1504_ = lean_box_float(v___x_1502_);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v_a_1499_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
lean_inc_ref(v___y_1497_);
lean_inc(v_trace_1040_);
v___x_1507_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1498_, v___y_1497_, v___y_1492_, v___y_1489_, v___y_1491_, v___f_1464_, v___x_1506_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1174_ = v___y_1492_;
v___y_1175_ = v___y_1493_;
v___y_1176_ = v___y_1494_;
v___y_1177_ = v___y_1496_;
v___y_1178_ = v___y_1495_;
v___y_1179_ = v___y_1497_;
v___y_1180_ = v___y_1498_;
v___y_1181_ = v___x_1507_;
goto v___jp_1173_;
}
v___jp_1508_:
{
lean_object* v___x_1520_; double v___x_1521_; double v___x_1522_; double v___x_1523_; double v___x_1524_; double v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1520_ = lean_io_mono_nanos_now();
v___x_1521_ = lean_float_of_nat(v___y_1511_);
v___x_1522_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1523_ = lean_float_div(v___x_1521_, v___x_1522_);
v___x_1524_ = lean_float_of_nat(v___x_1520_);
v___x_1525_ = lean_float_div(v___x_1524_, v___x_1522_);
v___x_1526_ = lean_box_float(v___x_1523_);
v___x_1527_ = lean_box_float(v___x_1525_);
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_a_1519_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
lean_inc_ref(v___y_1517_);
lean_inc(v_trace_1040_);
v___x_1530_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1518_, v___y_1517_, v___y_1510_, v___y_1514_, v___y_1509_, v___f_1242_, v___x_1529_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1225_ = v___y_1510_;
v___y_1226_ = v___y_1512_;
v___y_1227_ = v___y_1513_;
v___y_1228_ = v___y_1515_;
v___y_1229_ = v___y_1517_;
v___y_1230_ = v___y_1518_;
v___y_1231_ = v___y_1516_;
v___y_1232_ = v___x_1530_;
goto v___jp_1224_;
}
v___jp_1531_:
{
lean_object* v___x_1543_; double v___x_1544_; double v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1543_ = lean_io_get_num_heartbeats();
v___x_1544_ = lean_float_of_nat(v___y_1541_);
v___x_1545_ = lean_float_of_nat(v___x_1543_);
v___x_1546_ = lean_box_float(v___x_1544_);
v___x_1547_ = lean_box_float(v___x_1545_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v_a_1542_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
lean_inc_ref(v___y_1539_);
lean_inc(v_trace_1040_);
v___x_1550_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1540_, v___y_1539_, v___y_1533_, v___y_1536_, v___y_1532_, v___f_1242_, v___x_1549_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1225_ = v___y_1533_;
v___y_1226_ = v___y_1534_;
v___y_1227_ = v___y_1535_;
v___y_1228_ = v___y_1537_;
v___y_1229_ = v___y_1539_;
v___y_1230_ = v___y_1540_;
v___y_1231_ = v___y_1538_;
v___y_1232_ = v___x_1550_;
goto v___jp_1224_;
}
v___jp_1551_:
{
lean_object* v___x_1564_; 
v___x_1564_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
if (v___y_1552_ == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref(v___x_1564_);
v___x_1566_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1040_);
v___x_1567_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1560_, v___y_1563_, v___y_1556_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set_tag(v___x_1570_, 1);
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
v___y_1509_ = v_a_1565_;
v___y_1510_ = v___y_1553_;
v___y_1511_ = v___x_1566_;
v___y_1512_ = v___y_1554_;
v___y_1513_ = v___y_1557_;
v___y_1514_ = v___y_1558_;
v___y_1515_ = v___y_1559_;
v___y_1516_ = v___y_1561_;
v___y_1517_ = v___y_1562_;
v___y_1518_ = v___y_1555_;
v_a_1519_ = v___x_1573_;
goto v___jp_1508_;
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_a_1576_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1567_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1567_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set_tag(v___x_1578_, 0);
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
v___y_1509_ = v_a_1565_;
v___y_1510_ = v___y_1553_;
v___y_1511_ = v___x_1566_;
v___y_1512_ = v___y_1554_;
v___y_1513_ = v___y_1557_;
v___y_1514_ = v___y_1558_;
v___y_1515_ = v___y_1559_;
v___y_1516_ = v___y_1561_;
v___y_1517_ = v___y_1562_;
v___y_1518_ = v___y_1555_;
v_a_1519_ = v___x_1581_;
goto v___jp_1508_;
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_a_1584_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1584_);
lean_dec_ref(v___x_1564_);
v___x_1585_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1040_);
v___x_1586_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1560_, v___y_1563_, v___y_1556_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 1);
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
v___y_1532_ = v_a_1584_;
v___y_1533_ = v___y_1553_;
v___y_1534_ = v___y_1554_;
v___y_1535_ = v___y_1557_;
v___y_1536_ = v___y_1558_;
v___y_1537_ = v___y_1559_;
v___y_1538_ = v___y_1561_;
v___y_1539_ = v___y_1562_;
v___y_1540_ = v___y_1555_;
v___y_1541_ = v___x_1585_;
v_a_1542_ = v___x_1592_;
goto v___jp_1531_;
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
v_a_1595_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1586_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1586_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set_tag(v___x_1597_, 0);
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
v___y_1532_ = v_a_1584_;
v___y_1533_ = v___y_1553_;
v___y_1534_ = v___y_1554_;
v___y_1535_ = v___y_1557_;
v___y_1536_ = v___y_1558_;
v___y_1537_ = v___y_1559_;
v___y_1538_ = v___y_1561_;
v___y_1539_ = v___y_1562_;
v___y_1540_ = v___y_1555_;
v___y_1541_ = v___x_1585_;
v_a_1542_ = v___x_1600_;
goto v___jp_1531_;
}
}
}
}
}
v___jp_1603_:
{
lean_object* v___x_1615_; double v___x_1616_; double v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1615_ = lean_io_get_num_heartbeats();
v___x_1616_ = lean_float_of_nat(v___y_1607_);
v___x_1617_ = lean_float_of_nat(v___x_1615_);
v___x_1618_ = lean_box_float(v___x_1616_);
v___x_1619_ = lean_box_float(v___x_1617_);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v_a_1614_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
lean_inc_ref(v___y_1612_);
lean_inc(v_trace_1040_);
v___x_1622_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1613_, v___y_1612_, v___y_1604_, v___y_1606_, v___y_1605_, v___f_1464_, v___x_1621_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1225_ = v___y_1604_;
v___y_1226_ = v___y_1608_;
v___y_1227_ = v___y_1609_;
v___y_1228_ = v___y_1610_;
v___y_1229_ = v___y_1612_;
v___y_1230_ = v___y_1613_;
v___y_1231_ = v___y_1611_;
v___y_1232_ = v___x_1622_;
goto v___jp_1224_;
}
v___jp_1623_:
{
lean_object* v___x_1635_; double v___x_1636_; double v___x_1637_; double v___x_1638_; double v___x_1639_; double v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1635_ = lean_io_mono_nanos_now();
v___x_1636_ = lean_float_of_nat(v___y_1625_);
v___x_1637_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1638_ = lean_float_div(v___x_1636_, v___x_1637_);
v___x_1639_ = lean_float_of_nat(v___x_1635_);
v___x_1640_ = lean_float_div(v___x_1639_, v___x_1637_);
v___x_1641_ = lean_box_float(v___x_1638_);
v___x_1642_ = lean_box_float(v___x_1640_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_a_1634_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
lean_inc_ref(v___y_1632_);
lean_inc(v_trace_1040_);
v___x_1645_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1633_, v___y_1632_, v___y_1624_, v___y_1627_, v___y_1626_, v___f_1464_, v___x_1644_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1225_ = v___y_1624_;
v___y_1226_ = v___y_1628_;
v___y_1227_ = v___y_1629_;
v___y_1228_ = v___y_1630_;
v___y_1229_ = v___y_1632_;
v___y_1230_ = v___y_1633_;
v___y_1231_ = v___y_1631_;
v___y_1232_ = v___x_1645_;
goto v___jp_1224_;
}
v___jp_1646_:
{
lean_object* v___x_1658_; double v___x_1659_; double v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1658_ = lean_io_get_num_heartbeats();
v___x_1659_ = lean_float_of_nat(v___y_1650_);
v___x_1660_ = lean_float_of_nat(v___x_1658_);
v___x_1661_ = lean_box_float(v___x_1659_);
v___x_1662_ = lean_box_float(v___x_1660_);
v___x_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1661_);
lean_ctor_set(v___x_1663_, 1, v___x_1662_);
v___x_1664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1664_, 0, v_a_1657_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
lean_inc_ref(v___y_1654_);
lean_inc(v_trace_1040_);
v___x_1665_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1655_, v___y_1654_, v___y_1647_, v___y_1656_, v___y_1651_, v___f_1368_, v___x_1664_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1225_ = v___y_1647_;
v___y_1226_ = v___y_1648_;
v___y_1227_ = v___y_1649_;
v___y_1228_ = v___y_1652_;
v___y_1229_ = v___y_1654_;
v___y_1230_ = v___y_1655_;
v___y_1231_ = v___y_1653_;
v___y_1232_ = v___x_1665_;
goto v___jp_1224_;
}
v___jp_1666_:
{
lean_object* v___x_1678_; double v___x_1679_; double v___x_1680_; double v___x_1681_; double v___x_1682_; double v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1678_ = lean_io_mono_nanos_now();
v___x_1679_ = lean_float_of_nat(v___y_1668_);
v___x_1680_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1681_ = lean_float_div(v___x_1679_, v___x_1680_);
v___x_1682_ = lean_float_of_nat(v___x_1678_);
v___x_1683_ = lean_float_div(v___x_1682_, v___x_1680_);
v___x_1684_ = lean_box_float(v___x_1681_);
v___x_1685_ = lean_box_float(v___x_1683_);
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1684_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_a_1677_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
lean_inc_ref(v___y_1674_);
lean_inc(v_trace_1040_);
v___x_1688_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1675_, v___y_1674_, v___y_1667_, v___y_1676_, v___y_1671_, v___f_1368_, v___x_1687_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1225_ = v___y_1667_;
v___y_1226_ = v___y_1669_;
v___y_1227_ = v___y_1670_;
v___y_1228_ = v___y_1672_;
v___y_1229_ = v___y_1674_;
v___y_1230_ = v___y_1675_;
v___y_1231_ = v___y_1673_;
v___y_1232_ = v___x_1688_;
goto v___jp_1224_;
}
v___jp_1689_:
{
lean_object* v___x_1702_; 
v___x_1702_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
if (v___y_1690_ == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1040_);
v___x_1705_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1691_, v___y_1701_, v___y_1695_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set_tag(v___x_1708_, 1);
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
v___y_1667_ = v___y_1692_;
v___y_1668_ = v___x_1704_;
v___y_1669_ = v___y_1693_;
v___y_1670_ = v___y_1696_;
v___y_1671_ = v_a_1703_;
v___y_1672_ = v___y_1697_;
v___y_1673_ = v___y_1698_;
v___y_1674_ = v___y_1699_;
v___y_1675_ = v___y_1694_;
v___y_1676_ = v___y_1700_;
v_a_1677_ = v___x_1711_;
goto v___jp_1666_;
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v_a_1714_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1705_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1705_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set_tag(v___x_1716_, 0);
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
v___y_1667_ = v___y_1692_;
v___y_1668_ = v___x_1704_;
v___y_1669_ = v___y_1693_;
v___y_1670_ = v___y_1696_;
v___y_1671_ = v_a_1703_;
v___y_1672_ = v___y_1697_;
v___y_1673_ = v___y_1698_;
v___y_1674_ = v___y_1699_;
v___y_1675_ = v___y_1694_;
v___y_1676_ = v___y_1700_;
v_a_1677_ = v___x_1719_;
goto v___jp_1666_;
}
}
}
}
else
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_a_1722_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1722_);
lean_dec_ref(v___x_1702_);
v___x_1723_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1040_);
v___x_1724_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1691_, v___y_1701_, v___y_1695_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 1);
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
v___y_1647_ = v___y_1692_;
v___y_1648_ = v___y_1693_;
v___y_1649_ = v___y_1696_;
v___y_1650_ = v___x_1723_;
v___y_1651_ = v_a_1722_;
v___y_1652_ = v___y_1697_;
v___y_1653_ = v___y_1698_;
v___y_1654_ = v___y_1699_;
v___y_1655_ = v___y_1694_;
v___y_1656_ = v___y_1700_;
v_a_1657_ = v___x_1730_;
goto v___jp_1646_;
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
v_a_1733_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1724_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1724_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set_tag(v___x_1735_, 0);
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
v___y_1647_ = v___y_1692_;
v___y_1648_ = v___y_1693_;
v___y_1649_ = v___y_1696_;
v___y_1650_ = v___x_1723_;
v___y_1651_ = v_a_1722_;
v___y_1652_ = v___y_1697_;
v___y_1653_ = v___y_1698_;
v___y_1654_ = v___y_1699_;
v___y_1655_ = v___y_1694_;
v___y_1656_ = v___y_1700_;
v_a_1657_ = v___x_1738_;
goto v___jp_1646_;
}
}
}
}
}
v___jp_1741_:
{
lean_object* v___x_1753_; double v___x_1754_; double v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1753_ = lean_io_get_num_heartbeats();
v___x_1754_ = lean_float_of_nat(v___y_1744_);
v___x_1755_ = lean_float_of_nat(v___x_1753_);
v___x_1756_ = lean_box_float(v___x_1754_);
v___x_1757_ = lean_box_float(v___x_1755_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v_a_1752_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
lean_inc_ref(v___y_1750_);
lean_inc(v_trace_1040_);
v___x_1760_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1751_, v___y_1750_, v___y_1743_, v___y_1742_, v___y_1746_, v___f_1242_, v___x_1759_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1174_ = v___y_1743_;
v___y_1175_ = v___y_1745_;
v___y_1176_ = v___y_1747_;
v___y_1177_ = v___y_1749_;
v___y_1178_ = v___y_1748_;
v___y_1179_ = v___y_1750_;
v___y_1180_ = v___y_1751_;
v___y_1181_ = v___x_1760_;
goto v___jp_1173_;
}
v___jp_1761_:
{
lean_object* v___x_1773_; double v___x_1774_; double v___x_1775_; double v___x_1776_; double v___x_1777_; double v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1773_ = lean_io_mono_nanos_now();
v___x_1774_ = lean_float_of_nat(v___y_1767_);
v___x_1775_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1776_ = lean_float_div(v___x_1774_, v___x_1775_);
v___x_1777_ = lean_float_of_nat(v___x_1773_);
v___x_1778_ = lean_float_div(v___x_1777_, v___x_1775_);
v___x_1779_ = lean_box_float(v___x_1776_);
v___x_1780_ = lean_box_float(v___x_1778_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v_a_1772_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
lean_inc_ref(v___y_1770_);
lean_inc(v_trace_1040_);
v___x_1783_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1771_, v___y_1770_, v___y_1763_, v___y_1762_, v___y_1765_, v___f_1242_, v___x_1782_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1174_ = v___y_1763_;
v___y_1175_ = v___y_1764_;
v___y_1176_ = v___y_1766_;
v___y_1177_ = v___y_1769_;
v___y_1178_ = v___y_1768_;
v___y_1179_ = v___y_1770_;
v___y_1180_ = v___y_1771_;
v___y_1181_ = v___x_1783_;
goto v___jp_1173_;
}
v___jp_1784_:
{
lean_object* v___x_1797_; 
v___x_1797_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
if (v___y_1785_ == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1798_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1040_);
v___x_1800_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1787_, v___y_1796_, v___y_1789_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 1);
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
v___y_1762_ = v___y_1786_;
v___y_1763_ = v___y_1788_;
v___y_1764_ = v___y_1790_;
v___y_1765_ = v_a_1798_;
v___y_1766_ = v___y_1793_;
v___y_1767_ = v___x_1799_;
v___y_1768_ = v___y_1791_;
v___y_1769_ = v___y_1794_;
v___y_1770_ = v___y_1795_;
v___y_1771_ = v___y_1792_;
v_a_1772_ = v___x_1806_;
goto v___jp_1761_;
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
v_a_1809_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1800_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1800_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 0);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
v___y_1762_ = v___y_1786_;
v___y_1763_ = v___y_1788_;
v___y_1764_ = v___y_1790_;
v___y_1765_ = v_a_1798_;
v___y_1766_ = v___y_1793_;
v___y_1767_ = v___x_1799_;
v___y_1768_ = v___y_1791_;
v___y_1769_ = v___y_1794_;
v___y_1770_ = v___y_1795_;
v___y_1771_ = v___y_1792_;
v_a_1772_ = v___x_1814_;
goto v___jp_1761_;
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_a_1817_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_a_1817_);
lean_dec_ref(v___x_1797_);
v___x_1818_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1040_);
v___x_1819_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1787_, v___y_1796_, v___y_1789_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 1);
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
v___y_1742_ = v___y_1786_;
v___y_1743_ = v___y_1788_;
v___y_1744_ = v___x_1818_;
v___y_1745_ = v___y_1790_;
v___y_1746_ = v_a_1817_;
v___y_1747_ = v___y_1793_;
v___y_1748_ = v___y_1791_;
v___y_1749_ = v___y_1794_;
v___y_1750_ = v___y_1795_;
v___y_1751_ = v___y_1792_;
v_a_1752_ = v___x_1825_;
goto v___jp_1741_;
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
v_a_1828_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1819_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1819_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 0);
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
v___y_1742_ = v___y_1786_;
v___y_1743_ = v___y_1788_;
v___y_1744_ = v___x_1818_;
v___y_1745_ = v___y_1790_;
v___y_1746_ = v_a_1817_;
v___y_1747_ = v___y_1793_;
v___y_1748_ = v___y_1791_;
v___y_1749_ = v___y_1794_;
v___y_1750_ = v___y_1795_;
v___y_1751_ = v___y_1792_;
v_a_1752_ = v___x_1833_;
goto v___jp_1741_;
}
}
}
}
}
v___jp_1836_:
{
lean_object* v___x_1844_; double v___x_1845_; double v___x_1846_; double v___x_1847_; double v___x_1848_; double v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1844_ = lean_io_mono_nanos_now();
v___x_1845_ = lean_float_of_nat(v___y_1840_);
v___x_1846_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1847_ = lean_float_div(v___x_1845_, v___x_1846_);
v___x_1848_ = lean_float_of_nat(v___x_1844_);
v___x_1849_ = lean_float_div(v___x_1848_, v___x_1846_);
v___x_1850_ = lean_box_float(v___x_1847_);
v___x_1851_ = lean_box_float(v___x_1849_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v_a_1843_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1842_, v___y_1841_, v___y_1839_, v___y_1838_, v___y_1837_, v___f_1464_, v___x_1853_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1854_;
}
v___jp_1855_:
{
lean_object* v___x_1863_; double v___x_1864_; double v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1863_ = lean_io_get_num_heartbeats();
v___x_1864_ = lean_float_of_nat(v___y_1859_);
v___x_1865_ = lean_float_of_nat(v___x_1863_);
v___x_1866_ = lean_box_float(v___x_1864_);
v___x_1867_ = lean_box_float(v___x_1865_);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_a_1862_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1861_, v___y_1860_, v___y_1858_, v___y_1857_, v___y_1856_, v___f_1464_, v___x_1869_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1870_;
}
v___jp_1871_:
{
lean_object* v___x_1879_; double v___x_1880_; double v___x_1881_; double v___x_1882_; double v___x_1883_; double v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1879_ = lean_io_mono_nanos_now();
v___x_1880_ = lean_float_of_nat(v___y_1874_);
v___x_1881_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1882_ = lean_float_div(v___x_1880_, v___x_1881_);
v___x_1883_ = lean_float_of_nat(v___x_1879_);
v___x_1884_ = lean_float_div(v___x_1883_, v___x_1881_);
v___x_1885_ = lean_box_float(v___x_1882_);
v___x_1886_ = lean_box_float(v___x_1884_);
v___x_1887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1885_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v_a_1878_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1877_, v___y_1876_, v___y_1873_, v___y_1875_, v___y_1872_, v___f_1368_, v___x_1888_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1889_;
}
v___jp_1890_:
{
lean_object* v___x_1898_; double v___x_1899_; double v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1898_ = lean_io_get_num_heartbeats();
v___x_1899_ = lean_float_of_nat(v___y_1893_);
v___x_1900_ = lean_float_of_nat(v___x_1898_);
v___x_1901_ = lean_box_float(v___x_1899_);
v___x_1902_ = lean_box_float(v___x_1900_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_a_1897_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1896_, v___y_1895_, v___y_1892_, v___y_1894_, v___y_1891_, v___f_1368_, v___x_1904_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1905_;
}
v___jp_1906_:
{
lean_object* v___x_1914_; lean_object* v_a_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1914_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref(v___x_1914_);
v___x_1916_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1917_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_1908_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1040_);
v___x_1919_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1907_, v___y_1913_, v___y_1909_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 1);
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
v___y_1872_ = v_a_1915_;
v___y_1873_ = v___y_1908_;
v___y_1874_ = v___x_1918_;
v___y_1875_ = v___y_1912_;
v___y_1876_ = v___y_1911_;
v___y_1877_ = v___y_1910_;
v_a_1878_ = v___x_1925_;
goto v___jp_1871_;
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_a_1928_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1919_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1919_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set_tag(v___x_1930_, 0);
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
v___y_1872_ = v_a_1915_;
v___y_1873_ = v___y_1908_;
v___y_1874_ = v___x_1918_;
v___y_1875_ = v___y_1912_;
v___y_1876_ = v___y_1911_;
v___y_1877_ = v___y_1910_;
v_a_1878_ = v___x_1933_;
goto v___jp_1871_;
}
}
}
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1040_);
v___x_1937_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1907_, v___y_1913_, v___y_1909_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 1);
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
v___y_1891_ = v_a_1915_;
v___y_1892_ = v___y_1908_;
v___y_1893_ = v___x_1936_;
v___y_1894_ = v___y_1912_;
v___y_1895_ = v___y_1911_;
v___y_1896_ = v___y_1910_;
v_a_1897_ = v___x_1943_;
goto v___jp_1890_;
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_a_1946_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1937_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1937_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set_tag(v___x_1948_, 0);
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
v___y_1891_ = v_a_1915_;
v___y_1892_ = v___y_1908_;
v___y_1893_ = v___x_1936_;
v___y_1894_ = v___y_1912_;
v___y_1895_ = v___y_1911_;
v___y_1896_ = v___y_1910_;
v_a_1897_ = v___x_1951_;
goto v___jp_1890_;
}
}
}
}
}
v___jp_1956_:
{
lean_object* v___x_1962_; lean_object* v_a_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1962_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref(v___x_1962_);
v___x_1964_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1965_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_1958_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1040_);
v___x_1967_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v_n_1955_, v___y_1961_, v_acc_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set_tag(v___x_1970_, 1);
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
v___y_1837_ = v_a_1963_;
v___y_1838_ = v___y_1957_;
v___y_1839_ = v___y_1958_;
v___y_1840_ = v___x_1966_;
v___y_1841_ = v___y_1960_;
v___y_1842_ = v___y_1959_;
v_a_1843_ = v___x_1973_;
goto v___jp_1836_;
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
v_a_1976_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1967_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1967_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set_tag(v___x_1978_, 0);
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
v___y_1837_ = v_a_1963_;
v___y_1838_ = v___y_1957_;
v___y_1839_ = v___y_1958_;
v___y_1840_ = v___x_1966_;
v___y_1841_ = v___y_1960_;
v___y_1842_ = v___y_1959_;
v_a_1843_ = v___x_1981_;
goto v___jp_1836_;
}
}
}
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1040_);
v___x_1985_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v_n_1955_, v___y_1961_, v_acc_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set_tag(v___x_1988_, 1);
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
v___y_1856_ = v_a_1963_;
v___y_1857_ = v___y_1957_;
v___y_1858_ = v___y_1958_;
v___y_1859_ = v___x_1984_;
v___y_1860_ = v___y_1960_;
v___y_1861_ = v___y_1959_;
v_a_1862_ = v___x_1991_;
goto v___jp_1855_;
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_a_1994_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1985_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1985_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 0);
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
v___y_1856_ = v_a_1963_;
v___y_1857_ = v___y_1957_;
v___y_1858_ = v___y_1958_;
v___y_1859_ = v___x_1984_;
v___y_1860_ = v___y_1960_;
v___y_1861_ = v___y_1959_;
v_a_1862_ = v___x_1999_;
goto v___jp_1855_;
}
}
}
}
}
v___jp_2002_:
{
if (v___y_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_dec_ref(v___y_2007_);
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v___y_2006_);
v___x_2012_ = lean_apply_6(v___y_2005_, v___y_2006_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref(v___x_2012_);
if (lean_obj_tag(v_a_2013_) == 0)
{
lean_object* v___x_2014_; lean_object* v_a_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
lean_inc(v_trace_1040_);
v___x_2014_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = lean_nat_add(v_n_1955_, v_one_1954_);
lean_dec(v_n_1955_);
v___x_2017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___y_2006_);
lean_ctor_set(v___x_2017_, 1, v_acc_1045_);
v___x_2018_ = lean_unbox(v_a_2015_);
if (v___x_2018_ == 0)
{
if (v___y_2003_ == 0)
{
lean_dec(v_a_2015_);
lean_dec_ref(v___y_2008_);
v_n_1043_ = v___x_2016_;
v_curr_1044_ = v___y_2010_;
v_acc_1045_ = v___x_2017_;
goto _start;
}
else
{
uint8_t v___x_2020_; 
v___x_2020_ = lean_unbox(v_a_2015_);
lean_dec(v_a_2015_);
v___y_1907_ = v___x_2016_;
v___y_1908_ = v___y_2004_;
v___y_1909_ = v___x_2017_;
v___y_1910_ = v___y_2009_;
v___y_1911_ = v___y_2008_;
v___y_1912_ = v___x_2020_;
v___y_1913_ = v___y_2010_;
goto v___jp_1906_;
}
}
else
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_unbox(v_a_2015_);
lean_dec(v_a_2015_);
v___y_1907_ = v___x_2016_;
v___y_1908_ = v___y_2004_;
v___y_1909_ = v___x_2017_;
v___y_1910_ = v___y_2009_;
v___y_1911_ = v___y_2008_;
v___y_1912_ = v___x_2021_;
v___y_1913_ = v___y_2010_;
goto v___jp_1906_;
}
}
else
{
lean_object* v_val_2022_; lean_object* v___x_2023_; lean_object* v_a_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
lean_dec(v___y_2006_);
v_val_2022_ = lean_ctor_get(v_a_2013_, 0);
lean_inc(v_val_2022_);
lean_dec_ref(v_a_2013_);
lean_inc(v_trace_1040_);
v___x_2023_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref(v___x_2023_);
v___x_2025_ = l_List_appendTR___redArg(v_val_2022_, v___y_2010_);
v___x_2026_ = lean_unbox(v_a_2024_);
if (v___x_2026_ == 0)
{
if (v___y_2003_ == 0)
{
lean_dec(v_a_2024_);
lean_dec_ref(v___y_2008_);
v_n_1043_ = v_n_1955_;
v_curr_1044_ = v___x_2025_;
goto _start;
}
else
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_unbox(v_a_2024_);
lean_dec(v_a_2024_);
v___y_1957_ = v___x_2028_;
v___y_1958_ = v___y_2004_;
v___y_1959_ = v___y_2009_;
v___y_1960_ = v___y_2008_;
v___y_1961_ = v___x_2025_;
goto v___jp_1956_;
}
}
else
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_unbox(v_a_2024_);
lean_dec(v_a_2024_);
v___y_1957_ = v___x_2029_;
v___y_1958_ = v___y_2004_;
v___y_1959_ = v___y_2009_;
v___y_1960_ = v___y_2008_;
v___y_1961_ = v___x_2025_;
goto v___jp_1956_;
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2006_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
v_a_2030_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2012_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2012_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
return v___y_2007_;
}
}
v___jp_2038_:
{
lean_object* v___x_2049_; 
v___x_2049_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
if (v___y_2040_ == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1040_);
v___x_2052_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v_n_1955_, v___y_2043_, v_acc_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set_tag(v___x_2055_, 1);
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
v___y_1466_ = v___y_2039_;
v___y_1467_ = v___x_2051_;
v___y_1468_ = v_a_2050_;
v___y_1469_ = v___y_2041_;
v___y_1470_ = v___y_2042_;
v___y_1471_ = v___y_2044_;
v___y_1472_ = v___y_2046_;
v___y_1473_ = v___y_2045_;
v___y_1474_ = v___y_2048_;
v___y_1475_ = v___y_2047_;
v_a_1476_ = v___x_2058_;
goto v___jp_1465_;
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_a_2061_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2052_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2052_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set_tag(v___x_2063_, 0);
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
v___y_1466_ = v___y_2039_;
v___y_1467_ = v___x_2051_;
v___y_1468_ = v_a_2050_;
v___y_1469_ = v___y_2041_;
v___y_1470_ = v___y_2042_;
v___y_1471_ = v___y_2044_;
v___y_1472_ = v___y_2046_;
v___y_1473_ = v___y_2045_;
v___y_1474_ = v___y_2048_;
v___y_1475_ = v___y_2047_;
v_a_1476_ = v___x_2066_;
goto v___jp_1465_;
}
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_a_2069_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2069_);
lean_dec_ref(v___x_2049_);
v___x_2070_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1040_);
v___x_2071_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v_n_1955_, v___y_2043_, v_acc_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 1);
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
v___y_1489_ = v___y_2039_;
v___y_1490_ = v___x_2070_;
v___y_1491_ = v_a_2069_;
v___y_1492_ = v___y_2041_;
v___y_1493_ = v___y_2042_;
v___y_1494_ = v___y_2044_;
v___y_1495_ = v___y_2046_;
v___y_1496_ = v___y_2045_;
v___y_1497_ = v___y_2048_;
v___y_1498_ = v___y_2047_;
v_a_1499_ = v___x_2077_;
goto v___jp_1488_;
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_a_2080_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2071_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2071_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 0);
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
v___y_1489_ = v___y_2039_;
v___y_1490_ = v___x_2070_;
v___y_1491_ = v_a_2069_;
v___y_1492_ = v___y_2041_;
v___y_1493_ = v___y_2042_;
v___y_1494_ = v___y_2044_;
v___y_1495_ = v___y_2046_;
v___y_1496_ = v___y_2045_;
v___y_1497_ = v___y_2048_;
v___y_1498_ = v___y_2047_;
v_a_1499_ = v___x_2085_;
goto v___jp_1488_;
}
}
}
}
}
v___jp_2088_:
{
if (v___y_2101_ == 0)
{
lean_object* v___x_2102_; 
lean_dec_ref(v___y_2095_);
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v___y_2097_);
v___x_2102_ = lean_apply_6(v___y_2091_, v___y_2097_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref(v___x_2102_);
if (lean_obj_tag(v_a_2103_) == 0)
{
lean_object* v___x_2104_; lean_object* v_a_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
lean_inc(v_trace_1040_);
v___x_2104_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = lean_nat_add(v_n_1955_, v_one_1954_);
lean_dec(v_n_1955_);
v___x_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___y_2097_);
lean_ctor_set(v___x_2107_, 1, v_acc_1045_);
v___x_2108_ = lean_unbox(v_a_2105_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = l_Lean_trace_profiler;
v___x_2110_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2090_, v___x_2109_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; 
lean_dec(v_a_2105_);
lean_inc(v_trace_1040_);
v___x_2111_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___x_2106_, v___y_2100_, v___x_2107_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1174_ = v___y_2090_;
v___y_1175_ = v___y_2092_;
v___y_1176_ = v___y_2096_;
v___y_1177_ = v___y_2098_;
v___y_1178_ = v___y_2093_;
v___y_1179_ = v___y_2099_;
v___y_1180_ = v___y_2094_;
v___y_1181_ = v___x_2111_;
goto v___jp_1173_;
}
else
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_unbox(v_a_2105_);
lean_dec(v_a_2105_);
v___y_1413_ = v___y_2089_;
v___y_1414_ = v___y_2090_;
v___y_1415_ = v___y_2092_;
v___y_1416_ = v___x_2106_;
v___y_1417_ = v___y_2093_;
v___y_1418_ = v___y_2094_;
v___y_1419_ = v___x_2112_;
v___y_1420_ = v___x_2107_;
v___y_1421_ = v___y_2096_;
v___y_1422_ = v___y_2098_;
v___y_1423_ = v___y_2099_;
v___y_1424_ = v___y_2100_;
goto v___jp_1412_;
}
}
else
{
uint8_t v___x_2113_; 
v___x_2113_ = lean_unbox(v_a_2105_);
lean_dec(v_a_2105_);
v___y_1413_ = v___y_2089_;
v___y_1414_ = v___y_2090_;
v___y_1415_ = v___y_2092_;
v___y_1416_ = v___x_2106_;
v___y_1417_ = v___y_2093_;
v___y_1418_ = v___y_2094_;
v___y_1419_ = v___x_2113_;
v___y_1420_ = v___x_2107_;
v___y_1421_ = v___y_2096_;
v___y_1422_ = v___y_2098_;
v___y_1423_ = v___y_2099_;
v___y_1424_ = v___y_2100_;
goto v___jp_1412_;
}
}
else
{
lean_object* v_val_2114_; lean_object* v___x_2115_; lean_object* v_a_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
lean_dec(v___y_2097_);
v_val_2114_ = lean_ctor_get(v_a_2103_, 0);
lean_inc(v_val_2114_);
lean_dec_ref(v_a_2103_);
lean_inc(v_trace_1040_);
v___x_2115_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
v___x_2117_ = l_List_appendTR___redArg(v_val_2114_, v___y_2100_);
v___x_2118_ = lean_unbox(v_a_2116_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = l_Lean_trace_profiler;
v___x_2120_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2090_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; 
lean_dec(v_a_2116_);
lean_inc(v_trace_1040_);
v___x_2121_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v_n_1955_, v___x_2117_, v_acc_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1174_ = v___y_2090_;
v___y_1175_ = v___y_2092_;
v___y_1176_ = v___y_2096_;
v___y_1177_ = v___y_2098_;
v___y_1178_ = v___y_2093_;
v___y_1179_ = v___y_2099_;
v___y_1180_ = v___y_2094_;
v___y_1181_ = v___x_2121_;
goto v___jp_1173_;
}
else
{
uint8_t v___x_2122_; 
v___x_2122_ = lean_unbox(v_a_2116_);
lean_dec(v_a_2116_);
v___y_2039_ = v___x_2122_;
v___y_2040_ = v___y_2089_;
v___y_2041_ = v___y_2090_;
v___y_2042_ = v___y_2092_;
v___y_2043_ = v___x_2117_;
v___y_2044_ = v___y_2096_;
v___y_2045_ = v___y_2098_;
v___y_2046_ = v___y_2093_;
v___y_2047_ = v___y_2094_;
v___y_2048_ = v___y_2099_;
goto v___jp_2038_;
}
}
else
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_unbox(v_a_2116_);
lean_dec(v_a_2116_);
v___y_2039_ = v___x_2123_;
v___y_2040_ = v___y_2089_;
v___y_2041_ = v___y_2090_;
v___y_2042_ = v___y_2092_;
v___y_2043_ = v___x_2117_;
v___y_2044_ = v___y_2096_;
v___y_2045_ = v___y_2098_;
v___y_2046_ = v___y_2093_;
v___y_2047_ = v___y_2094_;
v___y_2048_ = v___y_2099_;
goto v___jp_2038_;
}
}
}
else
{
lean_object* v_a_2124_; 
lean_dec(v___y_2100_);
lean_dec(v___y_2097_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec_ref(v_cfg_1039_);
v_a_2124_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2124_);
lean_dec_ref(v___x_2102_);
v___y_1164_ = v___y_2090_;
v___y_1165_ = v___y_2092_;
v___y_1166_ = v___y_2096_;
v___y_1167_ = v___y_2093_;
v___y_1168_ = v___y_2098_;
v___y_1169_ = v___y_2094_;
v___y_1170_ = v___y_2099_;
v_a_1171_ = v_a_2124_;
goto v___jp_1163_;
}
}
else
{
lean_dec(v___y_2100_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2091_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec_ref(v_cfg_1039_);
v___y_1164_ = v___y_2090_;
v___y_1165_ = v___y_2092_;
v___y_1166_ = v___y_2096_;
v___y_1167_ = v___y_2093_;
v___y_1168_ = v___y_2098_;
v___y_1169_ = v___y_2094_;
v___y_1170_ = v___y_2099_;
v_a_1171_ = v___y_2095_;
goto v___jp_1163_;
}
}
v___jp_2125_:
{
lean_object* v___x_2136_; 
v___x_2136_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
if (v___y_2126_ == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref(v___x_2136_);
v___x_2138_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1040_);
v___x_2139_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v_n_1955_, v___y_2127_, v_acc_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set_tag(v___x_2142_, 1);
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
v___y_1624_ = v___y_2128_;
v___y_1625_ = v___x_2138_;
v___y_1626_ = v_a_2137_;
v___y_1627_ = v___y_2129_;
v___y_1628_ = v___y_2130_;
v___y_1629_ = v___y_2131_;
v___y_1630_ = v___y_2132_;
v___y_1631_ = v___y_2135_;
v___y_1632_ = v___y_2134_;
v___y_1633_ = v___y_2133_;
v_a_1634_ = v___x_2145_;
goto v___jp_1623_;
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
v_a_2148_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2139_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2139_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set_tag(v___x_2150_, 0);
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
v___y_1624_ = v___y_2128_;
v___y_1625_ = v___x_2138_;
v___y_1626_ = v_a_2137_;
v___y_1627_ = v___y_2129_;
v___y_1628_ = v___y_2130_;
v___y_1629_ = v___y_2131_;
v___y_1630_ = v___y_2132_;
v___y_1631_ = v___y_2135_;
v___y_1632_ = v___y_2134_;
v___y_1633_ = v___y_2133_;
v_a_1634_ = v___x_2153_;
goto v___jp_1623_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_a_2156_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2156_);
lean_dec_ref(v___x_2136_);
v___x_2157_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1040_);
v___x_2158_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v_n_1955_, v___y_2127_, v_acc_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
lean_ctor_set_tag(v___x_2161_, 1);
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
v___y_1604_ = v___y_2128_;
v___y_1605_ = v_a_2156_;
v___y_1606_ = v___y_2129_;
v___y_1607_ = v___x_2157_;
v___y_1608_ = v___y_2130_;
v___y_1609_ = v___y_2131_;
v___y_1610_ = v___y_2132_;
v___y_1611_ = v___y_2135_;
v___y_1612_ = v___y_2134_;
v___y_1613_ = v___y_2133_;
v_a_1614_ = v___x_2164_;
goto v___jp_1603_;
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
v_a_2167_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2158_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2158_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set_tag(v___x_2169_, 0);
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
v___y_1604_ = v___y_2128_;
v___y_1605_ = v_a_2156_;
v___y_1606_ = v___y_2129_;
v___y_1607_ = v___x_2157_;
v___y_1608_ = v___y_2130_;
v___y_1609_ = v___y_2131_;
v___y_1610_ = v___y_2132_;
v___y_1611_ = v___y_2135_;
v___y_1612_ = v___y_2134_;
v___y_1613_ = v___y_2133_;
v_a_1614_ = v___x_2172_;
goto v___jp_1603_;
}
}
}
}
}
v___jp_2175_:
{
if (v___y_2188_ == 0)
{
lean_object* v___x_2189_; 
lean_dec_ref(v___y_2180_);
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v___y_2183_);
v___x_2189_ = lean_apply_6(v___y_2178_, v___y_2183_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref(v___x_2189_);
if (lean_obj_tag(v_a_2190_) == 0)
{
lean_object* v___x_2191_; lean_object* v_a_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
lean_inc(v_trace_1040_);
v___x_2191_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
lean_dec_ref(v___x_2191_);
v___x_2193_ = lean_nat_add(v_n_1955_, v_one_1954_);
lean_dec(v_n_1955_);
v___x_2194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___y_2183_);
lean_ctor_set(v___x_2194_, 1, v_acc_1045_);
v___x_2195_ = lean_unbox(v_a_2192_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2196_ = l_Lean_trace_profiler;
v___x_2197_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2177_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; 
lean_dec(v_a_2192_);
lean_inc(v_trace_1040_);
v___x_2198_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___x_2193_, v___y_2187_, v___x_2194_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1225_ = v___y_2177_;
v___y_1226_ = v___y_2179_;
v___y_1227_ = v___y_2182_;
v___y_1228_ = v___y_2184_;
v___y_1229_ = v___y_2186_;
v___y_1230_ = v___y_2181_;
v___y_1231_ = v___y_2185_;
v___y_1232_ = v___x_2198_;
goto v___jp_1224_;
}
else
{
uint8_t v___x_2199_; 
v___x_2199_ = lean_unbox(v_a_2192_);
lean_dec(v_a_2192_);
v___y_1690_ = v___y_2176_;
v___y_1691_ = v___x_2193_;
v___y_1692_ = v___y_2177_;
v___y_1693_ = v___y_2179_;
v___y_1694_ = v___y_2181_;
v___y_1695_ = v___x_2194_;
v___y_1696_ = v___y_2182_;
v___y_1697_ = v___y_2184_;
v___y_1698_ = v___y_2185_;
v___y_1699_ = v___y_2186_;
v___y_1700_ = v___x_2199_;
v___y_1701_ = v___y_2187_;
goto v___jp_1689_;
}
}
else
{
uint8_t v___x_2200_; 
v___x_2200_ = lean_unbox(v_a_2192_);
lean_dec(v_a_2192_);
v___y_1690_ = v___y_2176_;
v___y_1691_ = v___x_2193_;
v___y_1692_ = v___y_2177_;
v___y_1693_ = v___y_2179_;
v___y_1694_ = v___y_2181_;
v___y_1695_ = v___x_2194_;
v___y_1696_ = v___y_2182_;
v___y_1697_ = v___y_2184_;
v___y_1698_ = v___y_2185_;
v___y_1699_ = v___y_2186_;
v___y_1700_ = v___x_2200_;
v___y_1701_ = v___y_2187_;
goto v___jp_1689_;
}
}
else
{
lean_object* v_val_2201_; lean_object* v___x_2202_; lean_object* v_a_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
lean_dec(v___y_2183_);
v_val_2201_ = lean_ctor_get(v_a_2190_, 0);
lean_inc(v_val_2201_);
lean_dec_ref(v_a_2190_);
lean_inc(v_trace_1040_);
v___x_2202_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = l_List_appendTR___redArg(v_val_2201_, v___y_2187_);
v___x_2205_ = lean_unbox(v_a_2203_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = l_Lean_trace_profiler;
v___x_2207_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2177_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; 
lean_dec(v_a_2203_);
lean_inc(v_trace_1040_);
v___x_2208_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v_n_1955_, v___x_2204_, v_acc_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1225_ = v___y_2177_;
v___y_1226_ = v___y_2179_;
v___y_1227_ = v___y_2182_;
v___y_1228_ = v___y_2184_;
v___y_1229_ = v___y_2186_;
v___y_1230_ = v___y_2181_;
v___y_1231_ = v___y_2185_;
v___y_1232_ = v___x_2208_;
goto v___jp_1224_;
}
else
{
uint8_t v___x_2209_; 
v___x_2209_ = lean_unbox(v_a_2203_);
lean_dec(v_a_2203_);
v___y_2126_ = v___y_2176_;
v___y_2127_ = v___x_2204_;
v___y_2128_ = v___y_2177_;
v___y_2129_ = v___x_2209_;
v___y_2130_ = v___y_2179_;
v___y_2131_ = v___y_2182_;
v___y_2132_ = v___y_2184_;
v___y_2133_ = v___y_2181_;
v___y_2134_ = v___y_2186_;
v___y_2135_ = v___y_2185_;
goto v___jp_2125_;
}
}
else
{
uint8_t v___x_2210_; 
v___x_2210_ = lean_unbox(v_a_2203_);
lean_dec(v_a_2203_);
v___y_2126_ = v___y_2176_;
v___y_2127_ = v___x_2204_;
v___y_2128_ = v___y_2177_;
v___y_2129_ = v___x_2210_;
v___y_2130_ = v___y_2179_;
v___y_2131_ = v___y_2182_;
v___y_2132_ = v___y_2184_;
v___y_2133_ = v___y_2181_;
v___y_2134_ = v___y_2186_;
v___y_2135_ = v___y_2185_;
goto v___jp_2125_;
}
}
}
else
{
lean_object* v_a_2211_; 
lean_dec(v___y_2187_);
lean_dec(v___y_2183_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec_ref(v_cfg_1039_);
v_a_2211_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2211_);
lean_dec_ref(v___x_2189_);
v___y_1215_ = v___y_2177_;
v___y_1216_ = v___y_2179_;
v___y_1217_ = v___y_2182_;
v___y_1218_ = v___y_2184_;
v___y_1219_ = v___y_2185_;
v___y_1220_ = v___y_2181_;
v___y_1221_ = v___y_2186_;
v_a_1222_ = v_a_2211_;
goto v___jp_1214_;
}
}
else
{
lean_dec(v___y_2187_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2178_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec_ref(v_cfg_1039_);
v___y_1215_ = v___y_2177_;
v___y_1216_ = v___y_2179_;
v___y_1217_ = v___y_2182_;
v___y_1218_ = v___y_2184_;
v___y_1219_ = v___y_2185_;
v___y_1220_ = v___y_2181_;
v___y_1221_ = v___y_2186_;
v_a_1222_ = v___y_2180_;
goto v___jp_1214_;
}
}
v___jp_2212_:
{
lean_object* v___x_2224_; lean_object* v_a_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2224_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2227_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2213_, v___x_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec_ref(v___y_2217_);
v___x_2228_ = lean_io_mono_nanos_now();
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v___y_2218_);
v___x_2229_ = lean_apply_6(v___y_2215_, v___y_2218_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; uint8_t v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = lean_unbox(v_a_2230_);
lean_dec(v_a_2230_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; 
lean_inc_ref(v_next_1041_);
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v___y_2218_);
v___x_2232_ = lean_apply_7(v_next_1041_, v___y_2218_, v___y_2219_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; 
lean_dec(v___y_2223_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2214_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec_ref(v_cfg_1039_);
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref(v___x_2232_);
v___y_1205_ = v___y_2213_;
v___y_1206_ = v_a_2225_;
v___y_1207_ = v___y_2216_;
v___y_1208_ = v___y_2220_;
v___y_1209_ = v___x_2228_;
v___y_1210_ = v___y_2221_;
v___y_1211_ = v___y_2222_;
v_a_1212_ = v_a_2233_;
goto v___jp_1204_;
}
else
{
lean_object* v_a_2234_; uint8_t v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2234_);
lean_dec_ref(v___x_2232_);
v___x_2235_ = l_Lean_Exception_isInterrupt(v_a_2234_);
if (v___x_2235_ == 0)
{
uint8_t v___x_2236_; 
lean_inc(v_a_2234_);
v___x_2236_ = l_Lean_Exception_isRuntime(v_a_2234_);
v___y_2176_ = v___x_2227_;
v___y_2177_ = v___y_2213_;
v___y_2178_ = v___y_2214_;
v___y_2179_ = v_a_2225_;
v___y_2180_ = v_a_2234_;
v___y_2181_ = v___y_2221_;
v___y_2182_ = v___y_2216_;
v___y_2183_ = v___y_2218_;
v___y_2184_ = v___y_2220_;
v___y_2185_ = v___x_2228_;
v___y_2186_ = v___y_2222_;
v___y_2187_ = v___y_2223_;
v___y_2188_ = v___x_2236_;
goto v___jp_2175_;
}
else
{
v___y_2176_ = v___x_2227_;
v___y_2177_ = v___y_2213_;
v___y_2178_ = v___y_2214_;
v___y_2179_ = v_a_2225_;
v___y_2180_ = v_a_2234_;
v___y_2181_ = v___y_2221_;
v___y_2182_ = v___y_2216_;
v___y_2183_ = v___y_2218_;
v___y_2184_ = v___y_2220_;
v___y_2185_ = v___x_2228_;
v___y_2186_ = v___y_2222_;
v___y_2187_ = v___y_2223_;
v___y_2188_ = v___x_2235_;
goto v___jp_2175_;
}
}
}
else
{
lean_object* v___x_2237_; lean_object* v_a_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
lean_dec_ref(v___y_2219_);
lean_dec_ref(v___y_2214_);
lean_inc(v_trace_1040_);
v___x_2237_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref(v___x_2237_);
v___x_2239_ = lean_nat_add(v_n_1955_, v_one_1954_);
lean_dec(v_n_1955_);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___y_2218_);
lean_ctor_set(v___x_2240_, 1, v_acc_1045_);
v___x_2241_ = lean_unbox(v_a_2238_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2242_ = l_Lean_trace_profiler;
v___x_2243_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2213_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; 
lean_dec(v_a_2238_);
lean_inc(v_trace_1040_);
v___x_2244_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___x_2239_, v___y_2223_, v___x_2240_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1225_ = v___y_2213_;
v___y_1226_ = v_a_2225_;
v___y_1227_ = v___y_2216_;
v___y_1228_ = v___y_2220_;
v___y_1229_ = v___y_2222_;
v___y_1230_ = v___y_2221_;
v___y_1231_ = v___x_2228_;
v___y_1232_ = v___x_2244_;
goto v___jp_1224_;
}
else
{
uint8_t v___x_2245_; 
v___x_2245_ = lean_unbox(v_a_2238_);
lean_dec(v_a_2238_);
v___y_1552_ = v___x_2227_;
v___y_1553_ = v___y_2213_;
v___y_1554_ = v_a_2225_;
v___y_1555_ = v___y_2221_;
v___y_1556_ = v___x_2240_;
v___y_1557_ = v___y_2216_;
v___y_1558_ = v___x_2245_;
v___y_1559_ = v___y_2220_;
v___y_1560_ = v___x_2239_;
v___y_1561_ = v___x_2228_;
v___y_1562_ = v___y_2222_;
v___y_1563_ = v___y_2223_;
goto v___jp_1551_;
}
}
else
{
uint8_t v___x_2246_; 
v___x_2246_ = lean_unbox(v_a_2238_);
lean_dec(v_a_2238_);
v___y_1552_ = v___x_2227_;
v___y_1553_ = v___y_2213_;
v___y_1554_ = v_a_2225_;
v___y_1555_ = v___y_2221_;
v___y_1556_ = v___x_2240_;
v___y_1557_ = v___y_2216_;
v___y_1558_ = v___x_2246_;
v___y_1559_ = v___y_2220_;
v___y_1560_ = v___x_2239_;
v___y_1561_ = v___x_2228_;
v___y_1562_ = v___y_2222_;
v___y_1563_ = v___y_2223_;
goto v___jp_1551_;
}
}
}
else
{
lean_object* v_a_2247_; 
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2214_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec_ref(v_cfg_1039_);
v_a_2247_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2247_);
lean_dec_ref(v___x_2229_);
v___y_1215_ = v___y_2213_;
v___y_1216_ = v_a_2225_;
v___y_1217_ = v___y_2216_;
v___y_1218_ = v___y_2220_;
v___y_1219_ = v___x_2228_;
v___y_1220_ = v___y_2221_;
v___y_1221_ = v___y_2222_;
v_a_1222_ = v_a_2247_;
goto v___jp_1214_;
}
}
else
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec_ref(v___y_2219_);
v___x_2248_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v___y_2218_);
v___x_2249_ = lean_apply_6(v___y_2215_, v___y_2218_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; uint8_t v___x_2251_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref(v___x_2249_);
v___x_2251_ = lean_unbox(v_a_2250_);
lean_dec(v_a_2250_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2252_; 
lean_inc_ref(v_next_1041_);
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v___y_2218_);
v___x_2252_ = lean_apply_7(v_next_1041_, v___y_2218_, v___y_2217_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; 
lean_dec(v___y_2223_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2214_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec_ref(v_cfg_1039_);
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref(v___x_2252_);
v___y_1154_ = v___y_2213_;
v___y_1155_ = v_a_2225_;
v___y_1156_ = v___y_2216_;
v___y_1157_ = v___x_2248_;
v___y_1158_ = v___y_2220_;
v___y_1159_ = v___y_2221_;
v___y_1160_ = v___y_2222_;
v_a_1161_ = v_a_2253_;
goto v___jp_1153_;
}
else
{
lean_object* v_a_2254_; uint8_t v___x_2255_; 
v_a_2254_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2254_);
lean_dec_ref(v___x_2252_);
v___x_2255_ = l_Lean_Exception_isInterrupt(v_a_2254_);
if (v___x_2255_ == 0)
{
uint8_t v___x_2256_; 
lean_inc(v_a_2254_);
v___x_2256_ = l_Lean_Exception_isRuntime(v_a_2254_);
v___y_2089_ = v___x_2227_;
v___y_2090_ = v___y_2213_;
v___y_2091_ = v___y_2214_;
v___y_2092_ = v_a_2225_;
v___y_2093_ = v___x_2248_;
v___y_2094_ = v___y_2221_;
v___y_2095_ = v_a_2254_;
v___y_2096_ = v___y_2216_;
v___y_2097_ = v___y_2218_;
v___y_2098_ = v___y_2220_;
v___y_2099_ = v___y_2222_;
v___y_2100_ = v___y_2223_;
v___y_2101_ = v___x_2256_;
goto v___jp_2088_;
}
else
{
v___y_2089_ = v___x_2227_;
v___y_2090_ = v___y_2213_;
v___y_2091_ = v___y_2214_;
v___y_2092_ = v_a_2225_;
v___y_2093_ = v___x_2248_;
v___y_2094_ = v___y_2221_;
v___y_2095_ = v_a_2254_;
v___y_2096_ = v___y_2216_;
v___y_2097_ = v___y_2218_;
v___y_2098_ = v___y_2220_;
v___y_2099_ = v___y_2222_;
v___y_2100_ = v___y_2223_;
v___y_2101_ = v___x_2255_;
goto v___jp_2088_;
}
}
}
else
{
lean_object* v___x_2257_; lean_object* v_a_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___y_2214_);
lean_inc(v_trace_1040_);
v___x_2257_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = lean_nat_add(v_n_1955_, v_one_1954_);
lean_dec(v_n_1955_);
v___x_2260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___y_2218_);
lean_ctor_set(v___x_2260_, 1, v_acc_1045_);
v___x_2261_ = lean_unbox(v_a_2258_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = l_Lean_trace_profiler;
v___x_2263_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2213_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; 
lean_dec(v_a_2258_);
lean_inc(v_trace_1040_);
v___x_2264_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___x_2259_, v___y_2223_, v___x_2260_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
v___y_1174_ = v___y_2213_;
v___y_1175_ = v_a_2225_;
v___y_1176_ = v___y_2216_;
v___y_1177_ = v___y_2220_;
v___y_1178_ = v___x_2248_;
v___y_1179_ = v___y_2222_;
v___y_1180_ = v___y_2221_;
v___y_1181_ = v___x_2264_;
goto v___jp_1173_;
}
else
{
uint8_t v___x_2265_; 
v___x_2265_ = lean_unbox(v_a_2258_);
lean_dec(v_a_2258_);
v___y_1785_ = v___x_2227_;
v___y_1786_ = v___x_2265_;
v___y_1787_ = v___x_2259_;
v___y_1788_ = v___y_2213_;
v___y_1789_ = v___x_2260_;
v___y_1790_ = v_a_2225_;
v___y_1791_ = v___x_2248_;
v___y_1792_ = v___y_2221_;
v___y_1793_ = v___y_2216_;
v___y_1794_ = v___y_2220_;
v___y_1795_ = v___y_2222_;
v___y_1796_ = v___y_2223_;
goto v___jp_1784_;
}
}
else
{
uint8_t v___x_2266_; 
v___x_2266_ = lean_unbox(v_a_2258_);
lean_dec(v_a_2258_);
v___y_1785_ = v___x_2227_;
v___y_1786_ = v___x_2266_;
v___y_1787_ = v___x_2259_;
v___y_1788_ = v___y_2213_;
v___y_1789_ = v___x_2260_;
v___y_1790_ = v_a_2225_;
v___y_1791_ = v___x_2248_;
v___y_1792_ = v___y_2221_;
v___y_1793_ = v___y_2216_;
v___y_1794_ = v___y_2220_;
v___y_1795_ = v___y_2222_;
v___y_1796_ = v___y_2223_;
goto v___jp_1784_;
}
}
}
else
{
lean_object* v_a_2267_; 
lean_dec(v___y_2223_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v___y_2214_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec_ref(v_cfg_1039_);
v_a_2267_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2267_);
lean_dec_ref(v___x_2249_);
v___y_1164_ = v___y_2213_;
v___y_1165_ = v_a_2225_;
v___y_1166_ = v___y_2216_;
v___y_1167_ = v___x_2248_;
v___y_1168_ = v___y_2220_;
v___y_1169_ = v___y_2221_;
v___y_1170_ = v___y_2222_;
v_a_1171_ = v_a_2267_;
goto v___jp_1163_;
}
}
}
v___jp_2268_:
{
if (v___y_2273_ == 0)
{
lean_object* v___x_2274_; 
lean_dec_ref(v___y_2271_);
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v___y_2270_);
v___x_2274_ = lean_apply_6(v___y_2269_, v___y_2270_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref(v___x_2274_);
if (lean_obj_tag(v_a_2275_) == 0)
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_nat_add(v_n_1955_, v_one_1954_);
lean_dec(v_n_1955_);
v___x_2277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___y_2270_);
lean_ctor_set(v___x_2277_, 1, v_acc_1045_);
v_n_1043_ = v___x_2276_;
v_curr_1044_ = v___y_2272_;
v_acc_1045_ = v___x_2277_;
goto _start;
}
else
{
lean_object* v_val_2279_; lean_object* v___x_2280_; 
lean_dec(v___y_2270_);
v_val_2279_ = lean_ctor_get(v_a_2275_, 0);
lean_inc(v_val_2279_);
lean_dec_ref(v_a_2275_);
v___x_2280_ = l_List_appendTR___redArg(v_val_2279_, v___y_2272_);
v_n_1043_ = v_n_1955_;
v_curr_1044_ = v___x_2280_;
goto _start;
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v___y_2272_);
lean_dec(v___y_2270_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
v_a_2282_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2274_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2274_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_dec(v___y_2272_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
return v___y_2271_;
}
}
v___jp_2290_:
{
if (lean_obj_tag(v_a_2291_) == 0)
{
if (lean_obj_tag(v_curr_1044_) == 0)
{
lean_object* v_options_2292_; uint8_t v_hasTrace_2293_; lean_object* v___x_2294_; 
lean_dec(v_n_1955_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec_ref(v_cfg_1039_);
v_options_2292_ = lean_ctor_get(v_a_1048_, 2);
v_hasTrace_2293_ = lean_ctor_get_uint8(v_options_2292_, sizeof(void*)*1);
v___x_2294_ = l_List_reverse___redArg(v_acc_1045_);
if (v_hasTrace_2293_ == 0)
{
lean_object* v___x_2295_; 
lean_dec(v_trace_1040_);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
return v___x_2295_;
}
else
{
lean_object* v___x_2296_; lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2310_; 
lean_inc(v_trace_1040_);
v___x_2296_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2310_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2310_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
v___x_2302_ = lean_unbox(v_a_2297_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = l_Lean_trace_profiler;
v___x_2304_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_2292_, v___x_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2306_; 
lean_dec(v_a_2297_);
lean_dec(v_trace_1040_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2294_);
v___x_2306_ = v___x_2299_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2294_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
else
{
uint8_t v___x_2308_; 
lean_del_object(v___x_2299_);
v___x_2308_ = lean_unbox(v_a_2297_);
lean_dec(v_a_2297_);
v___y_1328_ = v_hasTrace_2293_;
v___y_1329_ = v___x_2294_;
v___y_1330_ = v_options_2292_;
v___y_1331_ = v___x_2301_;
v___y_1332_ = v___x_2308_;
goto v___jp_1327_;
}
}
else
{
uint8_t v___x_2309_; 
lean_del_object(v___x_2299_);
v___x_2309_ = lean_unbox(v_a_2297_);
lean_dec(v_a_2297_);
v___y_1328_ = v_hasTrace_2293_;
v___y_1329_ = v___x_2294_;
v___y_1330_ = v_options_2292_;
v___y_1331_ = v___x_2301_;
v___y_1332_ = v___x_2309_;
goto v___jp_1327_;
}
}
}
}
else
{
lean_object* v_head_2311_; lean_object* v_tail_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2392_; 
v_head_2311_ = lean_ctor_get(v_curr_1044_, 0);
v_tail_2312_ = lean_ctor_get(v_curr_1044_, 1);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_curr_1044_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2314_ = v_curr_1044_;
v_isShared_2315_ = v_isSharedCheck_2392_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_tail_2312_);
lean_inc(v_head_2311_);
lean_dec(v_curr_1044_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2392_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v_a_2317_; uint8_t v___x_2318_; uint8_t v___x_2319_; 
v___x_2316_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(v_head_2311_, v_a_1047_);
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref(v___x_2316_);
v___x_2318_ = 1;
v___x_2319_ = lean_unbox(v_a_2317_);
lean_dec(v_a_2317_);
if (v___x_2319_ == 0)
{
lean_object* v_options_2320_; uint8_t v_hasTrace_2321_; 
v_options_2320_ = lean_ctor_get(v_a_1048_, 2);
v_hasTrace_2321_ = lean_ctor_get_uint8(v_options_2320_, sizeof(void*)*1);
if (v_hasTrace_2321_ == 0)
{
lean_object* v___x_2322_; 
lean_inc_ref(v_suspend_1240_);
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v_head_2311_);
v___x_2322_ = lean_apply_6(v_suspend_1240_, v_head_2311_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; uint8_t v___x_2324_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref(v___x_2322_);
v___x_2324_ = lean_unbox(v_a_2323_);
lean_dec(v_a_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___f_2325_; lean_object* v___x_2326_; 
lean_del_object(v___x_2314_);
lean_inc(v_acc_1045_);
lean_inc(v_n_1955_);
lean_inc(v_goals_1042_);
lean_inc_ref(v_next_1041_);
lean_inc(v_trace_1040_);
lean_inc_ref(v_cfg_1039_);
lean_inc(v_tail_2312_);
v___f_2325_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2325_, 0, v_tail_2312_);
lean_closure_set(v___f_2325_, 1, v_cfg_1039_);
lean_closure_set(v___f_2325_, 2, v_trace_1040_);
lean_closure_set(v___f_2325_, 3, v_next_1041_);
lean_closure_set(v___f_2325_, 4, v_goals_1042_);
lean_closure_set(v___f_2325_, 5, v_n_1955_);
lean_closure_set(v___f_2325_, 6, v_acc_1045_);
lean_inc_ref(v_next_1041_);
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v_head_2311_);
v___x_2326_ = lean_apply_7(v_next_1041_, v_head_2311_, v___f_2325_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_dec(v_tail_2312_);
lean_dec(v_head_2311_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
return v___x_2326_;
}
else
{
lean_object* v_a_2327_; uint8_t v___x_2328_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
v___x_2328_ = l_Lean_Exception_isInterrupt(v_a_2327_);
if (v___x_2328_ == 0)
{
uint8_t v___x_2329_; 
v___x_2329_ = l_Lean_Exception_isRuntime(v_a_2327_);
lean_inc_ref(v_discharge_1241_);
v___y_2269_ = v_discharge_1241_;
v___y_2270_ = v_head_2311_;
v___y_2271_ = v___x_2326_;
v___y_2272_ = v_tail_2312_;
v___y_2273_ = v___x_2329_;
goto v___jp_2268_;
}
else
{
lean_dec(v_a_2327_);
lean_inc_ref(v_discharge_1241_);
v___y_2269_ = v_discharge_1241_;
v___y_2270_ = v_head_2311_;
v___y_2271_ = v___x_2326_;
v___y_2272_ = v_tail_2312_;
v___y_2273_ = v___x_2328_;
goto v___jp_2268_;
}
}
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2330_ = lean_nat_add(v_n_1955_, v_one_1954_);
lean_dec(v_n_1955_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v_acc_1045_);
v___x_2332_ = v___x_2314_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_head_2311_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_acc_1045_);
v___x_2332_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
v_n_1043_ = v___x_2330_;
v_curr_1044_ = v_tail_2312_;
v_acc_1045_ = v___x_2332_;
goto _start;
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_del_object(v___x_2314_);
lean_dec(v_tail_2312_);
lean_dec(v_head_2311_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
v_a_2335_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2322_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2322_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v___x_2343_; lean_object* v_a_2344_; lean_object* v___f_2345_; lean_object* v___f_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
lean_inc(v_trace_1040_);
v___x_2343_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref(v___x_2343_);
lean_inc(v_acc_1045_);
lean_inc(v_n_1955_);
lean_inc(v_goals_1042_);
lean_inc_ref(v_next_1041_);
lean_inc(v_trace_1040_);
lean_inc_ref(v_cfg_1039_);
lean_inc(v_tail_2312_);
v___f_2345_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2345_, 0, v_tail_2312_);
lean_closure_set(v___f_2345_, 1, v_cfg_1039_);
lean_closure_set(v___f_2345_, 2, v_trace_1040_);
lean_closure_set(v___f_2345_, 3, v_next_1041_);
lean_closure_set(v___f_2345_, 4, v_goals_1042_);
lean_closure_set(v___f_2345_, 5, v_n_1955_);
lean_closure_set(v___f_2345_, 6, v_acc_1045_);
lean_inc(v_head_2311_);
v___f_2346_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(v___f_2346_, 0, v_head_2311_);
v___x_2347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
v___x_2348_ = lean_unbox(v_a_2344_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; uint8_t v___x_2350_; 
v___x_2349_ = l_Lean_trace_profiler;
v___x_2350_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_2320_, v___x_2349_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; 
lean_dec_ref(v___f_2346_);
lean_dec(v_a_2344_);
lean_inc_ref(v_suspend_1240_);
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v_head_2311_);
v___x_2351_ = lean_apply_6(v_suspend_1240_, v_head_2311_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; uint8_t v___x_2353_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref(v___x_2351_);
v___x_2353_ = lean_unbox(v_a_2352_);
lean_dec(v_a_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; 
lean_del_object(v___x_2314_);
lean_inc_ref(v_next_1041_);
lean_inc(v_a_1049_);
lean_inc_ref(v_a_1048_);
lean_inc(v_a_1047_);
lean_inc_ref(v_a_1046_);
lean_inc(v_head_2311_);
v___x_2354_ = lean_apply_7(v_next_1041_, v_head_2311_, v___f_2345_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, lean_box(0));
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_dec(v_tail_2312_);
lean_dec(v_head_2311_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
return v___x_2354_;
}
else
{
lean_object* v_a_2355_; uint8_t v___x_2356_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
v___x_2356_ = l_Lean_Exception_isInterrupt(v_a_2355_);
if (v___x_2356_ == 0)
{
uint8_t v___x_2357_; 
v___x_2357_ = l_Lean_Exception_isRuntime(v_a_2355_);
lean_inc_ref(v_discharge_1241_);
v___y_2003_ = v___x_2350_;
v___y_2004_ = v_options_2320_;
v___y_2005_ = v_discharge_1241_;
v___y_2006_ = v_head_2311_;
v___y_2007_ = v___x_2354_;
v___y_2008_ = v___x_2347_;
v___y_2009_ = v___x_2318_;
v___y_2010_ = v_tail_2312_;
v___y_2011_ = v___x_2357_;
goto v___jp_2002_;
}
else
{
lean_dec(v_a_2355_);
lean_inc_ref(v_discharge_1241_);
v___y_2003_ = v___x_2350_;
v___y_2004_ = v_options_2320_;
v___y_2005_ = v_discharge_1241_;
v___y_2006_ = v_head_2311_;
v___y_2007_ = v___x_2354_;
v___y_2008_ = v___x_2347_;
v___y_2009_ = v___x_2318_;
v___y_2010_ = v_tail_2312_;
v___y_2011_ = v___x_2356_;
goto v___jp_2002_;
}
}
}
else
{
lean_object* v___x_2358_; lean_object* v_a_2359_; lean_object* v___x_2360_; lean_object* v___x_2362_; 
lean_dec_ref(v___f_2345_);
lean_inc(v_trace_1040_);
v___x_2358_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref(v___x_2358_);
v___x_2360_ = lean_nat_add(v_n_1955_, v_one_1954_);
lean_dec(v_n_1955_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v_acc_1045_);
v___x_2362_ = v___x_2314_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_head_2311_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_acc_1045_);
v___x_2362_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
uint8_t v___x_2363_; 
v___x_2363_ = lean_unbox(v_a_2359_);
if (v___x_2363_ == 0)
{
if (v___x_2350_ == 0)
{
lean_dec(v_a_2359_);
v_n_1043_ = v___x_2360_;
v_curr_1044_ = v_tail_2312_;
v_acc_1045_ = v___x_2362_;
goto _start;
}
else
{
uint8_t v___x_2365_; 
v___x_2365_ = lean_unbox(v_a_2359_);
lean_dec(v_a_2359_);
v___y_1279_ = v___x_2362_;
v___y_1280_ = v___x_2360_;
v___y_1281_ = v_options_2320_;
v___y_1282_ = v___x_2318_;
v___y_1283_ = v___x_2347_;
v___y_1284_ = v___x_2365_;
v___y_1285_ = v_tail_2312_;
goto v___jp_1278_;
}
}
else
{
uint8_t v___x_2366_; 
v___x_2366_ = lean_unbox(v_a_2359_);
lean_dec(v_a_2359_);
v___y_1279_ = v___x_2362_;
v___y_1280_ = v___x_2360_;
v___y_1281_ = v_options_2320_;
v___y_1282_ = v___x_2318_;
v___y_1283_ = v___x_2347_;
v___y_1284_ = v___x_2366_;
v___y_1285_ = v_tail_2312_;
goto v___jp_1278_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec_ref(v___f_2345_);
lean_del_object(v___x_2314_);
lean_dec(v_tail_2312_);
lean_dec(v_head_2311_);
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
v_a_2368_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2351_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2351_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
uint8_t v___x_2376_; 
lean_del_object(v___x_2314_);
v___x_2376_ = lean_unbox(v_a_2344_);
lean_dec(v_a_2344_);
lean_inc_ref(v___f_2345_);
lean_inc_ref(v_suspend_1240_);
lean_inc_ref(v_discharge_1241_);
v___y_2213_ = v_options_2320_;
v___y_2214_ = v_discharge_1241_;
v___y_2215_ = v_suspend_1240_;
v___y_2216_ = v___f_2346_;
v___y_2217_ = v___f_2345_;
v___y_2218_ = v_head_2311_;
v___y_2219_ = v___f_2345_;
v___y_2220_ = v___x_2376_;
v___y_2221_ = v___x_2318_;
v___y_2222_ = v___x_2347_;
v___y_2223_ = v_tail_2312_;
goto v___jp_2212_;
}
}
else
{
uint8_t v___x_2377_; 
lean_del_object(v___x_2314_);
v___x_2377_ = lean_unbox(v_a_2344_);
lean_dec(v_a_2344_);
lean_inc_ref(v___f_2345_);
lean_inc_ref(v_suspend_1240_);
lean_inc_ref(v_discharge_1241_);
v___y_2213_ = v_options_2320_;
v___y_2214_ = v_discharge_1241_;
v___y_2215_ = v_suspend_1240_;
v___y_2216_ = v___f_2346_;
v___y_2217_ = v___f_2345_;
v___y_2218_ = v_head_2311_;
v___y_2219_ = v___f_2345_;
v___y_2220_ = v___x_2377_;
v___y_2221_ = v___x_2318_;
v___y_2222_ = v___x_2347_;
v___y_2223_ = v_tail_2312_;
goto v___jp_2212_;
}
}
}
else
{
lean_object* v_options_2378_; uint8_t v_hasTrace_2379_; lean_object* v___x_2380_; 
lean_del_object(v___x_2314_);
v_options_2378_ = lean_ctor_get(v_a_1048_, 2);
v_hasTrace_2379_ = lean_ctor_get_uint8(v_options_2378_, sizeof(void*)*1);
v___x_2380_ = lean_nat_add(v_n_1955_, v_one_1954_);
lean_dec(v_n_1955_);
if (v_hasTrace_2379_ == 0)
{
lean_dec(v_head_2311_);
v_n_1043_ = v___x_2380_;
v_curr_1044_ = v_tail_2312_;
goto _start;
}
else
{
lean_object* v___x_2382_; lean_object* v_a_2383_; lean_object* v___f_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
lean_inc(v_trace_1040_);
v___x_2382_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1040_, v_a_1048_);
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref(v___x_2382_);
v___f_2384_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2384_, 0, v_head_2311_);
v___x_2385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
v___x_2386_ = lean_unbox(v_a_2383_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = l_Lean_trace_profiler;
v___x_2388_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_2378_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_dec_ref(v___f_2384_);
lean_dec(v_a_2383_);
v_n_1043_ = v___x_2380_;
v_curr_1044_ = v_tail_2312_;
goto _start;
}
else
{
uint8_t v___x_2390_; 
v___x_2390_ = lean_unbox(v_a_2383_);
lean_dec(v_a_2383_);
v___y_1089_ = v___x_2380_;
v___y_1090_ = v___x_2390_;
v___y_1091_ = v_options_2378_;
v___y_1092_ = v___f_2384_;
v___y_1093_ = v___x_2385_;
v___y_1094_ = v___x_2318_;
v___y_1095_ = v_tail_2312_;
goto v___jp_1088_;
}
}
else
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_unbox(v_a_2383_);
lean_dec(v_a_2383_);
v___y_1089_ = v___x_2380_;
v___y_1090_ = v___x_2391_;
v___y_1091_ = v_options_2378_;
v___y_1092_ = v___f_2384_;
v___y_1093_ = v___x_2385_;
v___y_1094_ = v___x_2318_;
v___y_1095_ = v_tail_2312_;
goto v___jp_1088_;
}
}
}
}
}
}
else
{
lean_object* v_val_2393_; 
lean_dec(v_curr_1044_);
v_val_2393_ = lean_ctor_get(v_a_2291_, 0);
lean_inc(v_val_2393_);
lean_dec_ref(v_a_2291_);
v_n_1043_ = v_n_1955_;
v_curr_1044_ = v_val_2393_;
goto _start;
}
}
v___jp_2395_:
{
if (lean_obj_tag(v___y_2396_) == 0)
{
lean_object* v_a_2397_; 
v_a_2397_ = lean_ctor_get(v___y_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref(v___y_2396_);
v_a_2291_ = v_a_2397_;
goto v___jp_2290_;
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec(v_n_1955_);
lean_dec(v_acc_1045_);
lean_dec(v_curr_1044_);
lean_dec(v_goals_1042_);
lean_dec_ref(v_next_1041_);
lean_dec(v_trace_1040_);
lean_dec_ref(v_cfg_1039_);
v_a_2398_ = lean_ctor_get(v___y_2396_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___y_2396_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___y_2396_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___y_2396_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
v___jp_1051_:
{
lean_object* v___x_1060_; double v___x_1061_; double v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1060_ = lean_io_get_num_heartbeats();
v___x_1061_ = lean_float_of_nat(v___y_1054_);
v___x_1062_ = lean_float_of_nat(v___x_1060_);
v___x_1063_ = lean_box_float(v___x_1061_);
v___x_1064_ = lean_box_float(v___x_1062_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_a_1059_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1058_, v___y_1057_, v___y_1055_, v___y_1053_, v___y_1052_, v___y_1056_, v___x_1066_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1067_;
}
v___jp_1068_:
{
lean_object* v___x_1077_; double v___x_1078_; double v___x_1079_; double v___x_1080_; double v___x_1081_; double v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1077_ = lean_io_mono_nanos_now();
v___x_1078_ = lean_float_of_nat(v___y_1071_);
v___x_1079_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1080_ = lean_float_div(v___x_1078_, v___x_1079_);
v___x_1081_ = lean_float_of_nat(v___x_1077_);
v___x_1082_ = lean_float_div(v___x_1081_, v___x_1079_);
v___x_1083_ = lean_box_float(v___x_1080_);
v___x_1084_ = lean_box_float(v___x_1082_);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_a_1076_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1075_, v___y_1074_, v___y_1072_, v___y_1070_, v___y_1069_, v___y_1073_, v___x_1086_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1087_;
}
v___jp_1088_:
{
lean_object* v___x_1096_; lean_object* v_a_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1096_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1049_);
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1099_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_1091_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1040_);
v___x_1101_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1089_, v___y_1095_, v_acc_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set_tag(v___x_1104_, 1);
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
v___y_1069_ = v_a_1097_;
v___y_1070_ = v___y_1090_;
v___y_1071_ = v___x_1100_;
v___y_1072_ = v___y_1091_;
v___y_1073_ = v___y_1092_;
v___y_1074_ = v___y_1093_;
v___y_1075_ = v___y_1094_;
v_a_1076_ = v___x_1107_;
goto v___jp_1068_;
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_a_1110_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1101_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1101_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 0);
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
v___y_1069_ = v_a_1097_;
v___y_1070_ = v___y_1090_;
v___y_1071_ = v___x_1100_;
v___y_1072_ = v___y_1091_;
v___y_1073_ = v___y_1092_;
v___y_1074_ = v___y_1093_;
v___y_1075_ = v___y_1094_;
v_a_1076_ = v___x_1115_;
goto v___jp_1068_;
}
}
}
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1040_);
v___x_1119_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1039_, v_trace_1040_, v_next_1041_, v_goals_1042_, v___y_1089_, v___y_1095_, v_acc_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 1);
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
v___y_1052_ = v_a_1097_;
v___y_1053_ = v___y_1090_;
v___y_1054_ = v___x_1118_;
v___y_1055_ = v___y_1091_;
v___y_1056_ = v___y_1092_;
v___y_1057_ = v___y_1093_;
v___y_1058_ = v___y_1094_;
v_a_1059_ = v___x_1125_;
goto v___jp_1051_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_a_1128_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1119_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1119_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 0);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
v___y_1052_ = v_a_1097_;
v___y_1053_ = v___y_1090_;
v___y_1054_ = v___x_1118_;
v___y_1055_ = v___y_1091_;
v___y_1056_ = v___y_1092_;
v___y_1057_ = v___y_1093_;
v___y_1058_ = v___y_1094_;
v_a_1059_ = v___x_1133_;
goto v___jp_1051_;
}
}
}
}
}
v___jp_1136_:
{
lean_object* v___x_1145_; double v___x_1146_; double v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1145_ = lean_io_get_num_heartbeats();
v___x_1146_ = lean_float_of_nat(v___y_1141_);
v___x_1147_ = lean_float_of_nat(v___x_1145_);
v___x_1148_ = lean_box_float(v___x_1146_);
v___x_1149_ = lean_box_float(v___x_1147_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_a_1144_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1143_, v___y_1142_, v___y_1137_, v___y_1140_, v___y_1138_, v___y_1139_, v___x_1151_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1152_;
}
v___jp_1153_:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_a_1161_);
v___y_1137_ = v___y_1154_;
v___y_1138_ = v___y_1155_;
v___y_1139_ = v___y_1156_;
v___y_1140_ = v___y_1158_;
v___y_1141_ = v___y_1157_;
v___y_1142_ = v___y_1160_;
v___y_1143_ = v___y_1159_;
v_a_1144_ = v___x_1162_;
goto v___jp_1136_;
}
v___jp_1163_:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_a_1171_);
v___y_1137_ = v___y_1164_;
v___y_1138_ = v___y_1165_;
v___y_1139_ = v___y_1166_;
v___y_1140_ = v___y_1168_;
v___y_1141_ = v___y_1167_;
v___y_1142_ = v___y_1170_;
v___y_1143_ = v___y_1169_;
v_a_1144_ = v___x_1172_;
goto v___jp_1136_;
}
v___jp_1173_:
{
if (lean_obj_tag(v___y_1181_) == 0)
{
lean_object* v_a_1182_; 
v_a_1182_ = lean_ctor_get(v___y_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref(v___y_1181_);
v___y_1154_ = v___y_1174_;
v___y_1155_ = v___y_1175_;
v___y_1156_ = v___y_1176_;
v___y_1157_ = v___y_1178_;
v___y_1158_ = v___y_1177_;
v___y_1159_ = v___y_1180_;
v___y_1160_ = v___y_1179_;
v_a_1161_ = v_a_1182_;
goto v___jp_1153_;
}
else
{
lean_object* v_a_1183_; 
v_a_1183_ = lean_ctor_get(v___y_1181_, 0);
lean_inc(v_a_1183_);
lean_dec_ref(v___y_1181_);
v___y_1164_ = v___y_1174_;
v___y_1165_ = v___y_1175_;
v___y_1166_ = v___y_1176_;
v___y_1167_ = v___y_1178_;
v___y_1168_ = v___y_1177_;
v___y_1169_ = v___y_1180_;
v___y_1170_ = v___y_1179_;
v_a_1171_ = v_a_1183_;
goto v___jp_1163_;
}
}
v___jp_1184_:
{
lean_object* v___x_1193_; double v___x_1194_; double v___x_1195_; double v___x_1196_; double v___x_1197_; double v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1193_ = lean_io_mono_nanos_now();
v___x_1194_ = lean_float_of_nat(v___y_1191_);
v___x_1195_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1196_ = lean_float_div(v___x_1194_, v___x_1195_);
v___x_1197_ = lean_float_of_nat(v___x_1193_);
v___x_1198_ = lean_float_div(v___x_1197_, v___x_1195_);
v___x_1199_ = lean_box_float(v___x_1196_);
v___x_1200_ = lean_box_float(v___x_1198_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_a_1192_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1040_, v___y_1190_, v___y_1189_, v___y_1185_, v___y_1188_, v___y_1186_, v___y_1187_, v___x_1202_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_);
return v___x_1203_;
}
v___jp_1204_:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_a_1212_);
v___y_1185_ = v___y_1205_;
v___y_1186_ = v___y_1206_;
v___y_1187_ = v___y_1207_;
v___y_1188_ = v___y_1208_;
v___y_1189_ = v___y_1211_;
v___y_1190_ = v___y_1210_;
v___y_1191_ = v___y_1209_;
v_a_1192_ = v___x_1213_;
goto v___jp_1184_;
}
v___jp_1214_:
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_a_1222_);
v___y_1185_ = v___y_1215_;
v___y_1186_ = v___y_1216_;
v___y_1187_ = v___y_1217_;
v___y_1188_ = v___y_1218_;
v___y_1189_ = v___y_1221_;
v___y_1190_ = v___y_1220_;
v___y_1191_ = v___y_1219_;
v_a_1192_ = v___x_1223_;
goto v___jp_1184_;
}
v___jp_1224_:
{
if (lean_obj_tag(v___y_1232_) == 0)
{
lean_object* v_a_1233_; 
v_a_1233_ = lean_ctor_get(v___y_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v___y_1232_);
v___y_1205_ = v___y_1225_;
v___y_1206_ = v___y_1226_;
v___y_1207_ = v___y_1227_;
v___y_1208_ = v___y_1228_;
v___y_1209_ = v___y_1231_;
v___y_1210_ = v___y_1230_;
v___y_1211_ = v___y_1229_;
v_a_1212_ = v_a_1233_;
goto v___jp_1204_;
}
else
{
lean_object* v_a_1234_; 
v_a_1234_ = lean_ctor_get(v___y_1232_, 0);
lean_inc(v_a_1234_);
lean_dec_ref(v___y_1232_);
v___y_1215_ = v___y_1225_;
v___y_1216_ = v___y_1226_;
v___y_1217_ = v___y_1227_;
v___y_1218_ = v___y_1228_;
v___y_1219_ = v___y_1231_;
v___y_1220_ = v___y_1230_;
v___y_1221_ = v___y_1229_;
v_a_1222_ = v_a_1234_;
goto v___jp_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2481_, lean_object* v_trace_2482_, lean_object* v_next_2483_, lean_object* v_goals_2484_, lean_object* v_n_2485_, lean_object* v_curr_2486_, lean_object* v_acc_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2481_, v_trace_2482_, v_next_2483_, v_goals_2484_, v_n_2485_, v_curr_2486_, v_acc_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object* v_tail_2494_, lean_object* v_cfg_2495_, lean_object* v_trace_2496_, lean_object* v_next_2497_, lean_object* v_goals_2498_, lean_object* v_n_2499_, lean_object* v_acc_2500_, lean_object* v_r_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = l_List_appendTR___redArg(v_r_2501_, v_tail_2494_);
v___x_2508_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2508_, 0, v_cfg_2495_);
lean_closure_set(v___x_2508_, 1, v_trace_2496_);
lean_closure_set(v___x_2508_, 2, v_next_2497_);
lean_closure_set(v___x_2508_, 3, v_goals_2498_);
lean_closure_set(v___x_2508_, 4, v_n_2499_);
lean_closure_set(v___x_2508_, 5, v___x_2507_);
lean_closure_set(v___x_2508_, 6, v_acc_2500_);
v___x_2509_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg(v___x_2508_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2510_, lean_object* v_msg_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2518_, lean_object* v_msg_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2518_, v_msg_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(lean_object* v_00_u03b1_2526_, lean_object* v_x_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_x_2527_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2534_, lean_object* v_x_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(v_00_u03b1_2534_, v_x_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_mvarId_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v___x_2548_; 
v___x_2548_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(v_mvarId_2542_, v___y_2544_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_mvarId_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_mvarId_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v_mvarId_2549_);
return v_res_2555_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11(lean_object* v_00_u03b2_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_){
_start:
{
uint8_t v___x_2559_; 
v___x_2559_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(v_x_2557_, v_x_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___boxed(lean_object* v_00_u03b2_2560_, lean_object* v_x_2561_, lean_object* v_x_2562_){
_start:
{
uint8_t v_res_2563_; lean_object* v_r_2564_; 
v_res_2563_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11(v_00_u03b2_2560_, v_x_2561_, v_x_2562_);
lean_dec(v_x_2562_);
v_r_2564_ = lean_box(v_res_2563_);
return v_r_2564_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13(lean_object* v_00_u03b2_2565_, lean_object* v_x_2566_, size_t v_x_2567_, lean_object* v_x_2568_){
_start:
{
uint8_t v___x_2569_; 
v___x_2569_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(v_x_2566_, v_x_2567_, v_x_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___boxed(lean_object* v_00_u03b2_2570_, lean_object* v_x_2571_, lean_object* v_x_2572_, lean_object* v_x_2573_){
_start:
{
size_t v_x_75129__boxed_2574_; uint8_t v_res_2575_; lean_object* v_r_2576_; 
v_x_75129__boxed_2574_ = lean_unbox_usize(v_x_2572_);
lean_dec(v_x_2572_);
v_res_2575_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13(v_00_u03b2_2570_, v_x_2571_, v_x_75129__boxed_2574_, v_x_2573_);
lean_dec(v_x_2573_);
v_r_2576_ = lean_box(v_res_2575_);
return v_r_2576_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16(lean_object* v_00_u03b2_2577_, lean_object* v_keys_2578_, lean_object* v_vals_2579_, lean_object* v_heq_2580_, lean_object* v_i_2581_, lean_object* v_k_2582_){
_start:
{
uint8_t v___x_2583_; 
v___x_2583_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(v_keys_2578_, v_i_2581_, v_k_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___boxed(lean_object* v_00_u03b2_2584_, lean_object* v_keys_2585_, lean_object* v_vals_2586_, lean_object* v_heq_2587_, lean_object* v_i_2588_, lean_object* v_k_2589_){
_start:
{
uint8_t v_res_2590_; lean_object* v_r_2591_; 
v_res_2590_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16(v_00_u03b2_2584_, v_keys_2585_, v_vals_2586_, v_heq_2587_, v_i_2588_, v_k_2589_);
lean_dec(v_k_2589_);
lean_dec_ref(v_vals_2586_);
lean_dec_ref(v_keys_2585_);
v_r_2591_ = lean_box(v_res_2590_);
return v_r_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2592_, lean_object* v_h__1_2593_, lean_object* v_h__2_2594_){
_start:
{
lean_object* v_zero_2595_; uint8_t v_isZero_2596_; 
v_zero_2595_ = lean_unsigned_to_nat(0u);
v_isZero_2596_ = lean_nat_dec_eq(v_n_2592_, v_zero_2595_);
if (v_isZero_2596_ == 1)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec(v_h__2_2594_);
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_apply_1(v_h__1_2593_, v___x_2597_);
return v___x_2598_;
}
else
{
lean_object* v_one_2599_; lean_object* v_n_2600_; lean_object* v___x_2601_; 
lean_dec(v_h__1_2593_);
v_one_2599_ = lean_unsigned_to_nat(1u);
v_n_2600_ = lean_nat_sub(v_n_2592_, v_one_2599_);
v___x_2601_ = lean_apply_1(v_h__2_2594_, v_n_2600_);
return v___x_2601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2602_, lean_object* v_h__1_2603_, lean_object* v_h__2_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2602_, v_h__1_2603_, v_h__2_2604_);
lean_dec(v_n_2602_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2606_, lean_object* v_n_2607_, lean_object* v_h__1_2608_, lean_object* v_h__2_2609_){
_start:
{
lean_object* v_zero_2610_; uint8_t v_isZero_2611_; 
v_zero_2610_ = lean_unsigned_to_nat(0u);
v_isZero_2611_ = lean_nat_dec_eq(v_n_2607_, v_zero_2610_);
if (v_isZero_2611_ == 1)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_dec(v_h__2_2609_);
v___x_2612_ = lean_box(0);
v___x_2613_ = lean_apply_1(v_h__1_2608_, v___x_2612_);
return v___x_2613_;
}
else
{
lean_object* v_one_2614_; lean_object* v_n_2615_; lean_object* v___x_2616_; 
lean_dec(v_h__1_2608_);
v_one_2614_ = lean_unsigned_to_nat(1u);
v_n_2615_ = lean_nat_sub(v_n_2607_, v_one_2614_);
v___x_2616_ = lean_apply_1(v_h__2_2609_, v_n_2615_);
return v___x_2616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* v_motive_2617_, lean_object* v_n_2618_, lean_object* v_h__1_2619_, lean_object* v_h__2_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(v_motive_2617_, v_n_2618_, v_h__1_2619_, v_h__2_2620_);
lean_dec(v_n_2618_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* v_procResult_x3f_2622_, lean_object* v_h__1_2623_, lean_object* v_h__2_2624_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2622_) == 0)
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec(v_h__1_2623_);
v___x_2625_ = lean_box(0);
v___x_2626_ = lean_apply_1(v_h__2_2624_, v___x_2625_);
return v___x_2626_;
}
else
{
lean_object* v_val_2627_; lean_object* v___x_2628_; 
lean_dec(v_h__2_2624_);
v_val_2627_ = lean_ctor_get(v_procResult_x3f_2622_, 0);
lean_inc(v_val_2627_);
lean_dec_ref(v_procResult_x3f_2622_);
v___x_2628_ = lean_apply_1(v_h__1_2623_, v_val_2627_);
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* v_motive_2629_, lean_object* v_procResult_x3f_2630_, lean_object* v_h__1_2631_, lean_object* v_h__2_2632_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2630_) == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_dec(v_h__1_2631_);
v___x_2633_ = lean_box(0);
v___x_2634_ = lean_apply_1(v_h__2_2632_, v___x_2633_);
return v___x_2634_;
}
else
{
lean_object* v_val_2635_; lean_object* v___x_2636_; 
lean_dec(v_h__2_2632_);
v_val_2635_ = lean_ctor_get(v_procResult_x3f_2630_, 0);
lean_inc(v_val_2635_);
lean_dec_ref(v_procResult_x3f_2630_);
v___x_2636_ = lean_apply_1(v_h__1_2631_, v_val_2635_);
return v___x_2636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2637_, lean_object* v_h__1_2638_, lean_object* v_h__2_2639_){
_start:
{
if (lean_obj_tag(v_curr_2637_) == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_dec(v_h__2_2639_);
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_apply_1(v_h__1_2638_, v___x_2640_);
return v___x_2641_;
}
else
{
lean_object* v_head_2642_; lean_object* v_tail_2643_; lean_object* v___x_2644_; 
lean_dec(v_h__1_2638_);
v_head_2642_ = lean_ctor_get(v_curr_2637_, 0);
lean_inc(v_head_2642_);
v_tail_2643_ = lean_ctor_get(v_curr_2637_, 1);
lean_inc(v_tail_2643_);
lean_dec_ref(v_curr_2637_);
v___x_2644_ = lean_apply_2(v_h__2_2639_, v_head_2642_, v_tail_2643_);
return v___x_2644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2645_, lean_object* v_curr_2646_, lean_object* v_h__1_2647_, lean_object* v_h__2_2648_){
_start:
{
if (lean_obj_tag(v_curr_2646_) == 0)
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec(v_h__2_2648_);
v___x_2649_ = lean_box(0);
v___x_2650_ = lean_apply_1(v_h__1_2647_, v___x_2649_);
return v___x_2650_;
}
else
{
lean_object* v_head_2651_; lean_object* v_tail_2652_; lean_object* v___x_2653_; 
lean_dec(v_h__1_2647_);
v_head_2651_ = lean_ctor_get(v_curr_2646_, 0);
lean_inc(v_head_2651_);
v_tail_2652_ = lean_ctor_get(v_curr_2646_, 1);
lean_inc(v_tail_2652_);
lean_dec_ref(v_curr_2646_);
v___x_2653_ = lean_apply_2(v_h__2_2648_, v_head_2651_, v_tail_2652_);
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2654_, lean_object* v_h__1_2655_, lean_object* v_h__2_2656_){
_start:
{
if (lean_obj_tag(v_____do__lift_2654_) == 0)
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
lean_dec(v_h__2_2656_);
v___x_2657_ = lean_box(0);
v___x_2658_ = lean_apply_1(v_h__1_2655_, v___x_2657_);
return v___x_2658_;
}
else
{
lean_object* v_val_2659_; lean_object* v___x_2660_; 
lean_dec(v_h__1_2655_);
v_val_2659_ = lean_ctor_get(v_____do__lift_2654_, 0);
lean_inc(v_val_2659_);
lean_dec_ref(v_____do__lift_2654_);
v___x_2660_ = lean_apply_1(v_h__2_2656_, v_val_2659_);
return v___x_2660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_2661_, lean_object* v_____do__lift_2662_, lean_object* v_h__1_2663_, lean_object* v_h__2_2664_){
_start:
{
if (lean_obj_tag(v_____do__lift_2662_) == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_dec(v_h__2_2664_);
v___x_2665_ = lean_box(0);
v___x_2666_ = lean_apply_1(v_h__1_2663_, v___x_2665_);
return v___x_2666_;
}
else
{
lean_object* v_val_2667_; lean_object* v___x_2668_; 
lean_dec(v_h__1_2663_);
v_val_2667_ = lean_ctor_get(v_____do__lift_2662_, 0);
lean_inc(v_val_2667_);
lean_dec_ref(v_____do__lift_2662_);
v___x_2668_ = lean_apply_1(v_h__2_2664_, v_val_2667_);
return v___x_2668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_2669_, lean_object* v_trace_2670_, lean_object* v_next_2671_, lean_object* v_orig_2672_, lean_object* v_g_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_maxDepth_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v_maxDepth_2679_ = lean_ctor_get(v_cfg_2669_, 0);
lean_inc(v_maxDepth_2679_);
v___x_2680_ = lean_box(0);
v___x_2681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2681_, 0, v_g_2673_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
v___x_2682_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2669_, v_trace_2670_, v_next_2671_, v_orig_2672_, v_maxDepth_2679_, v___x_2681_, v___x_2680_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_2683_, lean_object* v_trace_2684_, lean_object* v_next_2685_, lean_object* v_orig_2686_, lean_object* v_g_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2683_, v_trace_2684_, v_next_2685_, v_orig_2686_, v_g_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
if (lean_obj_tag(v_a_2694_) == 0)
{
lean_object* v___x_2696_; 
v___x_2696_ = l_List_reverse___redArg(v_a_2695_);
return v___x_2696_;
}
else
{
lean_object* v_head_2697_; lean_object* v_tail_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2707_; 
v_head_2697_ = lean_ctor_get(v_a_2694_, 0);
v_tail_2698_ = lean_ctor_get(v_a_2694_, 1);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_a_2694_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2700_ = v_a_2694_;
v_isShared_2701_ = v_isSharedCheck_2707_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_tail_2698_);
lean_inc(v_head_2697_);
lean_dec(v_a_2694_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2707_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2702_ = l_Lean_MessageData_ofFormat(v_head_2697_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v_a_2695_);
lean_ctor_set(v___x_2700_, 0, v___x_2702_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2702_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v_a_2695_);
v___x_2704_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
v_a_2694_ = v_tail_2698_;
v_a_2695_ = v___x_2704_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_2710_ = l_Lean_stringToMessageData(v___x_2709_);
return v___x_2710_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_2713_ = l_Lean_stringToMessageData(v___x_2712_);
return v___x_2713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_2716_ = l_Lean_stringToMessageData(v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_2717_, lean_object* v_snd_2718_, lean_object* v_x_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2717_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref(v___x_2725_);
v___x_2727_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_2718_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2747_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2747_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2747_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2745_; 
v___x_2732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_2733_ = lean_box(0);
v___x_2734_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2726_, v___x_2733_);
v___x_2735_ = l_Lean_MessageData_ofList(v___x_2734_);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2732_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_2740_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2728_, v___x_2733_);
v___x_2741_ = l_Lean_MessageData_ofList(v___x_2740_);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2739_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2738_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2743_);
v___x_2745_ = v___x_2730_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2755_; 
lean_dec(v_a_2726_);
v_a_2748_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2750_ = v___x_2727_;
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2727_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2755_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2753_; 
if (v_isShared_2751_ == 0)
{
v___x_2753_ = v___x_2750_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2748_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec(v_snd_2718_);
v_a_2756_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2725_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2725_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_2764_, lean_object* v_snd_2765_, lean_object* v_x_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2764_, v_snd_2765_, v_x_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec_ref(v_x_2766_);
return v_res_2772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_2775_ = l_Lean_stringToMessageData(v___x_2774_);
return v___x_2775_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_2778_ = l_Lean_stringToMessageData(v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_2779_, lean_object* v___x_2780_, lean_object* v_x_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2779_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref(v___x_2787_);
v___x_2789_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_2780_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2807_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2807_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2807_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2805_; 
v___x_2794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_2795_ = lean_box(0);
v___x_2796_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2788_, v___x_2795_);
v___x_2797_ = l_Lean_MessageData_ofList(v___x_2796_);
v___x_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2794_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_2800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2798_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2790_, v___x_2795_);
v___x_2802_ = l_Lean_MessageData_ofList(v___x_2801_);
v___x_2803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2800_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2803_);
v___x_2805_ = v___x_2792_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2803_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v_a_2788_);
v_a_2808_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2789_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2789_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v___x_2780_);
v_a_2816_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2787_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2787_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_2824_, lean_object* v___x_2825_, lean_object* v_x_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2824_, v___x_2825_, v_x_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec_ref(v_x_2826_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t v___x_2833_, lean_object* v_x_2834_, lean_object* v_x_2835_, lean_object* v___y_2836_){
_start:
{
if (lean_obj_tag(v_x_2834_) == 0)
{
lean_object* v___x_2838_; 
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_x_2835_);
return v___x_2838_;
}
else
{
lean_object* v_head_2839_; lean_object* v_tail_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2855_; 
v_head_2839_ = lean_ctor_get(v_x_2834_, 0);
v_tail_2840_ = lean_ctor_get(v_x_2834_, 1);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_x_2834_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2842_ = v_x_2834_;
v_isShared_2843_ = v_isSharedCheck_2855_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_tail_2840_);
lean_inc(v_head_2839_);
lean_dec(v_x_2834_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2855_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
uint8_t v_a_2850_; lean_object* v___x_2852_; lean_object* v_a_2853_; uint8_t v___x_2854_; 
v___x_2852_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(v_head_2839_, v___y_2836_);
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref(v___x_2852_);
v___x_2854_ = lean_unbox(v_a_2853_);
lean_dec(v_a_2853_);
if (v___x_2854_ == 0)
{
goto v___jp_2844_;
}
else
{
v_a_2850_ = v___x_2833_;
goto v___jp_2849_;
}
v___jp_2844_:
{
lean_object* v___x_2846_; 
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 1, v_x_2835_);
v___x_2846_ = v___x_2842_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_head_2839_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_x_2835_);
v___x_2846_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
v_x_2834_ = v_tail_2840_;
v_x_2835_ = v___x_2846_;
goto _start;
}
}
v___jp_2849_:
{
if (v_a_2850_ == 0)
{
lean_del_object(v___x_2842_);
lean_dec(v_head_2839_);
v_x_2834_ = v_tail_2840_;
goto _start;
}
else
{
goto v___jp_2844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v___x_2856_, lean_object* v_x_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v___x_50602__boxed_2861_; lean_object* v_res_2862_; 
v___x_50602__boxed_2861_ = lean_unbox(v___x_2856_);
v_res_2862_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_50602__boxed_2861_, v_x_2857_, v_x_2858_, v___y_2859_);
lean_dec(v___y_2859_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
if (lean_obj_tag(v_a_2863_) == 0)
{
lean_object* v___x_2865_; 
v___x_2865_ = lean_array_to_list(v_a_2864_);
return v___x_2865_;
}
else
{
lean_object* v_head_2866_; lean_object* v_tail_2867_; lean_object* v___x_2868_; 
v_head_2866_ = lean_ctor_get(v_a_2863_, 0);
lean_inc(v_head_2866_);
v_tail_2867_ = lean_ctor_get(v_a_2863_, 1);
lean_inc(v_tail_2867_);
lean_dec_ref(v_a_2863_);
v___x_2868_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2864_, v_head_2866_);
v_a_2863_ = v_tail_2867_;
v_a_2864_ = v___x_2868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
if (lean_obj_tag(v_a_2871_) == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_dec(v_goals_2870_);
v___x_2879_ = lean_array_to_list(v_a_2872_);
v___x_2880_ = lean_array_to_list(v_a_2873_);
v___x_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
return v___x_2882_;
}
else
{
lean_object* v_head_2883_; lean_object* v_tail_2884_; lean_object* v___x_2885_; 
v_head_2883_ = lean_ctor_get(v_a_2871_, 0);
lean_inc(v_head_2883_);
v_tail_2884_ = lean_ctor_get(v_a_2871_, 1);
lean_inc(v_tail_2884_);
lean_dec_ref(v_a_2871_);
lean_inc(v_head_2883_);
lean_inc(v_goals_2870_);
v___x_2885_ = l_Lean_MVarId_isIndependentOf(v_goals_2870_, v_head_2883_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; uint8_t v___x_2887_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___x_2885_);
v___x_2887_ = lean_unbox(v_a_2886_);
lean_dec(v_a_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; 
v___x_2888_ = lean_array_push(v_a_2873_, v_head_2883_);
v_a_2871_ = v_tail_2884_;
v_a_2873_ = v___x_2888_;
goto _start;
}
else
{
lean_object* v___x_2890_; 
v___x_2890_ = lean_array_push(v_a_2872_, v_head_2883_);
v_a_2871_ = v_tail_2884_;
v_a_2872_ = v___x_2890_;
goto _start;
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_tail_2884_);
lean_dec(v_head_2883_);
lean_dec_ref(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_goals_2870_);
v_a_2892_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2885_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2885_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
if (lean_obj_tag(v_a_2910_) == 0)
{
lean_object* v___x_2912_; 
v___x_2912_ = lean_array_to_list(v_a_2911_);
return v___x_2912_;
}
else
{
lean_object* v_head_2913_; 
v_head_2913_ = lean_ctor_get(v_a_2910_, 0);
if (lean_obj_tag(v_head_2913_) == 0)
{
lean_object* v_tail_2914_; lean_object* v_val_2915_; lean_object* v___x_2916_; 
lean_inc_ref(v_head_2913_);
v_tail_2914_ = lean_ctor_get(v_a_2910_, 1);
lean_inc(v_tail_2914_);
lean_dec_ref(v_a_2910_);
v_val_2915_ = lean_ctor_get(v_head_2913_, 0);
lean_inc(v_val_2915_);
lean_dec_ref(v_head_2913_);
v___x_2916_ = lean_array_push(v_a_2911_, v_val_2915_);
v_a_2910_ = v_tail_2914_;
v_a_2911_ = v___x_2916_;
goto _start;
}
else
{
lean_object* v_tail_2918_; 
v_tail_2918_ = lean_ctor_get(v_a_2910_, 1);
lean_inc(v_tail_2918_);
lean_dec_ref(v_a_2910_);
v_a_2910_ = v_tail_2918_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_2920_, lean_object* v_x_2921_, lean_object* v_x_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
if (lean_obj_tag(v_x_2921_) == 0)
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_dec_ref(v_f_2920_);
v___x_2928_ = l_List_reverse___redArg(v_x_2922_);
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
return v___x_2929_;
}
else
{
lean_object* v_head_2930_; lean_object* v_tail_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2976_; 
v_head_2930_ = lean_ctor_get(v_x_2921_, 0);
v_tail_2931_ = lean_ctor_get(v_x_2921_, 1);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_x_2921_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2933_ = v_x_2921_;
v_isShared_2934_ = v_isSharedCheck_2976_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_tail_2931_);
lean_inc(v_head_2930_);
lean_dec(v_x_2921_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2976_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v_a_2936_; lean_object* v___x_2941_; 
v___x_2941_ = l_Lean_Meta_saveState___redArg(v___y_2924_, v___y_2926_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2943_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref(v___x_2941_);
lean_inc_ref(v_f_2920_);
lean_inc(v___y_2926_);
lean_inc_ref(v___y_2925_);
lean_inc(v___y_2924_);
lean_inc_ref(v___y_2923_);
lean_inc(v_head_2930_);
v___x_2943_ = lean_apply_6(v_f_2920_, v_head_2930_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, lean_box(0));
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; 
lean_dec(v_a_2942_);
lean_dec(v_head_2930_);
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v_a_2944_);
v_a_2936_ = v___x_2945_;
goto v___jp_2935_;
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2967_; 
v_a_2946_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2948_ = v___x_2943_;
v_isShared_2949_ = v_isSharedCheck_2967_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2943_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2967_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
uint8_t v___y_2951_; uint8_t v___x_2965_; 
v___x_2965_ = l_Lean_Exception_isInterrupt(v_a_2946_);
if (v___x_2965_ == 0)
{
uint8_t v___x_2966_; 
lean_inc(v_a_2946_);
v___x_2966_ = l_Lean_Exception_isRuntime(v_a_2946_);
v___y_2951_ = v___x_2966_;
goto v___jp_2950_;
}
else
{
v___y_2951_ = v___x_2965_;
goto v___jp_2950_;
}
v___jp_2950_:
{
if (v___y_2951_ == 0)
{
lean_object* v___x_2952_; 
lean_del_object(v___x_2948_);
lean_dec(v_a_2946_);
v___x_2952_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2942_, v___y_2924_, v___y_2926_);
lean_dec(v_a_2942_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v___x_2953_; 
lean_dec_ref(v___x_2952_);
v___x_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2953_, 0, v_head_2930_);
v_a_2936_ = v___x_2953_;
goto v___jp_2935_;
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_del_object(v___x_2933_);
lean_dec(v_tail_2931_);
lean_dec(v_head_2930_);
lean_dec(v_x_2922_);
lean_dec_ref(v_f_2920_);
v_a_2954_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2952_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2952_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
else
{
lean_object* v___x_2963_; 
lean_dec(v_a_2942_);
lean_del_object(v___x_2933_);
lean_dec(v_tail_2931_);
lean_dec(v_head_2930_);
lean_dec(v_x_2922_);
lean_dec_ref(v_f_2920_);
if (v_isShared_2949_ == 0)
{
v___x_2963_ = v___x_2948_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2946_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_del_object(v___x_2933_);
lean_dec(v_tail_2931_);
lean_dec(v_head_2930_);
lean_dec(v_x_2922_);
lean_dec_ref(v_f_2920_);
v_a_2968_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2941_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2941_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
v___jp_2935_:
{
lean_object* v___x_2938_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v_x_2922_);
lean_ctor_set(v___x_2933_, 0, v_a_2936_);
v___x_2938_ = v___x_2933_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2936_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_x_2922_);
v___x_2938_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
v_x_2921_ = v_tail_2931_;
v_x_2922_ = v___x_2938_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_2977_, lean_object* v_x_2978_, lean_object* v_x_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2977_, v_x_2978_, v_x_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
if (lean_obj_tag(v_a_2986_) == 0)
{
lean_object* v___x_2988_; 
v___x_2988_ = lean_array_to_list(v_a_2987_);
return v___x_2988_;
}
else
{
lean_object* v_head_2989_; 
v_head_2989_ = lean_ctor_get(v_a_2986_, 0);
if (lean_obj_tag(v_head_2989_) == 1)
{
lean_object* v_tail_2990_; lean_object* v_val_2991_; lean_object* v___x_2992_; 
lean_inc_ref(v_head_2989_);
v_tail_2990_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_tail_2990_);
lean_dec_ref(v_a_2986_);
v_val_2991_ = lean_ctor_get(v_head_2989_, 0);
lean_inc(v_val_2991_);
lean_dec_ref(v_head_2989_);
v___x_2992_ = lean_array_push(v_a_2987_, v_val_2991_);
v_a_2986_ = v_tail_2990_;
v_a_2987_ = v___x_2992_;
goto _start;
}
else
{
lean_object* v_tail_2994_; 
v_tail_2994_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_tail_2994_);
lean_dec_ref(v_a_2986_);
v_a_2986_ = v_tail_2994_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_2996_, lean_object* v_f_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_box(0);
v___x_3004_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2997_, v_L_2996_, v___x_3003_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3016_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3016_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3016_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3014_; 
v___x_3009_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_3005_);
v___x_3010_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_3005_, v___x_3009_);
v___x_3011_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_3005_, v___x_3009_);
v___x_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3012_);
v___x_3014_ = v___x_3007_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
v_a_3017_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3004_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3004_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* v_L_3025_, lean_object* v_f_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_3025_, v_f_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t v___x_3033_, uint8_t v___x_3034_, lean_object* v_x_3035_, lean_object* v_x_3036_, lean_object* v___y_3037_){
_start:
{
if (lean_obj_tag(v_x_3035_) == 0)
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_x_3036_);
return v___x_3039_;
}
else
{
lean_object* v_head_3040_; lean_object* v_tail_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3055_; 
v_head_3040_ = lean_ctor_get(v_x_3035_, 0);
v_tail_3041_ = lean_ctor_get(v_x_3035_, 1);
v_isSharedCheck_3055_ = !lean_is_exclusive(v_x_3035_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3043_ = v_x_3035_;
v_isShared_3044_ = v_isSharedCheck_3055_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_tail_3041_);
lean_inc(v_head_3040_);
lean_dec(v_x_3035_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3055_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
uint8_t v_a_3046_; lean_object* v___x_3052_; lean_object* v_a_3053_; uint8_t v___x_3054_; 
v___x_3052_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(v_head_3040_, v___y_3037_);
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref(v___x_3052_);
v___x_3054_ = lean_unbox(v_a_3053_);
lean_dec(v_a_3053_);
if (v___x_3054_ == 0)
{
v_a_3046_ = v___x_3033_;
goto v___jp_3045_;
}
else
{
v_a_3046_ = v___x_3034_;
goto v___jp_3045_;
}
v___jp_3045_:
{
if (v_a_3046_ == 0)
{
lean_del_object(v___x_3043_);
lean_dec(v_head_3040_);
v_x_3035_ = v_tail_3041_;
goto _start;
}
else
{
lean_object* v___x_3049_; 
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 1, v_x_3036_);
v___x_3049_ = v___x_3043_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_head_3040_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_x_3036_);
v___x_3049_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
v_x_3035_ = v_tail_3041_;
v_x_3036_ = v___x_3049_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* v___x_3056_, lean_object* v___x_3057_, lean_object* v_x_3058_, lean_object* v_x_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
uint8_t v___x_50956__boxed_3062_; uint8_t v___x_50957__boxed_3063_; lean_object* v_res_3064_; 
v___x_50956__boxed_3062_ = lean_unbox(v___x_3056_);
v___x_50957__boxed_3063_ = lean_unbox(v___x_3057_);
v_res_3064_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_50956__boxed_3062_, v___x_50957__boxed_3063_, v_x_3058_, v_x_3059_, v___y_3060_);
lean_dec(v___y_3060_);
return v_res_3064_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
v___x_3067_ = l_Lean_stringToMessageData(v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_3070_, lean_object* v_trace_3071_, lean_object* v_next_3072_, lean_object* v_orig_3073_, lean_object* v_goals_3074_, lean_object* v_remaining_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2));
lean_inc(v_remaining_3075_);
lean_inc(v_goals_3074_);
v___x_3085_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_3074_, v_remaining_3075_, v___x_3084_, v___x_3084_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v_fst_3087_; lean_object* v_snd_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_4330_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref(v___x_3085_);
v_fst_3087_ = lean_ctor_get(v_a_3086_, 0);
v_snd_3088_ = lean_ctor_get(v_a_3086_, 1);
v_isSharedCheck_4330_ = !lean_is_exclusive(v_a_3086_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_3090_ = v_a_3086_;
v_isShared_3091_ = v_isSharedCheck_4330_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_snd_3088_);
lean_inc(v_fst_3087_);
lean_dec(v_a_3086_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_4330_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
uint8_t v___x_3092_; 
v___x_3092_ = l_List_isEmpty___redArg(v_fst_3087_);
if (v___x_3092_ == 0)
{
lean_object* v_options_3093_; uint8_t v_hasTrace_3094_; lean_object* v___f_3095_; 
lean_dec(v_remaining_3075_);
v_options_3093_ = lean_ctor_get(v_a_3078_, 2);
v_hasTrace_3094_ = lean_ctor_get_uint8(v_options_3093_, sizeof(void*)*1);
lean_inc(v_orig_3073_);
lean_inc_ref(v_next_3072_);
lean_inc(v_trace_3071_);
lean_inc_ref(v_cfg_3070_);
v___f_3095_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3095_, 0, v_cfg_3070_);
lean_closure_set(v___f_3095_, 1, v_trace_3071_);
lean_closure_set(v___f_3095_, 2, v_next_3072_);
lean_closure_set(v___f_3095_, 3, v_orig_3073_);
if (v_hasTrace_3094_ == 0)
{
lean_object* v___x_3096_; 
lean_del_object(v___x_3090_);
v___x_3096_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3087_, v___f_3095_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3166_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3166_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3166_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v_fst_3101_; lean_object* v_snd_3102_; lean_object* v___x_3103_; lean_object* v_a_3105_; lean_object* v___y_3112_; lean_object* v___y_3115_; lean_object* v___y_3116_; uint8_t v___y_3117_; lean_object* v___y_3128_; lean_object* v_a_3143_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v_fst_3101_ = lean_ctor_get(v_a_3097_, 0);
lean_inc(v_fst_3101_);
v_snd_3102_ = lean_ctor_get(v_a_3097_, 1);
lean_inc(v_snd_3102_);
lean_dec(v_a_3097_);
v___x_3103_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3102_, v___x_3084_);
v___x_3161_ = lean_box(0);
v___x_3162_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_hasTrace_3094_, v_goals_3074_, v___x_3161_, v_a_3077_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3164_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref(v___x_3162_);
v___x_3164_ = l_List_reverse___redArg(v_a_3163_);
v_a_3143_ = v___x_3164_;
goto v___jp_3142_;
}
else
{
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3165_; 
v_a_3165_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3165_);
lean_dec_ref(v___x_3162_);
v_a_3143_ = v_a_3165_;
goto v___jp_3142_;
}
else
{
lean_dec(v___x_3103_);
lean_dec(v_fst_3101_);
lean_del_object(v___x_3099_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
return v___x_3162_;
}
}
v___jp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3106_ = l_List_appendTR___redArg(v___x_3103_, v_fst_3101_);
v___x_3107_ = l_List_appendTR___redArg(v___x_3106_, v_a_3105_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3107_);
v___x_3109_ = v___x_3099_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
v___jp_3111_:
{
if (lean_obj_tag(v___y_3112_) == 0)
{
lean_object* v_a_3113_; 
v_a_3113_ = lean_ctor_get(v___y_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref(v___y_3112_);
v_a_3105_ = v_a_3113_;
goto v___jp_3104_;
}
else
{
lean_dec(v___x_3103_);
lean_dec(v_fst_3101_);
lean_del_object(v___x_3099_);
return v___y_3112_;
}
}
v___jp_3114_:
{
if (v___y_3117_ == 0)
{
lean_object* v___x_3118_; 
lean_dec_ref(v___y_3116_);
v___x_3118_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3115_, v_a_3077_, v_a_3079_);
lean_dec_ref(v___y_3115_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec_ref(v___x_3118_);
v_a_3105_ = v_snd_3088_;
goto v___jp_3104_;
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v___x_3103_);
lean_dec(v_fst_3101_);
lean_del_object(v___x_3099_);
lean_dec(v_snd_3088_);
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_dec_ref(v___y_3115_);
lean_dec(v_snd_3088_);
v___y_3112_ = v___y_3116_;
goto v___jp_3111_;
}
}
v___jp_3127_:
{
uint8_t v___x_3129_; 
v___x_3129_ = l_List_isEmpty___redArg(v_fst_3101_);
lean_dec(v_fst_3101_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
lean_dec(v___y_3128_);
lean_dec(v___x_3103_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
v___x_3130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3131_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3130_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3131_;
}
else
{
lean_object* v___x_3132_; 
v___x_3132_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3128_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3141_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3135_ = v___x_3132_;
v_isShared_3136_ = v_isSharedCheck_3141_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3141_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3137_ = l_List_appendTR___redArg(v___x_3103_, v_a_3133_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v___x_3137_);
v___x_3139_ = v___x_3135_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3137_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
else
{
lean_dec(v___x_3103_);
return v___x_3132_;
}
}
}
v___jp_3142_:
{
uint8_t v_commitIndependentGoals_3144_; lean_object* v___x_3145_; 
v_commitIndependentGoals_3144_ = lean_ctor_get_uint8(v_cfg_3070_, sizeof(void*)*4);
lean_inc(v___x_3103_);
v___x_3145_ = l_List_appendTR___redArg(v_a_3143_, v___x_3103_);
if (v_commitIndependentGoals_3144_ == 0)
{
lean_del_object(v___x_3099_);
v___y_3128_ = v___x_3145_;
goto v___jp_3127_;
}
else
{
uint8_t v___x_3146_; 
v___x_3146_ = l_List_isEmpty___redArg(v___x_3103_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Lean_Meta_saveState___redArg(v_a_3077_, v_a_3079_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3149_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref(v___x_3147_);
lean_inc(v_snd_3088_);
v___x_3149_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___x_3145_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_dec(v_a_3148_);
lean_dec(v_snd_3088_);
v___y_3112_ = v___x_3149_;
goto v___jp_3111_;
}
else
{
lean_object* v_a_3150_; uint8_t v___x_3151_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc(v_a_3150_);
v___x_3151_ = l_Lean_Exception_isInterrupt(v_a_3150_);
if (v___x_3151_ == 0)
{
uint8_t v___x_3152_; 
v___x_3152_ = l_Lean_Exception_isRuntime(v_a_3150_);
v___y_3115_ = v_a_3148_;
v___y_3116_ = v___x_3149_;
v___y_3117_ = v___x_3152_;
goto v___jp_3114_;
}
else
{
lean_dec(v_a_3150_);
v___y_3115_ = v_a_3148_;
v___y_3116_ = v___x_3149_;
v___y_3117_ = v___x_3151_;
goto v___jp_3114_;
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v___x_3145_);
lean_dec(v___x_3103_);
lean_dec(v_fst_3101_);
lean_del_object(v___x_3099_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
v_a_3153_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3147_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3147_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
else
{
lean_del_object(v___x_3099_);
v___y_3128_ = v___x_3145_;
goto v___jp_3127_;
}
}
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec(v_snd_3088_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
v_a_3167_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_3096_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3096_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
else
{
lean_object* v___x_3175_; 
lean_inc(v_trace_3071_);
v___x_3175_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_3071_, v_a_3078_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_a_3176_; lean_object* v___f_3177_; lean_object* v___x_3178_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v_a_3182_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v_a_3200_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v_a_3205_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v_a_3212_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; uint8_t v___y_3230_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3253_; lean_object* v___y_3254_; uint8_t v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v_a_3259_; lean_object* v___y_3269_; lean_object* v___y_3270_; uint8_t v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v_a_3275_; lean_object* v___y_3278_; lean_object* v___y_3279_; uint8_t v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v_a_3284_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; uint8_t v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v_a_3295_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; uint8_t v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; uint8_t v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; uint8_t v___y_3321_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; uint8_t v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3342_; lean_object* v___y_3343_; uint8_t v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3352_; lean_object* v___y_3353_; uint8_t v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3364_; uint8_t v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; uint8_t v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v_a_3373_; lean_object* v___y_3380_; uint8_t v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v_a_3386_; lean_object* v___y_3399_; uint8_t v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v_a_3405_; lean_object* v___y_3408_; lean_object* v___y_3409_; uint8_t v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v_a_3416_; lean_object* v___y_3420_; uint8_t v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v_a_3426_; lean_object* v___y_3429_; uint8_t v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3439_; uint8_t v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3448_; uint8_t v___y_3449_; lean_object* v___y_3450_; uint8_t v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3463_; lean_object* v___y_3464_; uint8_t v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3475_; lean_object* v___y_3476_; uint8_t v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; uint8_t v___y_3485_; lean_object* v___y_3489_; lean_object* v___y_3490_; uint8_t v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3506_; uint8_t v___y_3507_; lean_object* v___y_3508_; uint8_t v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v_a_3515_; lean_object* v___y_3520_; lean_object* v___y_3521_; uint8_t v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3561_; lean_object* v___y_3562_; uint8_t v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v_a_3566_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v_a_3573_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v_a_3586_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v_a_3593_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v_a_3599_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3608_; uint8_t v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v_a_3614_; uint8_t v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v_a_3633_; lean_object* v___y_3636_; uint8_t v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v_a_3644_; uint8_t v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v_a_3654_; lean_object* v___y_3657_; uint8_t v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; uint8_t v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3676_; uint8_t v___y_3677_; uint8_t v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; uint8_t v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; uint8_t v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; uint8_t v___y_3713_; lean_object* v___y_3717_; uint8_t v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3734_; uint8_t v___y_3735_; uint8_t v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v_a_3743_; lean_object* v___y_3748_; uint8_t v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v_a_3754_; uint8_t v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v_a_3770_; lean_object* v___y_3773_; uint8_t v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v_a_3781_; uint8_t v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v_a_3791_; lean_object* v___y_3794_; uint8_t v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3804_; uint8_t v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3816_; uint8_t v___y_3817_; lean_object* v___y_3818_; uint8_t v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; uint8_t v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; uint8_t v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; uint8_t v___y_3852_; lean_object* v___y_3856_; uint8_t v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; uint8_t v___y_3873_; lean_object* v___y_3874_; uint8_t v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v_a_3882_; uint8_t v___y_3887_; lean_object* v___y_3888_; uint8_t v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; uint8_t v___y_3922_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; uint8_t v___y_3942_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; uint8_t v___y_3963_; lean_object* v_a_3964_; uint8_t v___x_4025_; 
v_a_3176_ = lean_ctor_get(v___x_3175_, 0);
lean_inc(v_a_3176_);
lean_dec_ref(v___x_3175_);
lean_inc(v_snd_3088_);
lean_inc(v_fst_3087_);
v___f_3177_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3177_, 0, v_fst_3087_);
lean_closure_set(v___f_3177_, 1, v_snd_3088_);
v___x_3178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
v___x_4025_ = lean_unbox(v_a_3176_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4026_; uint8_t v___x_4027_; 
v___x_4026_ = l_Lean_trace_profiler;
v___x_4027_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_3093_, v___x_4026_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; 
lean_dec_ref(v___f_3177_);
lean_dec(v_a_3176_);
lean_del_object(v___x_3090_);
v___x_4028_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3087_, v___f_3095_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v_fst_4030_; lean_object* v_snd_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4310_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref(v___x_4028_);
v_fst_4030_ = lean_ctor_get(v_a_4029_, 0);
v_snd_4031_ = lean_ctor_get(v_a_4029_, 1);
v_isSharedCheck_4310_ = !lean_is_exclusive(v_a_4029_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4033_ = v_a_4029_;
v_isShared_4034_ = v_isSharedCheck_4310_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_snd_4031_);
lean_inc(v_fst_4030_);
lean_dec(v_a_4029_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4310_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4035_; 
lean_inc(v_trace_3071_);
v___x_4035_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_3071_, v_a_3078_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4301_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4301_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4301_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4040_; lean_object* v___y_4042_; lean_object* v_a_4055_; lean_object* v___y_4062_; lean_object* v___y_4065_; lean_object* v___y_4066_; uint8_t v___y_4067_; lean_object* v___y_4078_; lean_object* v_a_4094_; lean_object* v___f_4098_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v_a_4102_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v_a_4117_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v_a_4122_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v_a_4128_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; uint8_t v___y_4140_; lean_object* v___y_4147_; uint8_t v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; uint8_t v___y_4163_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4178_; uint8_t v___y_4179_; lean_object* v___y_4180_; lean_object* v_a_4181_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v_a_4188_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v_a_4204_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v_a_4209_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v_a_4215_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4229_; uint8_t v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; uint8_t v___y_4248_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4263_; uint8_t v___y_4264_; lean_object* v___y_4265_; lean_object* v_a_4266_; lean_object* v___x_4270_; uint8_t v___x_4296_; 
v___x_4040_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_4031_, v___x_3084_);
lean_inc(v___x_4040_);
lean_inc(v_fst_4030_);
v___f_4098_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_4098_, 0, v_fst_4030_);
lean_closure_set(v___f_4098_, 1, v___x_4040_);
v___x_4270_ = lean_box(0);
v___x_4296_ = lean_unbox(v_a_4036_);
if (v___x_4296_ == 0)
{
if (v___x_4027_ == 0)
{
lean_object* v___x_4297_; 
lean_dec_ref(v___f_4098_);
lean_dec(v_a_4036_);
lean_del_object(v___x_4033_);
v___x_4297_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3094_, v___x_4027_, v_goals_3074_, v___x_4270_, v_a_3077_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4299_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref(v___x_4297_);
v___x_4299_ = l_List_reverse___redArg(v_a_4298_);
v_a_4094_ = v___x_4299_;
goto v___jp_4093_;
}
else
{
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4300_; 
v_a_4300_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4300_);
lean_dec_ref(v___x_4297_);
v_a_4094_ = v_a_4300_;
goto v___jp_4093_;
}
else
{
lean_dec(v___x_4040_);
lean_del_object(v___x_4038_);
lean_dec(v_fst_4030_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
return v___x_4297_;
}
}
}
else
{
lean_del_object(v___x_4038_);
goto v___jp_4271_;
}
}
else
{
lean_del_object(v___x_4038_);
goto v___jp_4271_;
}
v___jp_4041_:
{
uint8_t v___x_4043_; 
v___x_4043_ = l_List_isEmpty___redArg(v_fst_4030_);
lean_dec(v_fst_4030_);
if (v___x_4043_ == 0)
{
lean_dec(v___y_4042_);
lean_dec(v___x_4040_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
goto v___jp_3081_;
}
else
{
if (v___x_4027_ == 0)
{
lean_object* v___x_4044_; 
v___x_4044_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_4042_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4053_; 
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4044_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4047_ = v___x_4044_;
v_isShared_4048_ = v_isSharedCheck_4053_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4044_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4053_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4049_; lean_object* v___x_4051_; 
v___x_4049_ = l_List_appendTR___redArg(v___x_4040_, v_a_4045_);
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 0, v___x_4049_);
v___x_4051_ = v___x_4047_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
else
{
lean_dec(v___x_4040_);
return v___x_4044_;
}
}
else
{
lean_dec(v___y_4042_);
lean_dec(v___x_4040_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
goto v___jp_3081_;
}
}
}
v___jp_4054_:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4059_; 
v___x_4056_ = l_List_appendTR___redArg(v___x_4040_, v_fst_4030_);
v___x_4057_ = l_List_appendTR___redArg(v___x_4056_, v_a_4055_);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v___x_4057_);
v___x_4059_ = v___x_4038_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
v___jp_4061_:
{
if (lean_obj_tag(v___y_4062_) == 0)
{
lean_object* v_a_4063_; 
v_a_4063_ = lean_ctor_get(v___y_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref(v___y_4062_);
v_a_4055_ = v_a_4063_;
goto v___jp_4054_;
}
else
{
lean_dec(v___x_4040_);
lean_del_object(v___x_4038_);
lean_dec(v_fst_4030_);
return v___y_4062_;
}
}
v___jp_4064_:
{
if (v___y_4067_ == 0)
{
lean_object* v___x_4068_; 
lean_dec_ref(v___y_4065_);
v___x_4068_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4066_, v_a_3077_, v_a_3079_);
lean_dec_ref(v___y_4066_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_dec_ref(v___x_4068_);
v_a_4055_ = v_snd_3088_;
goto v___jp_4054_;
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_dec(v___x_4040_);
lean_del_object(v___x_4038_);
lean_dec(v_fst_4030_);
lean_dec(v_snd_3088_);
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4068_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4068_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4068_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
else
{
lean_dec_ref(v___y_4066_);
lean_dec(v_snd_3088_);
v___y_4062_ = v___y_4065_;
goto v___jp_4061_;
}
}
v___jp_4077_:
{
lean_object* v___x_4079_; 
v___x_4079_ = l_Lean_Meta_saveState___redArg(v_a_3077_, v_a_3079_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4081_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref(v___x_4079_);
lean_inc(v_snd_3088_);
v___x_4081_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_4078_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_dec(v_a_4080_);
lean_dec(v_snd_3088_);
v___y_4062_ = v___x_4081_;
goto v___jp_4061_;
}
else
{
lean_object* v_a_4082_; uint8_t v___x_4083_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
v___x_4083_ = l_Lean_Exception_isInterrupt(v_a_4082_);
if (v___x_4083_ == 0)
{
uint8_t v___x_4084_; 
v___x_4084_ = l_Lean_Exception_isRuntime(v_a_4082_);
v___y_4065_ = v___x_4081_;
v___y_4066_ = v_a_4080_;
v___y_4067_ = v___x_4084_;
goto v___jp_4064_;
}
else
{
lean_dec(v_a_4082_);
v___y_4065_ = v___x_4081_;
v___y_4066_ = v_a_4080_;
v___y_4067_ = v___x_4083_;
goto v___jp_4064_;
}
}
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec(v___y_4078_);
lean_dec(v___x_4040_);
lean_del_object(v___x_4038_);
lean_dec(v_fst_4030_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
v_a_4085_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4079_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4079_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
v___jp_4093_:
{
uint8_t v_commitIndependentGoals_4095_; lean_object* v___x_4096_; 
v_commitIndependentGoals_4095_ = lean_ctor_get_uint8(v_cfg_3070_, sizeof(void*)*4);
lean_inc(v___x_4040_);
v___x_4096_ = l_List_appendTR___redArg(v_a_4094_, v___x_4040_);
if (v_commitIndependentGoals_4095_ == 0)
{
lean_del_object(v___x_4038_);
v___y_4042_ = v___x_4096_;
goto v___jp_4041_;
}
else
{
uint8_t v___x_4097_; 
v___x_4097_ = l_List_isEmpty___redArg(v___x_4040_);
if (v___x_4097_ == 0)
{
v___y_4078_ = v___x_4096_;
goto v___jp_4077_;
}
else
{
if (v___x_4027_ == 0)
{
lean_del_object(v___x_4038_);
v___y_4042_ = v___x_4096_;
goto v___jp_4041_;
}
else
{
v___y_4078_ = v___x_4096_;
goto v___jp_4077_;
}
}
}
}
v___jp_4099_:
{
lean_object* v___x_4103_; double v___x_4104_; double v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4109_; 
v___x_4103_ = lean_io_get_num_heartbeats();
v___x_4104_ = lean_float_of_nat(v___y_4100_);
v___x_4105_ = lean_float_of_nat(v___x_4103_);
v___x_4106_ = lean_box_float(v___x_4104_);
v___x_4107_ = lean_box_float(v___x_4105_);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 1, v___x_4107_);
lean_ctor_set(v___x_4033_, 0, v___x_4106_);
v___x_4109_ = v___x_4033_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4106_);
lean_ctor_set(v_reuseFailAlloc_4113_, 1, v___x_4107_);
v___x_4109_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
lean_object* v___x_4110_; uint8_t v___x_4111_; lean_object* v___x_4112_; 
v___x_4110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4110_, 0, v_a_4102_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = lean_unbox(v_a_4036_);
lean_dec(v_a_4036_);
v___x_4112_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3071_, v_hasTrace_3094_, v___x_3178_, v_options_3093_, v___x_4111_, v___y_4101_, v___f_4098_, v___x_4110_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_4112_;
}
}
v___jp_4114_:
{
lean_object* v___x_4118_; 
v___x_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4118_, 0, v_a_4117_);
v___y_4100_ = v___y_4115_;
v___y_4101_ = v___y_4116_;
v_a_4102_ = v___x_4118_;
goto v___jp_4099_;
}
v___jp_4119_:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = l_List_appendTR___redArg(v___x_4040_, v_fst_4030_);
v___x_4124_ = l_List_appendTR___redArg(v___x_4123_, v_a_4122_);
v___y_4115_ = v___y_4120_;
v___y_4116_ = v___y_4121_;
v_a_4117_ = v___x_4124_;
goto v___jp_4114_;
}
v___jp_4125_:
{
lean_object* v___x_4129_; 
v___x_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4129_, 0, v_a_4128_);
v___y_4100_ = v___y_4126_;
v___y_4101_ = v___y_4127_;
v_a_4102_ = v___x_4129_;
goto v___jp_4099_;
}
v___jp_4130_:
{
if (lean_obj_tag(v___y_4133_) == 0)
{
lean_object* v_a_4134_; 
v_a_4134_ = lean_ctor_get(v___y_4133_, 0);
lean_inc(v_a_4134_);
lean_dec_ref(v___y_4133_);
v___y_4115_ = v___y_4131_;
v___y_4116_ = v___y_4132_;
v_a_4117_ = v_a_4134_;
goto v___jp_4114_;
}
else
{
lean_object* v_a_4135_; 
v_a_4135_ = lean_ctor_get(v___y_4133_, 0);
lean_inc(v_a_4135_);
lean_dec_ref(v___y_4133_);
v___y_4126_ = v___y_4131_;
v___y_4127_ = v___y_4132_;
v_a_4128_ = v_a_4135_;
goto v___jp_4125_;
}
}
v___jp_4136_:
{
if (v___y_4140_ == 0)
{
lean_object* v___x_4141_; 
lean_inc(v_trace_3071_);
v___x_4141_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_4139_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4143_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref(v___x_4141_);
v___x_4143_ = l_List_appendTR___redArg(v___x_4040_, v_a_4142_);
v___y_4115_ = v___y_4137_;
v___y_4116_ = v___y_4138_;
v_a_4117_ = v___x_4143_;
goto v___jp_4114_;
}
else
{
lean_dec(v___x_4040_);
v___y_4131_ = v___y_4137_;
v___y_4132_ = v___y_4138_;
v___y_4133_ = v___x_4141_;
goto v___jp_4130_;
}
}
else
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
lean_dec(v___y_4139_);
lean_dec(v___x_4040_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___x_4144_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4145_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4144_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_4131_ = v___y_4137_;
v___y_4132_ = v___y_4138_;
v___y_4133_ = v___x_4145_;
goto v___jp_4130_;
}
}
v___jp_4146_:
{
uint8_t v___x_4151_; 
v___x_4151_ = l_List_isEmpty___redArg(v_fst_4030_);
lean_dec(v_fst_4030_);
if (v___x_4151_ == 0)
{
v___y_4137_ = v___y_4147_;
v___y_4138_ = v___y_4149_;
v___y_4139_ = v___y_4150_;
v___y_4140_ = v___y_4148_;
goto v___jp_4136_;
}
else
{
v___y_4137_ = v___y_4147_;
v___y_4138_ = v___y_4149_;
v___y_4139_ = v___y_4150_;
v___y_4140_ = v___x_4027_;
goto v___jp_4136_;
}
}
v___jp_4152_:
{
if (lean_obj_tag(v___y_4155_) == 0)
{
lean_object* v_a_4156_; 
v_a_4156_ = lean_ctor_get(v___y_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref(v___y_4155_);
v___y_4120_ = v___y_4153_;
v___y_4121_ = v___y_4154_;
v_a_4122_ = v_a_4156_;
goto v___jp_4119_;
}
else
{
lean_object* v_a_4157_; 
lean_dec(v___x_4040_);
lean_dec(v_fst_4030_);
v_a_4157_ = lean_ctor_get(v___y_4155_, 0);
lean_inc(v_a_4157_);
lean_dec_ref(v___y_4155_);
v___y_4126_ = v___y_4153_;
v___y_4127_ = v___y_4154_;
v_a_4128_ = v_a_4157_;
goto v___jp_4125_;
}
}
v___jp_4158_:
{
if (v___y_4163_ == 0)
{
lean_object* v___x_4164_; 
lean_dec_ref(v___y_4162_);
v___x_4164_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4159_, v_a_3077_, v_a_3079_);
lean_dec_ref(v___y_4159_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_dec_ref(v___x_4164_);
v___y_4120_ = v___y_4160_;
v___y_4121_ = v___y_4161_;
v_a_4122_ = v_snd_3088_;
goto v___jp_4119_;
}
else
{
lean_object* v_a_4165_; 
lean_dec(v___x_4040_);
lean_dec(v_fst_4030_);
lean_dec(v_snd_3088_);
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref(v___x_4164_);
v___y_4126_ = v___y_4160_;
v___y_4127_ = v___y_4161_;
v_a_4128_ = v_a_4165_;
goto v___jp_4125_;
}
}
else
{
lean_dec_ref(v___y_4159_);
lean_dec(v_snd_3088_);
v___y_4153_ = v___y_4160_;
v___y_4154_ = v___y_4161_;
v___y_4155_ = v___y_4162_;
goto v___jp_4152_;
}
}
v___jp_4166_:
{
lean_object* v___x_4170_; 
v___x_4170_ = l_Lean_Meta_saveState___redArg(v_a_3077_, v_a_3079_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_object* v_a_4171_; lean_object* v___x_4172_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref(v___x_4170_);
lean_inc(v_snd_3088_);
lean_inc(v_trace_3071_);
v___x_4172_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_4169_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_dec(v_a_4171_);
lean_dec(v_snd_3088_);
v___y_4153_ = v___y_4167_;
v___y_4154_ = v___y_4168_;
v___y_4155_ = v___x_4172_;
goto v___jp_4152_;
}
else
{
lean_object* v_a_4173_; uint8_t v___x_4174_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
v___x_4174_ = l_Lean_Exception_isInterrupt(v_a_4173_);
if (v___x_4174_ == 0)
{
uint8_t v___x_4175_; 
v___x_4175_ = l_Lean_Exception_isRuntime(v_a_4173_);
v___y_4159_ = v_a_4171_;
v___y_4160_ = v___y_4167_;
v___y_4161_ = v___y_4168_;
v___y_4162_ = v___x_4172_;
v___y_4163_ = v___x_4175_;
goto v___jp_4158_;
}
else
{
lean_dec(v_a_4173_);
v___y_4159_ = v_a_4171_;
v___y_4160_ = v___y_4167_;
v___y_4161_ = v___y_4168_;
v___y_4162_ = v___x_4172_;
v___y_4163_ = v___x_4174_;
goto v___jp_4158_;
}
}
}
else
{
lean_object* v_a_4176_; 
lean_dec(v___y_4169_);
lean_dec(v___x_4040_);
lean_dec(v_fst_4030_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_4176_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4176_);
lean_dec_ref(v___x_4170_);
v___y_4126_ = v___y_4167_;
v___y_4127_ = v___y_4168_;
v_a_4128_ = v_a_4176_;
goto v___jp_4125_;
}
}
v___jp_4177_:
{
uint8_t v_commitIndependentGoals_4182_; lean_object* v___x_4183_; 
v_commitIndependentGoals_4182_ = lean_ctor_get_uint8(v_cfg_3070_, sizeof(void*)*4);
lean_inc(v___x_4040_);
v___x_4183_ = l_List_appendTR___redArg(v_a_4181_, v___x_4040_);
if (v_commitIndependentGoals_4182_ == 0)
{
v___y_4147_ = v___y_4178_;
v___y_4148_ = v___y_4179_;
v___y_4149_ = v___y_4180_;
v___y_4150_ = v___x_4183_;
goto v___jp_4146_;
}
else
{
uint8_t v___x_4184_; 
v___x_4184_ = l_List_isEmpty___redArg(v___x_4040_);
if (v___x_4184_ == 0)
{
v___y_4167_ = v___y_4178_;
v___y_4168_ = v___y_4180_;
v___y_4169_ = v___x_4183_;
goto v___jp_4166_;
}
else
{
if (v___x_4027_ == 0)
{
v___y_4147_ = v___y_4178_;
v___y_4148_ = v___y_4179_;
v___y_4149_ = v___y_4180_;
v___y_4150_ = v___x_4183_;
goto v___jp_4146_;
}
else
{
v___y_4167_ = v___y_4178_;
v___y_4168_ = v___y_4180_;
v___y_4169_ = v___x_4183_;
goto v___jp_4166_;
}
}
}
}
v___jp_4185_:
{
lean_object* v___x_4189_; double v___x_4190_; double v___x_4191_; double v___x_4192_; double v___x_4193_; double v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; uint8_t v___x_4199_; lean_object* v___x_4200_; 
v___x_4189_ = lean_io_mono_nanos_now();
v___x_4190_ = lean_float_of_nat(v___y_4186_);
v___x_4191_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_4192_ = lean_float_div(v___x_4190_, v___x_4191_);
v___x_4193_ = lean_float_of_nat(v___x_4189_);
v___x_4194_ = lean_float_div(v___x_4193_, v___x_4191_);
v___x_4195_ = lean_box_float(v___x_4192_);
v___x_4196_ = lean_box_float(v___x_4194_);
v___x_4197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4195_);
lean_ctor_set(v___x_4197_, 1, v___x_4196_);
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v_a_4188_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = lean_unbox(v_a_4036_);
lean_dec(v_a_4036_);
v___x_4200_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3071_, v_hasTrace_3094_, v___x_3178_, v_options_3093_, v___x_4199_, v___y_4187_, v___f_4098_, v___x_4198_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_4200_;
}
v___jp_4201_:
{
lean_object* v___x_4205_; 
v___x_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4205_, 0, v_a_4204_);
v___y_4186_ = v___y_4202_;
v___y_4187_ = v___y_4203_;
v_a_4188_ = v___x_4205_;
goto v___jp_4185_;
}
v___jp_4206_:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = l_List_appendTR___redArg(v___x_4040_, v_fst_4030_);
v___x_4211_ = l_List_appendTR___redArg(v___x_4210_, v_a_4209_);
v___y_4202_ = v___y_4207_;
v___y_4203_ = v___y_4208_;
v_a_4204_ = v___x_4211_;
goto v___jp_4201_;
}
v___jp_4212_:
{
lean_object* v___x_4216_; 
v___x_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4216_, 0, v_a_4215_);
v___y_4186_ = v___y_4213_;
v___y_4187_ = v___y_4214_;
v_a_4188_ = v___x_4216_;
goto v___jp_4185_;
}
v___jp_4217_:
{
if (lean_obj_tag(v___y_4220_) == 0)
{
lean_object* v_a_4221_; 
v_a_4221_ = lean_ctor_get(v___y_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref(v___y_4220_);
v___y_4202_ = v___y_4218_;
v___y_4203_ = v___y_4219_;
v_a_4204_ = v_a_4221_;
goto v___jp_4201_;
}
else
{
lean_object* v_a_4222_; 
v_a_4222_ = lean_ctor_get(v___y_4220_, 0);
lean_inc(v_a_4222_);
lean_dec_ref(v___y_4220_);
v___y_4213_ = v___y_4218_;
v___y_4214_ = v___y_4219_;
v_a_4215_ = v_a_4222_;
goto v___jp_4212_;
}
}
v___jp_4223_:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4227_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4226_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_4218_ = v___y_4224_;
v___y_4219_ = v___y_4225_;
v___y_4220_ = v___x_4227_;
goto v___jp_4217_;
}
v___jp_4228_:
{
uint8_t v___x_4233_; 
v___x_4233_ = l_List_isEmpty___redArg(v_fst_4030_);
lean_dec(v_fst_4030_);
if (v___x_4233_ == 0)
{
lean_dec(v___y_4232_);
lean_dec(v___x_4040_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___y_4224_ = v___y_4229_;
v___y_4225_ = v___y_4231_;
goto v___jp_4223_;
}
else
{
if (v___y_4230_ == 0)
{
lean_object* v___x_4234_; 
lean_inc(v_trace_3071_);
v___x_4234_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_4232_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; lean_object* v___x_4236_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_a_4235_);
lean_dec_ref(v___x_4234_);
v___x_4236_ = l_List_appendTR___redArg(v___x_4040_, v_a_4235_);
v___y_4202_ = v___y_4229_;
v___y_4203_ = v___y_4231_;
v_a_4204_ = v___x_4236_;
goto v___jp_4201_;
}
else
{
lean_dec(v___x_4040_);
v___y_4218_ = v___y_4229_;
v___y_4219_ = v___y_4231_;
v___y_4220_ = v___x_4234_;
goto v___jp_4217_;
}
}
else
{
lean_dec(v___y_4232_);
lean_dec(v___x_4040_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___y_4224_ = v___y_4229_;
v___y_4225_ = v___y_4231_;
goto v___jp_4223_;
}
}
}
v___jp_4237_:
{
if (lean_obj_tag(v___y_4240_) == 0)
{
lean_object* v_a_4241_; 
v_a_4241_ = lean_ctor_get(v___y_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref(v___y_4240_);
v___y_4207_ = v___y_4238_;
v___y_4208_ = v___y_4239_;
v_a_4209_ = v_a_4241_;
goto v___jp_4206_;
}
else
{
lean_object* v_a_4242_; 
lean_dec(v___x_4040_);
lean_dec(v_fst_4030_);
v_a_4242_ = lean_ctor_get(v___y_4240_, 0);
lean_inc(v_a_4242_);
lean_dec_ref(v___y_4240_);
v___y_4213_ = v___y_4238_;
v___y_4214_ = v___y_4239_;
v_a_4215_ = v_a_4242_;
goto v___jp_4212_;
}
}
v___jp_4243_:
{
if (v___y_4248_ == 0)
{
lean_object* v___x_4249_; 
lean_dec_ref(v___y_4246_);
v___x_4249_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4245_, v_a_3077_, v_a_3079_);
lean_dec_ref(v___y_4245_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_dec_ref(v___x_4249_);
v___y_4207_ = v___y_4244_;
v___y_4208_ = v___y_4247_;
v_a_4209_ = v_snd_3088_;
goto v___jp_4206_;
}
else
{
lean_object* v_a_4250_; 
lean_dec(v___x_4040_);
lean_dec(v_fst_4030_);
lean_dec(v_snd_3088_);
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_a_4250_);
lean_dec_ref(v___x_4249_);
v___y_4213_ = v___y_4244_;
v___y_4214_ = v___y_4247_;
v_a_4215_ = v_a_4250_;
goto v___jp_4212_;
}
}
else
{
lean_dec_ref(v___y_4245_);
lean_dec(v_snd_3088_);
v___y_4238_ = v___y_4244_;
v___y_4239_ = v___y_4247_;
v___y_4240_ = v___y_4246_;
goto v___jp_4237_;
}
}
v___jp_4251_:
{
lean_object* v___x_4255_; 
v___x_4255_ = l_Lean_Meta_saveState___redArg(v_a_3077_, v_a_3079_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; lean_object* v___x_4257_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref(v___x_4255_);
lean_inc(v_snd_3088_);
lean_inc(v_trace_3071_);
v___x_4257_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_4254_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_dec(v_a_4256_);
lean_dec(v_snd_3088_);
v___y_4238_ = v___y_4252_;
v___y_4239_ = v___y_4253_;
v___y_4240_ = v___x_4257_;
goto v___jp_4237_;
}
else
{
lean_object* v_a_4258_; uint8_t v___x_4259_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
v___x_4259_ = l_Lean_Exception_isInterrupt(v_a_4258_);
if (v___x_4259_ == 0)
{
uint8_t v___x_4260_; 
v___x_4260_ = l_Lean_Exception_isRuntime(v_a_4258_);
v___y_4244_ = v___y_4252_;
v___y_4245_ = v_a_4256_;
v___y_4246_ = v___x_4257_;
v___y_4247_ = v___y_4253_;
v___y_4248_ = v___x_4260_;
goto v___jp_4243_;
}
else
{
lean_dec(v_a_4258_);
v___y_4244_ = v___y_4252_;
v___y_4245_ = v_a_4256_;
v___y_4246_ = v___x_4257_;
v___y_4247_ = v___y_4253_;
v___y_4248_ = v___x_4259_;
goto v___jp_4243_;
}
}
}
else
{
lean_object* v_a_4261_; 
lean_dec(v___y_4254_);
lean_dec(v___x_4040_);
lean_dec(v_fst_4030_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_4261_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4261_);
lean_dec_ref(v___x_4255_);
v___y_4213_ = v___y_4252_;
v___y_4214_ = v___y_4253_;
v_a_4215_ = v_a_4261_;
goto v___jp_4212_;
}
}
v___jp_4262_:
{
uint8_t v_commitIndependentGoals_4267_; lean_object* v___x_4268_; 
v_commitIndependentGoals_4267_ = lean_ctor_get_uint8(v_cfg_3070_, sizeof(void*)*4);
lean_inc(v___x_4040_);
v___x_4268_ = l_List_appendTR___redArg(v_a_4266_, v___x_4040_);
if (v_commitIndependentGoals_4267_ == 0)
{
v___y_4229_ = v___y_4263_;
v___y_4230_ = v___y_4264_;
v___y_4231_ = v___y_4265_;
v___y_4232_ = v___x_4268_;
goto v___jp_4228_;
}
else
{
uint8_t v___x_4269_; 
v___x_4269_ = l_List_isEmpty___redArg(v___x_4040_);
if (v___x_4269_ == 0)
{
v___y_4252_ = v___y_4263_;
v___y_4253_ = v___y_4265_;
v___y_4254_ = v___x_4268_;
goto v___jp_4251_;
}
else
{
if (v___y_4264_ == 0)
{
v___y_4229_ = v___y_4263_;
v___y_4230_ = v___y_4264_;
v___y_4231_ = v___y_4265_;
v___y_4232_ = v___x_4268_;
goto v___jp_4228_;
}
else
{
v___y_4252_ = v___y_4263_;
v___y_4253_ = v___y_4265_;
v___y_4254_ = v___x_4268_;
goto v___jp_4251_;
}
}
}
}
v___jp_4271_:
{
lean_object* v___x_4272_; 
v___x_4272_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_3079_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; lean_object* v___x_4274_; uint8_t v___x_4275_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc(v_a_4273_);
lean_dec_ref(v___x_4272_);
v___x_4274_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4275_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_3093_, v___x_4274_);
if (v___x_4275_ == 0)
{
lean_object* v___x_4276_; lean_object* v___x_4277_; 
lean_del_object(v___x_4033_);
v___x_4276_ = lean_io_mono_nanos_now();
v___x_4277_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3094_, v___x_4027_, v_goals_3074_, v___x_4270_, v_a_3077_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___x_4279_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref(v___x_4277_);
v___x_4279_ = l_List_reverse___redArg(v_a_4278_);
v___y_4263_ = v___x_4276_;
v___y_4264_ = v___x_4275_;
v___y_4265_ = v_a_4273_;
v_a_4266_ = v___x_4279_;
goto v___jp_4262_;
}
else
{
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4280_; 
v_a_4280_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4280_);
lean_dec_ref(v___x_4277_);
v___y_4263_ = v___x_4276_;
v___y_4264_ = v___x_4275_;
v___y_4265_ = v_a_4273_;
v_a_4266_ = v_a_4280_;
goto v___jp_4262_;
}
else
{
lean_object* v_a_4281_; 
lean_dec(v___x_4040_);
lean_dec(v_fst_4030_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_4281_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4281_);
lean_dec_ref(v___x_4277_);
v___y_4213_ = v___x_4276_;
v___y_4214_ = v_a_4273_;
v_a_4215_ = v_a_4281_;
goto v___jp_4212_;
}
}
}
else
{
lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4282_ = lean_io_get_num_heartbeats();
v___x_4283_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3094_, v___x_4027_, v_goals_3074_, v___x_4270_, v_a_3077_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_a_4284_; lean_object* v___x_4285_; 
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
lean_inc(v_a_4284_);
lean_dec_ref(v___x_4283_);
v___x_4285_ = l_List_reverse___redArg(v_a_4284_);
v___y_4178_ = v___x_4282_;
v___y_4179_ = v___x_4275_;
v___y_4180_ = v_a_4273_;
v_a_4181_ = v___x_4285_;
goto v___jp_4177_;
}
else
{
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_object* v_a_4286_; 
v_a_4286_ = lean_ctor_get(v___x_4283_, 0);
lean_inc(v_a_4286_);
lean_dec_ref(v___x_4283_);
v___y_4178_ = v___x_4282_;
v___y_4179_ = v___x_4275_;
v___y_4180_ = v_a_4273_;
v_a_4181_ = v_a_4286_;
goto v___jp_4177_;
}
else
{
lean_object* v_a_4287_; 
lean_dec(v___x_4040_);
lean_dec(v_fst_4030_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_4287_ = lean_ctor_get(v___x_4283_, 0);
lean_inc(v_a_4287_);
lean_dec_ref(v___x_4283_);
v___y_4126_ = v___x_4282_;
v___y_4127_ = v_a_4273_;
v_a_4128_ = v_a_4287_;
goto v___jp_4125_;
}
}
}
}
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec_ref(v___f_4098_);
lean_dec(v___x_4040_);
lean_dec(v_a_4036_);
lean_del_object(v___x_4033_);
lean_dec(v_fst_4030_);
lean_dec(v_snd_3088_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
v_a_4288_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4272_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4272_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
}
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_del_object(v___x_4033_);
lean_dec(v_snd_4031_);
lean_dec(v_fst_4030_);
lean_dec(v_snd_3088_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
v_a_4302_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4035_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4035_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
lean_dec(v_snd_3088_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
v_a_4311_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4028_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4028_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
else
{
goto v___jp_3968_;
}
}
else
{
goto v___jp_3968_;
}
v___jp_3179_:
{
lean_object* v___x_3183_; double v___x_3184_; double v___x_3185_; double v___x_3186_; double v___x_3187_; double v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3192_; 
v___x_3183_ = lean_io_mono_nanos_now();
v___x_3184_ = lean_float_of_nat(v___y_3181_);
v___x_3185_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3186_ = lean_float_div(v___x_3184_, v___x_3185_);
v___x_3187_ = lean_float_of_nat(v___x_3183_);
v___x_3188_ = lean_float_div(v___x_3187_, v___x_3185_);
v___x_3189_ = lean_box_float(v___x_3186_);
v___x_3190_ = lean_box_float(v___x_3188_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 1, v___x_3190_);
lean_ctor_set(v___x_3090_, 0, v___x_3189_);
v___x_3192_ = v___x_3090_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v___x_3190_);
v___x_3192_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3193_; uint8_t v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v_a_3182_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = lean_unbox(v_a_3176_);
lean_dec(v_a_3176_);
v___x_3195_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3071_, v_hasTrace_3094_, v___x_3178_, v_options_3093_, v___x_3194_, v___y_3180_, v___f_3177_, v___x_3193_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3195_;
}
}
v___jp_3197_:
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3201_, 0, v_a_3200_);
v___y_3180_ = v___y_3198_;
v___y_3181_ = v___y_3199_;
v_a_3182_ = v___x_3201_;
goto v___jp_3179_;
}
v___jp_3202_:
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3206_, 0, v_a_3205_);
v___y_3180_ = v___y_3203_;
v___y_3181_ = v___y_3204_;
v_a_3182_ = v___x_3206_;
goto v___jp_3179_;
}
v___jp_3207_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = l_List_appendTR___redArg(v___y_3211_, v___y_3209_);
v___x_3214_ = l_List_appendTR___redArg(v___x_3213_, v_a_3212_);
v___y_3203_ = v___y_3208_;
v___y_3204_ = v___y_3210_;
v_a_3205_ = v___x_3214_;
goto v___jp_3202_;
}
v___jp_3215_:
{
if (lean_obj_tag(v___y_3220_) == 0)
{
lean_object* v_a_3221_; 
v_a_3221_ = lean_ctor_get(v___y_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref(v___y_3220_);
v___y_3208_ = v___y_3216_;
v___y_3209_ = v___y_3217_;
v___y_3210_ = v___y_3218_;
v___y_3211_ = v___y_3219_;
v_a_3212_ = v_a_3221_;
goto v___jp_3207_;
}
else
{
lean_object* v_a_3222_; 
lean_dec(v___y_3219_);
lean_dec(v___y_3217_);
v_a_3222_ = lean_ctor_get(v___y_3220_, 0);
lean_inc(v_a_3222_);
lean_dec_ref(v___y_3220_);
v___y_3198_ = v___y_3216_;
v___y_3199_ = v___y_3218_;
v_a_3200_ = v_a_3222_;
goto v___jp_3197_;
}
}
v___jp_3223_:
{
if (v___y_3230_ == 0)
{
lean_object* v___x_3231_; 
lean_dec_ref(v___y_3228_);
v___x_3231_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3226_, v_a_3077_, v_a_3079_);
lean_dec_ref(v___y_3226_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_dec_ref(v___x_3231_);
v___y_3208_ = v___y_3224_;
v___y_3209_ = v___y_3225_;
v___y_3210_ = v___y_3227_;
v___y_3211_ = v___y_3229_;
v_a_3212_ = v_snd_3088_;
goto v___jp_3207_;
}
else
{
lean_object* v_a_3232_; 
lean_dec(v___y_3229_);
lean_dec(v___y_3225_);
lean_dec(v_snd_3088_);
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref(v___x_3231_);
v___y_3198_ = v___y_3224_;
v___y_3199_ = v___y_3227_;
v_a_3200_ = v_a_3232_;
goto v___jp_3197_;
}
}
else
{
lean_dec_ref(v___y_3226_);
lean_dec(v_snd_3088_);
v___y_3216_ = v___y_3224_;
v___y_3217_ = v___y_3225_;
v___y_3218_ = v___y_3227_;
v___y_3219_ = v___y_3229_;
v___y_3220_ = v___y_3228_;
goto v___jp_3215_;
}
}
v___jp_3233_:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_Meta_saveState___redArg(v_a_3077_, v_a_3079_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3241_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref(v___x_3239_);
lean_inc(v_snd_3088_);
lean_inc(v_trace_3071_);
v___x_3241_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3237_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_dec(v_a_3240_);
lean_dec(v_snd_3088_);
v___y_3216_ = v___y_3234_;
v___y_3217_ = v___y_3235_;
v___y_3218_ = v___y_3236_;
v___y_3219_ = v___y_3238_;
v___y_3220_ = v___x_3241_;
goto v___jp_3215_;
}
else
{
lean_object* v_a_3242_; uint8_t v___x_3243_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
v___x_3243_ = l_Lean_Exception_isInterrupt(v_a_3242_);
if (v___x_3243_ == 0)
{
uint8_t v___x_3244_; 
v___x_3244_ = l_Lean_Exception_isRuntime(v_a_3242_);
v___y_3224_ = v___y_3234_;
v___y_3225_ = v___y_3235_;
v___y_3226_ = v_a_3240_;
v___y_3227_ = v___y_3236_;
v___y_3228_ = v___x_3241_;
v___y_3229_ = v___y_3238_;
v___y_3230_ = v___x_3244_;
goto v___jp_3223_;
}
else
{
lean_dec(v_a_3242_);
v___y_3224_ = v___y_3234_;
v___y_3225_ = v___y_3235_;
v___y_3226_ = v_a_3240_;
v___y_3227_ = v___y_3236_;
v___y_3228_ = v___x_3241_;
v___y_3229_ = v___y_3238_;
v___y_3230_ = v___x_3243_;
goto v___jp_3223_;
}
}
}
else
{
lean_object* v_a_3245_; 
lean_dec(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec(v___y_3235_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3245_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3245_);
lean_dec_ref(v___x_3239_);
v___y_3198_ = v___y_3234_;
v___y_3199_ = v___y_3236_;
v_a_3200_ = v_a_3245_;
goto v___jp_3197_;
}
}
v___jp_3246_:
{
if (lean_obj_tag(v___y_3249_) == 0)
{
lean_object* v_a_3250_; 
v_a_3250_ = lean_ctor_get(v___y_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref(v___y_3249_);
v___y_3203_ = v___y_3247_;
v___y_3204_ = v___y_3248_;
v_a_3205_ = v_a_3250_;
goto v___jp_3202_;
}
else
{
lean_object* v_a_3251_; 
v_a_3251_ = lean_ctor_get(v___y_3249_, 0);
lean_inc(v_a_3251_);
lean_dec_ref(v___y_3249_);
v___y_3198_ = v___y_3247_;
v___y_3199_ = v___y_3248_;
v_a_3200_ = v_a_3251_;
goto v___jp_3197_;
}
}
v___jp_3252_:
{
lean_object* v___x_3260_; double v___x_3261_; double v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3260_ = lean_io_get_num_heartbeats();
v___x_3261_ = lean_float_of_nat(v___y_3254_);
v___x_3262_ = lean_float_of_nat(v___x_3260_);
v___x_3263_ = lean_box_float(v___x_3261_);
v___x_3264_ = lean_box_float(v___x_3262_);
v___x_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3266_, 0, v_a_3259_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
lean_inc(v_trace_3071_);
v___x_3267_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3071_, v_hasTrace_3094_, v___x_3178_, v_options_3093_, v___y_3255_, v___y_3256_, v___y_3258_, v___x_3266_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_3247_ = v___y_3253_;
v___y_3248_ = v___y_3257_;
v___y_3249_ = v___x_3267_;
goto v___jp_3246_;
}
v___jp_3268_:
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v_a_3275_);
v___y_3253_ = v___y_3269_;
v___y_3254_ = v___y_3270_;
v___y_3255_ = v___y_3271_;
v___y_3256_ = v___y_3272_;
v___y_3257_ = v___y_3274_;
v___y_3258_ = v___y_3273_;
v_a_3259_ = v___x_3276_;
goto v___jp_3252_;
}
v___jp_3277_:
{
lean_object* v___x_3285_; 
v___x_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3285_, 0, v_a_3284_);
v___y_3253_ = v___y_3278_;
v___y_3254_ = v___y_3279_;
v___y_3255_ = v___y_3280_;
v___y_3256_ = v___y_3281_;
v___y_3257_ = v___y_3283_;
v___y_3258_ = v___y_3282_;
v_a_3259_ = v___x_3285_;
goto v___jp_3252_;
}
v___jp_3286_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = l_List_appendTR___redArg(v___y_3294_, v___y_3289_);
v___x_3297_ = l_List_appendTR___redArg(v___x_3296_, v_a_3295_);
v___y_3278_ = v___y_3287_;
v___y_3279_ = v___y_3288_;
v___y_3280_ = v___y_3290_;
v___y_3281_ = v___y_3291_;
v___y_3282_ = v___y_3293_;
v___y_3283_ = v___y_3292_;
v_a_3284_ = v___x_3297_;
goto v___jp_3277_;
}
v___jp_3298_:
{
if (lean_obj_tag(v___y_3307_) == 0)
{
lean_object* v_a_3308_; 
v_a_3308_ = lean_ctor_get(v___y_3307_, 0);
lean_inc(v_a_3308_);
lean_dec_ref(v___y_3307_);
v___y_3287_ = v___y_3299_;
v___y_3288_ = v___y_3301_;
v___y_3289_ = v___y_3300_;
v___y_3290_ = v___y_3302_;
v___y_3291_ = v___y_3303_;
v___y_3292_ = v___y_3305_;
v___y_3293_ = v___y_3304_;
v___y_3294_ = v___y_3306_;
v_a_3295_ = v_a_3308_;
goto v___jp_3286_;
}
else
{
lean_object* v_a_3309_; 
lean_dec(v___y_3306_);
lean_dec(v___y_3300_);
v_a_3309_ = lean_ctor_get(v___y_3307_, 0);
lean_inc(v_a_3309_);
lean_dec_ref(v___y_3307_);
v___y_3269_ = v___y_3299_;
v___y_3270_ = v___y_3301_;
v___y_3271_ = v___y_3302_;
v___y_3272_ = v___y_3303_;
v___y_3273_ = v___y_3304_;
v___y_3274_ = v___y_3305_;
v_a_3275_ = v_a_3309_;
goto v___jp_3268_;
}
}
v___jp_3310_:
{
if (v___y_3321_ == 0)
{
lean_object* v___x_3322_; 
lean_dec_ref(v___y_3316_);
v___x_3322_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3320_, v_a_3077_, v_a_3079_);
lean_dec_ref(v___y_3320_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_dec_ref(v___x_3322_);
v___y_3287_ = v___y_3311_;
v___y_3288_ = v___y_3313_;
v___y_3289_ = v___y_3312_;
v___y_3290_ = v___y_3314_;
v___y_3291_ = v___y_3315_;
v___y_3292_ = v___y_3318_;
v___y_3293_ = v___y_3317_;
v___y_3294_ = v___y_3319_;
v_a_3295_ = v_snd_3088_;
goto v___jp_3286_;
}
else
{
lean_object* v_a_3323_; 
lean_dec(v___y_3319_);
lean_dec(v___y_3312_);
lean_dec(v_snd_3088_);
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref(v___x_3322_);
v___y_3269_ = v___y_3311_;
v___y_3270_ = v___y_3313_;
v___y_3271_ = v___y_3314_;
v___y_3272_ = v___y_3315_;
v___y_3273_ = v___y_3317_;
v___y_3274_ = v___y_3318_;
v_a_3275_ = v_a_3323_;
goto v___jp_3268_;
}
}
else
{
lean_dec_ref(v___y_3320_);
lean_dec(v_snd_3088_);
v___y_3299_ = v___y_3311_;
v___y_3300_ = v___y_3312_;
v___y_3301_ = v___y_3313_;
v___y_3302_ = v___y_3314_;
v___y_3303_ = v___y_3315_;
v___y_3304_ = v___y_3317_;
v___y_3305_ = v___y_3318_;
v___y_3306_ = v___y_3319_;
v___y_3307_ = v___y_3316_;
goto v___jp_3298_;
}
}
v___jp_3324_:
{
lean_object* v___x_3334_; 
v___x_3334_ = l_Lean_Meta_saveState___redArg(v_a_3077_, v_a_3079_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref(v___x_3334_);
lean_inc(v_snd_3088_);
lean_inc(v_trace_3071_);
v___x_3336_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3332_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_dec(v_a_3335_);
lean_dec(v_snd_3088_);
v___y_3299_ = v___y_3325_;
v___y_3300_ = v___y_3327_;
v___y_3301_ = v___y_3326_;
v___y_3302_ = v___y_3328_;
v___y_3303_ = v___y_3329_;
v___y_3304_ = v___y_3331_;
v___y_3305_ = v___y_3330_;
v___y_3306_ = v___y_3333_;
v___y_3307_ = v___x_3336_;
goto v___jp_3298_;
}
else
{
lean_object* v_a_3337_; uint8_t v___x_3338_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_a_3337_);
v___x_3338_ = l_Lean_Exception_isInterrupt(v_a_3337_);
if (v___x_3338_ == 0)
{
uint8_t v___x_3339_; 
v___x_3339_ = l_Lean_Exception_isRuntime(v_a_3337_);
v___y_3311_ = v___y_3325_;
v___y_3312_ = v___y_3327_;
v___y_3313_ = v___y_3326_;
v___y_3314_ = v___y_3328_;
v___y_3315_ = v___y_3329_;
v___y_3316_ = v___x_3336_;
v___y_3317_ = v___y_3331_;
v___y_3318_ = v___y_3330_;
v___y_3319_ = v___y_3333_;
v___y_3320_ = v_a_3335_;
v___y_3321_ = v___x_3339_;
goto v___jp_3310_;
}
else
{
lean_dec(v_a_3337_);
v___y_3311_ = v___y_3325_;
v___y_3312_ = v___y_3327_;
v___y_3313_ = v___y_3326_;
v___y_3314_ = v___y_3328_;
v___y_3315_ = v___y_3329_;
v___y_3316_ = v___x_3336_;
v___y_3317_ = v___y_3331_;
v___y_3318_ = v___y_3330_;
v___y_3319_ = v___y_3333_;
v___y_3320_ = v_a_3335_;
v___y_3321_ = v___x_3338_;
goto v___jp_3310_;
}
}
}
else
{
lean_object* v_a_3340_; 
lean_dec(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec(v___y_3327_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3340_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3340_);
lean_dec_ref(v___x_3334_);
v___y_3269_ = v___y_3325_;
v___y_3270_ = v___y_3326_;
v___y_3271_ = v___y_3328_;
v___y_3272_ = v___y_3329_;
v___y_3273_ = v___y_3331_;
v___y_3274_ = v___y_3330_;
v_a_3275_ = v_a_3340_;
goto v___jp_3268_;
}
}
v___jp_3341_:
{
if (lean_obj_tag(v___y_3348_) == 0)
{
lean_object* v_a_3349_; 
v_a_3349_ = lean_ctor_get(v___y_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref(v___y_3348_);
v___y_3278_ = v___y_3342_;
v___y_3279_ = v___y_3343_;
v___y_3280_ = v___y_3344_;
v___y_3281_ = v___y_3345_;
v___y_3282_ = v___y_3347_;
v___y_3283_ = v___y_3346_;
v_a_3284_ = v_a_3349_;
goto v___jp_3277_;
}
else
{
lean_object* v_a_3350_; 
v_a_3350_ = lean_ctor_get(v___y_3348_, 0);
lean_inc(v_a_3350_);
lean_dec_ref(v___y_3348_);
v___y_3269_ = v___y_3342_;
v___y_3270_ = v___y_3343_;
v___y_3271_ = v___y_3344_;
v___y_3272_ = v___y_3345_;
v___y_3273_ = v___y_3347_;
v___y_3274_ = v___y_3346_;
v_a_3275_ = v_a_3350_;
goto v___jp_3268_;
}
}
v___jp_3351_:
{
lean_object* v___x_3360_; 
lean_inc(v_trace_3071_);
v___x_3360_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3358_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref(v___x_3360_);
v___x_3362_ = l_List_appendTR___redArg(v___y_3359_, v_a_3361_);
v___y_3278_ = v___y_3352_;
v___y_3279_ = v___y_3353_;
v___y_3280_ = v___y_3354_;
v___y_3281_ = v___y_3355_;
v___y_3282_ = v___y_3357_;
v___y_3283_ = v___y_3356_;
v_a_3284_ = v___x_3362_;
goto v___jp_3277_;
}
else
{
lean_dec(v___y_3359_);
v___y_3342_ = v___y_3352_;
v___y_3343_ = v___y_3353_;
v___y_3344_ = v___y_3354_;
v___y_3345_ = v___y_3355_;
v___y_3346_ = v___y_3356_;
v___y_3347_ = v___y_3357_;
v___y_3348_ = v___x_3360_;
goto v___jp_3341_;
}
}
v___jp_3363_:
{
uint8_t v_commitIndependentGoals_3374_; lean_object* v___x_3375_; 
v_commitIndependentGoals_3374_ = lean_ctor_get_uint8(v_cfg_3070_, sizeof(void*)*4);
lean_inc(v___y_3372_);
v___x_3375_ = l_List_appendTR___redArg(v_a_3373_, v___y_3372_);
if (v_commitIndependentGoals_3374_ == 0)
{
lean_dec(v___y_3366_);
if (v___y_3365_ == 0)
{
v___y_3352_ = v___y_3364_;
v___y_3353_ = v___y_3367_;
v___y_3354_ = v___y_3368_;
v___y_3355_ = v___y_3369_;
v___y_3356_ = v___y_3371_;
v___y_3357_ = v___y_3370_;
v___y_3358_ = v___x_3375_;
v___y_3359_ = v___y_3372_;
goto v___jp_3351_;
}
else
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_dec(v___x_3375_);
lean_dec(v___y_3372_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___x_3376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3377_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3376_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_3342_ = v___y_3364_;
v___y_3343_ = v___y_3367_;
v___y_3344_ = v___y_3368_;
v___y_3345_ = v___y_3369_;
v___y_3346_ = v___y_3371_;
v___y_3347_ = v___y_3370_;
v___y_3348_ = v___x_3377_;
goto v___jp_3341_;
}
}
else
{
uint8_t v___x_3378_; 
v___x_3378_ = l_List_isEmpty___redArg(v___y_3372_);
if (v___x_3378_ == 0)
{
v___y_3325_ = v___y_3364_;
v___y_3326_ = v___y_3367_;
v___y_3327_ = v___y_3366_;
v___y_3328_ = v___y_3368_;
v___y_3329_ = v___y_3369_;
v___y_3330_ = v___y_3371_;
v___y_3331_ = v___y_3370_;
v___y_3332_ = v___x_3375_;
v___y_3333_ = v___y_3372_;
goto v___jp_3324_;
}
else
{
if (v___y_3365_ == 0)
{
lean_dec(v___y_3366_);
v___y_3352_ = v___y_3364_;
v___y_3353_ = v___y_3367_;
v___y_3354_ = v___y_3368_;
v___y_3355_ = v___y_3369_;
v___y_3356_ = v___y_3371_;
v___y_3357_ = v___y_3370_;
v___y_3358_ = v___x_3375_;
v___y_3359_ = v___y_3372_;
goto v___jp_3351_;
}
else
{
v___y_3325_ = v___y_3364_;
v___y_3326_ = v___y_3367_;
v___y_3327_ = v___y_3366_;
v___y_3328_ = v___y_3368_;
v___y_3329_ = v___y_3369_;
v___y_3330_ = v___y_3371_;
v___y_3331_ = v___y_3370_;
v___y_3332_ = v___x_3375_;
v___y_3333_ = v___y_3372_;
goto v___jp_3324_;
}
}
}
}
v___jp_3379_:
{
lean_object* v___x_3387_; double v___x_3388_; double v___x_3389_; double v___x_3390_; double v___x_3391_; double v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3387_ = lean_io_mono_nanos_now();
v___x_3388_ = lean_float_of_nat(v___y_3385_);
v___x_3389_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3390_ = lean_float_div(v___x_3388_, v___x_3389_);
v___x_3391_ = lean_float_of_nat(v___x_3387_);
v___x_3392_ = lean_float_div(v___x_3391_, v___x_3389_);
v___x_3393_ = lean_box_float(v___x_3390_);
v___x_3394_ = lean_box_float(v___x_3392_);
v___x_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3393_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v_a_3386_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
lean_inc(v_trace_3071_);
v___x_3397_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3071_, v_hasTrace_3094_, v___x_3178_, v_options_3093_, v___y_3381_, v___y_3382_, v___y_3384_, v___x_3396_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_3247_ = v___y_3380_;
v___y_3248_ = v___y_3383_;
v___y_3249_ = v___x_3397_;
goto v___jp_3246_;
}
v___jp_3398_:
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3406_, 0, v_a_3405_);
v___y_3380_ = v___y_3399_;
v___y_3381_ = v___y_3400_;
v___y_3382_ = v___y_3401_;
v___y_3383_ = v___y_3403_;
v___y_3384_ = v___y_3402_;
v___y_3385_ = v___y_3404_;
v_a_3386_ = v___x_3406_;
goto v___jp_3379_;
}
v___jp_3407_:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = l_List_appendTR___redArg(v___y_3415_, v___y_3409_);
v___x_3418_ = l_List_appendTR___redArg(v___x_3417_, v_a_3416_);
v___y_3399_ = v___y_3408_;
v___y_3400_ = v___y_3410_;
v___y_3401_ = v___y_3411_;
v___y_3402_ = v___y_3413_;
v___y_3403_ = v___y_3412_;
v___y_3404_ = v___y_3414_;
v_a_3405_ = v___x_3418_;
goto v___jp_3398_;
}
v___jp_3419_:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v_a_3426_);
v___y_3380_ = v___y_3420_;
v___y_3381_ = v___y_3421_;
v___y_3382_ = v___y_3422_;
v___y_3383_ = v___y_3424_;
v___y_3384_ = v___y_3423_;
v___y_3385_ = v___y_3425_;
v_a_3386_ = v___x_3427_;
goto v___jp_3379_;
}
v___jp_3428_:
{
if (lean_obj_tag(v___y_3435_) == 0)
{
lean_object* v_a_3436_; 
v_a_3436_ = lean_ctor_get(v___y_3435_, 0);
lean_inc(v_a_3436_);
lean_dec_ref(v___y_3435_);
v___y_3399_ = v___y_3429_;
v___y_3400_ = v___y_3430_;
v___y_3401_ = v___y_3431_;
v___y_3402_ = v___y_3433_;
v___y_3403_ = v___y_3432_;
v___y_3404_ = v___y_3434_;
v_a_3405_ = v_a_3436_;
goto v___jp_3398_;
}
else
{
lean_object* v_a_3437_; 
v_a_3437_ = lean_ctor_get(v___y_3435_, 0);
lean_inc(v_a_3437_);
lean_dec_ref(v___y_3435_);
v___y_3420_ = v___y_3429_;
v___y_3421_ = v___y_3430_;
v___y_3422_ = v___y_3431_;
v___y_3423_ = v___y_3433_;
v___y_3424_ = v___y_3432_;
v___y_3425_ = v___y_3434_;
v_a_3426_ = v_a_3437_;
goto v___jp_3419_;
}
}
v___jp_3438_:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3446_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3445_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_3429_ = v___y_3439_;
v___y_3430_ = v___y_3440_;
v___y_3431_ = v___y_3441_;
v___y_3432_ = v___y_3443_;
v___y_3433_ = v___y_3442_;
v___y_3434_ = v___y_3444_;
v___y_3435_ = v___x_3446_;
goto v___jp_3428_;
}
v___jp_3447_:
{
uint8_t v___x_3458_; 
v___x_3458_ = l_List_isEmpty___redArg(v___y_3450_);
lean_dec(v___y_3450_);
if (v___x_3458_ == 0)
{
lean_dec(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___y_3439_ = v___y_3448_;
v___y_3440_ = v___y_3451_;
v___y_3441_ = v___y_3452_;
v___y_3442_ = v___y_3454_;
v___y_3443_ = v___y_3453_;
v___y_3444_ = v___y_3455_;
goto v___jp_3438_;
}
else
{
if (v___y_3449_ == 0)
{
lean_object* v___x_3459_; 
lean_inc(v_trace_3071_);
v___x_3459_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3457_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref(v___x_3459_);
v___x_3461_ = l_List_appendTR___redArg(v___y_3456_, v_a_3460_);
v___y_3399_ = v___y_3448_;
v___y_3400_ = v___y_3451_;
v___y_3401_ = v___y_3452_;
v___y_3402_ = v___y_3454_;
v___y_3403_ = v___y_3453_;
v___y_3404_ = v___y_3455_;
v_a_3405_ = v___x_3461_;
goto v___jp_3398_;
}
else
{
lean_dec(v___y_3456_);
v___y_3429_ = v___y_3448_;
v___y_3430_ = v___y_3451_;
v___y_3431_ = v___y_3452_;
v___y_3432_ = v___y_3453_;
v___y_3433_ = v___y_3454_;
v___y_3434_ = v___y_3455_;
v___y_3435_ = v___x_3459_;
goto v___jp_3428_;
}
}
else
{
lean_dec(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___y_3439_ = v___y_3448_;
v___y_3440_ = v___y_3451_;
v___y_3441_ = v___y_3452_;
v___y_3442_ = v___y_3454_;
v___y_3443_ = v___y_3453_;
v___y_3444_ = v___y_3455_;
goto v___jp_3438_;
}
}
}
v___jp_3462_:
{
if (lean_obj_tag(v___y_3471_) == 0)
{
lean_object* v_a_3472_; 
v_a_3472_ = lean_ctor_get(v___y_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref(v___y_3471_);
v___y_3408_ = v___y_3463_;
v___y_3409_ = v___y_3464_;
v___y_3410_ = v___y_3465_;
v___y_3411_ = v___y_3466_;
v___y_3412_ = v___y_3468_;
v___y_3413_ = v___y_3467_;
v___y_3414_ = v___y_3469_;
v___y_3415_ = v___y_3470_;
v_a_3416_ = v_a_3472_;
goto v___jp_3407_;
}
else
{
lean_object* v_a_3473_; 
lean_dec(v___y_3470_);
lean_dec(v___y_3464_);
v_a_3473_ = lean_ctor_get(v___y_3471_, 0);
lean_inc(v_a_3473_);
lean_dec_ref(v___y_3471_);
v___y_3420_ = v___y_3463_;
v___y_3421_ = v___y_3465_;
v___y_3422_ = v___y_3466_;
v___y_3423_ = v___y_3467_;
v___y_3424_ = v___y_3468_;
v___y_3425_ = v___y_3469_;
v_a_3426_ = v_a_3473_;
goto v___jp_3419_;
}
}
v___jp_3474_:
{
if (v___y_3485_ == 0)
{
lean_object* v___x_3486_; 
lean_dec_ref(v___y_3478_);
v___x_3486_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3484_, v_a_3077_, v_a_3079_);
lean_dec_ref(v___y_3484_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_dec_ref(v___x_3486_);
v___y_3408_ = v___y_3475_;
v___y_3409_ = v___y_3476_;
v___y_3410_ = v___y_3477_;
v___y_3411_ = v___y_3479_;
v___y_3412_ = v___y_3481_;
v___y_3413_ = v___y_3480_;
v___y_3414_ = v___y_3482_;
v___y_3415_ = v___y_3483_;
v_a_3416_ = v_snd_3088_;
goto v___jp_3407_;
}
else
{
lean_object* v_a_3487_; 
lean_dec(v___y_3483_);
lean_dec(v___y_3476_);
lean_dec(v_snd_3088_);
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref(v___x_3486_);
v___y_3420_ = v___y_3475_;
v___y_3421_ = v___y_3477_;
v___y_3422_ = v___y_3479_;
v___y_3423_ = v___y_3480_;
v___y_3424_ = v___y_3481_;
v___y_3425_ = v___y_3482_;
v_a_3426_ = v_a_3487_;
goto v___jp_3419_;
}
}
else
{
lean_dec_ref(v___y_3484_);
lean_dec(v_snd_3088_);
v___y_3463_ = v___y_3475_;
v___y_3464_ = v___y_3476_;
v___y_3465_ = v___y_3477_;
v___y_3466_ = v___y_3479_;
v___y_3467_ = v___y_3480_;
v___y_3468_ = v___y_3481_;
v___y_3469_ = v___y_3482_;
v___y_3470_ = v___y_3483_;
v___y_3471_ = v___y_3478_;
goto v___jp_3462_;
}
}
v___jp_3488_:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Meta_saveState___redArg(v_a_3077_, v_a_3079_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3500_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref(v___x_3498_);
lean_inc(v_snd_3088_);
lean_inc(v_trace_3071_);
v___x_3500_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3497_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_dec(v_a_3499_);
lean_dec(v_snd_3088_);
v___y_3463_ = v___y_3489_;
v___y_3464_ = v___y_3490_;
v___y_3465_ = v___y_3491_;
v___y_3466_ = v___y_3492_;
v___y_3467_ = v___y_3494_;
v___y_3468_ = v___y_3493_;
v___y_3469_ = v___y_3495_;
v___y_3470_ = v___y_3496_;
v___y_3471_ = v___x_3500_;
goto v___jp_3462_;
}
else
{
lean_object* v_a_3501_; uint8_t v___x_3502_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
v___x_3502_ = l_Lean_Exception_isInterrupt(v_a_3501_);
if (v___x_3502_ == 0)
{
uint8_t v___x_3503_; 
v___x_3503_ = l_Lean_Exception_isRuntime(v_a_3501_);
v___y_3475_ = v___y_3489_;
v___y_3476_ = v___y_3490_;
v___y_3477_ = v___y_3491_;
v___y_3478_ = v___x_3500_;
v___y_3479_ = v___y_3492_;
v___y_3480_ = v___y_3494_;
v___y_3481_ = v___y_3493_;
v___y_3482_ = v___y_3495_;
v___y_3483_ = v___y_3496_;
v___y_3484_ = v_a_3499_;
v___y_3485_ = v___x_3503_;
goto v___jp_3474_;
}
else
{
lean_dec(v_a_3501_);
v___y_3475_ = v___y_3489_;
v___y_3476_ = v___y_3490_;
v___y_3477_ = v___y_3491_;
v___y_3478_ = v___x_3500_;
v___y_3479_ = v___y_3492_;
v___y_3480_ = v___y_3494_;
v___y_3481_ = v___y_3493_;
v___y_3482_ = v___y_3495_;
v___y_3483_ = v___y_3496_;
v___y_3484_ = v_a_3499_;
v___y_3485_ = v___x_3502_;
goto v___jp_3474_;
}
}
}
else
{
lean_object* v_a_3504_; 
lean_dec(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec(v___y_3490_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3504_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___x_3498_);
v___y_3420_ = v___y_3489_;
v___y_3421_ = v___y_3491_;
v___y_3422_ = v___y_3492_;
v___y_3423_ = v___y_3494_;
v___y_3424_ = v___y_3493_;
v___y_3425_ = v___y_3495_;
v_a_3426_ = v_a_3504_;
goto v___jp_3419_;
}
}
v___jp_3505_:
{
uint8_t v_commitIndependentGoals_3516_; lean_object* v___x_3517_; 
v_commitIndependentGoals_3516_ = lean_ctor_get_uint8(v_cfg_3070_, sizeof(void*)*4);
lean_inc(v___y_3514_);
v___x_3517_ = l_List_appendTR___redArg(v_a_3515_, v___y_3514_);
if (v_commitIndependentGoals_3516_ == 0)
{
v___y_3448_ = v___y_3506_;
v___y_3449_ = v___y_3507_;
v___y_3450_ = v___y_3508_;
v___y_3451_ = v___y_3509_;
v___y_3452_ = v___y_3510_;
v___y_3453_ = v___y_3511_;
v___y_3454_ = v___y_3512_;
v___y_3455_ = v___y_3513_;
v___y_3456_ = v___y_3514_;
v___y_3457_ = v___x_3517_;
goto v___jp_3447_;
}
else
{
uint8_t v___x_3518_; 
v___x_3518_ = l_List_isEmpty___redArg(v___y_3514_);
if (v___x_3518_ == 0)
{
v___y_3489_ = v___y_3506_;
v___y_3490_ = v___y_3508_;
v___y_3491_ = v___y_3509_;
v___y_3492_ = v___y_3510_;
v___y_3493_ = v___y_3511_;
v___y_3494_ = v___y_3512_;
v___y_3495_ = v___y_3513_;
v___y_3496_ = v___y_3514_;
v___y_3497_ = v___x_3517_;
goto v___jp_3488_;
}
else
{
if (v___y_3507_ == 0)
{
v___y_3448_ = v___y_3506_;
v___y_3449_ = v___y_3507_;
v___y_3450_ = v___y_3508_;
v___y_3451_ = v___y_3509_;
v___y_3452_ = v___y_3510_;
v___y_3453_ = v___y_3511_;
v___y_3454_ = v___y_3512_;
v___y_3455_ = v___y_3513_;
v___y_3456_ = v___y_3514_;
v___y_3457_ = v___x_3517_;
goto v___jp_3447_;
}
else
{
v___y_3489_ = v___y_3506_;
v___y_3490_ = v___y_3508_;
v___y_3491_ = v___y_3509_;
v___y_3492_ = v___y_3510_;
v___y_3493_ = v___y_3511_;
v___y_3494_ = v___y_3512_;
v___y_3495_ = v___y_3513_;
v___y_3496_ = v___y_3514_;
v___y_3497_ = v___x_3517_;
goto v___jp_3488_;
}
}
}
}
v___jp_3519_:
{
lean_object* v___x_3528_; 
v___x_3528_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_3079_);
if (lean_obj_tag(v___x_3528_) == 0)
{
if (v___y_3522_ == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref(v___x_3528_);
v___x_3530_ = lean_io_mono_nanos_now();
v___x_3531_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3094_, v___y_3522_, v_goals_3074_, v___y_3524_, v_a_3077_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref(v___x_3531_);
v___x_3533_ = l_List_reverse___redArg(v_a_3532_);
v___y_3506_ = v___y_3520_;
v___y_3507_ = v___y_3522_;
v___y_3508_ = v___y_3521_;
v___y_3509_ = v___y_3523_;
v___y_3510_ = v_a_3529_;
v___y_3511_ = v___y_3526_;
v___y_3512_ = v___y_3525_;
v___y_3513_ = v___x_3530_;
v___y_3514_ = v___y_3527_;
v_a_3515_ = v___x_3533_;
goto v___jp_3505_;
}
else
{
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3534_; 
v_a_3534_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3534_);
lean_dec_ref(v___x_3531_);
v___y_3506_ = v___y_3520_;
v___y_3507_ = v___y_3522_;
v___y_3508_ = v___y_3521_;
v___y_3509_ = v___y_3523_;
v___y_3510_ = v_a_3529_;
v___y_3511_ = v___y_3526_;
v___y_3512_ = v___y_3525_;
v___y_3513_ = v___x_3530_;
v___y_3514_ = v___y_3527_;
v_a_3515_ = v_a_3534_;
goto v___jp_3505_;
}
else
{
lean_object* v_a_3535_; 
lean_dec(v___y_3527_);
lean_dec(v___y_3521_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3535_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3535_);
lean_dec_ref(v___x_3531_);
v___y_3420_ = v___y_3520_;
v___y_3421_ = v___y_3523_;
v___y_3422_ = v_a_3529_;
v___y_3423_ = v___y_3525_;
v___y_3424_ = v___y_3526_;
v___y_3425_ = v___x_3530_;
v_a_3426_ = v_a_3535_;
goto v___jp_3419_;
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v_a_3536_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3536_);
lean_dec_ref(v___x_3528_);
v___x_3537_ = lean_io_get_num_heartbeats();
v___x_3538_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3094_, v___y_3522_, v_goals_3074_, v___y_3524_, v_a_3077_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3540_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref(v___x_3538_);
v___x_3540_ = l_List_reverse___redArg(v_a_3539_);
v___y_3364_ = v___y_3520_;
v___y_3365_ = v___y_3522_;
v___y_3366_ = v___y_3521_;
v___y_3367_ = v___x_3537_;
v___y_3368_ = v___y_3523_;
v___y_3369_ = v_a_3536_;
v___y_3370_ = v___y_3525_;
v___y_3371_ = v___y_3526_;
v___y_3372_ = v___y_3527_;
v_a_3373_ = v___x_3540_;
goto v___jp_3363_;
}
else
{
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3541_; 
v_a_3541_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3541_);
lean_dec_ref(v___x_3538_);
v___y_3364_ = v___y_3520_;
v___y_3365_ = v___y_3522_;
v___y_3366_ = v___y_3521_;
v___y_3367_ = v___x_3537_;
v___y_3368_ = v___y_3523_;
v___y_3369_ = v_a_3536_;
v___y_3370_ = v___y_3525_;
v___y_3371_ = v___y_3526_;
v___y_3372_ = v___y_3527_;
v_a_3373_ = v_a_3541_;
goto v___jp_3363_;
}
else
{
lean_object* v_a_3542_; 
lean_dec(v___y_3527_);
lean_dec(v___y_3521_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3542_ = lean_ctor_get(v___x_3538_, 0);
lean_inc(v_a_3542_);
lean_dec_ref(v___x_3538_);
v___y_3269_ = v___y_3520_;
v___y_3270_ = v___x_3537_;
v___y_3271_ = v___y_3523_;
v___y_3272_ = v_a_3536_;
v___y_3273_ = v___y_3525_;
v___y_3274_ = v___y_3526_;
v_a_3275_ = v_a_3542_;
goto v___jp_3268_;
}
}
}
}
else
{
lean_object* v_a_3543_; 
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec(v___y_3521_);
lean_dec(v_snd_3088_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3543_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3543_);
lean_dec_ref(v___x_3528_);
v___y_3198_ = v___y_3520_;
v___y_3199_ = v___y_3526_;
v_a_3200_ = v_a_3543_;
goto v___jp_3197_;
}
}
v___jp_3544_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3548_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3547_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_3247_ = v___y_3545_;
v___y_3248_ = v___y_3546_;
v___y_3249_ = v___x_3548_;
goto v___jp_3246_;
}
v___jp_3549_:
{
uint8_t v___x_3556_; 
v___x_3556_ = l_List_isEmpty___redArg(v___y_3551_);
lean_dec(v___y_3551_);
if (v___x_3556_ == 0)
{
lean_dec(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___y_3545_ = v___y_3550_;
v___y_3546_ = v___y_3553_;
goto v___jp_3544_;
}
else
{
if (v___y_3552_ == 0)
{
lean_object* v___x_3557_; 
lean_inc(v_trace_3071_);
v___x_3557_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3554_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3559_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref(v___x_3557_);
v___x_3559_ = l_List_appendTR___redArg(v___y_3555_, v_a_3558_);
v___y_3203_ = v___y_3550_;
v___y_3204_ = v___y_3553_;
v_a_3205_ = v___x_3559_;
goto v___jp_3202_;
}
else
{
lean_dec(v___y_3555_);
v___y_3247_ = v___y_3550_;
v___y_3248_ = v___y_3553_;
v___y_3249_ = v___x_3557_;
goto v___jp_3246_;
}
}
else
{
lean_dec(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___y_3545_ = v___y_3550_;
v___y_3546_ = v___y_3553_;
goto v___jp_3544_;
}
}
}
v___jp_3560_:
{
uint8_t v_commitIndependentGoals_3567_; lean_object* v___x_3568_; 
v_commitIndependentGoals_3567_ = lean_ctor_get_uint8(v_cfg_3070_, sizeof(void*)*4);
lean_inc(v___y_3565_);
v___x_3568_ = l_List_appendTR___redArg(v_a_3566_, v___y_3565_);
if (v_commitIndependentGoals_3567_ == 0)
{
v___y_3550_ = v___y_3561_;
v___y_3551_ = v___y_3562_;
v___y_3552_ = v___y_3563_;
v___y_3553_ = v___y_3564_;
v___y_3554_ = v___x_3568_;
v___y_3555_ = v___y_3565_;
goto v___jp_3549_;
}
else
{
uint8_t v___x_3569_; 
v___x_3569_ = l_List_isEmpty___redArg(v___y_3565_);
if (v___x_3569_ == 0)
{
v___y_3234_ = v___y_3561_;
v___y_3235_ = v___y_3562_;
v___y_3236_ = v___y_3564_;
v___y_3237_ = v___x_3568_;
v___y_3238_ = v___y_3565_;
goto v___jp_3233_;
}
else
{
if (v___y_3563_ == 0)
{
v___y_3550_ = v___y_3561_;
v___y_3551_ = v___y_3562_;
v___y_3552_ = v___y_3563_;
v___y_3553_ = v___y_3564_;
v___y_3554_ = v___x_3568_;
v___y_3555_ = v___y_3565_;
goto v___jp_3549_;
}
else
{
v___y_3234_ = v___y_3561_;
v___y_3235_ = v___y_3562_;
v___y_3236_ = v___y_3564_;
v___y_3237_ = v___x_3568_;
v___y_3238_ = v___y_3565_;
goto v___jp_3233_;
}
}
}
}
v___jp_3570_:
{
lean_object* v___x_3574_; double v___x_3575_; double v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; lean_object* v___x_3582_; 
v___x_3574_ = lean_io_get_num_heartbeats();
v___x_3575_ = lean_float_of_nat(v___y_3572_);
v___x_3576_ = lean_float_of_nat(v___x_3574_);
v___x_3577_ = lean_box_float(v___x_3575_);
v___x_3578_ = lean_box_float(v___x_3576_);
v___x_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3577_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
v___x_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3580_, 0, v_a_3573_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
v___x_3581_ = lean_unbox(v_a_3176_);
lean_dec(v_a_3176_);
v___x_3582_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3071_, v_hasTrace_3094_, v___x_3178_, v_options_3093_, v___x_3581_, v___y_3571_, v___f_3177_, v___x_3580_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3582_;
}
v___jp_3583_:
{
lean_object* v___x_3587_; 
v___x_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3587_, 0, v_a_3586_);
v___y_3571_ = v___y_3584_;
v___y_3572_ = v___y_3585_;
v_a_3573_ = v___x_3587_;
goto v___jp_3570_;
}
v___jp_3588_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = l_List_appendTR___redArg(v___y_3591_, v___y_3590_);
v___x_3595_ = l_List_appendTR___redArg(v___x_3594_, v_a_3593_);
v___y_3584_ = v___y_3589_;
v___y_3585_ = v___y_3592_;
v_a_3586_ = v___x_3595_;
goto v___jp_3583_;
}
v___jp_3596_:
{
lean_object* v___x_3600_; 
v___x_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3600_, 0, v_a_3599_);
v___y_3571_ = v___y_3597_;
v___y_3572_ = v___y_3598_;
v_a_3573_ = v___x_3600_;
goto v___jp_3570_;
}
v___jp_3601_:
{
if (lean_obj_tag(v___y_3604_) == 0)
{
lean_object* v_a_3605_; 
v_a_3605_ = lean_ctor_get(v___y_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref(v___y_3604_);
v___y_3584_ = v___y_3602_;
v___y_3585_ = v___y_3603_;
v_a_3586_ = v_a_3605_;
goto v___jp_3583_;
}
else
{
lean_object* v_a_3606_; 
v_a_3606_ = lean_ctor_get(v___y_3604_, 0);
lean_inc(v_a_3606_);
lean_dec_ref(v___y_3604_);
v___y_3597_ = v___y_3602_;
v___y_3598_ = v___y_3603_;
v_a_3599_ = v_a_3606_;
goto v___jp_3596_;
}
}
v___jp_3607_:
{
lean_object* v___x_3615_; double v___x_3616_; double v___x_3617_; double v___x_3618_; double v___x_3619_; double v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3615_ = lean_io_mono_nanos_now();
v___x_3616_ = lean_float_of_nat(v___y_3610_);
v___x_3617_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3618_ = lean_float_div(v___x_3616_, v___x_3617_);
v___x_3619_ = lean_float_of_nat(v___x_3615_);
v___x_3620_ = lean_float_div(v___x_3619_, v___x_3617_);
v___x_3621_ = lean_box_float(v___x_3618_);
v___x_3622_ = lean_box_float(v___x_3620_);
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3621_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
v___x_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3624_, 0, v_a_3614_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
lean_inc(v_trace_3071_);
v___x_3625_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3071_, v_hasTrace_3094_, v___x_3178_, v_options_3093_, v___y_3609_, v___y_3611_, v___y_3612_, v___x_3624_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_3602_ = v___y_3608_;
v___y_3603_ = v___y_3613_;
v___y_3604_ = v___x_3625_;
goto v___jp_3601_;
}
v___jp_3626_:
{
lean_object* v___x_3634_; 
v___x_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3634_, 0, v_a_3633_);
v___y_3608_ = v___y_3628_;
v___y_3609_ = v___y_3627_;
v___y_3610_ = v___y_3629_;
v___y_3611_ = v___y_3630_;
v___y_3612_ = v___y_3631_;
v___y_3613_ = v___y_3632_;
v_a_3614_ = v___x_3634_;
goto v___jp_3607_;
}
v___jp_3635_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = l_List_appendTR___redArg(v___y_3640_, v___y_3639_);
v___x_3646_ = l_List_appendTR___redArg(v___x_3645_, v_a_3644_);
v___y_3627_ = v___y_3637_;
v___y_3628_ = v___y_3636_;
v___y_3629_ = v___y_3638_;
v___y_3630_ = v___y_3641_;
v___y_3631_ = v___y_3642_;
v___y_3632_ = v___y_3643_;
v_a_3633_ = v___x_3646_;
goto v___jp_3626_;
}
v___jp_3647_:
{
lean_object* v___x_3655_; 
v___x_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3655_, 0, v_a_3654_);
v___y_3608_ = v___y_3649_;
v___y_3609_ = v___y_3648_;
v___y_3610_ = v___y_3650_;
v___y_3611_ = v___y_3651_;
v___y_3612_ = v___y_3652_;
v___y_3613_ = v___y_3653_;
v_a_3614_ = v___x_3655_;
goto v___jp_3607_;
}
v___jp_3656_:
{
if (lean_obj_tag(v___y_3663_) == 0)
{
lean_object* v_a_3664_; 
v_a_3664_ = lean_ctor_get(v___y_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref(v___y_3663_);
v___y_3627_ = v___y_3658_;
v___y_3628_ = v___y_3657_;
v___y_3629_ = v___y_3659_;
v___y_3630_ = v___y_3660_;
v___y_3631_ = v___y_3661_;
v___y_3632_ = v___y_3662_;
v_a_3633_ = v_a_3664_;
goto v___jp_3626_;
}
else
{
lean_object* v_a_3665_; 
v_a_3665_ = lean_ctor_get(v___y_3663_, 0);
lean_inc(v_a_3665_);
lean_dec_ref(v___y_3663_);
v___y_3648_ = v___y_3658_;
v___y_3649_ = v___y_3657_;
v___y_3650_ = v___y_3659_;
v___y_3651_ = v___y_3660_;
v___y_3652_ = v___y_3661_;
v___y_3653_ = v___y_3662_;
v_a_3654_ = v_a_3665_;
goto v___jp_3647_;
}
}
v___jp_3666_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3674_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3673_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_3657_ = v___y_3668_;
v___y_3658_ = v___y_3667_;
v___y_3659_ = v___y_3669_;
v___y_3660_ = v___y_3670_;
v___y_3661_ = v___y_3671_;
v___y_3662_ = v___y_3672_;
v___y_3663_ = v___x_3674_;
goto v___jp_3656_;
}
v___jp_3675_:
{
uint8_t v___x_3686_; 
v___x_3686_ = l_List_isEmpty___redArg(v___y_3681_);
lean_dec(v___y_3681_);
if (v___x_3686_ == 0)
{
lean_dec(v___y_3684_);
lean_dec(v___y_3680_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___y_3667_ = v___y_3677_;
v___y_3668_ = v___y_3676_;
v___y_3669_ = v___y_3679_;
v___y_3670_ = v___y_3682_;
v___y_3671_ = v___y_3683_;
v___y_3672_ = v___y_3685_;
goto v___jp_3666_;
}
else
{
if (v___y_3678_ == 0)
{
lean_object* v___x_3687_; 
lean_inc(v_trace_3071_);
v___x_3687_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3684_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; lean_object* v___x_3689_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref(v___x_3687_);
v___x_3689_ = l_List_appendTR___redArg(v___y_3680_, v_a_3688_);
v___y_3627_ = v___y_3677_;
v___y_3628_ = v___y_3676_;
v___y_3629_ = v___y_3679_;
v___y_3630_ = v___y_3682_;
v___y_3631_ = v___y_3683_;
v___y_3632_ = v___y_3685_;
v_a_3633_ = v___x_3689_;
goto v___jp_3626_;
}
else
{
lean_dec(v___y_3680_);
v___y_3657_ = v___y_3676_;
v___y_3658_ = v___y_3677_;
v___y_3659_ = v___y_3679_;
v___y_3660_ = v___y_3682_;
v___y_3661_ = v___y_3683_;
v___y_3662_ = v___y_3685_;
v___y_3663_ = v___x_3687_;
goto v___jp_3656_;
}
}
else
{
lean_dec(v___y_3684_);
lean_dec(v___y_3680_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___y_3667_ = v___y_3677_;
v___y_3668_ = v___y_3676_;
v___y_3669_ = v___y_3679_;
v___y_3670_ = v___y_3682_;
v___y_3671_ = v___y_3683_;
v___y_3672_ = v___y_3685_;
goto v___jp_3666_;
}
}
}
v___jp_3690_:
{
if (lean_obj_tag(v___y_3699_) == 0)
{
lean_object* v_a_3700_; 
v_a_3700_ = lean_ctor_get(v___y_3699_, 0);
lean_inc(v_a_3700_);
lean_dec_ref(v___y_3699_);
v___y_3636_ = v___y_3692_;
v___y_3637_ = v___y_3691_;
v___y_3638_ = v___y_3693_;
v___y_3639_ = v___y_3695_;
v___y_3640_ = v___y_3694_;
v___y_3641_ = v___y_3696_;
v___y_3642_ = v___y_3697_;
v___y_3643_ = v___y_3698_;
v_a_3644_ = v_a_3700_;
goto v___jp_3635_;
}
else
{
lean_object* v_a_3701_; 
lean_dec(v___y_3695_);
lean_dec(v___y_3694_);
v_a_3701_ = lean_ctor_get(v___y_3699_, 0);
lean_inc(v_a_3701_);
lean_dec_ref(v___y_3699_);
v___y_3648_ = v___y_3691_;
v___y_3649_ = v___y_3692_;
v___y_3650_ = v___y_3693_;
v___y_3651_ = v___y_3696_;
v___y_3652_ = v___y_3697_;
v___y_3653_ = v___y_3698_;
v_a_3654_ = v_a_3701_;
goto v___jp_3647_;
}
}
v___jp_3702_:
{
if (v___y_3713_ == 0)
{
lean_object* v___x_3714_; 
lean_dec_ref(v___y_3708_);
v___x_3714_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3712_, v_a_3077_, v_a_3079_);
lean_dec_ref(v___y_3712_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_dec_ref(v___x_3714_);
v___y_3636_ = v___y_3704_;
v___y_3637_ = v___y_3703_;
v___y_3638_ = v___y_3705_;
v___y_3639_ = v___y_3707_;
v___y_3640_ = v___y_3706_;
v___y_3641_ = v___y_3709_;
v___y_3642_ = v___y_3710_;
v___y_3643_ = v___y_3711_;
v_a_3644_ = v_snd_3088_;
goto v___jp_3635_;
}
else
{
lean_object* v_a_3715_; 
lean_dec(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec(v_snd_3088_);
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc(v_a_3715_);
lean_dec_ref(v___x_3714_);
v___y_3648_ = v___y_3703_;
v___y_3649_ = v___y_3704_;
v___y_3650_ = v___y_3705_;
v___y_3651_ = v___y_3709_;
v___y_3652_ = v___y_3710_;
v___y_3653_ = v___y_3711_;
v_a_3654_ = v_a_3715_;
goto v___jp_3647_;
}
}
else
{
lean_dec_ref(v___y_3712_);
lean_dec(v_snd_3088_);
v___y_3691_ = v___y_3703_;
v___y_3692_ = v___y_3704_;
v___y_3693_ = v___y_3705_;
v___y_3694_ = v___y_3706_;
v___y_3695_ = v___y_3707_;
v___y_3696_ = v___y_3709_;
v___y_3697_ = v___y_3710_;
v___y_3698_ = v___y_3711_;
v___y_3699_ = v___y_3708_;
goto v___jp_3690_;
}
}
v___jp_3716_:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_Meta_saveState___redArg(v_a_3077_, v_a_3079_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3728_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref(v___x_3726_);
lean_inc(v_snd_3088_);
lean_inc(v_trace_3071_);
v___x_3728_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3724_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_dec(v_a_3727_);
lean_dec(v_snd_3088_);
v___y_3691_ = v___y_3718_;
v___y_3692_ = v___y_3717_;
v___y_3693_ = v___y_3719_;
v___y_3694_ = v___y_3721_;
v___y_3695_ = v___y_3720_;
v___y_3696_ = v___y_3722_;
v___y_3697_ = v___y_3723_;
v___y_3698_ = v___y_3725_;
v___y_3699_ = v___x_3728_;
goto v___jp_3690_;
}
else
{
lean_object* v_a_3729_; uint8_t v___x_3730_; 
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_a_3729_);
v___x_3730_ = l_Lean_Exception_isInterrupt(v_a_3729_);
if (v___x_3730_ == 0)
{
uint8_t v___x_3731_; 
v___x_3731_ = l_Lean_Exception_isRuntime(v_a_3729_);
v___y_3703_ = v___y_3718_;
v___y_3704_ = v___y_3717_;
v___y_3705_ = v___y_3719_;
v___y_3706_ = v___y_3721_;
v___y_3707_ = v___y_3720_;
v___y_3708_ = v___x_3728_;
v___y_3709_ = v___y_3722_;
v___y_3710_ = v___y_3723_;
v___y_3711_ = v___y_3725_;
v___y_3712_ = v_a_3727_;
v___y_3713_ = v___x_3731_;
goto v___jp_3702_;
}
else
{
lean_dec(v_a_3729_);
v___y_3703_ = v___y_3718_;
v___y_3704_ = v___y_3717_;
v___y_3705_ = v___y_3719_;
v___y_3706_ = v___y_3721_;
v___y_3707_ = v___y_3720_;
v___y_3708_ = v___x_3728_;
v___y_3709_ = v___y_3722_;
v___y_3710_ = v___y_3723_;
v___y_3711_ = v___y_3725_;
v___y_3712_ = v_a_3727_;
v___y_3713_ = v___x_3730_;
goto v___jp_3702_;
}
}
}
else
{
lean_object* v_a_3732_; 
lean_dec(v___y_3724_);
lean_dec(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3732_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3732_);
lean_dec_ref(v___x_3726_);
v___y_3648_ = v___y_3718_;
v___y_3649_ = v___y_3717_;
v___y_3650_ = v___y_3719_;
v___y_3651_ = v___y_3722_;
v___y_3652_ = v___y_3723_;
v___y_3653_ = v___y_3725_;
v_a_3654_ = v_a_3732_;
goto v___jp_3647_;
}
}
v___jp_3733_:
{
uint8_t v_commitIndependentGoals_3744_; lean_object* v___x_3745_; 
v_commitIndependentGoals_3744_ = lean_ctor_get_uint8(v_cfg_3070_, sizeof(void*)*4);
lean_inc(v___y_3739_);
v___x_3745_ = l_List_appendTR___redArg(v_a_3743_, v___y_3739_);
if (v_commitIndependentGoals_3744_ == 0)
{
v___y_3676_ = v___y_3734_;
v___y_3677_ = v___y_3735_;
v___y_3678_ = v___y_3736_;
v___y_3679_ = v___y_3737_;
v___y_3680_ = v___y_3739_;
v___y_3681_ = v___y_3738_;
v___y_3682_ = v___y_3740_;
v___y_3683_ = v___y_3741_;
v___y_3684_ = v___x_3745_;
v___y_3685_ = v___y_3742_;
goto v___jp_3675_;
}
else
{
uint8_t v___x_3746_; 
v___x_3746_ = l_List_isEmpty___redArg(v___y_3739_);
if (v___x_3746_ == 0)
{
v___y_3717_ = v___y_3734_;
v___y_3718_ = v___y_3735_;
v___y_3719_ = v___y_3737_;
v___y_3720_ = v___y_3738_;
v___y_3721_ = v___y_3739_;
v___y_3722_ = v___y_3740_;
v___y_3723_ = v___y_3741_;
v___y_3724_ = v___x_3745_;
v___y_3725_ = v___y_3742_;
goto v___jp_3716_;
}
else
{
if (v___y_3736_ == 0)
{
v___y_3676_ = v___y_3734_;
v___y_3677_ = v___y_3735_;
v___y_3678_ = v___y_3736_;
v___y_3679_ = v___y_3737_;
v___y_3680_ = v___y_3739_;
v___y_3681_ = v___y_3738_;
v___y_3682_ = v___y_3740_;
v___y_3683_ = v___y_3741_;
v___y_3684_ = v___x_3745_;
v___y_3685_ = v___y_3742_;
goto v___jp_3675_;
}
else
{
v___y_3717_ = v___y_3734_;
v___y_3718_ = v___y_3735_;
v___y_3719_ = v___y_3737_;
v___y_3720_ = v___y_3738_;
v___y_3721_ = v___y_3739_;
v___y_3722_ = v___y_3740_;
v___y_3723_ = v___y_3741_;
v___y_3724_ = v___x_3745_;
v___y_3725_ = v___y_3742_;
goto v___jp_3716_;
}
}
}
}
v___jp_3747_:
{
lean_object* v___x_3755_; double v___x_3756_; double v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3755_ = lean_io_get_num_heartbeats();
v___x_3756_ = lean_float_of_nat(v___y_3750_);
v___x_3757_ = lean_float_of_nat(v___x_3755_);
v___x_3758_ = lean_box_float(v___x_3756_);
v___x_3759_ = lean_box_float(v___x_3757_);
v___x_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3758_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3761_, 0, v_a_3754_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
lean_inc(v_trace_3071_);
v___x_3762_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3071_, v_hasTrace_3094_, v___x_3178_, v_options_3093_, v___y_3749_, v___y_3751_, v___y_3752_, v___x_3761_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_3602_ = v___y_3748_;
v___y_3603_ = v___y_3753_;
v___y_3604_ = v___x_3762_;
goto v___jp_3601_;
}
v___jp_3763_:
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3771_, 0, v_a_3770_);
v___y_3748_ = v___y_3765_;
v___y_3749_ = v___y_3764_;
v___y_3750_ = v___y_3766_;
v___y_3751_ = v___y_3767_;
v___y_3752_ = v___y_3768_;
v___y_3753_ = v___y_3769_;
v_a_3754_ = v___x_3771_;
goto v___jp_3747_;
}
v___jp_3772_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3782_ = l_List_appendTR___redArg(v___y_3776_, v___y_3775_);
v___x_3783_ = l_List_appendTR___redArg(v___x_3782_, v_a_3781_);
v___y_3764_ = v___y_3774_;
v___y_3765_ = v___y_3773_;
v___y_3766_ = v___y_3777_;
v___y_3767_ = v___y_3778_;
v___y_3768_ = v___y_3779_;
v___y_3769_ = v___y_3780_;
v_a_3770_ = v___x_3783_;
goto v___jp_3763_;
}
v___jp_3784_:
{
lean_object* v___x_3792_; 
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v_a_3791_);
v___y_3748_ = v___y_3786_;
v___y_3749_ = v___y_3785_;
v___y_3750_ = v___y_3787_;
v___y_3751_ = v___y_3788_;
v___y_3752_ = v___y_3789_;
v___y_3753_ = v___y_3790_;
v_a_3754_ = v___x_3792_;
goto v___jp_3747_;
}
v___jp_3793_:
{
if (lean_obj_tag(v___y_3800_) == 0)
{
lean_object* v_a_3801_; 
v_a_3801_ = lean_ctor_get(v___y_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref(v___y_3800_);
v___y_3764_ = v___y_3795_;
v___y_3765_ = v___y_3794_;
v___y_3766_ = v___y_3796_;
v___y_3767_ = v___y_3797_;
v___y_3768_ = v___y_3798_;
v___y_3769_ = v___y_3799_;
v_a_3770_ = v_a_3801_;
goto v___jp_3763_;
}
else
{
lean_object* v_a_3802_; 
v_a_3802_ = lean_ctor_get(v___y_3800_, 0);
lean_inc(v_a_3802_);
lean_dec_ref(v___y_3800_);
v___y_3785_ = v___y_3795_;
v___y_3786_ = v___y_3794_;
v___y_3787_ = v___y_3796_;
v___y_3788_ = v___y_3797_;
v___y_3789_ = v___y_3798_;
v___y_3790_ = v___y_3799_;
v_a_3791_ = v_a_3802_;
goto v___jp_3784_;
}
}
v___jp_3803_:
{
lean_object* v___x_3812_; 
lean_inc(v_trace_3071_);
v___x_3812_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3806_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3814_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref(v___x_3812_);
v___x_3814_ = l_List_appendTR___redArg(v___y_3807_, v_a_3813_);
v___y_3764_ = v___y_3805_;
v___y_3765_ = v___y_3804_;
v___y_3766_ = v___y_3808_;
v___y_3767_ = v___y_3809_;
v___y_3768_ = v___y_3810_;
v___y_3769_ = v___y_3811_;
v_a_3770_ = v___x_3814_;
goto v___jp_3763_;
}
else
{
lean_dec(v___y_3807_);
v___y_3794_ = v___y_3804_;
v___y_3795_ = v___y_3805_;
v___y_3796_ = v___y_3808_;
v___y_3797_ = v___y_3809_;
v___y_3798_ = v___y_3810_;
v___y_3799_ = v___y_3811_;
v___y_3800_ = v___x_3812_;
goto v___jp_3793_;
}
}
v___jp_3815_:
{
uint8_t v___x_3826_; 
v___x_3826_ = l_List_isEmpty___redArg(v___y_3821_);
lean_dec(v___y_3821_);
if (v___x_3826_ == 0)
{
if (v___y_3819_ == 0)
{
v___y_3804_ = v___y_3818_;
v___y_3805_ = v___y_3817_;
v___y_3806_ = v___y_3816_;
v___y_3807_ = v___y_3820_;
v___y_3808_ = v___y_3822_;
v___y_3809_ = v___y_3823_;
v___y_3810_ = v___y_3824_;
v___y_3811_ = v___y_3825_;
goto v___jp_3803_;
}
else
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
lean_dec(v___y_3820_);
lean_dec(v___y_3816_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___x_3827_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3828_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3827_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_3794_ = v___y_3818_;
v___y_3795_ = v___y_3817_;
v___y_3796_ = v___y_3822_;
v___y_3797_ = v___y_3823_;
v___y_3798_ = v___y_3824_;
v___y_3799_ = v___y_3825_;
v___y_3800_ = v___x_3828_;
goto v___jp_3793_;
}
}
else
{
v___y_3804_ = v___y_3818_;
v___y_3805_ = v___y_3817_;
v___y_3806_ = v___y_3816_;
v___y_3807_ = v___y_3820_;
v___y_3808_ = v___y_3822_;
v___y_3809_ = v___y_3823_;
v___y_3810_ = v___y_3824_;
v___y_3811_ = v___y_3825_;
goto v___jp_3803_;
}
}
v___jp_3829_:
{
if (lean_obj_tag(v___y_3838_) == 0)
{
lean_object* v_a_3839_; 
v_a_3839_ = lean_ctor_get(v___y_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref(v___y_3838_);
v___y_3773_ = v___y_3831_;
v___y_3774_ = v___y_3830_;
v___y_3775_ = v___y_3833_;
v___y_3776_ = v___y_3832_;
v___y_3777_ = v___y_3834_;
v___y_3778_ = v___y_3835_;
v___y_3779_ = v___y_3836_;
v___y_3780_ = v___y_3837_;
v_a_3781_ = v_a_3839_;
goto v___jp_3772_;
}
else
{
lean_object* v_a_3840_; 
lean_dec(v___y_3833_);
lean_dec(v___y_3832_);
v_a_3840_ = lean_ctor_get(v___y_3838_, 0);
lean_inc(v_a_3840_);
lean_dec_ref(v___y_3838_);
v___y_3785_ = v___y_3830_;
v___y_3786_ = v___y_3831_;
v___y_3787_ = v___y_3834_;
v___y_3788_ = v___y_3835_;
v___y_3789_ = v___y_3836_;
v___y_3790_ = v___y_3837_;
v_a_3791_ = v_a_3840_;
goto v___jp_3784_;
}
}
v___jp_3841_:
{
if (v___y_3852_ == 0)
{
lean_object* v___x_3853_; 
lean_dec_ref(v___y_3850_);
v___x_3853_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3847_, v_a_3077_, v_a_3079_);
lean_dec_ref(v___y_3847_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_dec_ref(v___x_3853_);
v___y_3773_ = v___y_3843_;
v___y_3774_ = v___y_3842_;
v___y_3775_ = v___y_3845_;
v___y_3776_ = v___y_3844_;
v___y_3777_ = v___y_3846_;
v___y_3778_ = v___y_3848_;
v___y_3779_ = v___y_3849_;
v___y_3780_ = v___y_3851_;
v_a_3781_ = v_snd_3088_;
goto v___jp_3772_;
}
else
{
lean_object* v_a_3854_; 
lean_dec(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec(v_snd_3088_);
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref(v___x_3853_);
v___y_3785_ = v___y_3842_;
v___y_3786_ = v___y_3843_;
v___y_3787_ = v___y_3846_;
v___y_3788_ = v___y_3848_;
v___y_3789_ = v___y_3849_;
v___y_3790_ = v___y_3851_;
v_a_3791_ = v_a_3854_;
goto v___jp_3784_;
}
}
else
{
lean_dec_ref(v___y_3847_);
lean_dec(v_snd_3088_);
v___y_3830_ = v___y_3842_;
v___y_3831_ = v___y_3843_;
v___y_3832_ = v___y_3844_;
v___y_3833_ = v___y_3845_;
v___y_3834_ = v___y_3846_;
v___y_3835_ = v___y_3848_;
v___y_3836_ = v___y_3849_;
v___y_3837_ = v___y_3851_;
v___y_3838_ = v___y_3850_;
goto v___jp_3829_;
}
}
v___jp_3855_:
{
lean_object* v___x_3865_; 
v___x_3865_ = l_Lean_Meta_saveState___redArg(v_a_3077_, v_a_3079_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v___x_3867_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref(v___x_3865_);
lean_inc(v_snd_3088_);
lean_inc(v_trace_3071_);
v___x_3867_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3858_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_dec(v_a_3866_);
lean_dec(v_snd_3088_);
v___y_3830_ = v___y_3857_;
v___y_3831_ = v___y_3856_;
v___y_3832_ = v___y_3860_;
v___y_3833_ = v___y_3859_;
v___y_3834_ = v___y_3861_;
v___y_3835_ = v___y_3862_;
v___y_3836_ = v___y_3863_;
v___y_3837_ = v___y_3864_;
v___y_3838_ = v___x_3867_;
goto v___jp_3829_;
}
else
{
lean_object* v_a_3868_; uint8_t v___x_3869_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
v___x_3869_ = l_Lean_Exception_isInterrupt(v_a_3868_);
if (v___x_3869_ == 0)
{
uint8_t v___x_3870_; 
v___x_3870_ = l_Lean_Exception_isRuntime(v_a_3868_);
v___y_3842_ = v___y_3857_;
v___y_3843_ = v___y_3856_;
v___y_3844_ = v___y_3860_;
v___y_3845_ = v___y_3859_;
v___y_3846_ = v___y_3861_;
v___y_3847_ = v_a_3866_;
v___y_3848_ = v___y_3862_;
v___y_3849_ = v___y_3863_;
v___y_3850_ = v___x_3867_;
v___y_3851_ = v___y_3864_;
v___y_3852_ = v___x_3870_;
goto v___jp_3841_;
}
else
{
lean_dec(v_a_3868_);
v___y_3842_ = v___y_3857_;
v___y_3843_ = v___y_3856_;
v___y_3844_ = v___y_3860_;
v___y_3845_ = v___y_3859_;
v___y_3846_ = v___y_3861_;
v___y_3847_ = v_a_3866_;
v___y_3848_ = v___y_3862_;
v___y_3849_ = v___y_3863_;
v___y_3850_ = v___x_3867_;
v___y_3851_ = v___y_3864_;
v___y_3852_ = v___x_3869_;
goto v___jp_3841_;
}
}
}
else
{
lean_object* v_a_3871_; 
lean_dec(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3871_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3871_);
lean_dec_ref(v___x_3865_);
v___y_3785_ = v___y_3857_;
v___y_3786_ = v___y_3856_;
v___y_3787_ = v___y_3861_;
v___y_3788_ = v___y_3862_;
v___y_3789_ = v___y_3863_;
v___y_3790_ = v___y_3864_;
v_a_3791_ = v_a_3871_;
goto v___jp_3784_;
}
}
v___jp_3872_:
{
uint8_t v_commitIndependentGoals_3883_; lean_object* v___x_3884_; 
v_commitIndependentGoals_3883_ = lean_ctor_get_uint8(v_cfg_3070_, sizeof(void*)*4);
lean_inc(v___y_3877_);
v___x_3884_ = l_List_appendTR___redArg(v_a_3882_, v___y_3877_);
if (v_commitIndependentGoals_3883_ == 0)
{
v___y_3816_ = v___x_3884_;
v___y_3817_ = v___y_3873_;
v___y_3818_ = v___y_3874_;
v___y_3819_ = v___y_3875_;
v___y_3820_ = v___y_3877_;
v___y_3821_ = v___y_3876_;
v___y_3822_ = v___y_3878_;
v___y_3823_ = v___y_3879_;
v___y_3824_ = v___y_3880_;
v___y_3825_ = v___y_3881_;
goto v___jp_3815_;
}
else
{
uint8_t v___x_3885_; 
v___x_3885_ = l_List_isEmpty___redArg(v___y_3877_);
if (v___x_3885_ == 0)
{
v___y_3856_ = v___y_3874_;
v___y_3857_ = v___y_3873_;
v___y_3858_ = v___x_3884_;
v___y_3859_ = v___y_3876_;
v___y_3860_ = v___y_3877_;
v___y_3861_ = v___y_3878_;
v___y_3862_ = v___y_3879_;
v___y_3863_ = v___y_3880_;
v___y_3864_ = v___y_3881_;
goto v___jp_3855_;
}
else
{
if (v___x_3092_ == 0)
{
v___y_3816_ = v___x_3884_;
v___y_3817_ = v___y_3873_;
v___y_3818_ = v___y_3874_;
v___y_3819_ = v___y_3875_;
v___y_3820_ = v___y_3877_;
v___y_3821_ = v___y_3876_;
v___y_3822_ = v___y_3878_;
v___y_3823_ = v___y_3879_;
v___y_3824_ = v___y_3880_;
v___y_3825_ = v___y_3881_;
goto v___jp_3815_;
}
else
{
v___y_3856_ = v___y_3874_;
v___y_3857_ = v___y_3873_;
v___y_3858_ = v___x_3884_;
v___y_3859_ = v___y_3876_;
v___y_3860_ = v___y_3877_;
v___y_3861_ = v___y_3878_;
v___y_3862_ = v___y_3879_;
v___y_3863_ = v___y_3880_;
v___y_3864_ = v___y_3881_;
goto v___jp_3855_;
}
}
}
}
v___jp_3886_:
{
lean_object* v___x_3895_; 
v___x_3895_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_3079_);
if (lean_obj_tag(v___x_3895_) == 0)
{
if (v___y_3889_ == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref(v___x_3895_);
v___x_3897_ = lean_io_mono_nanos_now();
v___x_3898_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3889_, v___x_3092_, v_goals_3074_, v___y_3892_, v_a_3077_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3900_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref(v___x_3898_);
v___x_3900_ = l_List_reverse___redArg(v_a_3899_);
v___y_3734_ = v___y_3888_;
v___y_3735_ = v___y_3887_;
v___y_3736_ = v___y_3889_;
v___y_3737_ = v___x_3897_;
v___y_3738_ = v___y_3891_;
v___y_3739_ = v___y_3890_;
v___y_3740_ = v_a_3896_;
v___y_3741_ = v___y_3893_;
v___y_3742_ = v___y_3894_;
v_a_3743_ = v___x_3900_;
goto v___jp_3733_;
}
else
{
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3901_; 
v_a_3901_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3901_);
lean_dec_ref(v___x_3898_);
v___y_3734_ = v___y_3888_;
v___y_3735_ = v___y_3887_;
v___y_3736_ = v___y_3889_;
v___y_3737_ = v___x_3897_;
v___y_3738_ = v___y_3891_;
v___y_3739_ = v___y_3890_;
v___y_3740_ = v_a_3896_;
v___y_3741_ = v___y_3893_;
v___y_3742_ = v___y_3894_;
v_a_3743_ = v_a_3901_;
goto v___jp_3733_;
}
else
{
lean_object* v_a_3902_; 
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3902_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3902_);
lean_dec_ref(v___x_3898_);
v___y_3648_ = v___y_3887_;
v___y_3649_ = v___y_3888_;
v___y_3650_ = v___x_3897_;
v___y_3651_ = v_a_3896_;
v___y_3652_ = v___y_3893_;
v___y_3653_ = v___y_3894_;
v_a_3654_ = v_a_3902_;
goto v___jp_3647_;
}
}
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_a_3903_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3903_);
lean_dec_ref(v___x_3895_);
v___x_3904_ = lean_io_get_num_heartbeats();
v___x_3905_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3889_, v___x_3092_, v_goals_3074_, v___y_3892_, v_a_3077_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3907_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref(v___x_3905_);
v___x_3907_ = l_List_reverse___redArg(v_a_3906_);
v___y_3873_ = v___y_3887_;
v___y_3874_ = v___y_3888_;
v___y_3875_ = v___y_3889_;
v___y_3876_ = v___y_3891_;
v___y_3877_ = v___y_3890_;
v___y_3878_ = v___x_3904_;
v___y_3879_ = v_a_3903_;
v___y_3880_ = v___y_3893_;
v___y_3881_ = v___y_3894_;
v_a_3882_ = v___x_3907_;
goto v___jp_3872_;
}
else
{
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3908_; 
v_a_3908_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3908_);
lean_dec_ref(v___x_3905_);
v___y_3873_ = v___y_3887_;
v___y_3874_ = v___y_3888_;
v___y_3875_ = v___y_3889_;
v___y_3876_ = v___y_3891_;
v___y_3877_ = v___y_3890_;
v___y_3878_ = v___x_3904_;
v___y_3879_ = v_a_3903_;
v___y_3880_ = v___y_3893_;
v___y_3881_ = v___y_3894_;
v_a_3882_ = v_a_3908_;
goto v___jp_3872_;
}
else
{
lean_object* v_a_3909_; 
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3909_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3909_);
lean_dec_ref(v___x_3905_);
v___y_3785_ = v___y_3887_;
v___y_3786_ = v___y_3888_;
v___y_3787_ = v___x_3904_;
v___y_3788_ = v_a_3903_;
v___y_3789_ = v___y_3893_;
v___y_3790_ = v___y_3894_;
v_a_3791_ = v_a_3909_;
goto v___jp_3784_;
}
}
}
}
else
{
lean_object* v_a_3910_; 
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec(v_snd_3088_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3910_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3910_);
lean_dec_ref(v___x_3895_);
v___y_3597_ = v___y_3888_;
v___y_3598_ = v___y_3894_;
v_a_3599_ = v_a_3910_;
goto v___jp_3596_;
}
}
v___jp_3911_:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3914_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3915_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3914_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
v___y_3602_ = v___y_3912_;
v___y_3603_ = v___y_3913_;
v___y_3604_ = v___x_3915_;
goto v___jp_3601_;
}
v___jp_3916_:
{
uint8_t v___x_3923_; 
v___x_3923_ = l_List_isEmpty___redArg(v___y_3919_);
lean_dec(v___y_3919_);
if (v___x_3923_ == 0)
{
lean_dec(v___y_3920_);
lean_dec(v___y_3918_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___y_3912_ = v___y_3917_;
v___y_3913_ = v___y_3921_;
goto v___jp_3911_;
}
else
{
if (v___y_3922_ == 0)
{
lean_object* v___x_3924_; 
lean_inc(v_trace_3071_);
v___x_3924_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3920_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3926_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref(v___x_3924_);
v___x_3926_ = l_List_appendTR___redArg(v___y_3918_, v_a_3925_);
v___y_3584_ = v___y_3917_;
v___y_3585_ = v___y_3921_;
v_a_3586_ = v___x_3926_;
goto v___jp_3583_;
}
else
{
lean_dec(v___y_3918_);
v___y_3602_ = v___y_3917_;
v___y_3603_ = v___y_3921_;
v___y_3604_ = v___x_3924_;
goto v___jp_3601_;
}
}
else
{
lean_dec(v___y_3920_);
lean_dec(v___y_3918_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v___y_3912_ = v___y_3917_;
v___y_3913_ = v___y_3921_;
goto v___jp_3911_;
}
}
}
v___jp_3927_:
{
if (lean_obj_tag(v___y_3932_) == 0)
{
lean_object* v_a_3933_; 
v_a_3933_ = lean_ctor_get(v___y_3932_, 0);
lean_inc(v_a_3933_);
lean_dec_ref(v___y_3932_);
v___y_3589_ = v___y_3928_;
v___y_3590_ = v___y_3930_;
v___y_3591_ = v___y_3929_;
v___y_3592_ = v___y_3931_;
v_a_3593_ = v_a_3933_;
goto v___jp_3588_;
}
else
{
lean_object* v_a_3934_; 
lean_dec(v___y_3930_);
lean_dec(v___y_3929_);
v_a_3934_ = lean_ctor_get(v___y_3932_, 0);
lean_inc(v_a_3934_);
lean_dec_ref(v___y_3932_);
v___y_3597_ = v___y_3928_;
v___y_3598_ = v___y_3931_;
v_a_3599_ = v_a_3934_;
goto v___jp_3596_;
}
}
v___jp_3935_:
{
if (v___y_3942_ == 0)
{
lean_object* v___x_3943_; 
lean_dec_ref(v___y_3940_);
v___x_3943_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3939_, v_a_3077_, v_a_3079_);
lean_dec_ref(v___y_3939_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_dec_ref(v___x_3943_);
v___y_3589_ = v___y_3936_;
v___y_3590_ = v___y_3938_;
v___y_3591_ = v___y_3937_;
v___y_3592_ = v___y_3941_;
v_a_3593_ = v_snd_3088_;
goto v___jp_3588_;
}
else
{
lean_object* v_a_3944_; 
lean_dec(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec(v_snd_3088_);
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref(v___x_3943_);
v___y_3597_ = v___y_3936_;
v___y_3598_ = v___y_3941_;
v_a_3599_ = v_a_3944_;
goto v___jp_3596_;
}
}
else
{
lean_dec_ref(v___y_3939_);
lean_dec(v_snd_3088_);
v___y_3928_ = v___y_3936_;
v___y_3929_ = v___y_3937_;
v___y_3930_ = v___y_3938_;
v___y_3931_ = v___y_3941_;
v___y_3932_ = v___y_3940_;
goto v___jp_3927_;
}
}
v___jp_3945_:
{
lean_object* v___x_3951_; 
v___x_3951_ = l_Lean_Meta_saveState___redArg(v_a_3077_, v_a_3079_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3953_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref(v___x_3951_);
lean_inc(v_snd_3088_);
lean_inc(v_trace_3071_);
v___x_3953_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v___y_3949_, v_snd_3088_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_dec(v_a_3952_);
lean_dec(v_snd_3088_);
v___y_3928_ = v___y_3946_;
v___y_3929_ = v___y_3948_;
v___y_3930_ = v___y_3947_;
v___y_3931_ = v___y_3950_;
v___y_3932_ = v___x_3953_;
goto v___jp_3927_;
}
else
{
lean_object* v_a_3954_; uint8_t v___x_3955_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
v___x_3955_ = l_Lean_Exception_isInterrupt(v_a_3954_);
if (v___x_3955_ == 0)
{
uint8_t v___x_3956_; 
v___x_3956_ = l_Lean_Exception_isRuntime(v_a_3954_);
v___y_3936_ = v___y_3946_;
v___y_3937_ = v___y_3948_;
v___y_3938_ = v___y_3947_;
v___y_3939_ = v_a_3952_;
v___y_3940_ = v___x_3953_;
v___y_3941_ = v___y_3950_;
v___y_3942_ = v___x_3956_;
goto v___jp_3935_;
}
else
{
lean_dec(v_a_3954_);
v___y_3936_ = v___y_3946_;
v___y_3937_ = v___y_3948_;
v___y_3938_ = v___y_3947_;
v___y_3939_ = v_a_3952_;
v___y_3940_ = v___x_3953_;
v___y_3941_ = v___y_3950_;
v___y_3942_ = v___x_3955_;
goto v___jp_3935_;
}
}
}
else
{
lean_object* v_a_3957_; 
lean_dec(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3957_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3957_);
lean_dec_ref(v___x_3951_);
v___y_3597_ = v___y_3946_;
v___y_3598_ = v___y_3950_;
v_a_3599_ = v_a_3957_;
goto v___jp_3596_;
}
}
v___jp_3958_:
{
uint8_t v_commitIndependentGoals_3965_; lean_object* v___x_3966_; 
v_commitIndependentGoals_3965_ = lean_ctor_get_uint8(v_cfg_3070_, sizeof(void*)*4);
lean_inc(v___y_3961_);
v___x_3966_ = l_List_appendTR___redArg(v_a_3964_, v___y_3961_);
if (v_commitIndependentGoals_3965_ == 0)
{
v___y_3917_ = v___y_3959_;
v___y_3918_ = v___y_3961_;
v___y_3919_ = v___y_3960_;
v___y_3920_ = v___x_3966_;
v___y_3921_ = v___y_3962_;
v___y_3922_ = v___y_3963_;
goto v___jp_3916_;
}
else
{
uint8_t v___x_3967_; 
v___x_3967_ = l_List_isEmpty___redArg(v___y_3961_);
if (v___x_3967_ == 0)
{
v___y_3946_ = v___y_3959_;
v___y_3947_ = v___y_3960_;
v___y_3948_ = v___y_3961_;
v___y_3949_ = v___x_3966_;
v___y_3950_ = v___y_3962_;
goto v___jp_3945_;
}
else
{
if (v___y_3963_ == 0)
{
v___y_3917_ = v___y_3959_;
v___y_3918_ = v___y_3961_;
v___y_3919_ = v___y_3960_;
v___y_3920_ = v___x_3966_;
v___y_3921_ = v___y_3962_;
v___y_3922_ = v___y_3963_;
goto v___jp_3916_;
}
else
{
v___y_3946_ = v___y_3959_;
v___y_3947_ = v___y_3960_;
v___y_3948_ = v___y_3961_;
v___y_3949_ = v___x_3966_;
v___y_3950_ = v___y_3962_;
goto v___jp_3945_;
}
}
}
}
v___jp_3968_:
{
lean_object* v___x_3969_; 
v___x_3969_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_3079_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref(v___x_3969_);
v___x_3971_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3972_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_3093_, v___x_3971_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = lean_io_mono_nanos_now();
v___x_3974_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3087_, v___f_3095_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v_fst_3976_; lean_object* v_snd_3977_; lean_object* v___x_3978_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3975_);
lean_dec_ref(v___x_3974_);
v_fst_3976_ = lean_ctor_get(v_a_3975_, 0);
lean_inc(v_fst_3976_);
v_snd_3977_ = lean_ctor_get(v_a_3975_, 1);
lean_inc(v_snd_3977_);
lean_dec(v_a_3975_);
lean_inc(v_trace_3071_);
v___x_3978_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_3071_, v_a_3078_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3980_; lean_object* v___f_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3979_);
lean_dec_ref(v___x_3978_);
v___x_3980_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3977_, v___x_3084_);
lean_inc(v___x_3980_);
lean_inc(v_fst_3976_);
v___f_3981_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3981_, 0, v_fst_3976_);
lean_closure_set(v___f_3981_, 1, v___x_3980_);
v___x_3982_ = lean_box(0);
v___x_3983_ = lean_unbox(v_a_3979_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; uint8_t v___x_3985_; 
v___x_3984_ = l_Lean_trace_profiler;
v___x_3985_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_3093_, v___x_3984_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; 
lean_dec_ref(v___f_3981_);
lean_dec(v_a_3979_);
v___x_3986_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3094_, v___x_3972_, v_goals_3074_, v___x_3982_, v_a_3077_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v_a_3987_; lean_object* v___x_3988_; 
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_3987_);
lean_dec_ref(v___x_3986_);
v___x_3988_ = l_List_reverse___redArg(v_a_3987_);
v___y_3561_ = v_a_3970_;
v___y_3562_ = v_fst_3976_;
v___y_3563_ = v___x_3985_;
v___y_3564_ = v___x_3973_;
v___y_3565_ = v___x_3980_;
v_a_3566_ = v___x_3988_;
goto v___jp_3560_;
}
else
{
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v_a_3989_; 
v_a_3989_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_3989_);
lean_dec_ref(v___x_3986_);
v___y_3561_ = v_a_3970_;
v___y_3562_ = v_fst_3976_;
v___y_3563_ = v___x_3985_;
v___y_3564_ = v___x_3973_;
v___y_3565_ = v___x_3980_;
v_a_3566_ = v_a_3989_;
goto v___jp_3560_;
}
else
{
lean_object* v_a_3990_; 
lean_dec(v___x_3980_);
lean_dec(v_fst_3976_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3990_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_3990_);
lean_dec_ref(v___x_3986_);
v___y_3198_ = v_a_3970_;
v___y_3199_ = v___x_3973_;
v_a_3200_ = v_a_3990_;
goto v___jp_3197_;
}
}
}
else
{
uint8_t v___x_3991_; 
v___x_3991_ = lean_unbox(v_a_3979_);
lean_dec(v_a_3979_);
v___y_3520_ = v_a_3970_;
v___y_3521_ = v_fst_3976_;
v___y_3522_ = v___x_3972_;
v___y_3523_ = v___x_3991_;
v___y_3524_ = v___x_3982_;
v___y_3525_ = v___f_3981_;
v___y_3526_ = v___x_3973_;
v___y_3527_ = v___x_3980_;
goto v___jp_3519_;
}
}
else
{
uint8_t v___x_3992_; 
v___x_3992_ = lean_unbox(v_a_3979_);
lean_dec(v_a_3979_);
v___y_3520_ = v_a_3970_;
v___y_3521_ = v_fst_3976_;
v___y_3522_ = v___x_3972_;
v___y_3523_ = v___x_3992_;
v___y_3524_ = v___x_3982_;
v___y_3525_ = v___f_3981_;
v___y_3526_ = v___x_3973_;
v___y_3527_ = v___x_3980_;
goto v___jp_3519_;
}
}
else
{
lean_object* v_a_3993_; 
lean_dec(v_snd_3977_);
lean_dec(v_fst_3976_);
lean_dec(v_snd_3088_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3993_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3993_);
lean_dec_ref(v___x_3978_);
v___y_3198_ = v_a_3970_;
v___y_3199_ = v___x_3973_;
v_a_3200_ = v_a_3993_;
goto v___jp_3197_;
}
}
else
{
lean_object* v_a_3994_; 
lean_dec(v_snd_3088_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_3994_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3994_);
lean_dec_ref(v___x_3974_);
v___y_3198_ = v_a_3970_;
v___y_3199_ = v___x_3973_;
v_a_3200_ = v_a_3994_;
goto v___jp_3197_;
}
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_del_object(v___x_3090_);
v___x_3995_ = lean_io_get_num_heartbeats();
v___x_3996_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3087_, v___f_3095_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v_fst_3998_; lean_object* v_snd_3999_; lean_object* v___x_4000_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref(v___x_3996_);
v_fst_3998_ = lean_ctor_get(v_a_3997_, 0);
lean_inc(v_fst_3998_);
v_snd_3999_ = lean_ctor_get(v_a_3997_, 1);
lean_inc(v_snd_3999_);
lean_dec(v_a_3997_);
lean_inc(v_trace_3071_);
v___x_4000_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_3071_, v_a_3078_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4002_; lean_object* v___f_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v___x_4000_);
v___x_4002_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3999_, v___x_3084_);
lean_inc(v___x_4002_);
lean_inc(v_fst_3998_);
v___f_4003_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_4003_, 0, v_fst_3998_);
lean_closure_set(v___f_4003_, 1, v___x_4002_);
v___x_4004_ = lean_box(0);
v___x_4005_ = lean_unbox(v_a_4001_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4006_; uint8_t v___x_4007_; 
v___x_4006_ = l_Lean_trace_profiler;
v___x_4007_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_3093_, v___x_4006_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4008_; 
lean_dec_ref(v___f_4003_);
lean_dec(v_a_4001_);
v___x_4008_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3972_, v___x_3092_, v_goals_3074_, v___x_4004_, v_a_3077_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref(v___x_4008_);
v___x_4010_ = l_List_reverse___redArg(v_a_4009_);
v___y_3959_ = v_a_3970_;
v___y_3960_ = v_fst_3998_;
v___y_3961_ = v___x_4002_;
v___y_3962_ = v___x_3995_;
v___y_3963_ = v___x_4007_;
v_a_3964_ = v___x_4010_;
goto v___jp_3958_;
}
else
{
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4011_; 
v_a_4011_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4011_);
lean_dec_ref(v___x_4008_);
v___y_3959_ = v_a_3970_;
v___y_3960_ = v_fst_3998_;
v___y_3961_ = v___x_4002_;
v___y_3962_ = v___x_3995_;
v___y_3963_ = v___x_4007_;
v_a_3964_ = v_a_4011_;
goto v___jp_3958_;
}
else
{
lean_object* v_a_4012_; 
lean_dec(v___x_4002_);
lean_dec(v_fst_3998_);
lean_dec(v_snd_3088_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_4012_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4012_);
lean_dec_ref(v___x_4008_);
v___y_3597_ = v_a_3970_;
v___y_3598_ = v___x_3995_;
v_a_3599_ = v_a_4012_;
goto v___jp_3596_;
}
}
}
else
{
uint8_t v___x_4013_; 
v___x_4013_ = lean_unbox(v_a_4001_);
lean_dec(v_a_4001_);
v___y_3887_ = v___x_4013_;
v___y_3888_ = v_a_3970_;
v___y_3889_ = v___x_3972_;
v___y_3890_ = v___x_4002_;
v___y_3891_ = v_fst_3998_;
v___y_3892_ = v___x_4004_;
v___y_3893_ = v___f_4003_;
v___y_3894_ = v___x_3995_;
goto v___jp_3886_;
}
}
else
{
uint8_t v___x_4014_; 
v___x_4014_ = lean_unbox(v_a_4001_);
lean_dec(v_a_4001_);
v___y_3887_ = v___x_4014_;
v___y_3888_ = v_a_3970_;
v___y_3889_ = v___x_3972_;
v___y_3890_ = v___x_4002_;
v___y_3891_ = v_fst_3998_;
v___y_3892_ = v___x_4004_;
v___y_3893_ = v___f_4003_;
v___y_3894_ = v___x_3995_;
goto v___jp_3886_;
}
}
else
{
lean_object* v_a_4015_; 
lean_dec(v_snd_3999_);
lean_dec(v_fst_3998_);
lean_dec(v_snd_3088_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_4015_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4015_);
lean_dec_ref(v___x_4000_);
v___y_3597_ = v_a_3970_;
v___y_3598_ = v___x_3995_;
v_a_3599_ = v_a_4015_;
goto v___jp_3596_;
}
}
else
{
lean_object* v_a_4016_; 
lean_dec(v_snd_3088_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec_ref(v_cfg_3070_);
v_a_4016_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_4016_);
lean_dec_ref(v___x_3996_);
v___y_3597_ = v_a_3970_;
v___y_3598_ = v___x_3995_;
v_a_3599_ = v_a_4016_;
goto v___jp_3596_;
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec_ref(v___f_3177_);
lean_dec(v_a_3176_);
lean_dec_ref(v___f_3095_);
lean_del_object(v___x_3090_);
lean_dec(v_snd_3088_);
lean_dec(v_fst_3087_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
v_a_4017_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_3969_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_3969_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_dec_ref(v___f_3095_);
lean_del_object(v___x_3090_);
lean_dec(v_snd_3088_);
lean_dec(v_fst_3087_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
v_a_4319_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_3175_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_3175_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
}
else
{
lean_object* v_maxDepth_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
lean_del_object(v___x_3090_);
lean_dec(v_snd_3088_);
lean_dec(v_fst_3087_);
lean_dec(v_goals_3074_);
v_maxDepth_4327_ = lean_ctor_get(v_cfg_3070_, 0);
lean_inc(v_maxDepth_4327_);
v___x_4328_ = lean_box(0);
v___x_4329_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_3070_, v_trace_3071_, v_next_3072_, v_orig_3073_, v_maxDepth_4327_, v_remaining_3075_, v___x_4328_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_4329_;
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec(v_remaining_3075_);
lean_dec(v_goals_3074_);
lean_dec(v_orig_3073_);
lean_dec_ref(v_next_3072_);
lean_dec(v_trace_3071_);
lean_dec_ref(v_cfg_3070_);
v_a_4331_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_3085_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_3085_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
v___jp_3081_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3083_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3082_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_);
return v___x_3083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_4339_, lean_object* v_trace_4340_, lean_object* v_next_4341_, lean_object* v_orig_4342_, lean_object* v_goals_4343_, lean_object* v_remaining_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4339_, v_trace_4340_, v_next_4341_, v_orig_4342_, v_goals_4343_, v_remaining_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_);
lean_dec(v_a_4348_);
lean_dec_ref(v_a_4347_);
lean_dec(v_a_4346_);
lean_dec_ref(v_a_4345_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_4351_, lean_object* v_00_u03b2_4352_, lean_object* v_L_4353_, lean_object* v_f_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; 
v___x_4360_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_4353_, v_f_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_4361_, lean_object* v_00_u03b2_4362_, lean_object* v_L_4363_, lean_object* v_f_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_4361_, v_00_u03b2_4362_, v_L_4363_, v_f_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_4371_, lean_object* v_x_4372_, lean_object* v_x_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v___x_4379_; 
v___x_4379_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_4371_, v_x_4372_, v_x_4373_, v___y_4375_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_4380_, lean_object* v_x_4381_, lean_object* v_x_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
uint8_t v___x_53604__boxed_4388_; lean_object* v_res_4389_; 
v___x_53604__boxed_4388_ = lean_unbox(v___x_4380_);
v_res_4389_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_53604__boxed_4388_, v_x_4381_, v_x_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
lean_dec(v___y_4386_);
lean_dec_ref(v___y_4385_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_4390_, uint8_t v___x_4391_, lean_object* v_x_4392_, lean_object* v_x_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v___x_4399_; 
v___x_4399_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_4390_, v___x_4391_, v_x_4392_, v_x_4393_, v___y_4395_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_4400_, lean_object* v___x_4401_, lean_object* v_x_4402_, lean_object* v_x_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
uint8_t v___x_53630__boxed_4409_; uint8_t v___x_53631__boxed_4410_; lean_object* v_res_4411_; 
v___x_53630__boxed_4409_ = lean_unbox(v___x_4400_);
v___x_53631__boxed_4410_ = lean_unbox(v___x_4401_);
v_res_4411_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_53630__boxed_4409_, v___x_53631__boxed_4410_, v_x_4402_, v_x_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_4412_, lean_object* v_00_u03b2_4413_, lean_object* v_f_4414_, lean_object* v_x_4415_, lean_object* v_x_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v___x_4422_; 
v___x_4422_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_4414_, v_x_4415_, v_x_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
return v___x_4422_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4423_, lean_object* v_00_u03b2_4424_, lean_object* v_f_4425_, lean_object* v_x_4426_, lean_object* v_x_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_4423_, v_00_u03b2_4424_, v_f_4425_, v_x_4426_, v_x_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_4434_, lean_object* v_00_u03b2_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_){
_start:
{
lean_object* v___x_4438_; 
v___x_4438_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_4436_, v_a_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_4439_, lean_object* v_00_u03b2_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_){
_start:
{
lean_object* v___x_4443_; 
v___x_4443_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_4441_, v_a_4442_);
return v___x_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_4444_, lean_object* v_g_4445_, lean_object* v_f_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v___x_4452_; 
lean_inc(v___y_4450_);
lean_inc_ref(v___y_4449_);
lean_inc(v___y_4448_);
lean_inc_ref(v___y_4447_);
v___x_4452_ = lean_apply_6(v_next_4444_, v_g_4445_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, lean_box(0));
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; lean_object* v___x_4454_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_a_4453_);
lean_dec_ref(v___x_4452_);
v___x_4454_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_4453_, v_f_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
return v___x_4454_;
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_dec_ref(v_f_4446_);
v_a_4455_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4452_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4452_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_4463_, lean_object* v_g_4464_, lean_object* v_f_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_4463_, v_g_4464_, v_f_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_4472_, lean_object* v_trace_4473_, lean_object* v_next_4474_, lean_object* v_goals_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_resolve_4481_; lean_object* v___x_4482_; 
v_resolve_4481_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_4481_, 0, v_next_4474_);
lean_inc_n(v_goals_4475_, 2);
v___x_4482_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4472_, v_trace_4473_, v_resolve_4481_, v_goals_4475_, v_goals_4475_, v_goals_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_4483_, lean_object* v_trace_4484_, lean_object* v_next_4485_, lean_object* v_goals_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_4483_, v_trace_4484_, v_next_4485_, v_goals_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_);
lean_dec(v_a_4490_);
lean_dec_ref(v_a_4489_);
lean_dec(v_a_4488_);
lean_dec_ref(v_a_4487_);
return v_res_4492_;
}
}
lean_object* runtime_initialize_Lean_Meta_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_IndependentOf(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_IndependentOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Iterator(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_IndependentOf(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_IndependentOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Backtrack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Backtrack(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Backtrack(builtin);
}
#ifdef __cplusplus
}
#endif

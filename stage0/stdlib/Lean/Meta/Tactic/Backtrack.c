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
lean_inc(v___y_262_);
v___x_268_ = lean_apply_5(v_x_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, lean_box(0));
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_a_267_);
lean_dec(v___y_264_);
lean_dec(v___y_262_);
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
lean_dec(v___y_264_);
lean_dec(v___y_262_);
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
lean_dec(v___y_264_);
lean_dec(v___y_262_);
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
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
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
lean_object* v_fileName_501_; lean_object* v_fileMap_502_; lean_object* v_options_503_; lean_object* v_currRecDepth_504_; lean_object* v_maxRecDepth_505_; lean_object* v_ref_506_; lean_object* v_currNamespace_507_; lean_object* v_openDecls_508_; lean_object* v_initHeartbeats_509_; lean_object* v_maxHeartbeats_510_; lean_object* v_quotContext_511_; lean_object* v_currMacroScope_512_; uint8_t v_diag_513_; lean_object* v_cancelTk_x3f_514_; uint8_t v_suppressElabErrors_515_; lean_object* v_inheritedTraceOptions_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_571_; 
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
v_isSharedCheck_571_ = !lean_is_exclusive(v___y_498_);
if (v_isSharedCheck_571_ == 0)
{
v___x_518_ = v___y_498_;
v_isShared_519_ = v_isSharedCheck_571_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_inheritedTraceOptions_516_);
lean_inc(v_cancelTk_x3f_514_);
lean_inc(v_currMacroScope_512_);
lean_inc(v_quotContext_511_);
lean_inc(v_maxHeartbeats_510_);
lean_inc(v_initHeartbeats_509_);
lean_inc(v_openDecls_508_);
lean_inc(v_currNamespace_507_);
lean_inc(v_ref_506_);
lean_inc(v_maxRecDepth_505_);
lean_inc(v_currRecDepth_504_);
lean_inc(v_options_503_);
lean_inc(v_fileMap_502_);
lean_inc(v_fileName_501_);
lean_dec(v___y_498_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_571_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v_traceState_521_; lean_object* v_traces_522_; lean_object* v_ref_523_; lean_object* v___x_525_; 
v___x_520_ = lean_st_ref_get(v___y_499_);
v_traceState_521_ = lean_ctor_get(v___x_520_, 4);
lean_inc_ref(v_traceState_521_);
lean_dec(v___x_520_);
v_traces_522_ = lean_ctor_get(v_traceState_521_, 0);
lean_inc_ref(v_traces_522_);
lean_dec_ref(v_traceState_521_);
v_ref_523_ = l_Lean_replaceRef(v_ref_494_, v_ref_506_);
lean_dec(v_ref_506_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 5, v_ref_523_);
v___x_525_ = v___x_518_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_fileName_501_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_fileMap_502_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_options_503_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_currRecDepth_504_);
lean_ctor_set(v_reuseFailAlloc_570_, 4, v_maxRecDepth_505_);
lean_ctor_set(v_reuseFailAlloc_570_, 5, v_ref_523_);
lean_ctor_set(v_reuseFailAlloc_570_, 6, v_currNamespace_507_);
lean_ctor_set(v_reuseFailAlloc_570_, 7, v_openDecls_508_);
lean_ctor_set(v_reuseFailAlloc_570_, 8, v_initHeartbeats_509_);
lean_ctor_set(v_reuseFailAlloc_570_, 9, v_maxHeartbeats_510_);
lean_ctor_set(v_reuseFailAlloc_570_, 10, v_quotContext_511_);
lean_ctor_set(v_reuseFailAlloc_570_, 11, v_currMacroScope_512_);
lean_ctor_set(v_reuseFailAlloc_570_, 12, v_cancelTk_x3f_514_);
lean_ctor_set(v_reuseFailAlloc_570_, 13, v_inheritedTraceOptions_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, sizeof(void*)*14, v_diag_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, sizeof(void*)*14 + 1, v_suppressElabErrors_515_);
v___x_525_ = v_reuseFailAlloc_570_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; size_t v_sz_527_; size_t v___x_528_; lean_object* v___x_529_; lean_object* v_msg_530_; lean_object* v___x_531_; lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_569_; 
v___x_526_ = l_Lean_PersistentArray_toArray___redArg(v_traces_522_);
lean_dec_ref(v_traces_522_);
v_sz_527_ = lean_array_size(v___x_526_);
v___x_528_ = ((size_t)0ULL);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8(v_sz_527_, v___x_528_, v___x_526_);
v_msg_530_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_530_, 0, v_data_493_);
lean_ctor_set(v_msg_530_, 1, v_msg_495_);
lean_ctor_set(v_msg_530_, 2, v___x_529_);
v___x_531_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_msg_530_, v___y_496_, v___y_497_, v___x_525_, v___y_499_);
lean_dec_ref(v___x_525_);
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_569_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_569_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_569_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v_traceState_537_; lean_object* v_env_538_; lean_object* v_nextMacroScope_539_; lean_object* v_ngen_540_; lean_object* v_auxDeclNGen_541_; lean_object* v_cache_542_; lean_object* v_messages_543_; lean_object* v_infoState_544_; lean_object* v_snapshotTasks_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_568_; 
v___x_536_ = lean_st_ref_take(v___y_499_);
v_traceState_537_ = lean_ctor_get(v___x_536_, 4);
v_env_538_ = lean_ctor_get(v___x_536_, 0);
v_nextMacroScope_539_ = lean_ctor_get(v___x_536_, 1);
v_ngen_540_ = lean_ctor_get(v___x_536_, 2);
v_auxDeclNGen_541_ = lean_ctor_get(v___x_536_, 3);
v_cache_542_ = lean_ctor_get(v___x_536_, 5);
v_messages_543_ = lean_ctor_get(v___x_536_, 6);
v_infoState_544_ = lean_ctor_get(v___x_536_, 7);
v_snapshotTasks_545_ = lean_ctor_get(v___x_536_, 8);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_568_ == 0)
{
v___x_547_ = v___x_536_;
v_isShared_548_ = v_isSharedCheck_568_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_snapshotTasks_545_);
lean_inc(v_infoState_544_);
lean_inc(v_messages_543_);
lean_inc(v_cache_542_);
lean_inc(v_traceState_537_);
lean_inc(v_auxDeclNGen_541_);
lean_inc(v_ngen_540_);
lean_inc(v_nextMacroScope_539_);
lean_inc(v_env_538_);
lean_dec(v___x_536_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_568_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
uint64_t v_tid_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_566_; 
v_tid_549_ = lean_ctor_get_uint64(v_traceState_537_, sizeof(void*)*1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_traceState_537_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v_traceState_537_, 0);
lean_dec(v_unused_567_);
v___x_551_ = v_traceState_537_;
v_isShared_552_ = v_isSharedCheck_566_;
goto v_resetjp_550_;
}
else
{
lean_dec(v_traceState_537_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_566_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v_ref_494_);
lean_ctor_set(v___x_553_, 1, v_a_532_);
v___x_554_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_492_, v___x_553_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_554_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_554_);
lean_ctor_set_uint64(v_reuseFailAlloc_565_, sizeof(void*)*1, v_tid_549_);
v___x_556_ = v_reuseFailAlloc_565_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 4, v___x_556_);
v___x_558_ = v___x_547_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_env_538_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_nextMacroScope_539_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_ngen_540_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_auxDeclNGen_541_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_564_, 5, v_cache_542_);
lean_ctor_set(v_reuseFailAlloc_564_, 6, v_messages_543_);
lean_ctor_set(v_reuseFailAlloc_564_, 7, v_infoState_544_);
lean_ctor_set(v_reuseFailAlloc_564_, 8, v_snapshotTasks_545_);
v___x_558_ = v_reuseFailAlloc_564_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_559_ = lean_st_ref_set(v___y_499_, v___x_558_);
v___x_560_ = lean_box(0);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_560_);
v___x_562_ = v___x_534_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___boxed(lean_object* v_oldTraces_572_, lean_object* v_data_573_, lean_object* v_ref_574_, lean_object* v_msg_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(v_oldTraces_572_, v_data_573_, v_ref_574_, v_msg_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_a_584_ = lean_ctor_get(v_x_582_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v_x_582_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v_x_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 1);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v_a_592_ = lean_ctor_get(v_x_582_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v_x_582_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v_x_582_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set_tag(v___x_594_, 0);
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg___boxed(lean_object* v_x_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_x_600_);
return v_res_602_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__0));
v___x_605_ = l_Lean_stringToMessageData(v___x_604_);
return v___x_605_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2(void){
_start:
{
lean_object* v___x_606_; double v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_float_of_nat(v___x_606_);
return v___x_607_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__3));
v___x_610_ = l_Lean_stringToMessageData(v___x_609_);
return v___x_610_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5(void){
_start:
{
lean_object* v___x_611_; double v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(1000u);
v___x_612_ = lean_float_of_nat(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(lean_object* v_cls_613_, uint8_t v_collapsed_614_, lean_object* v_tag_615_, lean_object* v_opts_616_, uint8_t v_clsEnabled_617_, lean_object* v_oldTraces_618_, lean_object* v_msg_619_, lean_object* v_resStartStop_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_fst_626_; lean_object* v_snd_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_725_; 
v_fst_626_ = lean_ctor_get(v_resStartStop_620_, 0);
v_snd_627_ = lean_ctor_get(v_resStartStop_620_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_resStartStop_620_);
if (v_isSharedCheck_725_ == 0)
{
v___x_629_ = v_resStartStop_620_;
v_isShared_630_ = v_isSharedCheck_725_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_snd_627_);
lean_inc(v_fst_626_);
lean_dec(v_resStartStop_620_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_725_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v_data_634_; lean_object* v_fst_645_; lean_object* v_snd_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_724_; 
v_fst_645_ = lean_ctor_get(v_snd_627_, 0);
v_snd_646_ = lean_ctor_get(v_snd_627_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_snd_627_);
if (v_isSharedCheck_724_ == 0)
{
v___x_648_ = v_snd_627_;
v_isShared_649_ = v_isSharedCheck_724_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_snd_646_);
lean_inc(v_fst_645_);
lean_dec(v_snd_627_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_724_;
goto v_resetjp_647_;
}
v___jp_631_:
{
lean_object* v___x_635_; 
v___x_635_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(v_oldTraces_618_, v_data_634_, v___y_632_, v___y_633_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v___x_636_; 
lean_dec_ref(v___x_635_);
v___x_636_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_fst_626_);
return v___x_636_;
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v_fst_626_);
v_a_637_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_635_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_635_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
v_resetjp_647_:
{
lean_object* v___x_650_; uint8_t v___x_651_; lean_object* v___y_653_; lean_object* v_a_654_; uint8_t v___y_678_; double v___y_709_; 
v___x_650_ = l_Lean_trace_profiler;
v___x_651_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_opts_616_, v___x_650_);
if (v___x_651_ == 0)
{
v___y_678_ = v___x_651_;
goto v___jp_677_;
}
else
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = l_Lean_trace_profiler_useHeartbeats;
v___x_715_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_opts_616_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; double v___x_718_; double v___x_719_; double v___x_720_; 
v___x_716_ = l_Lean_trace_profiler_threshold;
v___x_717_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(v_opts_616_, v___x_716_);
v___x_718_ = lean_float_of_nat(v___x_717_);
v___x_719_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5);
v___x_720_ = lean_float_div(v___x_718_, v___x_719_);
v___y_709_ = v___x_720_;
goto v___jp_708_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; double v___x_723_; 
v___x_721_ = l_Lean_trace_profiler_threshold;
v___x_722_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(v_opts_616_, v___x_721_);
v___x_723_ = lean_float_of_nat(v___x_722_);
v___y_709_ = v___x_723_;
goto v___jp_708_;
}
}
v___jp_652_:
{
uint8_t v_result_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v_result_655_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13(v_fst_626_);
v___x_656_ = l_Lean_TraceResult_toEmoji(v_result_655_);
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
v___x_658_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1);
if (v_isShared_649_ == 0)
{
lean_ctor_set_tag(v___x_648_, 7);
lean_ctor_set(v___x_648_, 1, v___x_658_);
lean_ctor_set(v___x_648_, 0, v___x_657_);
v___x_660_ = v___x_648_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_658_);
v___x_660_ = v_reuseFailAlloc_671_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v_m_662_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 7);
lean_ctor_set(v___x_629_, 1, v_a_654_);
lean_ctor_set(v___x_629_, 0, v___x_660_);
v_m_662_ = v___x_629_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_a_654_);
v_m_662_ = v_reuseFailAlloc_670_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; double v___x_665_; lean_object* v_data_666_; 
v___x_663_ = lean_box(v_result_655_);
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
v___x_665_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2);
lean_inc_ref(v_tag_615_);
lean_inc_ref(v___x_664_);
lean_inc(v_cls_613_);
v_data_666_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_666_, 0, v_cls_613_);
lean_ctor_set(v_data_666_, 1, v___x_664_);
lean_ctor_set(v_data_666_, 2, v_tag_615_);
lean_ctor_set_float(v_data_666_, sizeof(void*)*3, v___x_665_);
lean_ctor_set_float(v_data_666_, sizeof(void*)*3 + 8, v___x_665_);
lean_ctor_set_uint8(v_data_666_, sizeof(void*)*3 + 16, v_collapsed_614_);
if (v___x_651_ == 0)
{
lean_dec_ref(v___x_664_);
lean_dec(v_snd_646_);
lean_dec(v_fst_645_);
lean_dec_ref(v_tag_615_);
lean_dec(v_cls_613_);
v___y_632_ = v___y_653_;
v___y_633_ = v_m_662_;
v_data_634_ = v_data_666_;
goto v___jp_631_;
}
else
{
lean_object* v_data_667_; double v___x_668_; double v___x_669_; 
lean_dec_ref(v_data_666_);
v_data_667_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_667_, 0, v_cls_613_);
lean_ctor_set(v_data_667_, 1, v___x_664_);
lean_ctor_set(v_data_667_, 2, v_tag_615_);
v___x_668_ = lean_unbox_float(v_fst_645_);
lean_dec(v_fst_645_);
lean_ctor_set_float(v_data_667_, sizeof(void*)*3, v___x_668_);
v___x_669_ = lean_unbox_float(v_snd_646_);
lean_dec(v_snd_646_);
lean_ctor_set_float(v_data_667_, sizeof(void*)*3 + 8, v___x_669_);
lean_ctor_set_uint8(v_data_667_, sizeof(void*)*3 + 16, v_collapsed_614_);
v___y_632_ = v___y_653_;
v___y_633_ = v_m_662_;
v_data_634_ = v_data_667_;
goto v___jp_631_;
}
}
}
}
v___jp_672_:
{
lean_object* v_ref_673_; lean_object* v___x_674_; 
v_ref_673_ = lean_ctor_get(v___y_623_, 5);
lean_inc(v___y_624_);
lean_inc_ref(v___y_623_);
lean_inc(v___y_622_);
lean_inc_ref(v___y_621_);
lean_inc(v_fst_626_);
v___x_674_ = lean_apply_6(v_msg_619_, v_fst_626_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, lean_box(0));
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref(v___x_674_);
lean_inc(v_ref_673_);
v___y_653_ = v_ref_673_;
v_a_654_ = v_a_675_;
goto v___jp_652_;
}
else
{
lean_object* v___x_676_; 
lean_dec_ref(v___x_674_);
v___x_676_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4);
lean_inc(v_ref_673_);
v___y_653_ = v_ref_673_;
v_a_654_ = v___x_676_;
goto v___jp_652_;
}
}
v___jp_677_:
{
if (v_clsEnabled_617_ == 0)
{
if (v___y_678_ == 0)
{
lean_object* v___x_679_; lean_object* v_traceState_680_; lean_object* v_env_681_; lean_object* v_nextMacroScope_682_; lean_object* v_ngen_683_; lean_object* v_auxDeclNGen_684_; lean_object* v_cache_685_; lean_object* v_messages_686_; lean_object* v_infoState_687_; lean_object* v_snapshotTasks_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_707_; 
lean_del_object(v___x_648_);
lean_dec(v_snd_646_);
lean_dec(v_fst_645_);
lean_del_object(v___x_629_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v_msg_619_);
lean_dec_ref(v_tag_615_);
lean_dec(v_cls_613_);
v___x_679_ = lean_st_ref_take(v___y_624_);
v_traceState_680_ = lean_ctor_get(v___x_679_, 4);
v_env_681_ = lean_ctor_get(v___x_679_, 0);
v_nextMacroScope_682_ = lean_ctor_get(v___x_679_, 1);
v_ngen_683_ = lean_ctor_get(v___x_679_, 2);
v_auxDeclNGen_684_ = lean_ctor_get(v___x_679_, 3);
v_cache_685_ = lean_ctor_get(v___x_679_, 5);
v_messages_686_ = lean_ctor_get(v___x_679_, 6);
v_infoState_687_ = lean_ctor_get(v___x_679_, 7);
v_snapshotTasks_688_ = lean_ctor_get(v___x_679_, 8);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_707_ == 0)
{
v___x_690_ = v___x_679_;
v_isShared_691_ = v_isSharedCheck_707_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_snapshotTasks_688_);
lean_inc(v_infoState_687_);
lean_inc(v_messages_686_);
lean_inc(v_cache_685_);
lean_inc(v_traceState_680_);
lean_inc(v_auxDeclNGen_684_);
lean_inc(v_ngen_683_);
lean_inc(v_nextMacroScope_682_);
lean_inc(v_env_681_);
lean_dec(v___x_679_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_707_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
uint64_t v_tid_692_; lean_object* v_traces_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_706_; 
v_tid_692_ = lean_ctor_get_uint64(v_traceState_680_, sizeof(void*)*1);
v_traces_693_ = lean_ctor_get(v_traceState_680_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v_traceState_680_);
if (v_isSharedCheck_706_ == 0)
{
v___x_695_ = v_traceState_680_;
v_isShared_696_ = v_isSharedCheck_706_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_traces_693_);
lean_dec(v_traceState_680_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_706_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_618_, v_traces_693_);
lean_dec_ref(v_traces_693_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_697_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_697_);
lean_ctor_set_uint64(v_reuseFailAlloc_705_, sizeof(void*)*1, v_tid_692_);
v___x_699_ = v_reuseFailAlloc_705_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 4, v___x_699_);
v___x_701_ = v___x_690_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_env_681_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_nextMacroScope_682_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_ngen_683_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_auxDeclNGen_684_);
lean_ctor_set(v_reuseFailAlloc_704_, 4, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_704_, 5, v_cache_685_);
lean_ctor_set(v_reuseFailAlloc_704_, 6, v_messages_686_);
lean_ctor_set(v_reuseFailAlloc_704_, 7, v_infoState_687_);
lean_ctor_set(v_reuseFailAlloc_704_, 8, v_snapshotTasks_688_);
v___x_701_ = v_reuseFailAlloc_704_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_st_ref_set(v___y_624_, v___x_701_);
lean_dec(v___y_624_);
v___x_703_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_fst_626_);
return v___x_703_;
}
}
}
}
}
else
{
goto v___jp_672_;
}
}
else
{
goto v___jp_672_;
}
}
v___jp_708_:
{
double v___x_710_; double v___x_711_; double v___x_712_; uint8_t v___x_713_; 
v___x_710_ = lean_unbox_float(v_snd_646_);
v___x_711_ = lean_unbox_float(v_fst_645_);
v___x_712_ = lean_float_sub(v___x_710_, v___x_711_);
v___x_713_ = lean_float_decLt(v___y_709_, v___x_712_);
v___y_678_ = v___x_713_;
goto v___jp_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___boxed(lean_object* v_cls_726_, lean_object* v_collapsed_727_, lean_object* v_tag_728_, lean_object* v_opts_729_, lean_object* v_clsEnabled_730_, lean_object* v_oldTraces_731_, lean_object* v_msg_732_, lean_object* v_resStartStop_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
uint8_t v_collapsed_boxed_739_; uint8_t v_clsEnabled_boxed_740_; lean_object* v_res_741_; 
v_collapsed_boxed_739_ = lean_unbox(v_collapsed_727_);
v_clsEnabled_boxed_740_ = lean_unbox(v_clsEnabled_730_);
v_res_741_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(v_cls_726_, v_collapsed_boxed_739_, v_tag_728_, v_opts_729_, v_clsEnabled_boxed_740_, v_oldTraces_731_, v_msg_732_, v_resStartStop_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec_ref(v_opts_729_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_ref_748_; lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_758_; 
v_ref_748_ = lean_ctor_get(v___y_745_, 5);
v___x_749_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_msg_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_758_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_758_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
lean_inc(v_ref_748_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_ref_748_);
lean_ctor_set(v___x_754_, 1, v_a_750_);
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 1);
lean_ctor_set(v___x_752_, 0, v___x_754_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
return v_res_765_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(lean_object* v_keys_766_, lean_object* v_i_767_, lean_object* v_k_768_){
_start:
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = lean_array_get_size(v_keys_766_);
v___x_770_ = lean_nat_dec_lt(v_i_767_, v___x_769_);
if (v___x_770_ == 0)
{
lean_dec(v_i_767_);
return v___x_770_;
}
else
{
lean_object* v_k_x27_771_; uint8_t v___x_772_; 
v_k_x27_771_ = lean_array_fget_borrowed(v_keys_766_, v_i_767_);
v___x_772_ = l_Lean_instBEqMVarId_beq(v_k_768_, v_k_x27_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_add(v_i_767_, v___x_773_);
lean_dec(v_i_767_);
v_i_767_ = v___x_774_;
goto _start;
}
else
{
lean_dec(v_i_767_);
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg___boxed(lean_object* v_keys_776_, lean_object* v_i_777_, lean_object* v_k_778_){
_start:
{
uint8_t v_res_779_; lean_object* v_r_780_; 
v_res_779_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(v_keys_776_, v_i_777_, v_k_778_);
lean_dec(v_k_778_);
lean_dec_ref(v_keys_776_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0(void){
_start:
{
size_t v___x_781_; size_t v___x_782_; size_t v___x_783_; 
v___x_781_ = ((size_t)5ULL);
v___x_782_ = ((size_t)1ULL);
v___x_783_ = lean_usize_shift_left(v___x_782_, v___x_781_);
return v___x_783_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1(void){
_start:
{
size_t v___x_784_; size_t v___x_785_; size_t v___x_786_; 
v___x_784_ = ((size_t)1ULL);
v___x_785_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0);
v___x_786_ = lean_usize_sub(v___x_785_, v___x_784_);
return v___x_786_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(lean_object* v_x_787_, size_t v_x_788_, lean_object* v_x_789_){
_start:
{
if (lean_obj_tag(v_x_787_) == 0)
{
lean_object* v_es_790_; lean_object* v___x_791_; size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; lean_object* v_j_795_; lean_object* v___x_796_; 
v_es_790_ = lean_ctor_get(v_x_787_, 0);
lean_inc_ref(v_es_790_);
lean_dec_ref(v_x_787_);
v___x_791_ = lean_box(2);
v___x_792_ = ((size_t)5ULL);
v___x_793_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1);
v___x_794_ = lean_usize_land(v_x_788_, v___x_793_);
v_j_795_ = lean_usize_to_nat(v___x_794_);
v___x_796_ = lean_array_get(v___x_791_, v_es_790_, v_j_795_);
lean_dec(v_j_795_);
lean_dec_ref(v_es_790_);
switch(lean_obj_tag(v___x_796_))
{
case 0:
{
lean_object* v_key_797_; uint8_t v___x_798_; 
v_key_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_key_797_);
lean_dec_ref(v___x_796_);
v___x_798_ = l_Lean_instBEqMVarId_beq(v_x_789_, v_key_797_);
lean_dec(v_key_797_);
return v___x_798_;
}
case 1:
{
lean_object* v_node_799_; size_t v___x_800_; 
v_node_799_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_node_799_);
lean_dec_ref(v___x_796_);
v___x_800_ = lean_usize_shift_right(v_x_788_, v___x_792_);
v_x_787_ = v_node_799_;
v_x_788_ = v___x_800_;
goto _start;
}
default: 
{
uint8_t v___x_802_; 
v___x_802_ = 0;
return v___x_802_;
}
}
}
else
{
lean_object* v_ks_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_ks_803_ = lean_ctor_get(v_x_787_, 0);
lean_inc_ref(v_ks_803_);
lean_dec_ref(v_x_787_);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(v_ks_803_, v___x_804_, v_x_789_);
lean_dec_ref(v_ks_803_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___boxed(lean_object* v_x_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
size_t v_x_72077__boxed_809_; uint8_t v_res_810_; lean_object* v_r_811_; 
v_x_72077__boxed_809_ = lean_unbox_usize(v_x_807_);
lean_dec(v_x_807_);
v_res_810_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(v_x_806_, v_x_72077__boxed_809_, v_x_808_);
lean_dec(v_x_808_);
v_r_811_ = lean_box(v_res_810_);
return v_r_811_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(lean_object* v_x_812_, lean_object* v_x_813_){
_start:
{
uint64_t v___x_814_; size_t v___x_815_; uint8_t v___x_816_; 
v___x_814_ = l_Lean_instHashableMVarId_hash(v_x_813_);
v___x_815_ = lean_uint64_to_usize(v___x_814_);
v___x_816_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(v_x_812_, v___x_815_, v_x_813_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg___boxed(lean_object* v_x_817_, lean_object* v_x_818_){
_start:
{
uint8_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(v_x_817_, v_x_818_);
lean_dec(v_x_818_);
v_r_820_ = lean_box(v_res_819_);
return v_r_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(lean_object* v_mvarId_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; lean_object* v_mctx_825_; lean_object* v_eAssignment_826_; uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_824_ = lean_st_ref_get(v___y_822_);
v_mctx_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc_ref(v_mctx_825_);
lean_dec(v___x_824_);
v_eAssignment_826_ = lean_ctor_get(v_mctx_825_, 7);
lean_inc_ref(v_eAssignment_826_);
lean_dec_ref(v_mctx_825_);
v___x_827_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(v_eAssignment_826_, v_mvarId_821_);
v___x_828_ = lean_box(v___x_827_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg___boxed(lean_object* v_mvarId_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(v_mvarId_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec(v_mvarId_830_);
return v_res_833_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_836_ = l_Lean_stringToMessageData(v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_head_837_, lean_object* v_x_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_845_, 0, v_head_837_);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_head_848_, lean_object* v_x_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_head_848_, v_x_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v_x_849_);
return v_res_855_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(lean_object* v_e_856_){
_start:
{
if (lean_obj_tag(v_e_856_) == 0)
{
uint8_t v___x_857_; 
v___x_857_ = 2;
return v___x_857_;
}
else
{
uint8_t v___x_858_; 
v___x_858_ = 0;
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4___boxed(lean_object* v_e_859_){
_start:
{
uint8_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(v_e_859_);
lean_dec_ref(v_e_859_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object* v_cls_862_, uint8_t v_collapsed_863_, lean_object* v_tag_864_, lean_object* v_opts_865_, uint8_t v_clsEnabled_866_, lean_object* v_oldTraces_867_, lean_object* v_msg_868_, lean_object* v_resStartStop_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_fst_875_; lean_object* v_snd_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_974_; 
v_fst_875_ = lean_ctor_get(v_resStartStop_869_, 0);
v_snd_876_ = lean_ctor_get(v_resStartStop_869_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_resStartStop_869_);
if (v_isSharedCheck_974_ == 0)
{
v___x_878_ = v_resStartStop_869_;
v_isShared_879_ = v_isSharedCheck_974_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_snd_876_);
lean_inc(v_fst_875_);
lean_dec(v_resStartStop_869_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_974_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v_data_883_; lean_object* v_fst_894_; lean_object* v_snd_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_973_; 
v_fst_894_ = lean_ctor_get(v_snd_876_, 0);
v_snd_895_ = lean_ctor_get(v_snd_876_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v_snd_876_);
if (v_isSharedCheck_973_ == 0)
{
v___x_897_ = v_snd_876_;
v_isShared_898_ = v_isSharedCheck_973_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_snd_895_);
lean_inc(v_fst_894_);
lean_dec(v_snd_876_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_973_;
goto v_resetjp_896_;
}
v___jp_880_:
{
lean_object* v___x_884_; 
v___x_884_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(v_oldTraces_867_, v_data_883_, v___y_881_, v___y_882_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v___x_885_; 
lean_dec_ref(v___x_884_);
v___x_885_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_fst_875_);
return v___x_885_;
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_fst_875_);
v_a_886_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_884_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_884_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
v_resetjp_896_:
{
lean_object* v___x_899_; uint8_t v___x_900_; lean_object* v___y_902_; lean_object* v_a_903_; uint8_t v___y_927_; double v___y_958_; 
v___x_899_ = l_Lean_trace_profiler;
v___x_900_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_opts_865_, v___x_899_);
if (v___x_900_ == 0)
{
v___y_927_ = v___x_900_;
goto v___jp_926_;
}
else
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = l_Lean_trace_profiler_useHeartbeats;
v___x_964_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_opts_865_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; double v___x_967_; double v___x_968_; double v___x_969_; 
v___x_965_ = l_Lean_trace_profiler_threshold;
v___x_966_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(v_opts_865_, v___x_965_);
v___x_967_ = lean_float_of_nat(v___x_966_);
v___x_968_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5);
v___x_969_ = lean_float_div(v___x_967_, v___x_968_);
v___y_958_ = v___x_969_;
goto v___jp_957_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; double v___x_972_; 
v___x_970_ = l_Lean_trace_profiler_threshold;
v___x_971_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(v_opts_865_, v___x_970_);
v___x_972_ = lean_float_of_nat(v___x_971_);
v___y_958_ = v___x_972_;
goto v___jp_957_;
}
}
v___jp_901_:
{
uint8_t v_result_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v_result_904_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(v_fst_875_);
v___x_905_ = l_Lean_TraceResult_toEmoji(v_result_904_);
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
v___x_907_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1);
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 7);
lean_ctor_set(v___x_897_, 1, v___x_907_);
lean_ctor_set(v___x_897_, 0, v___x_906_);
v___x_909_ = v___x_897_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_907_);
v___x_909_ = v_reuseFailAlloc_920_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v_m_911_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set_tag(v___x_878_, 7);
lean_ctor_set(v___x_878_, 1, v_a_903_);
lean_ctor_set(v___x_878_, 0, v___x_909_);
v_m_911_ = v___x_878_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_a_903_);
v_m_911_ = v_reuseFailAlloc_919_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; lean_object* v___x_913_; double v___x_914_; lean_object* v_data_915_; 
v___x_912_ = lean_box(v_result_904_);
v___x_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
v___x_914_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2);
lean_inc_ref(v_tag_864_);
lean_inc_ref(v___x_913_);
lean_inc(v_cls_862_);
v_data_915_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_915_, 0, v_cls_862_);
lean_ctor_set(v_data_915_, 1, v___x_913_);
lean_ctor_set(v_data_915_, 2, v_tag_864_);
lean_ctor_set_float(v_data_915_, sizeof(void*)*3, v___x_914_);
lean_ctor_set_float(v_data_915_, sizeof(void*)*3 + 8, v___x_914_);
lean_ctor_set_uint8(v_data_915_, sizeof(void*)*3 + 16, v_collapsed_863_);
if (v___x_900_ == 0)
{
lean_dec_ref(v___x_913_);
lean_dec(v_snd_895_);
lean_dec(v_fst_894_);
lean_dec_ref(v_tag_864_);
lean_dec(v_cls_862_);
v___y_881_ = v___y_902_;
v___y_882_ = v_m_911_;
v_data_883_ = v_data_915_;
goto v___jp_880_;
}
else
{
lean_object* v_data_916_; double v___x_917_; double v___x_918_; 
lean_dec_ref(v_data_915_);
v_data_916_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_916_, 0, v_cls_862_);
lean_ctor_set(v_data_916_, 1, v___x_913_);
lean_ctor_set(v_data_916_, 2, v_tag_864_);
v___x_917_ = lean_unbox_float(v_fst_894_);
lean_dec(v_fst_894_);
lean_ctor_set_float(v_data_916_, sizeof(void*)*3, v___x_917_);
v___x_918_ = lean_unbox_float(v_snd_895_);
lean_dec(v_snd_895_);
lean_ctor_set_float(v_data_916_, sizeof(void*)*3 + 8, v___x_918_);
lean_ctor_set_uint8(v_data_916_, sizeof(void*)*3 + 16, v_collapsed_863_);
v___y_881_ = v___y_902_;
v___y_882_ = v_m_911_;
v_data_883_ = v_data_916_;
goto v___jp_880_;
}
}
}
}
v___jp_921_:
{
lean_object* v_ref_922_; lean_object* v___x_923_; 
v_ref_922_ = lean_ctor_get(v___y_872_, 5);
lean_inc(v___y_873_);
lean_inc_ref(v___y_872_);
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
lean_inc(v_fst_875_);
v___x_923_ = lean_apply_6(v_msg_868_, v_fst_875_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, lean_box(0));
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref(v___x_923_);
lean_inc(v_ref_922_);
v___y_902_ = v_ref_922_;
v_a_903_ = v_a_924_;
goto v___jp_901_;
}
else
{
lean_object* v___x_925_; 
lean_dec_ref(v___x_923_);
v___x_925_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4);
lean_inc(v_ref_922_);
v___y_902_ = v_ref_922_;
v_a_903_ = v___x_925_;
goto v___jp_901_;
}
}
v___jp_926_:
{
if (v_clsEnabled_866_ == 0)
{
if (v___y_927_ == 0)
{
lean_object* v___x_928_; lean_object* v_traceState_929_; lean_object* v_env_930_; lean_object* v_nextMacroScope_931_; lean_object* v_ngen_932_; lean_object* v_auxDeclNGen_933_; lean_object* v_cache_934_; lean_object* v_messages_935_; lean_object* v_infoState_936_; lean_object* v_snapshotTasks_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_956_; 
lean_del_object(v___x_897_);
lean_dec(v_snd_895_);
lean_dec(v_fst_894_);
lean_del_object(v___x_878_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec_ref(v_msg_868_);
lean_dec_ref(v_tag_864_);
lean_dec(v_cls_862_);
v___x_928_ = lean_st_ref_take(v___y_873_);
v_traceState_929_ = lean_ctor_get(v___x_928_, 4);
v_env_930_ = lean_ctor_get(v___x_928_, 0);
v_nextMacroScope_931_ = lean_ctor_get(v___x_928_, 1);
v_ngen_932_ = lean_ctor_get(v___x_928_, 2);
v_auxDeclNGen_933_ = lean_ctor_get(v___x_928_, 3);
v_cache_934_ = lean_ctor_get(v___x_928_, 5);
v_messages_935_ = lean_ctor_get(v___x_928_, 6);
v_infoState_936_ = lean_ctor_get(v___x_928_, 7);
v_snapshotTasks_937_ = lean_ctor_get(v___x_928_, 8);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_956_ == 0)
{
v___x_939_ = v___x_928_;
v_isShared_940_ = v_isSharedCheck_956_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_snapshotTasks_937_);
lean_inc(v_infoState_936_);
lean_inc(v_messages_935_);
lean_inc(v_cache_934_);
lean_inc(v_traceState_929_);
lean_inc(v_auxDeclNGen_933_);
lean_inc(v_ngen_932_);
lean_inc(v_nextMacroScope_931_);
lean_inc(v_env_930_);
lean_dec(v___x_928_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_956_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
uint64_t v_tid_941_; lean_object* v_traces_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_955_; 
v_tid_941_ = lean_ctor_get_uint64(v_traceState_929_, sizeof(void*)*1);
v_traces_942_ = lean_ctor_get(v_traceState_929_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v_traceState_929_);
if (v_isSharedCheck_955_ == 0)
{
v___x_944_ = v_traceState_929_;
v_isShared_945_ = v_isSharedCheck_955_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_traces_942_);
lean_dec(v_traceState_929_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_955_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_946_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_867_, v_traces_942_);
lean_dec_ref(v_traces_942_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_946_);
lean_ctor_set_uint64(v_reuseFailAlloc_954_, sizeof(void*)*1, v_tid_941_);
v___x_948_ = v_reuseFailAlloc_954_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 4, v___x_948_);
v___x_950_ = v___x_939_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_env_930_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_nextMacroScope_931_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v_ngen_932_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_auxDeclNGen_933_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_953_, 5, v_cache_934_);
lean_ctor_set(v_reuseFailAlloc_953_, 6, v_messages_935_);
lean_ctor_set(v_reuseFailAlloc_953_, 7, v_infoState_936_);
lean_ctor_set(v_reuseFailAlloc_953_, 8, v_snapshotTasks_937_);
v___x_950_ = v_reuseFailAlloc_953_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_st_ref_set(v___y_873_, v___x_950_);
lean_dec(v___y_873_);
v___x_952_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_fst_875_);
return v___x_952_;
}
}
}
}
}
else
{
goto v___jp_921_;
}
}
else
{
goto v___jp_921_;
}
}
v___jp_957_:
{
double v___x_959_; double v___x_960_; double v___x_961_; uint8_t v___x_962_; 
v___x_959_ = lean_unbox_float(v_snd_895_);
v___x_960_ = lean_unbox_float(v_fst_894_);
v___x_961_ = lean_float_sub(v___x_959_, v___x_960_);
v___x_962_ = lean_float_decLt(v___y_958_, v___x_961_);
v___y_927_ = v___x_962_;
goto v___jp_926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object* v_cls_975_, lean_object* v_collapsed_976_, lean_object* v_tag_977_, lean_object* v_opts_978_, lean_object* v_clsEnabled_979_, lean_object* v_oldTraces_980_, lean_object* v_msg_981_, lean_object* v_resStartStop_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v_collapsed_boxed_988_; uint8_t v_clsEnabled_boxed_989_; lean_object* v_res_990_; 
v_collapsed_boxed_988_ = lean_unbox(v_collapsed_976_);
v_clsEnabled_boxed_989_ = lean_unbox(v_clsEnabled_979_);
v_res_990_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_cls_975_, v_collapsed_boxed_988_, v_tag_977_, v_opts_978_, v_clsEnabled_boxed_989_, v_oldTraces_980_, v_msg_981_, v_resStartStop_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec_ref(v_opts_978_);
return v_res_990_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object* v_head_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1012_; 
v___x_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1001_, 0, v_head_994_);
v___x_1002_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v___x_1001_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1012_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1012_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_a_1003_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1008_);
v___x_1010_ = v___x_1005_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object* v_head_1013_, lean_object* v_x_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(v_head_1013_, v_x_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec_ref(v_x_1014_);
return v_res_1020_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_1021_; double v___x_1022_; 
v___x_1021_ = lean_unsigned_to_nat(1000000000u);
v___x_1022_ = lean_float_of_nat(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* v_tail_1031_, lean_object* v_cfg_1032_, lean_object* v_trace_1033_, lean_object* v_next_1034_, lean_object* v_goals_1035_, lean_object* v_n_1036_, lean_object* v_acc_1037_, lean_object* v_r_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_1031_, v_cfg_1032_, v_trace_1033_, v_next_1034_, v_goals_1035_, v_n_1036_, v_acc_1037_, v_r_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_1045_, lean_object* v_trace_1046_, lean_object* v_next_1047_, lean_object* v_goals_1048_, lean_object* v_n_1049_, lean_object* v_curr_1050_, lean_object* v_acc_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
uint8_t v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; uint8_t v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v_a_1065_; uint8_t v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; uint8_t v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v_a_1082_; uint8_t v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; uint8_t v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; uint8_t v___y_1146_; lean_object* v___y_1147_; uint8_t v___y_1148_; lean_object* v___y_1149_; lean_object* v_a_1150_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; uint8_t v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; uint8_t v___y_1166_; lean_object* v_a_1167_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; uint8_t v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; uint8_t v___y_1176_; lean_object* v_a_1177_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; uint8_t v___y_1183_; lean_object* v___y_1184_; uint8_t v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1191_; lean_object* v___y_1192_; uint8_t v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; uint8_t v___y_1196_; lean_object* v___y_1197_; lean_object* v_a_1198_; lean_object* v___y_1211_; lean_object* v___y_1212_; uint8_t v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; uint8_t v___y_1217_; lean_object* v_a_1218_; lean_object* v___y_1221_; lean_object* v___y_1222_; uint8_t v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; uint8_t v___y_1227_; lean_object* v_a_1228_; lean_object* v___y_1231_; lean_object* v___y_1232_; uint8_t v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; uint8_t v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v_zero_1241_; uint8_t v_isZero_1242_; 
v_zero_1241_ = lean_unsigned_to_nat(0u);
v_isZero_1242_ = lean_nat_dec_eq(v_n_1049_, v_zero_1241_);
if (v_isZero_1242_ == 1)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v_acc_1051_);
lean_dec(v_curr_1050_);
lean_dec(v_n_1049_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
v___x_1243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1244_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1243_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
return v___x_1244_;
}
else
{
lean_object* v_proc_1245_; lean_object* v_suspend_1246_; lean_object* v_discharge_1247_; lean_object* v___f_1248_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; uint8_t v___y_1253_; uint8_t v___y_1254_; lean_object* v___y_1255_; lean_object* v_a_1256_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; uint8_t v___y_1272_; uint8_t v___y_1273_; lean_object* v___y_1274_; lean_object* v_a_1275_; lean_object* v___y_1285_; lean_object* v___y_1286_; uint8_t v___y_1287_; uint8_t v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___f_1332_; uint8_t v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; uint8_t v___y_1337_; lean_object* v___y_1338_; lean_object* v___f_1374_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; uint8_t v___y_1379_; lean_object* v___y_1380_; uint8_t v___y_1381_; lean_object* v___y_1382_; uint8_t v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v_a_1386_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; uint8_t v___y_1399_; uint8_t v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; uint8_t v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v_a_1406_; lean_object* v___y_1419_; lean_object* v___y_1420_; uint8_t v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; uint8_t v___y_1424_; lean_object* v___y_1425_; uint8_t v___y_1426_; lean_object* v___y_1427_; uint8_t v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___f_1470_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; uint8_t v___y_1475_; uint8_t v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; uint8_t v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v_a_1482_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; uint8_t v___y_1498_; uint8_t v___y_1499_; lean_object* v___y_1500_; uint8_t v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v_a_1505_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; uint8_t v___y_1519_; uint8_t v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; uint8_t v___y_1523_; lean_object* v___y_1524_; lean_object* v_a_1525_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; uint8_t v___y_1541_; uint8_t v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; uint8_t v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v_a_1548_; lean_object* v___y_1558_; uint8_t v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; uint8_t v___y_1565_; uint8_t v___y_1566_; lean_object* v___y_1567_; uint8_t v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1610_; lean_object* v___y_1611_; uint8_t v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; uint8_t v___y_1615_; uint8_t v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v_a_1620_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; uint8_t v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; uint8_t v___y_1636_; uint8_t v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v_a_1640_; lean_object* v___y_1653_; lean_object* v___y_1654_; uint8_t v___y_1655_; uint8_t v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; uint8_t v___y_1661_; lean_object* v___y_1662_; lean_object* v_a_1663_; lean_object* v___y_1673_; lean_object* v___y_1674_; uint8_t v___y_1675_; uint8_t v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; uint8_t v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v_a_1683_; lean_object* v___y_1696_; lean_object* v___y_1697_; uint8_t v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; uint8_t v___y_1702_; uint8_t v___y_1703_; lean_object* v___y_1704_; uint8_t v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; uint8_t v___y_1751_; uint8_t v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; uint8_t v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v_a_1758_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; uint8_t v___y_1771_; uint8_t v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; uint8_t v___y_1776_; lean_object* v___y_1777_; lean_object* v_a_1778_; lean_object* v___y_1791_; lean_object* v___y_1792_; uint8_t v___y_1793_; uint8_t v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; uint8_t v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1843_; lean_object* v___y_1844_; uint8_t v___y_1845_; uint8_t v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v_a_1849_; lean_object* v___y_1862_; lean_object* v___y_1863_; uint8_t v___y_1864_; uint8_t v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v_a_1868_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; uint8_t v___y_1881_; uint8_t v___y_1882_; lean_object* v___y_1883_; lean_object* v_a_1884_; lean_object* v___y_1897_; lean_object* v___y_1898_; uint8_t v___y_1899_; uint8_t v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v_a_1903_; lean_object* v___y_1913_; uint8_t v___y_1914_; uint8_t v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v_one_1960_; lean_object* v_n_1961_; lean_object* v___y_1963_; lean_object* v___y_1964_; uint8_t v___y_1965_; uint8_t v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_2009_; lean_object* v___y_2010_; uint8_t v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; uint8_t v___y_2016_; uint8_t v___y_2017_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; uint8_t v___y_2049_; uint8_t v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2095_; lean_object* v___y_2096_; uint8_t v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; uint8_t v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; lean_object* v___y_2106_; uint8_t v___y_2107_; lean_object* v___y_2132_; lean_object* v___y_2133_; uint8_t v___y_2134_; uint8_t v___y_2135_; lean_object* v___y_2136_; uint8_t v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; uint8_t v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2182_; uint8_t v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; uint8_t v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; uint8_t v___y_2192_; lean_object* v___y_2193_; uint8_t v___y_2194_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; uint8_t v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; uint8_t v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; uint8_t v___y_2279_; lean_object* v_a_2297_; lean_object* v___y_2402_; lean_object* v___x_2412_; 
v_proc_1245_ = lean_ctor_get(v_cfg_1045_, 1);
v_suspend_1246_ = lean_ctor_get(v_cfg_1045_, 2);
v_discharge_1247_ = lean_ctor_get(v_cfg_1045_, 3);
v___f_1248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1470_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1960_ = lean_unsigned_to_nat(1u);
v_n_1961_ = lean_nat_sub(v_n_1049_, v_one_1960_);
lean_dec(v_n_1049_);
lean_inc_ref(v_proc_1245_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_curr_1050_);
lean_inc(v_goals_1048_);
v___x_2412_ = lean_apply_7(v_proc_1245_, v_goals_1048_, v_curr_1050_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref(v___x_2412_);
v_a_2297_ = v_a_2413_;
goto v___jp_2296_;
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2486_; 
v_a_2414_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2416_ = v___x_2412_;
v_isShared_2417_ = v_isSharedCheck_2486_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2412_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2486_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___f_2418_; lean_object* v___y_2420_; uint8_t v___y_2421_; uint8_t v___y_2422_; lean_object* v___y_2423_; uint8_t v___y_2460_; uint8_t v___x_2484_; 
lean_inc(v_a_2414_);
v___f_2418_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(v___f_2418_, 0, v_a_2414_);
v___x_2484_ = l_Lean_Exception_isInterrupt(v_a_2414_);
if (v___x_2484_ == 0)
{
uint8_t v___x_2485_; 
lean_inc(v_a_2414_);
v___x_2485_ = l_Lean_Exception_isRuntime(v_a_2414_);
v___y_2460_ = v___x_2485_;
goto v___jp_2459_;
}
else
{
v___y_2460_ = v___x_2484_;
goto v___jp_2459_;
}
v___jp_2419_:
{
lean_object* v___x_2424_; lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2458_; 
v___x_2424_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2458_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2458_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2430_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2420_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
v___x_2431_ = lean_io_mono_nanos_now();
v___x_2432_ = lean_io_mono_nanos_now();
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_a_2414_);
v___x_2434_ = v___x_2427_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2414_);
v___x_2434_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
double v___x_2435_; double v___x_2436_; double v___x_2437_; double v___x_2438_; double v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2435_ = lean_float_of_nat(v___x_2431_);
v___x_2436_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2437_ = lean_float_div(v___x_2435_, v___x_2436_);
v___x_2438_ = lean_float_of_nat(v___x_2432_);
v___x_2439_ = lean_float_div(v___x_2438_, v___x_2436_);
v___x_2440_ = lean_box_float(v___x_2437_);
v___x_2441_ = lean_box_float(v___x_2439_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2434_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2444_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(v_trace_1046_, v___y_2421_, v___y_2423_, v___y_2420_, v___y_2422_, v_a_2425_, v___f_2418_, v___x_2443_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_2420_);
v___y_2402_ = v___x_2444_;
goto v___jp_2401_;
}
}
else
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2446_ = lean_io_get_num_heartbeats();
v___x_2447_ = lean_io_get_num_heartbeats();
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v_a_2414_);
v___x_2449_ = v___x_2427_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2414_);
v___x_2449_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
double v___x_2450_; double v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2450_ = lean_float_of_nat(v___x_2446_);
v___x_2451_ = lean_float_of_nat(v___x_2447_);
v___x_2452_ = lean_box_float(v___x_2450_);
v___x_2453_ = lean_box_float(v___x_2451_);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2449_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2456_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(v_trace_1046_, v___y_2421_, v___y_2423_, v___y_2420_, v___y_2422_, v_a_2425_, v___f_2418_, v___x_2455_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_2420_);
v___y_2402_ = v___x_2456_;
goto v___jp_2401_;
}
}
}
}
v___jp_2459_:
{
if (v___y_2460_ == 0)
{
lean_object* v_options_2461_; uint8_t v_hasTrace_2462_; 
v_options_2461_ = lean_ctor_get(v_a_1054_, 2);
v_hasTrace_2462_ = lean_ctor_get_uint8(v_options_2461_, sizeof(void*)*1);
if (v_hasTrace_2462_ == 0)
{
lean_object* v___x_2464_; 
lean_dec_ref(v___f_2418_);
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_curr_1050_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
if (v_isShared_2417_ == 0)
{
v___x_2464_ = v___x_2416_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2414_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
else
{
lean_object* v___x_2466_; lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2480_; 
lean_del_object(v___x_2416_);
lean_inc(v_trace_1046_);
v___x_2466_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2480_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2480_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
v___x_2472_ = lean_unbox(v_a_2467_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2473_ = l_Lean_trace_profiler;
v___x_2474_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_2461_, v___x_2473_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2476_; 
lean_dec(v_a_2467_);
lean_dec_ref(v___f_2418_);
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_curr_1050_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set_tag(v___x_2469_, 1);
lean_ctor_set(v___x_2469_, 0, v_a_2414_);
v___x_2476_ = v___x_2469_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2414_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
else
{
uint8_t v___x_2478_; 
lean_del_object(v___x_2469_);
v___x_2478_ = lean_unbox(v_a_2467_);
lean_dec(v_a_2467_);
lean_inc_ref(v_options_2461_);
v___y_2420_ = v_options_2461_;
v___y_2421_ = v_hasTrace_2462_;
v___y_2422_ = v___x_2478_;
v___y_2423_ = v___x_2471_;
goto v___jp_2419_;
}
}
else
{
uint8_t v___x_2479_; 
lean_del_object(v___x_2469_);
v___x_2479_ = lean_unbox(v_a_2467_);
lean_dec(v_a_2467_);
lean_inc_ref(v_options_2461_);
v___y_2420_ = v_options_2461_;
v___y_2421_ = v_hasTrace_2462_;
v___y_2422_ = v___x_2479_;
v___y_2423_ = v___x_2471_;
goto v___jp_2419_;
}
}
}
}
else
{
lean_object* v___x_2482_; 
lean_dec_ref(v___f_2418_);
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_curr_1050_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
if (v_isShared_2417_ == 0)
{
v___x_2482_ = v___x_2416_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2414_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
v___jp_1249_:
{
lean_object* v___x_1257_; double v___x_1258_; double v___x_1259_; double v___x_1260_; double v___x_1261_; double v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1257_ = lean_io_mono_nanos_now();
v___x_1258_ = lean_float_of_nat(v___y_1252_);
v___x_1259_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1260_ = lean_float_div(v___x_1258_, v___x_1259_);
v___x_1261_ = lean_float_of_nat(v___x_1257_);
v___x_1262_ = lean_float_div(v___x_1261_, v___x_1259_);
v___x_1263_ = lean_box_float(v___x_1260_);
v___x_1264_ = lean_box_float(v___x_1262_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_a_1256_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1253_, v___y_1250_, v___y_1255_, v___y_1254_, v___y_1251_, v___f_1248_, v___x_1266_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1255_);
return v___x_1267_;
}
v___jp_1268_:
{
lean_object* v___x_1276_; double v___x_1277_; double v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1276_ = lean_io_get_num_heartbeats();
v___x_1277_ = lean_float_of_nat(v___y_1271_);
v___x_1278_ = lean_float_of_nat(v___x_1276_);
v___x_1279_ = lean_box_float(v___x_1277_);
v___x_1280_ = lean_box_float(v___x_1278_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_a_1275_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1272_, v___y_1269_, v___y_1274_, v___y_1273_, v___y_1270_, v___f_1248_, v___x_1282_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1274_);
return v___x_1283_;
}
v___jp_1284_:
{
lean_object* v___x_1292_; lean_object* v_a_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1292_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1295_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_1291_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_io_mono_nanos_now();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1297_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1290_, v___y_1289_, v___y_1286_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set_tag(v___x_1300_, 1);
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
v___y_1250_ = v___y_1285_;
v___y_1251_ = v_a_1293_;
v___y_1252_ = v___x_1296_;
v___y_1253_ = v___y_1287_;
v___y_1254_ = v___y_1288_;
v___y_1255_ = v___y_1291_;
v_a_1256_ = v___x_1303_;
goto v___jp_1249_;
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v_a_1306_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1297_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1297_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set_tag(v___x_1308_, 0);
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
v___y_1250_ = v___y_1285_;
v___y_1251_ = v_a_1293_;
v___y_1252_ = v___x_1296_;
v___y_1253_ = v___y_1287_;
v___y_1254_ = v___y_1288_;
v___y_1255_ = v___y_1291_;
v_a_1256_ = v___x_1311_;
goto v___jp_1249_;
}
}
}
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1315_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1290_, v___y_1289_, v___y_1286_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 1);
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
v___y_1269_ = v___y_1285_;
v___y_1270_ = v_a_1293_;
v___y_1271_ = v___x_1314_;
v___y_1272_ = v___y_1287_;
v___y_1273_ = v___y_1288_;
v___y_1274_ = v___y_1291_;
v_a_1275_ = v___x_1321_;
goto v___jp_1268_;
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
v_a_1324_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1315_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1315_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 0);
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
v___y_1269_ = v___y_1285_;
v___y_1270_ = v_a_1293_;
v___y_1271_ = v___x_1314_;
v___y_1272_ = v___y_1287_;
v___y_1273_ = v___y_1288_;
v___y_1274_ = v___y_1291_;
v_a_1275_ = v___x_1329_;
goto v___jp_1268_;
}
}
}
}
}
v___jp_1333_:
{
lean_object* v___x_1339_; lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1373_; 
v___x_1339_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1342_ = v___x_1339_;
v_isShared_1343_ = v_isSharedCheck_1373_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1339_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1373_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1344_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1345_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_1335_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1346_ = lean_io_mono_nanos_now();
v___x_1347_ = lean_io_mono_nanos_now();
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 1);
lean_ctor_set(v___x_1342_, 0, v___y_1338_);
v___x_1349_ = v___x_1342_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___y_1338_);
v___x_1349_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
double v___x_1350_; double v___x_1351_; double v___x_1352_; double v___x_1353_; double v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1350_ = lean_float_of_nat(v___x_1346_);
v___x_1351_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1352_ = lean_float_div(v___x_1350_, v___x_1351_);
v___x_1353_ = lean_float_of_nat(v___x_1347_);
v___x_1354_ = lean_float_div(v___x_1353_, v___x_1351_);
v___x_1355_ = lean_box_float(v___x_1352_);
v___x_1356_ = lean_box_float(v___x_1354_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1349_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1334_, v___y_1336_, v___y_1335_, v___y_1337_, v_a_1340_, v___f_1332_, v___x_1358_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1335_);
return v___x_1359_;
}
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1361_ = lean_io_get_num_heartbeats();
v___x_1362_ = lean_io_get_num_heartbeats();
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 1);
lean_ctor_set(v___x_1342_, 0, v___y_1338_);
v___x_1364_ = v___x_1342_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___y_1338_);
v___x_1364_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
double v___x_1365_; double v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1365_ = lean_float_of_nat(v___x_1361_);
v___x_1366_ = lean_float_of_nat(v___x_1362_);
v___x_1367_ = lean_box_float(v___x_1365_);
v___x_1368_ = lean_box_float(v___x_1366_);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1367_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1364_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1334_, v___y_1336_, v___y_1335_, v___y_1337_, v_a_1340_, v___f_1332_, v___x_1370_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1335_);
return v___x_1371_;
}
}
}
}
v___jp_1375_:
{
lean_object* v___x_1387_; double v___x_1388_; double v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1387_ = lean_io_get_num_heartbeats();
v___x_1388_ = lean_float_of_nat(v___y_1380_);
v___x_1389_ = lean_float_of_nat(v___x_1387_);
v___x_1390_ = lean_box_float(v___x_1388_);
v___x_1391_ = lean_box_float(v___x_1389_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v_a_1386_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1377_);
lean_inc(v_trace_1046_);
v___x_1394_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1381_, v___y_1377_, v___y_1384_, v___y_1379_, v___y_1385_, v___f_1374_, v___x_1393_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1180_ = v___y_1377_;
v___y_1181_ = v___y_1376_;
v___y_1182_ = v___y_1378_;
v___y_1183_ = v___y_1381_;
v___y_1184_ = v___y_1382_;
v___y_1185_ = v___y_1383_;
v___y_1186_ = v___y_1384_;
v___y_1187_ = v___x_1394_;
goto v___jp_1179_;
}
v___jp_1395_:
{
lean_object* v___x_1407_; double v___x_1408_; double v___x_1409_; double v___x_1410_; double v___x_1411_; double v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1407_ = lean_io_mono_nanos_now();
v___x_1408_ = lean_float_of_nat(v___y_1401_);
v___x_1409_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1410_ = lean_float_div(v___x_1408_, v___x_1409_);
v___x_1411_ = lean_float_of_nat(v___x_1407_);
v___x_1412_ = lean_float_div(v___x_1411_, v___x_1409_);
v___x_1413_ = lean_box_float(v___x_1410_);
v___x_1414_ = lean_box_float(v___x_1412_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v_a_1406_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1397_);
lean_inc(v_trace_1046_);
v___x_1417_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1400_, v___y_1397_, v___y_1404_, v___y_1399_, v___y_1405_, v___f_1374_, v___x_1416_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1180_ = v___y_1397_;
v___y_1181_ = v___y_1396_;
v___y_1182_ = v___y_1398_;
v___y_1183_ = v___y_1400_;
v___y_1184_ = v___y_1402_;
v___y_1185_ = v___y_1403_;
v___y_1186_ = v___y_1404_;
v___y_1187_ = v___x_1417_;
goto v___jp_1179_;
}
v___jp_1418_:
{
lean_object* v___x_1431_; 
v___x_1431_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
if (v___y_1421_ == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = lean_io_mono_nanos_now();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1434_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1430_, v___y_1427_, v___y_1425_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set_tag(v___x_1437_, 1);
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
v___y_1396_ = v___y_1419_;
v___y_1397_ = v___y_1420_;
v___y_1398_ = v___y_1423_;
v___y_1399_ = v___y_1424_;
v___y_1400_ = v___y_1426_;
v___y_1401_ = v___x_1433_;
v___y_1402_ = v___y_1422_;
v___y_1403_ = v___y_1428_;
v___y_1404_ = v___y_1429_;
v___y_1405_ = v_a_1432_;
v_a_1406_ = v___x_1440_;
goto v___jp_1395_;
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
v_a_1443_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1434_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1434_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set_tag(v___x_1445_, 0);
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
v___y_1396_ = v___y_1419_;
v___y_1397_ = v___y_1420_;
v___y_1398_ = v___y_1423_;
v___y_1399_ = v___y_1424_;
v___y_1400_ = v___y_1426_;
v___y_1401_ = v___x_1433_;
v___y_1402_ = v___y_1422_;
v___y_1403_ = v___y_1428_;
v___y_1404_ = v___y_1429_;
v___y_1405_ = v_a_1432_;
v_a_1406_ = v___x_1448_;
goto v___jp_1395_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v_a_1451_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1431_);
v___x_1452_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1453_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1430_, v___y_1427_, v___y_1425_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
lean_ctor_set_tag(v___x_1456_, 1);
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
v___y_1376_ = v___y_1419_;
v___y_1377_ = v___y_1420_;
v___y_1378_ = v___y_1423_;
v___y_1379_ = v___y_1424_;
v___y_1380_ = v___x_1452_;
v___y_1381_ = v___y_1426_;
v___y_1382_ = v___y_1422_;
v___y_1383_ = v___y_1428_;
v___y_1384_ = v___y_1429_;
v___y_1385_ = v_a_1451_;
v_a_1386_ = v___x_1459_;
goto v___jp_1375_;
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
v_a_1462_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1453_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1453_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set_tag(v___x_1464_, 0);
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
v___y_1376_ = v___y_1419_;
v___y_1377_ = v___y_1420_;
v___y_1378_ = v___y_1423_;
v___y_1379_ = v___y_1424_;
v___y_1380_ = v___x_1452_;
v___y_1381_ = v___y_1426_;
v___y_1382_ = v___y_1422_;
v___y_1383_ = v___y_1428_;
v___y_1384_ = v___y_1429_;
v___y_1385_ = v_a_1451_;
v_a_1386_ = v___x_1467_;
goto v___jp_1375_;
}
}
}
}
}
v___jp_1471_:
{
lean_object* v___x_1483_; double v___x_1484_; double v___x_1485_; double v___x_1486_; double v___x_1487_; double v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1483_ = lean_io_mono_nanos_now();
v___x_1484_ = lean_float_of_nat(v___y_1477_);
v___x_1485_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1486_ = lean_float_div(v___x_1484_, v___x_1485_);
v___x_1487_ = lean_float_of_nat(v___x_1483_);
v___x_1488_ = lean_float_div(v___x_1487_, v___x_1485_);
v___x_1489_ = lean_box_float(v___x_1486_);
v___x_1490_ = lean_box_float(v___x_1488_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_a_1482_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1473_);
lean_inc(v_trace_1046_);
v___x_1493_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1476_, v___y_1473_, v___y_1480_, v___y_1475_, v___y_1481_, v___f_1470_, v___x_1492_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1180_ = v___y_1473_;
v___y_1181_ = v___y_1472_;
v___y_1182_ = v___y_1474_;
v___y_1183_ = v___y_1476_;
v___y_1184_ = v___y_1478_;
v___y_1185_ = v___y_1479_;
v___y_1186_ = v___y_1480_;
v___y_1187_ = v___x_1493_;
goto v___jp_1179_;
}
v___jp_1494_:
{
lean_object* v___x_1506_; double v___x_1507_; double v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1506_ = lean_io_get_num_heartbeats();
v___x_1507_ = lean_float_of_nat(v___y_1504_);
v___x_1508_ = lean_float_of_nat(v___x_1506_);
v___x_1509_ = lean_box_float(v___x_1507_);
v___x_1510_ = lean_box_float(v___x_1508_);
v___x_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v_a_1505_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1496_);
lean_inc(v_trace_1046_);
v___x_1513_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1499_, v___y_1496_, v___y_1502_, v___y_1498_, v___y_1503_, v___f_1470_, v___x_1512_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1180_ = v___y_1496_;
v___y_1181_ = v___y_1495_;
v___y_1182_ = v___y_1497_;
v___y_1183_ = v___y_1499_;
v___y_1184_ = v___y_1500_;
v___y_1185_ = v___y_1501_;
v___y_1186_ = v___y_1502_;
v___y_1187_ = v___x_1513_;
goto v___jp_1179_;
}
v___jp_1514_:
{
lean_object* v___x_1526_; double v___x_1527_; double v___x_1528_; double v___x_1529_; double v___x_1530_; double v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1526_ = lean_io_mono_nanos_now();
v___x_1527_ = lean_float_of_nat(v___y_1516_);
v___x_1528_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1529_ = lean_float_div(v___x_1527_, v___x_1528_);
v___x_1530_ = lean_float_of_nat(v___x_1526_);
v___x_1531_ = lean_float_div(v___x_1530_, v___x_1528_);
v___x_1532_ = lean_box_float(v___x_1529_);
v___x_1533_ = lean_box_float(v___x_1531_);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1525_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1515_);
lean_inc(v_trace_1046_);
v___x_1536_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1520_, v___y_1515_, v___y_1524_, v___y_1519_, v___y_1518_, v___f_1248_, v___x_1535_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1231_ = v___y_1515_;
v___y_1232_ = v___y_1517_;
v___y_1233_ = v___y_1520_;
v___y_1234_ = v___y_1521_;
v___y_1235_ = v___y_1522_;
v___y_1236_ = v___y_1523_;
v___y_1237_ = v___y_1524_;
v___y_1238_ = v___x_1536_;
goto v___jp_1230_;
}
v___jp_1537_:
{
lean_object* v___x_1549_; double v___x_1550_; double v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1549_ = lean_io_get_num_heartbeats();
v___x_1550_ = lean_float_of_nat(v___y_1547_);
v___x_1551_ = lean_float_of_nat(v___x_1549_);
v___x_1552_ = lean_box_float(v___x_1550_);
v___x_1553_ = lean_box_float(v___x_1551_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_a_1548_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1538_);
lean_inc(v_trace_1046_);
v___x_1556_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1542_, v___y_1538_, v___y_1546_, v___y_1541_, v___y_1540_, v___f_1248_, v___x_1555_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1231_ = v___y_1538_;
v___y_1232_ = v___y_1539_;
v___y_1233_ = v___y_1542_;
v___y_1234_ = v___y_1543_;
v___y_1235_ = v___y_1544_;
v___y_1236_ = v___y_1545_;
v___y_1237_ = v___y_1546_;
v___y_1238_ = v___x_1556_;
goto v___jp_1230_;
}
v___jp_1557_:
{
lean_object* v___x_1570_; 
v___x_1570_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
if (v___y_1559_ == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref(v___x_1570_);
v___x_1572_ = lean_io_mono_nanos_now();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1573_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1564_, v___y_1567_, v___y_1562_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
lean_ctor_set_tag(v___x_1576_, 1);
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
v___y_1515_ = v___y_1558_;
v___y_1516_ = v___x_1572_;
v___y_1517_ = v___y_1563_;
v___y_1518_ = v_a_1571_;
v___y_1519_ = v___y_1565_;
v___y_1520_ = v___y_1566_;
v___y_1521_ = v___y_1560_;
v___y_1522_ = v___y_1561_;
v___y_1523_ = v___y_1568_;
v___y_1524_ = v___y_1569_;
v_a_1525_ = v___x_1579_;
goto v___jp_1514_;
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
v_a_1582_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1573_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1573_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 0);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
v___y_1515_ = v___y_1558_;
v___y_1516_ = v___x_1572_;
v___y_1517_ = v___y_1563_;
v___y_1518_ = v_a_1571_;
v___y_1519_ = v___y_1565_;
v___y_1520_ = v___y_1566_;
v___y_1521_ = v___y_1560_;
v___y_1522_ = v___y_1561_;
v___y_1523_ = v___y_1568_;
v___y_1524_ = v___y_1569_;
v_a_1525_ = v___x_1587_;
goto v___jp_1514_;
}
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_a_1590_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1590_);
lean_dec_ref(v___x_1570_);
v___x_1591_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1592_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1564_, v___y_1567_, v___y_1562_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 1);
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
v___y_1538_ = v___y_1558_;
v___y_1539_ = v___y_1563_;
v___y_1540_ = v_a_1590_;
v___y_1541_ = v___y_1565_;
v___y_1542_ = v___y_1566_;
v___y_1543_ = v___y_1560_;
v___y_1544_ = v___y_1561_;
v___y_1545_ = v___y_1568_;
v___y_1546_ = v___y_1569_;
v___y_1547_ = v___x_1591_;
v_a_1548_ = v___x_1598_;
goto v___jp_1537_;
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1592_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1592_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 0);
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
v___y_1538_ = v___y_1558_;
v___y_1539_ = v___y_1563_;
v___y_1540_ = v_a_1590_;
v___y_1541_ = v___y_1565_;
v___y_1542_ = v___y_1566_;
v___y_1543_ = v___y_1560_;
v___y_1544_ = v___y_1561_;
v___y_1545_ = v___y_1568_;
v___y_1546_ = v___y_1569_;
v___y_1547_ = v___x_1591_;
v_a_1548_ = v___x_1606_;
goto v___jp_1537_;
}
}
}
}
}
v___jp_1609_:
{
lean_object* v___x_1621_; double v___x_1622_; double v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1621_ = lean_io_get_num_heartbeats();
v___x_1622_ = lean_float_of_nat(v___y_1619_);
v___x_1623_ = lean_float_of_nat(v___x_1621_);
v___x_1624_ = lean_box_float(v___x_1622_);
v___x_1625_ = lean_box_float(v___x_1623_);
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v_a_1620_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1610_);
lean_inc(v_trace_1046_);
v___x_1628_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1612_, v___y_1610_, v___y_1617_, v___y_1615_, v___y_1618_, v___f_1470_, v___x_1627_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1231_ = v___y_1610_;
v___y_1232_ = v___y_1611_;
v___y_1233_ = v___y_1612_;
v___y_1234_ = v___y_1613_;
v___y_1235_ = v___y_1614_;
v___y_1236_ = v___y_1616_;
v___y_1237_ = v___y_1617_;
v___y_1238_ = v___x_1628_;
goto v___jp_1230_;
}
v___jp_1629_:
{
lean_object* v___x_1641_; double v___x_1642_; double v___x_1643_; double v___x_1644_; double v___x_1645_; double v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1641_ = lean_io_mono_nanos_now();
v___x_1642_ = lean_float_of_nat(v___y_1632_);
v___x_1643_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1644_ = lean_float_div(v___x_1642_, v___x_1643_);
v___x_1645_ = lean_float_of_nat(v___x_1641_);
v___x_1646_ = lean_float_div(v___x_1645_, v___x_1643_);
v___x_1647_ = lean_box_float(v___x_1644_);
v___x_1648_ = lean_box_float(v___x_1646_);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1650_, 0, v_a_1640_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1630_);
lean_inc(v_trace_1046_);
v___x_1651_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1633_, v___y_1630_, v___y_1638_, v___y_1636_, v___y_1639_, v___f_1470_, v___x_1650_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1231_ = v___y_1630_;
v___y_1232_ = v___y_1631_;
v___y_1233_ = v___y_1633_;
v___y_1234_ = v___y_1634_;
v___y_1235_ = v___y_1635_;
v___y_1236_ = v___y_1637_;
v___y_1237_ = v___y_1638_;
v___y_1238_ = v___x_1651_;
goto v___jp_1230_;
}
v___jp_1652_:
{
lean_object* v___x_1664_; double v___x_1665_; double v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1664_ = lean_io_get_num_heartbeats();
v___x_1665_ = lean_float_of_nat(v___y_1657_);
v___x_1666_ = lean_float_of_nat(v___x_1664_);
v___x_1667_ = lean_box_float(v___x_1665_);
v___x_1668_ = lean_box_float(v___x_1666_);
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v_a_1663_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1653_);
lean_inc(v_trace_1046_);
v___x_1671_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1656_, v___y_1653_, v___y_1662_, v___y_1655_, v___y_1659_, v___f_1374_, v___x_1670_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1231_ = v___y_1653_;
v___y_1232_ = v___y_1654_;
v___y_1233_ = v___y_1656_;
v___y_1234_ = v___y_1658_;
v___y_1235_ = v___y_1660_;
v___y_1236_ = v___y_1661_;
v___y_1237_ = v___y_1662_;
v___y_1238_ = v___x_1671_;
goto v___jp_1230_;
}
v___jp_1672_:
{
lean_object* v___x_1684_; double v___x_1685_; double v___x_1686_; double v___x_1687_; double v___x_1688_; double v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1684_ = lean_io_mono_nanos_now();
v___x_1685_ = lean_float_of_nat(v___y_1682_);
v___x_1686_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1687_ = lean_float_div(v___x_1685_, v___x_1686_);
v___x_1688_ = lean_float_of_nat(v___x_1684_);
v___x_1689_ = lean_float_div(v___x_1688_, v___x_1686_);
v___x_1690_ = lean_box_float(v___x_1687_);
v___x_1691_ = lean_box_float(v___x_1689_);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1690_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_a_1683_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1673_);
lean_inc(v_trace_1046_);
v___x_1694_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1676_, v___y_1673_, v___y_1681_, v___y_1675_, v___y_1678_, v___f_1374_, v___x_1693_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1231_ = v___y_1673_;
v___y_1232_ = v___y_1674_;
v___y_1233_ = v___y_1676_;
v___y_1234_ = v___y_1677_;
v___y_1235_ = v___y_1679_;
v___y_1236_ = v___y_1680_;
v___y_1237_ = v___y_1681_;
v___y_1238_ = v___x_1694_;
goto v___jp_1230_;
}
v___jp_1695_:
{
lean_object* v___x_1708_; 
v___x_1708_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
if (v___y_1698_ == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref(v___x_1708_);
v___x_1710_ = lean_io_mono_nanos_now();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1711_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1697_, v___y_1704_, v___y_1707_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 1);
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
v___y_1673_ = v___y_1696_;
v___y_1674_ = v___y_1701_;
v___y_1675_ = v___y_1702_;
v___y_1676_ = v___y_1703_;
v___y_1677_ = v___y_1699_;
v___y_1678_ = v_a_1709_;
v___y_1679_ = v___y_1700_;
v___y_1680_ = v___y_1705_;
v___y_1681_ = v___y_1706_;
v___y_1682_ = v___x_1710_;
v_a_1683_ = v___x_1717_;
goto v___jp_1672_;
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v_a_1720_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1711_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1711_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 0);
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
v___y_1673_ = v___y_1696_;
v___y_1674_ = v___y_1701_;
v___y_1675_ = v___y_1702_;
v___y_1676_ = v___y_1703_;
v___y_1677_ = v___y_1699_;
v___y_1678_ = v_a_1709_;
v___y_1679_ = v___y_1700_;
v___y_1680_ = v___y_1705_;
v___y_1681_ = v___y_1706_;
v___y_1682_ = v___x_1710_;
v_a_1683_ = v___x_1725_;
goto v___jp_1672_;
}
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_a_1728_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1728_);
lean_dec_ref(v___x_1708_);
v___x_1729_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1730_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1697_, v___y_1704_, v___y_1707_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set_tag(v___x_1733_, 1);
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
v___y_1653_ = v___y_1696_;
v___y_1654_ = v___y_1701_;
v___y_1655_ = v___y_1702_;
v___y_1656_ = v___y_1703_;
v___y_1657_ = v___x_1729_;
v___y_1658_ = v___y_1699_;
v___y_1659_ = v_a_1728_;
v___y_1660_ = v___y_1700_;
v___y_1661_ = v___y_1705_;
v___y_1662_ = v___y_1706_;
v_a_1663_ = v___x_1736_;
goto v___jp_1652_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1730_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1730_);
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
v___y_1653_ = v___y_1696_;
v___y_1654_ = v___y_1701_;
v___y_1655_ = v___y_1702_;
v___y_1656_ = v___y_1703_;
v___y_1657_ = v___x_1729_;
v___y_1658_ = v___y_1699_;
v___y_1659_ = v_a_1728_;
v___y_1660_ = v___y_1700_;
v___y_1661_ = v___y_1705_;
v___y_1662_ = v___y_1706_;
v_a_1663_ = v___x_1744_;
goto v___jp_1652_;
}
}
}
}
}
v___jp_1747_:
{
lean_object* v___x_1759_; double v___x_1760_; double v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1759_ = lean_io_get_num_heartbeats();
v___x_1760_ = lean_float_of_nat(v___y_1757_);
v___x_1761_ = lean_float_of_nat(v___x_1759_);
v___x_1762_ = lean_box_float(v___x_1760_);
v___x_1763_ = lean_box_float(v___x_1761_);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1762_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_a_1758_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1749_);
lean_inc(v_trace_1046_);
v___x_1766_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1752_, v___y_1749_, v___y_1756_, v___y_1751_, v___y_1753_, v___f_1248_, v___x_1765_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1180_ = v___y_1749_;
v___y_1181_ = v___y_1748_;
v___y_1182_ = v___y_1750_;
v___y_1183_ = v___y_1752_;
v___y_1184_ = v___y_1754_;
v___y_1185_ = v___y_1755_;
v___y_1186_ = v___y_1756_;
v___y_1187_ = v___x_1766_;
goto v___jp_1179_;
}
v___jp_1767_:
{
lean_object* v___x_1779_; double v___x_1780_; double v___x_1781_; double v___x_1782_; double v___x_1783_; double v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1779_ = lean_io_mono_nanos_now();
v___x_1780_ = lean_float_of_nat(v___y_1773_);
v___x_1781_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1782_ = lean_float_div(v___x_1780_, v___x_1781_);
v___x_1783_ = lean_float_of_nat(v___x_1779_);
v___x_1784_ = lean_float_div(v___x_1783_, v___x_1781_);
v___x_1785_ = lean_box_float(v___x_1782_);
v___x_1786_ = lean_box_float(v___x_1784_);
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_a_1778_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc_ref(v___y_1769_);
lean_inc(v_trace_1046_);
v___x_1789_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1772_, v___y_1769_, v___y_1777_, v___y_1771_, v___y_1774_, v___f_1248_, v___x_1788_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1180_ = v___y_1769_;
v___y_1181_ = v___y_1768_;
v___y_1182_ = v___y_1770_;
v___y_1183_ = v___y_1772_;
v___y_1184_ = v___y_1775_;
v___y_1185_ = v___y_1776_;
v___y_1186_ = v___y_1777_;
v___y_1187_ = v___x_1789_;
goto v___jp_1179_;
}
v___jp_1790_:
{
lean_object* v___x_1803_; 
v___x_1803_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
if (v___y_1793_ == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref(v___x_1803_);
v___x_1805_ = lean_io_mono_nanos_now();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1806_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1795_, v___y_1800_, v___y_1799_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set_tag(v___x_1809_, 1);
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
v___y_1768_ = v___y_1791_;
v___y_1769_ = v___y_1792_;
v___y_1770_ = v___y_1797_;
v___y_1771_ = v___y_1794_;
v___y_1772_ = v___y_1798_;
v___y_1773_ = v___x_1805_;
v___y_1774_ = v_a_1804_;
v___y_1775_ = v___y_1796_;
v___y_1776_ = v___y_1801_;
v___y_1777_ = v___y_1802_;
v_a_1778_ = v___x_1812_;
goto v___jp_1767_;
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
v_a_1815_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1806_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1806_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 0);
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
v___y_1768_ = v___y_1791_;
v___y_1769_ = v___y_1792_;
v___y_1770_ = v___y_1797_;
v___y_1771_ = v___y_1794_;
v___y_1772_ = v___y_1798_;
v___y_1773_ = v___x_1805_;
v___y_1774_ = v_a_1804_;
v___y_1775_ = v___y_1796_;
v___y_1776_ = v___y_1801_;
v___y_1777_ = v___y_1802_;
v_a_1778_ = v___x_1820_;
goto v___jp_1767_;
}
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_a_1823_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1823_);
lean_dec_ref(v___x_1803_);
v___x_1824_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1825_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1795_, v___y_1800_, v___y_1799_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 1);
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
v___y_1748_ = v___y_1791_;
v___y_1749_ = v___y_1792_;
v___y_1750_ = v___y_1797_;
v___y_1751_ = v___y_1794_;
v___y_1752_ = v___y_1798_;
v___y_1753_ = v_a_1823_;
v___y_1754_ = v___y_1796_;
v___y_1755_ = v___y_1801_;
v___y_1756_ = v___y_1802_;
v___y_1757_ = v___x_1824_;
v_a_1758_ = v___x_1831_;
goto v___jp_1747_;
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
v_a_1834_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1825_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1825_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set_tag(v___x_1836_, 0);
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
v___y_1748_ = v___y_1791_;
v___y_1749_ = v___y_1792_;
v___y_1750_ = v___y_1797_;
v___y_1751_ = v___y_1794_;
v___y_1752_ = v___y_1798_;
v___y_1753_ = v_a_1823_;
v___y_1754_ = v___y_1796_;
v___y_1755_ = v___y_1801_;
v___y_1756_ = v___y_1802_;
v___y_1757_ = v___x_1824_;
v_a_1758_ = v___x_1839_;
goto v___jp_1747_;
}
}
}
}
}
v___jp_1842_:
{
lean_object* v___x_1850_; double v___x_1851_; double v___x_1852_; double v___x_1853_; double v___x_1854_; double v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1850_ = lean_io_mono_nanos_now();
v___x_1851_ = lean_float_of_nat(v___y_1848_);
v___x_1852_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1853_ = lean_float_div(v___x_1851_, v___x_1852_);
v___x_1854_ = lean_float_of_nat(v___x_1850_);
v___x_1855_ = lean_float_div(v___x_1854_, v___x_1852_);
v___x_1856_ = lean_box_float(v___x_1853_);
v___x_1857_ = lean_box_float(v___x_1855_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1856_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v_a_1849_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1845_, v___y_1843_, v___y_1847_, v___y_1846_, v___y_1844_, v___f_1470_, v___x_1859_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1847_);
return v___x_1860_;
}
v___jp_1861_:
{
lean_object* v___x_1869_; double v___x_1870_; double v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1869_ = lean_io_get_num_heartbeats();
v___x_1870_ = lean_float_of_nat(v___y_1867_);
v___x_1871_ = lean_float_of_nat(v___x_1869_);
v___x_1872_ = lean_box_float(v___x_1870_);
v___x_1873_ = lean_box_float(v___x_1871_);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v_a_1868_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1864_, v___y_1862_, v___y_1866_, v___y_1865_, v___y_1863_, v___f_1470_, v___x_1875_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1866_);
return v___x_1876_;
}
v___jp_1877_:
{
lean_object* v___x_1885_; double v___x_1886_; double v___x_1887_; double v___x_1888_; double v___x_1889_; double v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1885_ = lean_io_mono_nanos_now();
v___x_1886_ = lean_float_of_nat(v___y_1879_);
v___x_1887_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1888_ = lean_float_div(v___x_1886_, v___x_1887_);
v___x_1889_ = lean_float_of_nat(v___x_1885_);
v___x_1890_ = lean_float_div(v___x_1889_, v___x_1887_);
v___x_1891_ = lean_box_float(v___x_1888_);
v___x_1892_ = lean_box_float(v___x_1890_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_a_1884_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1881_, v___y_1878_, v___y_1883_, v___y_1882_, v___y_1880_, v___f_1374_, v___x_1894_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1883_);
return v___x_1895_;
}
v___jp_1896_:
{
lean_object* v___x_1904_; double v___x_1905_; double v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1904_ = lean_io_get_num_heartbeats();
v___x_1905_ = lean_float_of_nat(v___y_1901_);
v___x_1906_ = lean_float_of_nat(v___x_1904_);
v___x_1907_ = lean_box_float(v___x_1905_);
v___x_1908_ = lean_box_float(v___x_1906_);
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_a_1903_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1899_, v___y_1897_, v___y_1902_, v___y_1900_, v___y_1898_, v___f_1374_, v___x_1910_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1902_);
return v___x_1911_;
}
v___jp_1912_:
{
lean_object* v___x_1920_; lean_object* v_a_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1920_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1920_);
v___x_1922_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1923_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_1919_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = lean_io_mono_nanos_now();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1925_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1918_, v___y_1917_, v___y_1916_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set_tag(v___x_1928_, 1);
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
v___y_1878_ = v___y_1913_;
v___y_1879_ = v___x_1924_;
v___y_1880_ = v_a_1921_;
v___y_1881_ = v___y_1914_;
v___y_1882_ = v___y_1915_;
v___y_1883_ = v___y_1919_;
v_a_1884_ = v___x_1931_;
goto v___jp_1877_;
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_a_1934_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1925_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1925_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 0);
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
v___y_1878_ = v___y_1913_;
v___y_1879_ = v___x_1924_;
v___y_1880_ = v_a_1921_;
v___y_1881_ = v___y_1914_;
v___y_1882_ = v___y_1915_;
v___y_1883_ = v___y_1919_;
v_a_1884_ = v___x_1939_;
goto v___jp_1877_;
}
}
}
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1943_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1918_, v___y_1917_, v___y_1916_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set_tag(v___x_1946_, 1);
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
v___y_1897_ = v___y_1913_;
v___y_1898_ = v_a_1921_;
v___y_1899_ = v___y_1914_;
v___y_1900_ = v___y_1915_;
v___y_1901_ = v___x_1942_;
v___y_1902_ = v___y_1919_;
v_a_1903_ = v___x_1949_;
goto v___jp_1896_;
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_a_1952_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1943_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1943_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 0);
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
v___y_1897_ = v___y_1913_;
v___y_1898_ = v_a_1921_;
v___y_1899_ = v___y_1914_;
v___y_1900_ = v___y_1915_;
v___y_1901_ = v___x_1942_;
v___y_1902_ = v___y_1919_;
v_a_1903_ = v___x_1957_;
goto v___jp_1896_;
}
}
}
}
}
v___jp_1962_:
{
lean_object* v___x_1968_; lean_object* v_a_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1968_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1968_);
v___x_1970_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1971_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_1967_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = lean_io_mono_nanos_now();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1973_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v_n_1961_, v___y_1963_, v_acc_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set_tag(v___x_1976_, 1);
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
v___y_1843_ = v___y_1964_;
v___y_1844_ = v_a_1969_;
v___y_1845_ = v___y_1965_;
v___y_1846_ = v___y_1966_;
v___y_1847_ = v___y_1967_;
v___y_1848_ = v___x_1972_;
v_a_1849_ = v___x_1979_;
goto v___jp_1842_;
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
v_a_1982_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1973_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1973_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set_tag(v___x_1984_, 0);
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
v___y_1843_ = v___y_1964_;
v___y_1844_ = v_a_1969_;
v___y_1845_ = v___y_1965_;
v___y_1846_ = v___y_1966_;
v___y_1847_ = v___y_1967_;
v___y_1848_ = v___x_1972_;
v_a_1849_ = v___x_1987_;
goto v___jp_1842_;
}
}
}
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1991_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v_n_1961_, v___y_1963_, v_acc_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set_tag(v___x_1994_, 1);
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
v___y_1862_ = v___y_1964_;
v___y_1863_ = v_a_1969_;
v___y_1864_ = v___y_1965_;
v___y_1865_ = v___y_1966_;
v___y_1866_ = v___y_1967_;
v___y_1867_ = v___x_1990_;
v_a_1868_ = v___x_1997_;
goto v___jp_1861_;
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
v_a_2000_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1991_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1991_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set_tag(v___x_2002_, 0);
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
v___y_1862_ = v___y_1964_;
v___y_1863_ = v_a_1969_;
v___y_1864_ = v___y_1965_;
v___y_1865_ = v___y_1966_;
v___y_1866_ = v___y_1967_;
v___y_1867_ = v___x_1990_;
v_a_1868_ = v___x_2005_;
goto v___jp_1861_;
}
}
}
}
}
v___jp_2008_:
{
if (v___y_2017_ == 0)
{
lean_object* v___x_2018_; 
lean_dec_ref(v___y_2015_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v___y_2010_);
v___x_2018_ = lean_apply_6(v___y_2012_, v___y_2010_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref(v___x_2018_);
if (lean_obj_tag(v_a_2019_) == 0)
{
lean_object* v___x_2020_; lean_object* v_a_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
lean_inc(v_trace_1046_);
v___x_2020_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref(v___x_2020_);
v___x_2022_ = lean_nat_add(v_n_1961_, v_one_1960_);
lean_dec(v_n_1961_);
v___x_2023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___y_2010_);
lean_ctor_set(v___x_2023_, 1, v_acc_1051_);
v___x_2024_ = lean_unbox(v_a_2021_);
if (v___x_2024_ == 0)
{
if (v___y_2016_ == 0)
{
lean_dec(v_a_2021_);
lean_dec_ref(v___y_2014_);
lean_dec_ref(v___y_2009_);
v_n_1049_ = v___x_2022_;
v_curr_1050_ = v___y_2013_;
v_acc_1051_ = v___x_2023_;
goto _start;
}
else
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_unbox(v_a_2021_);
lean_dec(v_a_2021_);
v___y_1913_ = v___y_2009_;
v___y_1914_ = v___y_2011_;
v___y_1915_ = v___x_2026_;
v___y_1916_ = v___x_2023_;
v___y_1917_ = v___y_2013_;
v___y_1918_ = v___x_2022_;
v___y_1919_ = v___y_2014_;
goto v___jp_1912_;
}
}
else
{
uint8_t v___x_2027_; 
v___x_2027_ = lean_unbox(v_a_2021_);
lean_dec(v_a_2021_);
v___y_1913_ = v___y_2009_;
v___y_1914_ = v___y_2011_;
v___y_1915_ = v___x_2027_;
v___y_1916_ = v___x_2023_;
v___y_1917_ = v___y_2013_;
v___y_1918_ = v___x_2022_;
v___y_1919_ = v___y_2014_;
goto v___jp_1912_;
}
}
else
{
lean_object* v_val_2028_; lean_object* v___x_2029_; lean_object* v_a_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
lean_dec(v___y_2010_);
v_val_2028_ = lean_ctor_get(v_a_2019_, 0);
lean_inc(v_val_2028_);
lean_dec_ref(v_a_2019_);
lean_inc(v_trace_1046_);
v___x_2029_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref(v___x_2029_);
v___x_2031_ = l_List_appendTR___redArg(v_val_2028_, v___y_2013_);
v___x_2032_ = lean_unbox(v_a_2030_);
if (v___x_2032_ == 0)
{
if (v___y_2016_ == 0)
{
lean_dec(v_a_2030_);
lean_dec_ref(v___y_2014_);
lean_dec_ref(v___y_2009_);
v_n_1049_ = v_n_1961_;
v_curr_1050_ = v___x_2031_;
goto _start;
}
else
{
uint8_t v___x_2034_; 
v___x_2034_ = lean_unbox(v_a_2030_);
lean_dec(v_a_2030_);
v___y_1963_ = v___x_2031_;
v___y_1964_ = v___y_2009_;
v___y_1965_ = v___y_2011_;
v___y_1966_ = v___x_2034_;
v___y_1967_ = v___y_2014_;
goto v___jp_1962_;
}
}
else
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_unbox(v_a_2030_);
lean_dec(v_a_2030_);
v___y_1963_ = v___x_2031_;
v___y_1964_ = v___y_2009_;
v___y_1965_ = v___y_2011_;
v___y_1966_ = v___x_2035_;
v___y_1967_ = v___y_2014_;
goto v___jp_1962_;
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
v_a_2036_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2018_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2018_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
return v___y_2015_;
}
}
v___jp_2044_:
{
lean_object* v___x_2055_; 
v___x_2055_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
if (v___y_2049_ == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___x_2055_);
v___x_2057_ = lean_io_mono_nanos_now();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2058_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v_n_1961_, v___y_2047_, v_acc_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set_tag(v___x_2061_, 1);
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
v___y_1472_ = v___y_2046_;
v___y_1473_ = v___y_2045_;
v___y_1474_ = v___y_2048_;
v___y_1475_ = v___y_2050_;
v___y_1476_ = v___y_2051_;
v___y_1477_ = v___x_2057_;
v___y_1478_ = v___y_2052_;
v___y_1479_ = v___y_2054_;
v___y_1480_ = v___y_2053_;
v___y_1481_ = v_a_2056_;
v_a_1482_ = v___x_2064_;
goto v___jp_1471_;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2058_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2058_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 0);
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
v___y_1472_ = v___y_2046_;
v___y_1473_ = v___y_2045_;
v___y_1474_ = v___y_2048_;
v___y_1475_ = v___y_2050_;
v___y_1476_ = v___y_2051_;
v___y_1477_ = v___x_2057_;
v___y_1478_ = v___y_2052_;
v___y_1479_ = v___y_2054_;
v___y_1480_ = v___y_2053_;
v___y_1481_ = v_a_2056_;
v_a_1482_ = v___x_2072_;
goto v___jp_1471_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_a_2075_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2055_);
v___x_2076_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2077_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v_n_1961_, v___y_2047_, v_acc_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 1);
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
v___y_1495_ = v___y_2046_;
v___y_1496_ = v___y_2045_;
v___y_1497_ = v___y_2048_;
v___y_1498_ = v___y_2050_;
v___y_1499_ = v___y_2051_;
v___y_1500_ = v___y_2052_;
v___y_1501_ = v___y_2054_;
v___y_1502_ = v___y_2053_;
v___y_1503_ = v_a_2075_;
v___y_1504_ = v___x_2076_;
v_a_1505_ = v___x_2083_;
goto v___jp_1494_;
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
v_a_2086_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2077_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2077_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set_tag(v___x_2088_, 0);
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
v___y_1495_ = v___y_2046_;
v___y_1496_ = v___y_2045_;
v___y_1497_ = v___y_2048_;
v___y_1498_ = v___y_2050_;
v___y_1499_ = v___y_2051_;
v___y_1500_ = v___y_2052_;
v___y_1501_ = v___y_2054_;
v___y_1502_ = v___y_2053_;
v___y_1503_ = v_a_2075_;
v___y_1504_ = v___x_2076_;
v_a_1505_ = v___x_2091_;
goto v___jp_1494_;
}
}
}
}
}
v___jp_2094_:
{
if (v___y_2107_ == 0)
{
lean_object* v___x_2108_; 
lean_dec_ref(v___y_2102_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v___y_2098_);
v___x_2108_ = lean_apply_6(v___y_2103_, v___y_2098_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref(v___x_2108_);
if (lean_obj_tag(v_a_2109_) == 0)
{
lean_object* v___x_2110_; lean_object* v_a_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
lean_inc(v_trace_1046_);
v___x_2110_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref(v___x_2110_);
v___x_2112_ = lean_nat_add(v_n_1961_, v_one_1960_);
lean_dec(v_n_1961_);
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___y_2098_);
lean_ctor_set(v___x_2113_, 1, v_acc_1051_);
v___x_2114_ = lean_unbox(v_a_2111_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = l_Lean_trace_profiler;
v___x_2116_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2106_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; 
lean_dec(v_a_2111_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2117_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___x_2112_, v___y_2104_, v___x_2113_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1180_ = v___y_2096_;
v___y_1181_ = v___y_2095_;
v___y_1182_ = v___y_2100_;
v___y_1183_ = v___y_2101_;
v___y_1184_ = v___y_2099_;
v___y_1185_ = v___y_2105_;
v___y_1186_ = v___y_2106_;
v___y_1187_ = v___x_2117_;
goto v___jp_1179_;
}
else
{
uint8_t v___x_2118_; 
v___x_2118_ = lean_unbox(v_a_2111_);
lean_dec(v_a_2111_);
v___y_1419_ = v___y_2095_;
v___y_1420_ = v___y_2096_;
v___y_1421_ = v___y_2097_;
v___y_1422_ = v___y_2099_;
v___y_1423_ = v___y_2100_;
v___y_1424_ = v___x_2118_;
v___y_1425_ = v___x_2113_;
v___y_1426_ = v___y_2101_;
v___y_1427_ = v___y_2104_;
v___y_1428_ = v___y_2105_;
v___y_1429_ = v___y_2106_;
v___y_1430_ = v___x_2112_;
goto v___jp_1418_;
}
}
else
{
uint8_t v___x_2119_; 
v___x_2119_ = lean_unbox(v_a_2111_);
lean_dec(v_a_2111_);
v___y_1419_ = v___y_2095_;
v___y_1420_ = v___y_2096_;
v___y_1421_ = v___y_2097_;
v___y_1422_ = v___y_2099_;
v___y_1423_ = v___y_2100_;
v___y_1424_ = v___x_2119_;
v___y_1425_ = v___x_2113_;
v___y_1426_ = v___y_2101_;
v___y_1427_ = v___y_2104_;
v___y_1428_ = v___y_2105_;
v___y_1429_ = v___y_2106_;
v___y_1430_ = v___x_2112_;
goto v___jp_1418_;
}
}
else
{
lean_object* v_val_2120_; lean_object* v___x_2121_; lean_object* v_a_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
lean_dec(v___y_2098_);
v_val_2120_ = lean_ctor_get(v_a_2109_, 0);
lean_inc(v_val_2120_);
lean_dec_ref(v_a_2109_);
lean_inc(v_trace_1046_);
v___x_2121_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref(v___x_2121_);
v___x_2123_ = l_List_appendTR___redArg(v_val_2120_, v___y_2104_);
v___x_2124_ = lean_unbox(v_a_2122_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = l_Lean_trace_profiler;
v___x_2126_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2106_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; 
lean_dec(v_a_2122_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2127_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v_n_1961_, v___x_2123_, v_acc_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1180_ = v___y_2096_;
v___y_1181_ = v___y_2095_;
v___y_1182_ = v___y_2100_;
v___y_1183_ = v___y_2101_;
v___y_1184_ = v___y_2099_;
v___y_1185_ = v___y_2105_;
v___y_1186_ = v___y_2106_;
v___y_1187_ = v___x_2127_;
goto v___jp_1179_;
}
else
{
uint8_t v___x_2128_; 
v___x_2128_ = lean_unbox(v_a_2122_);
lean_dec(v_a_2122_);
v___y_2045_ = v___y_2096_;
v___y_2046_ = v___y_2095_;
v___y_2047_ = v___x_2123_;
v___y_2048_ = v___y_2100_;
v___y_2049_ = v___y_2097_;
v___y_2050_ = v___x_2128_;
v___y_2051_ = v___y_2101_;
v___y_2052_ = v___y_2099_;
v___y_2053_ = v___y_2106_;
v___y_2054_ = v___y_2105_;
goto v___jp_2044_;
}
}
else
{
uint8_t v___x_2129_; 
v___x_2129_ = lean_unbox(v_a_2122_);
lean_dec(v_a_2122_);
v___y_2045_ = v___y_2096_;
v___y_2046_ = v___y_2095_;
v___y_2047_ = v___x_2123_;
v___y_2048_ = v___y_2100_;
v___y_2049_ = v___y_2097_;
v___y_2050_ = v___x_2129_;
v___y_2051_ = v___y_2101_;
v___y_2052_ = v___y_2099_;
v___y_2053_ = v___y_2106_;
v___y_2054_ = v___y_2105_;
goto v___jp_2044_;
}
}
}
else
{
lean_object* v_a_2130_; 
lean_dec(v___y_2104_);
lean_dec(v___y_2098_);
lean_dec(v_n_1961_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec_ref(v_cfg_1045_);
v_a_2130_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2108_);
v___y_1170_ = v___y_2095_;
v___y_1171_ = v___y_2096_;
v___y_1172_ = v___y_2100_;
v___y_1173_ = v___y_2101_;
v___y_1174_ = v___y_2099_;
v___y_1175_ = v___y_2106_;
v___y_1176_ = v___y_2105_;
v_a_1177_ = v_a_2130_;
goto v___jp_1169_;
}
}
else
{
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2098_);
lean_dec(v_n_1961_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec_ref(v_cfg_1045_);
v___y_1170_ = v___y_2095_;
v___y_1171_ = v___y_2096_;
v___y_1172_ = v___y_2100_;
v___y_1173_ = v___y_2101_;
v___y_1174_ = v___y_2099_;
v___y_1175_ = v___y_2106_;
v___y_1176_ = v___y_2105_;
v_a_1177_ = v___y_2102_;
goto v___jp_1169_;
}
}
v___jp_2131_:
{
lean_object* v___x_2142_; 
v___x_2142_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
if (v___y_2134_ == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref(v___x_2142_);
v___x_2144_ = lean_io_mono_nanos_now();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2145_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v_n_1961_, v___y_2141_, v_acc_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set_tag(v___x_2148_, 1);
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
v___y_1630_ = v___y_2132_;
v___y_1631_ = v___y_2133_;
v___y_1632_ = v___x_2144_;
v___y_1633_ = v___y_2135_;
v___y_1634_ = v___y_2136_;
v___y_1635_ = v___y_2138_;
v___y_1636_ = v___y_2137_;
v___y_1637_ = v___y_2140_;
v___y_1638_ = v___y_2139_;
v___y_1639_ = v_a_2143_;
v_a_1640_ = v___x_2151_;
goto v___jp_1629_;
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
v_a_2154_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2145_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2145_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set_tag(v___x_2156_, 0);
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
v___y_1630_ = v___y_2132_;
v___y_1631_ = v___y_2133_;
v___y_1632_ = v___x_2144_;
v___y_1633_ = v___y_2135_;
v___y_1634_ = v___y_2136_;
v___y_1635_ = v___y_2138_;
v___y_1636_ = v___y_2137_;
v___y_1637_ = v___y_2140_;
v___y_1638_ = v___y_2139_;
v___y_1639_ = v_a_2143_;
v_a_1640_ = v___x_2159_;
goto v___jp_1629_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v_a_2162_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2162_);
lean_dec_ref(v___x_2142_);
v___x_2163_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2164_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v_n_1961_, v___y_2141_, v_acc_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2164_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2164_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set_tag(v___x_2167_, 1);
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
v___y_1610_ = v___y_2132_;
v___y_1611_ = v___y_2133_;
v___y_1612_ = v___y_2135_;
v___y_1613_ = v___y_2136_;
v___y_1614_ = v___y_2138_;
v___y_1615_ = v___y_2137_;
v___y_1616_ = v___y_2140_;
v___y_1617_ = v___y_2139_;
v___y_1618_ = v_a_2162_;
v___y_1619_ = v___x_2163_;
v_a_1620_ = v___x_2170_;
goto v___jp_1609_;
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
v_a_2173_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2164_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2164_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
lean_ctor_set_tag(v___x_2175_, 0);
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
v___y_1610_ = v___y_2132_;
v___y_1611_ = v___y_2133_;
v___y_1612_ = v___y_2135_;
v___y_1613_ = v___y_2136_;
v___y_1614_ = v___y_2138_;
v___y_1615_ = v___y_2137_;
v___y_1616_ = v___y_2140_;
v___y_1617_ = v___y_2139_;
v___y_1618_ = v_a_2162_;
v___y_1619_ = v___x_2163_;
v_a_1620_ = v___x_2178_;
goto v___jp_1609_;
}
}
}
}
}
v___jp_2181_:
{
if (v___y_2194_ == 0)
{
lean_object* v___x_2195_; 
lean_dec_ref(v___y_2186_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v___y_2184_);
v___x_2195_ = lean_apply_6(v___y_2190_, v___y_2184_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
if (lean_obj_tag(v_a_2196_) == 0)
{
lean_object* v___x_2197_; lean_object* v_a_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
lean_inc(v_trace_1046_);
v___x_2197_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = lean_nat_add(v_n_1961_, v_one_1960_);
lean_dec(v_n_1961_);
v___x_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___y_2184_);
lean_ctor_set(v___x_2200_, 1, v_acc_1051_);
v___x_2201_ = lean_unbox(v_a_2198_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; uint8_t v___x_2203_; 
v___x_2202_ = l_Lean_trace_profiler;
v___x_2203_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2193_, v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; 
lean_dec(v_a_2198_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2204_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___x_2199_, v___y_2191_, v___x_2200_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1231_ = v___y_2182_;
v___y_1232_ = v___y_2188_;
v___y_1233_ = v___y_2189_;
v___y_1234_ = v___y_2185_;
v___y_1235_ = v___y_2187_;
v___y_1236_ = v___y_2192_;
v___y_1237_ = v___y_2193_;
v___y_1238_ = v___x_2204_;
goto v___jp_1230_;
}
else
{
uint8_t v___x_2205_; 
v___x_2205_ = lean_unbox(v_a_2198_);
lean_dec(v_a_2198_);
v___y_1696_ = v___y_2182_;
v___y_1697_ = v___x_2199_;
v___y_1698_ = v___y_2183_;
v___y_1699_ = v___y_2185_;
v___y_1700_ = v___y_2187_;
v___y_1701_ = v___y_2188_;
v___y_1702_ = v___x_2205_;
v___y_1703_ = v___y_2189_;
v___y_1704_ = v___y_2191_;
v___y_1705_ = v___y_2192_;
v___y_1706_ = v___y_2193_;
v___y_1707_ = v___x_2200_;
goto v___jp_1695_;
}
}
else
{
uint8_t v___x_2206_; 
v___x_2206_ = lean_unbox(v_a_2198_);
lean_dec(v_a_2198_);
v___y_1696_ = v___y_2182_;
v___y_1697_ = v___x_2199_;
v___y_1698_ = v___y_2183_;
v___y_1699_ = v___y_2185_;
v___y_1700_ = v___y_2187_;
v___y_1701_ = v___y_2188_;
v___y_1702_ = v___x_2206_;
v___y_1703_ = v___y_2189_;
v___y_1704_ = v___y_2191_;
v___y_1705_ = v___y_2192_;
v___y_1706_ = v___y_2193_;
v___y_1707_ = v___x_2200_;
goto v___jp_1695_;
}
}
else
{
lean_object* v_val_2207_; lean_object* v___x_2208_; lean_object* v_a_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
lean_dec(v___y_2184_);
v_val_2207_ = lean_ctor_get(v_a_2196_, 0);
lean_inc(v_val_2207_);
lean_dec_ref(v_a_2196_);
lean_inc(v_trace_1046_);
v___x_2208_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref(v___x_2208_);
v___x_2210_ = l_List_appendTR___redArg(v_val_2207_, v___y_2191_);
v___x_2211_ = lean_unbox(v_a_2209_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; uint8_t v___x_2213_; 
v___x_2212_ = l_Lean_trace_profiler;
v___x_2213_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2193_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
lean_dec(v_a_2209_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2214_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v_n_1961_, v___x_2210_, v_acc_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1231_ = v___y_2182_;
v___y_1232_ = v___y_2188_;
v___y_1233_ = v___y_2189_;
v___y_1234_ = v___y_2185_;
v___y_1235_ = v___y_2187_;
v___y_1236_ = v___y_2192_;
v___y_1237_ = v___y_2193_;
v___y_1238_ = v___x_2214_;
goto v___jp_1230_;
}
else
{
uint8_t v___x_2215_; 
v___x_2215_ = lean_unbox(v_a_2209_);
lean_dec(v_a_2209_);
v___y_2132_ = v___y_2182_;
v___y_2133_ = v___y_2188_;
v___y_2134_ = v___y_2183_;
v___y_2135_ = v___y_2189_;
v___y_2136_ = v___y_2185_;
v___y_2137_ = v___x_2215_;
v___y_2138_ = v___y_2187_;
v___y_2139_ = v___y_2193_;
v___y_2140_ = v___y_2192_;
v___y_2141_ = v___x_2210_;
goto v___jp_2131_;
}
}
else
{
uint8_t v___x_2216_; 
v___x_2216_ = lean_unbox(v_a_2209_);
lean_dec(v_a_2209_);
v___y_2132_ = v___y_2182_;
v___y_2133_ = v___y_2188_;
v___y_2134_ = v___y_2183_;
v___y_2135_ = v___y_2189_;
v___y_2136_ = v___y_2185_;
v___y_2137_ = v___x_2216_;
v___y_2138_ = v___y_2187_;
v___y_2139_ = v___y_2193_;
v___y_2140_ = v___y_2192_;
v___y_2141_ = v___x_2210_;
goto v___jp_2131_;
}
}
}
else
{
lean_object* v_a_2217_; 
lean_dec(v___y_2191_);
lean_dec(v___y_2184_);
lean_dec(v_n_1961_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec_ref(v_cfg_1045_);
v_a_2217_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2217_);
lean_dec_ref(v___x_2195_);
v___y_1221_ = v___y_2182_;
v___y_1222_ = v___y_2188_;
v___y_1223_ = v___y_2189_;
v___y_1224_ = v___y_2185_;
v___y_1225_ = v___y_2187_;
v___y_1226_ = v___y_2193_;
v___y_1227_ = v___y_2192_;
v_a_1228_ = v_a_2217_;
goto v___jp_1220_;
}
}
else
{
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2184_);
lean_dec(v_n_1961_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec_ref(v_cfg_1045_);
v___y_1221_ = v___y_2182_;
v___y_1222_ = v___y_2188_;
v___y_1223_ = v___y_2189_;
v___y_1224_ = v___y_2185_;
v___y_1225_ = v___y_2187_;
v___y_1226_ = v___y_2193_;
v___y_1227_ = v___y_2192_;
v_a_1228_ = v___y_2186_;
goto v___jp_1220_;
}
}
v___jp_2218_:
{
lean_object* v___x_2230_; lean_object* v_a_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2230_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref(v___x_2230_);
v___x_2232_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2233_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2229_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
lean_dec_ref(v___y_2222_);
v___x_2234_ = lean_io_mono_nanos_now();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v___y_2221_);
v___x_2235_ = lean_apply_6(v___y_2227_, v___y_2221_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; uint8_t v___x_2237_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = lean_unbox(v_a_2236_);
lean_dec(v_a_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; 
lean_inc_ref(v_next_1047_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v___y_2221_);
v___x_2238_ = lean_apply_7(v_next_1047_, v___y_2221_, v___y_2219_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; 
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2221_);
lean_dec(v_n_1961_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec_ref(v_cfg_1045_);
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref(v___x_2238_);
v___y_1211_ = v___y_2220_;
v___y_1212_ = v_a_2231_;
v___y_1213_ = v___y_2223_;
v___y_1214_ = v___x_2234_;
v___y_1215_ = v___y_2226_;
v___y_1216_ = v___y_2229_;
v___y_1217_ = v___y_2228_;
v_a_1218_ = v_a_2239_;
goto v___jp_1210_;
}
else
{
lean_object* v_a_2240_; uint8_t v___x_2241_; 
v_a_2240_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2240_);
lean_dec_ref(v___x_2238_);
v___x_2241_ = l_Lean_Exception_isInterrupt(v_a_2240_);
if (v___x_2241_ == 0)
{
uint8_t v___x_2242_; 
lean_inc(v_a_2240_);
v___x_2242_ = l_Lean_Exception_isRuntime(v_a_2240_);
v___y_2182_ = v___y_2220_;
v___y_2183_ = v___x_2233_;
v___y_2184_ = v___y_2221_;
v___y_2185_ = v___x_2234_;
v___y_2186_ = v_a_2240_;
v___y_2187_ = v___y_2226_;
v___y_2188_ = v_a_2231_;
v___y_2189_ = v___y_2223_;
v___y_2190_ = v___y_2224_;
v___y_2191_ = v___y_2225_;
v___y_2192_ = v___y_2228_;
v___y_2193_ = v___y_2229_;
v___y_2194_ = v___x_2242_;
goto v___jp_2181_;
}
else
{
v___y_2182_ = v___y_2220_;
v___y_2183_ = v___x_2233_;
v___y_2184_ = v___y_2221_;
v___y_2185_ = v___x_2234_;
v___y_2186_ = v_a_2240_;
v___y_2187_ = v___y_2226_;
v___y_2188_ = v_a_2231_;
v___y_2189_ = v___y_2223_;
v___y_2190_ = v___y_2224_;
v___y_2191_ = v___y_2225_;
v___y_2192_ = v___y_2228_;
v___y_2193_ = v___y_2229_;
v___y_2194_ = v___x_2241_;
goto v___jp_2181_;
}
}
}
else
{
lean_object* v___x_2243_; lean_object* v_a_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2219_);
lean_inc(v_trace_1046_);
v___x_2243_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = lean_nat_add(v_n_1961_, v_one_1960_);
lean_dec(v_n_1961_);
v___x_2246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___y_2221_);
lean_ctor_set(v___x_2246_, 1, v_acc_1051_);
v___x_2247_ = lean_unbox(v_a_2244_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; uint8_t v___x_2249_; 
v___x_2248_ = l_Lean_trace_profiler;
v___x_2249_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2229_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; 
lean_dec(v_a_2244_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2250_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___x_2245_, v___y_2225_, v___x_2246_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1231_ = v___y_2220_;
v___y_1232_ = v_a_2231_;
v___y_1233_ = v___y_2223_;
v___y_1234_ = v___x_2234_;
v___y_1235_ = v___y_2226_;
v___y_1236_ = v___y_2228_;
v___y_1237_ = v___y_2229_;
v___y_1238_ = v___x_2250_;
goto v___jp_1230_;
}
else
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_unbox(v_a_2244_);
lean_dec(v_a_2244_);
v___y_1558_ = v___y_2220_;
v___y_1559_ = v___x_2233_;
v___y_1560_ = v___x_2234_;
v___y_1561_ = v___y_2226_;
v___y_1562_ = v___x_2246_;
v___y_1563_ = v_a_2231_;
v___y_1564_ = v___x_2245_;
v___y_1565_ = v___x_2251_;
v___y_1566_ = v___y_2223_;
v___y_1567_ = v___y_2225_;
v___y_1568_ = v___y_2228_;
v___y_1569_ = v___y_2229_;
goto v___jp_1557_;
}
}
else
{
uint8_t v___x_2252_; 
v___x_2252_ = lean_unbox(v_a_2244_);
lean_dec(v_a_2244_);
v___y_1558_ = v___y_2220_;
v___y_1559_ = v___x_2233_;
v___y_1560_ = v___x_2234_;
v___y_1561_ = v___y_2226_;
v___y_1562_ = v___x_2246_;
v___y_1563_ = v_a_2231_;
v___y_1564_ = v___x_2245_;
v___y_1565_ = v___x_2252_;
v___y_1566_ = v___y_2223_;
v___y_1567_ = v___y_2225_;
v___y_1568_ = v___y_2228_;
v___y_1569_ = v___y_2229_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v_a_2253_; 
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2219_);
lean_dec(v_n_1961_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec_ref(v_cfg_1045_);
v_a_2253_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2253_);
lean_dec_ref(v___x_2235_);
v___y_1221_ = v___y_2220_;
v___y_1222_ = v_a_2231_;
v___y_1223_ = v___y_2223_;
v___y_1224_ = v___x_2234_;
v___y_1225_ = v___y_2226_;
v___y_1226_ = v___y_2229_;
v___y_1227_ = v___y_2228_;
v_a_1228_ = v_a_2253_;
goto v___jp_1220_;
}
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec_ref(v___y_2219_);
v___x_2254_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v___y_2221_);
v___x_2255_ = lean_apply_6(v___y_2227_, v___y_2221_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; uint8_t v___x_2257_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref(v___x_2255_);
v___x_2257_ = lean_unbox(v_a_2256_);
lean_dec(v_a_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; 
lean_inc_ref(v_next_1047_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v___y_2221_);
v___x_2258_ = lean_apply_7(v_next_1047_, v___y_2221_, v___y_2222_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; 
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2221_);
lean_dec(v_n_1961_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec_ref(v_cfg_1045_);
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref(v___x_2258_);
v___y_1160_ = v___x_2254_;
v___y_1161_ = v___y_2220_;
v___y_1162_ = v_a_2231_;
v___y_1163_ = v___y_2223_;
v___y_1164_ = v___y_2226_;
v___y_1165_ = v___y_2229_;
v___y_1166_ = v___y_2228_;
v_a_1167_ = v_a_2259_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_2260_; uint8_t v___x_2261_; 
v_a_2260_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2260_);
lean_dec_ref(v___x_2258_);
v___x_2261_ = l_Lean_Exception_isInterrupt(v_a_2260_);
if (v___x_2261_ == 0)
{
uint8_t v___x_2262_; 
lean_inc(v_a_2260_);
v___x_2262_ = l_Lean_Exception_isRuntime(v_a_2260_);
v___y_2095_ = v___x_2254_;
v___y_2096_ = v___y_2220_;
v___y_2097_ = v___x_2233_;
v___y_2098_ = v___y_2221_;
v___y_2099_ = v___y_2226_;
v___y_2100_ = v_a_2231_;
v___y_2101_ = v___y_2223_;
v___y_2102_ = v_a_2260_;
v___y_2103_ = v___y_2224_;
v___y_2104_ = v___y_2225_;
v___y_2105_ = v___y_2228_;
v___y_2106_ = v___y_2229_;
v___y_2107_ = v___x_2262_;
goto v___jp_2094_;
}
else
{
v___y_2095_ = v___x_2254_;
v___y_2096_ = v___y_2220_;
v___y_2097_ = v___x_2233_;
v___y_2098_ = v___y_2221_;
v___y_2099_ = v___y_2226_;
v___y_2100_ = v_a_2231_;
v___y_2101_ = v___y_2223_;
v___y_2102_ = v_a_2260_;
v___y_2103_ = v___y_2224_;
v___y_2104_ = v___y_2225_;
v___y_2105_ = v___y_2228_;
v___y_2106_ = v___y_2229_;
v___y_2107_ = v___x_2261_;
goto v___jp_2094_;
}
}
}
else
{
lean_object* v___x_2263_; lean_object* v_a_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2222_);
lean_inc(v_trace_1046_);
v___x_2263_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref(v___x_2263_);
v___x_2265_ = lean_nat_add(v_n_1961_, v_one_1960_);
lean_dec(v_n_1961_);
v___x_2266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___y_2221_);
lean_ctor_set(v___x_2266_, 1, v_acc_1051_);
v___x_2267_ = lean_unbox(v_a_2264_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; uint8_t v___x_2269_; 
v___x_2268_ = l_Lean_trace_profiler;
v___x_2269_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_2229_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2270_; 
lean_dec(v_a_2264_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_2270_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___x_2265_, v___y_2225_, v___x_2266_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
v___y_1180_ = v___y_2220_;
v___y_1181_ = v___x_2254_;
v___y_1182_ = v_a_2231_;
v___y_1183_ = v___y_2223_;
v___y_1184_ = v___y_2226_;
v___y_1185_ = v___y_2228_;
v___y_1186_ = v___y_2229_;
v___y_1187_ = v___x_2270_;
goto v___jp_1179_;
}
else
{
uint8_t v___x_2271_; 
v___x_2271_ = lean_unbox(v_a_2264_);
lean_dec(v_a_2264_);
v___y_1791_ = v___x_2254_;
v___y_1792_ = v___y_2220_;
v___y_1793_ = v___x_2233_;
v___y_1794_ = v___x_2271_;
v___y_1795_ = v___x_2265_;
v___y_1796_ = v___y_2226_;
v___y_1797_ = v_a_2231_;
v___y_1798_ = v___y_2223_;
v___y_1799_ = v___x_2266_;
v___y_1800_ = v___y_2225_;
v___y_1801_ = v___y_2228_;
v___y_1802_ = v___y_2229_;
goto v___jp_1790_;
}
}
else
{
uint8_t v___x_2272_; 
v___x_2272_ = lean_unbox(v_a_2264_);
lean_dec(v_a_2264_);
v___y_1791_ = v___x_2254_;
v___y_1792_ = v___y_2220_;
v___y_1793_ = v___x_2233_;
v___y_1794_ = v___x_2272_;
v___y_1795_ = v___x_2265_;
v___y_1796_ = v___y_2226_;
v___y_1797_ = v_a_2231_;
v___y_1798_ = v___y_2223_;
v___y_1799_ = v___x_2266_;
v___y_1800_ = v___y_2225_;
v___y_1801_ = v___y_2228_;
v___y_1802_ = v___y_2229_;
goto v___jp_1790_;
}
}
}
else
{
lean_object* v_a_2273_; 
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec(v_n_1961_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec_ref(v_cfg_1045_);
v_a_2273_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2273_);
lean_dec_ref(v___x_2255_);
v___y_1170_ = v___x_2254_;
v___y_1171_ = v___y_2220_;
v___y_1172_ = v_a_2231_;
v___y_1173_ = v___y_2223_;
v___y_1174_ = v___y_2226_;
v___y_1175_ = v___y_2229_;
v___y_1176_ = v___y_2228_;
v_a_1177_ = v_a_2273_;
goto v___jp_1169_;
}
}
}
v___jp_2274_:
{
if (v___y_2279_ == 0)
{
lean_object* v___x_2280_; 
lean_dec_ref(v___y_2276_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v___y_2275_);
v___x_2280_ = lean_apply_6(v___y_2277_, v___y_2275_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref(v___x_2280_);
if (lean_obj_tag(v_a_2281_) == 0)
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = lean_nat_add(v_n_1961_, v_one_1960_);
lean_dec(v_n_1961_);
v___x_2283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___y_2275_);
lean_ctor_set(v___x_2283_, 1, v_acc_1051_);
v_n_1049_ = v___x_2282_;
v_curr_1050_ = v___y_2278_;
v_acc_1051_ = v___x_2283_;
goto _start;
}
else
{
lean_object* v_val_2285_; lean_object* v___x_2286_; 
lean_dec(v___y_2275_);
v_val_2285_ = lean_ctor_get(v_a_2281_, 0);
lean_inc(v_val_2285_);
lean_dec_ref(v_a_2281_);
v___x_2286_ = l_List_appendTR___redArg(v_val_2285_, v___y_2278_);
v_n_1049_ = v_n_1961_;
v_curr_1050_ = v___x_2286_;
goto _start;
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v___y_2278_);
lean_dec(v___y_2275_);
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
v_a_2288_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2280_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2280_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2275_);
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
return v___y_2276_;
}
}
v___jp_2296_:
{
if (lean_obj_tag(v_a_2297_) == 0)
{
if (lean_obj_tag(v_curr_1050_) == 0)
{
lean_object* v_options_2298_; uint8_t v_hasTrace_2299_; lean_object* v___x_2300_; 
lean_dec(v_n_1961_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec_ref(v_cfg_1045_);
v_options_2298_ = lean_ctor_get(v_a_1054_, 2);
v_hasTrace_2299_ = lean_ctor_get_uint8(v_options_2298_, sizeof(void*)*1);
v___x_2300_ = l_List_reverse___redArg(v_acc_1051_);
if (v_hasTrace_2299_ == 0)
{
lean_object* v___x_2301_; 
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_trace_1046_);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
else
{
lean_object* v___x_2302_; lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2316_; 
lean_inc(v_trace_1046_);
v___x_2302_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2316_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2316_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
v___x_2308_ = lean_unbox(v_a_2303_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = l_Lean_trace_profiler;
v___x_2310_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_2298_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2312_; 
lean_dec(v_a_2303_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_trace_1046_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2300_);
v___x_2312_ = v___x_2305_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2300_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
else
{
uint8_t v___x_2314_; 
lean_del_object(v___x_2305_);
v___x_2314_ = lean_unbox(v_a_2303_);
lean_dec(v_a_2303_);
lean_inc_ref(v_options_2298_);
v___y_1334_ = v_hasTrace_2299_;
v___y_1335_ = v_options_2298_;
v___y_1336_ = v___x_2307_;
v___y_1337_ = v___x_2314_;
v___y_1338_ = v___x_2300_;
goto v___jp_1333_;
}
}
else
{
uint8_t v___x_2315_; 
lean_del_object(v___x_2305_);
v___x_2315_ = lean_unbox(v_a_2303_);
lean_dec(v_a_2303_);
lean_inc_ref(v_options_2298_);
v___y_1334_ = v_hasTrace_2299_;
v___y_1335_ = v_options_2298_;
v___y_1336_ = v___x_2307_;
v___y_1337_ = v___x_2315_;
v___y_1338_ = v___x_2300_;
goto v___jp_1333_;
}
}
}
}
else
{
lean_object* v_head_2317_; lean_object* v_tail_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2398_; 
v_head_2317_ = lean_ctor_get(v_curr_1050_, 0);
v_tail_2318_ = lean_ctor_get(v_curr_1050_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_curr_1050_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2320_ = v_curr_1050_;
v_isShared_2321_ = v_isSharedCheck_2398_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_tail_2318_);
lean_inc(v_head_2317_);
lean_dec(v_curr_1050_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2398_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v_a_2323_; uint8_t v___x_2324_; uint8_t v___x_2325_; 
v___x_2322_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(v_head_2317_, v_a_1053_);
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref(v___x_2322_);
v___x_2324_ = 1;
v___x_2325_ = lean_unbox(v_a_2323_);
lean_dec(v_a_2323_);
if (v___x_2325_ == 0)
{
lean_object* v_options_2326_; uint8_t v_hasTrace_2327_; 
v_options_2326_ = lean_ctor_get(v_a_1054_, 2);
v_hasTrace_2327_ = lean_ctor_get_uint8(v_options_2326_, sizeof(void*)*1);
if (v_hasTrace_2327_ == 0)
{
lean_object* v___x_2328_; 
lean_inc_ref(v_suspend_1246_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_head_2317_);
v___x_2328_ = lean_apply_6(v_suspend_1246_, v_head_2317_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; uint8_t v___x_2330_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = lean_unbox(v_a_2329_);
lean_dec(v_a_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___f_2331_; lean_object* v___x_2332_; 
lean_del_object(v___x_2320_);
lean_inc(v_acc_1051_);
lean_inc(v_n_1961_);
lean_inc(v_goals_1048_);
lean_inc_ref(v_next_1047_);
lean_inc(v_trace_1046_);
lean_inc_ref(v_cfg_1045_);
lean_inc(v_tail_2318_);
v___f_2331_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2331_, 0, v_tail_2318_);
lean_closure_set(v___f_2331_, 1, v_cfg_1045_);
lean_closure_set(v___f_2331_, 2, v_trace_1046_);
lean_closure_set(v___f_2331_, 3, v_next_1047_);
lean_closure_set(v___f_2331_, 4, v_goals_1048_);
lean_closure_set(v___f_2331_, 5, v_n_1961_);
lean_closure_set(v___f_2331_, 6, v_acc_1051_);
lean_inc_ref(v_next_1047_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_head_2317_);
v___x_2332_ = lean_apply_7(v_next_1047_, v_head_2317_, v___f_2331_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_dec(v_tail_2318_);
lean_dec(v_head_2317_);
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
return v___x_2332_;
}
else
{
lean_object* v_a_2333_; uint8_t v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
v___x_2334_ = l_Lean_Exception_isInterrupt(v_a_2333_);
if (v___x_2334_ == 0)
{
uint8_t v___x_2335_; 
v___x_2335_ = l_Lean_Exception_isRuntime(v_a_2333_);
lean_inc_ref(v_discharge_1247_);
v___y_2275_ = v_head_2317_;
v___y_2276_ = v___x_2332_;
v___y_2277_ = v_discharge_1247_;
v___y_2278_ = v_tail_2318_;
v___y_2279_ = v___x_2335_;
goto v___jp_2274_;
}
else
{
lean_dec(v_a_2333_);
lean_inc_ref(v_discharge_1247_);
v___y_2275_ = v_head_2317_;
v___y_2276_ = v___x_2332_;
v___y_2277_ = v_discharge_1247_;
v___y_2278_ = v_tail_2318_;
v___y_2279_ = v___x_2334_;
goto v___jp_2274_;
}
}
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2336_ = lean_nat_add(v_n_1961_, v_one_1960_);
lean_dec(v_n_1961_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v_acc_1051_);
v___x_2338_ = v___x_2320_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_head_2317_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_acc_1051_);
v___x_2338_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
v_n_1049_ = v___x_2336_;
v_curr_1050_ = v_tail_2318_;
v_acc_1051_ = v___x_2338_;
goto _start;
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_del_object(v___x_2320_);
lean_dec(v_tail_2318_);
lean_dec(v_head_2317_);
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
v_a_2341_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2328_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2328_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v___x_2349_; lean_object* v_a_2350_; lean_object* v___f_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
lean_inc(v_trace_1046_);
v___x_2349_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
lean_inc(v_acc_1051_);
lean_inc(v_n_1961_);
lean_inc(v_goals_1048_);
lean_inc_ref(v_next_1047_);
lean_inc(v_trace_1046_);
lean_inc_ref(v_cfg_1045_);
lean_inc(v_tail_2318_);
v___f_2351_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2351_, 0, v_tail_2318_);
lean_closure_set(v___f_2351_, 1, v_cfg_1045_);
lean_closure_set(v___f_2351_, 2, v_trace_1046_);
lean_closure_set(v___f_2351_, 3, v_next_1047_);
lean_closure_set(v___f_2351_, 4, v_goals_1048_);
lean_closure_set(v___f_2351_, 5, v_n_1961_);
lean_closure_set(v___f_2351_, 6, v_acc_1051_);
lean_inc(v_head_2317_);
v___f_2352_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(v___f_2352_, 0, v_head_2317_);
v___x_2353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
v___x_2354_ = lean_unbox(v_a_2350_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2355_ = l_Lean_trace_profiler;
v___x_2356_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_2326_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
lean_dec_ref(v___f_2352_);
lean_dec(v_a_2350_);
lean_inc_ref(v_suspend_1246_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_head_2317_);
v___x_2357_ = lean_apply_6(v_suspend_1246_, v_head_2317_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; uint8_t v___x_2359_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref(v___x_2357_);
v___x_2359_ = lean_unbox(v_a_2358_);
lean_dec(v_a_2358_);
if (v___x_2359_ == 0)
{
lean_object* v___x_2360_; 
lean_del_object(v___x_2320_);
lean_inc_ref(v_next_1047_);
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_head_2317_);
v___x_2360_ = lean_apply_7(v_next_1047_, v_head_2317_, v___f_2351_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, lean_box(0));
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_dec(v_tail_2318_);
lean_dec(v_head_2317_);
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
return v___x_2360_;
}
else
{
lean_object* v_a_2361_; uint8_t v___x_2362_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
v___x_2362_ = l_Lean_Exception_isInterrupt(v_a_2361_);
if (v___x_2362_ == 0)
{
uint8_t v___x_2363_; 
v___x_2363_ = l_Lean_Exception_isRuntime(v_a_2361_);
lean_inc_ref(v_options_2326_);
lean_inc_ref(v_discharge_1247_);
v___y_2009_ = v___x_2353_;
v___y_2010_ = v_head_2317_;
v___y_2011_ = v___x_2324_;
v___y_2012_ = v_discharge_1247_;
v___y_2013_ = v_tail_2318_;
v___y_2014_ = v_options_2326_;
v___y_2015_ = v___x_2360_;
v___y_2016_ = v___x_2356_;
v___y_2017_ = v___x_2363_;
goto v___jp_2008_;
}
else
{
lean_dec(v_a_2361_);
lean_inc_ref(v_options_2326_);
lean_inc_ref(v_discharge_1247_);
v___y_2009_ = v___x_2353_;
v___y_2010_ = v_head_2317_;
v___y_2011_ = v___x_2324_;
v___y_2012_ = v_discharge_1247_;
v___y_2013_ = v_tail_2318_;
v___y_2014_ = v_options_2326_;
v___y_2015_ = v___x_2360_;
v___y_2016_ = v___x_2356_;
v___y_2017_ = v___x_2362_;
goto v___jp_2008_;
}
}
}
else
{
lean_object* v___x_2364_; lean_object* v_a_2365_; lean_object* v___x_2366_; lean_object* v___x_2368_; 
lean_dec_ref(v___f_2351_);
lean_inc(v_trace_1046_);
v___x_2364_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref(v___x_2364_);
v___x_2366_ = lean_nat_add(v_n_1961_, v_one_1960_);
lean_dec(v_n_1961_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v_acc_1051_);
v___x_2368_ = v___x_2320_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_head_2317_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_acc_1051_);
v___x_2368_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
uint8_t v___x_2369_; 
v___x_2369_ = lean_unbox(v_a_2365_);
if (v___x_2369_ == 0)
{
if (v___x_2356_ == 0)
{
lean_dec(v_a_2365_);
v_n_1049_ = v___x_2366_;
v_curr_1050_ = v_tail_2318_;
v_acc_1051_ = v___x_2368_;
goto _start;
}
else
{
uint8_t v___x_2371_; 
v___x_2371_ = lean_unbox(v_a_2365_);
lean_dec(v_a_2365_);
lean_inc_ref(v_options_2326_);
v___y_1285_ = v___x_2353_;
v___y_1286_ = v___x_2368_;
v___y_1287_ = v___x_2324_;
v___y_1288_ = v___x_2371_;
v___y_1289_ = v_tail_2318_;
v___y_1290_ = v___x_2366_;
v___y_1291_ = v_options_2326_;
goto v___jp_1284_;
}
}
else
{
uint8_t v___x_2372_; 
v___x_2372_ = lean_unbox(v_a_2365_);
lean_dec(v_a_2365_);
lean_inc_ref(v_options_2326_);
v___y_1285_ = v___x_2353_;
v___y_1286_ = v___x_2368_;
v___y_1287_ = v___x_2324_;
v___y_1288_ = v___x_2372_;
v___y_1289_ = v_tail_2318_;
v___y_1290_ = v___x_2366_;
v___y_1291_ = v_options_2326_;
goto v___jp_1284_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec_ref(v___f_2351_);
lean_del_object(v___x_2320_);
lean_dec(v_tail_2318_);
lean_dec(v_head_2317_);
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
v_a_2374_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2357_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2357_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
uint8_t v___x_2382_; 
lean_del_object(v___x_2320_);
v___x_2382_ = lean_unbox(v_a_2350_);
lean_dec(v_a_2350_);
lean_inc_ref(v_options_2326_);
lean_inc_ref(v_suspend_1246_);
lean_inc_ref(v_discharge_1247_);
lean_inc_ref(v___f_2351_);
v___y_2219_ = v___f_2351_;
v___y_2220_ = v___x_2353_;
v___y_2221_ = v_head_2317_;
v___y_2222_ = v___f_2351_;
v___y_2223_ = v___x_2324_;
v___y_2224_ = v_discharge_1247_;
v___y_2225_ = v_tail_2318_;
v___y_2226_ = v___f_2352_;
v___y_2227_ = v_suspend_1246_;
v___y_2228_ = v___x_2382_;
v___y_2229_ = v_options_2326_;
goto v___jp_2218_;
}
}
else
{
uint8_t v___x_2383_; 
lean_del_object(v___x_2320_);
v___x_2383_ = lean_unbox(v_a_2350_);
lean_dec(v_a_2350_);
lean_inc_ref(v_options_2326_);
lean_inc_ref(v_suspend_1246_);
lean_inc_ref(v_discharge_1247_);
lean_inc_ref(v___f_2351_);
v___y_2219_ = v___f_2351_;
v___y_2220_ = v___x_2353_;
v___y_2221_ = v_head_2317_;
v___y_2222_ = v___f_2351_;
v___y_2223_ = v___x_2324_;
v___y_2224_ = v_discharge_1247_;
v___y_2225_ = v_tail_2318_;
v___y_2226_ = v___f_2352_;
v___y_2227_ = v_suspend_1246_;
v___y_2228_ = v___x_2383_;
v___y_2229_ = v_options_2326_;
goto v___jp_2218_;
}
}
}
else
{
lean_object* v_options_2384_; uint8_t v_hasTrace_2385_; lean_object* v___x_2386_; 
lean_del_object(v___x_2320_);
v_options_2384_ = lean_ctor_get(v_a_1054_, 2);
v_hasTrace_2385_ = lean_ctor_get_uint8(v_options_2384_, sizeof(void*)*1);
v___x_2386_ = lean_nat_add(v_n_1961_, v_one_1960_);
lean_dec(v_n_1961_);
if (v_hasTrace_2385_ == 0)
{
lean_dec(v_head_2317_);
v_n_1049_ = v___x_2386_;
v_curr_1050_ = v_tail_2318_;
goto _start;
}
else
{
lean_object* v___x_2388_; lean_object* v_a_2389_; lean_object* v___f_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
lean_inc(v_trace_1046_);
v___x_2388_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_1046_, v_a_1054_);
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref(v___x_2388_);
v___f_2390_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2390_, 0, v_head_2317_);
v___x_2391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
v___x_2392_ = lean_unbox(v_a_2389_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = l_Lean_trace_profiler;
v___x_2394_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_2384_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_dec_ref(v___f_2390_);
lean_dec(v_a_2389_);
v_n_1049_ = v___x_2386_;
v_curr_1050_ = v_tail_2318_;
goto _start;
}
else
{
uint8_t v___x_2396_; 
v___x_2396_ = lean_unbox(v_a_2389_);
lean_dec(v_a_2389_);
lean_inc_ref(v_options_2384_);
v___y_1095_ = v___x_2396_;
v___y_1096_ = v_options_2384_;
v___y_1097_ = v___x_2386_;
v___y_1098_ = v___x_2324_;
v___y_1099_ = v_tail_2318_;
v___y_1100_ = v___x_2391_;
v___y_1101_ = v___f_2390_;
goto v___jp_1094_;
}
}
else
{
uint8_t v___x_2397_; 
v___x_2397_ = lean_unbox(v_a_2389_);
lean_dec(v_a_2389_);
lean_inc_ref(v_options_2384_);
v___y_1095_ = v___x_2397_;
v___y_1096_ = v_options_2384_;
v___y_1097_ = v___x_2386_;
v___y_1098_ = v___x_2324_;
v___y_1099_ = v_tail_2318_;
v___y_1100_ = v___x_2391_;
v___y_1101_ = v___f_2390_;
goto v___jp_1094_;
}
}
}
}
}
}
else
{
lean_object* v_val_2399_; 
lean_dec(v_curr_1050_);
v_val_2399_ = lean_ctor_get(v_a_2297_, 0);
lean_inc(v_val_2399_);
lean_dec_ref(v_a_2297_);
v_n_1049_ = v_n_1961_;
v_curr_1050_ = v_val_2399_;
goto _start;
}
}
v___jp_2401_:
{
if (lean_obj_tag(v___y_2402_) == 0)
{
lean_object* v_a_2403_; 
v_a_2403_ = lean_ctor_get(v___y_2402_, 0);
lean_inc(v_a_2403_);
lean_dec_ref(v___y_2402_);
v_a_2297_ = v_a_2403_;
goto v___jp_2296_;
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_n_1961_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_acc_1051_);
lean_dec(v_curr_1050_);
lean_dec(v_goals_1048_);
lean_dec_ref(v_next_1047_);
lean_dec(v_trace_1046_);
lean_dec_ref(v_cfg_1045_);
v_a_2404_ = lean_ctor_get(v___y_2402_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___y_2402_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___y_2402_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___y_2402_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
v___jp_1057_:
{
lean_object* v___x_1066_; double v___x_1067_; double v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1066_ = lean_io_get_num_heartbeats();
v___x_1067_ = lean_float_of_nat(v___y_1059_);
v___x_1068_ = lean_float_of_nat(v___x_1066_);
v___x_1069_ = lean_box_float(v___x_1067_);
v___x_1070_ = lean_box_float(v___x_1068_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_a_1065_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1062_, v___y_1063_, v___y_1060_, v___y_1058_, v___y_1061_, v___y_1064_, v___x_1072_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1060_);
return v___x_1073_;
}
v___jp_1074_:
{
lean_object* v___x_1083_; double v___x_1084_; double v___x_1085_; double v___x_1086_; double v___x_1087_; double v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1083_ = lean_io_mono_nanos_now();
v___x_1084_ = lean_float_of_nat(v___y_1081_);
v___x_1085_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1086_ = lean_float_div(v___x_1084_, v___x_1085_);
v___x_1087_ = lean_float_of_nat(v___x_1083_);
v___x_1088_ = lean_float_div(v___x_1087_, v___x_1085_);
v___x_1089_ = lean_box_float(v___x_1086_);
v___x_1090_ = lean_box_float(v___x_1088_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_a_1082_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1078_, v___y_1079_, v___y_1076_, v___y_1075_, v___y_1077_, v___y_1080_, v___x_1092_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1076_);
return v___x_1093_;
}
v___jp_1094_:
{
lean_object* v___x_1102_; lean_object* v_a_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1102_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_1055_);
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1102_);
v___x_1104_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1105_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v___y_1096_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_io_mono_nanos_now();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1107_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1097_, v___y_1099_, v_acc_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 1);
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
v___y_1075_ = v___y_1095_;
v___y_1076_ = v___y_1096_;
v___y_1077_ = v_a_1103_;
v___y_1078_ = v___y_1098_;
v___y_1079_ = v___y_1100_;
v___y_1080_ = v___y_1101_;
v___y_1081_ = v___x_1106_;
v_a_1082_ = v___x_1113_;
goto v___jp_1074_;
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_a_1116_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1107_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1107_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 0);
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
v___y_1075_ = v___y_1095_;
v___y_1076_ = v___y_1096_;
v___y_1077_ = v_a_1103_;
v___y_1078_ = v___y_1098_;
v___y_1079_ = v___y_1100_;
v___y_1080_ = v___y_1101_;
v___y_1081_ = v___x_1106_;
v_a_1082_ = v___x_1121_;
goto v___jp_1074_;
}
}
}
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1055_);
lean_inc_ref(v_a_1054_);
lean_inc(v_a_1053_);
lean_inc_ref(v_a_1052_);
lean_inc(v_trace_1046_);
v___x_1125_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1045_, v_trace_1046_, v_next_1047_, v_goals_1048_, v___y_1097_, v___y_1099_, v_acc_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 1);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
v___y_1058_ = v___y_1095_;
v___y_1059_ = v___x_1124_;
v___y_1060_ = v___y_1096_;
v___y_1061_ = v_a_1103_;
v___y_1062_ = v___y_1098_;
v___y_1063_ = v___y_1100_;
v___y_1064_ = v___y_1101_;
v_a_1065_ = v___x_1131_;
goto v___jp_1057_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
v_a_1134_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1125_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1125_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 0);
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
v___y_1058_ = v___y_1095_;
v___y_1059_ = v___x_1124_;
v___y_1060_ = v___y_1096_;
v___y_1061_ = v_a_1103_;
v___y_1062_ = v___y_1098_;
v___y_1063_ = v___y_1100_;
v___y_1064_ = v___y_1101_;
v_a_1065_ = v___x_1139_;
goto v___jp_1057_;
}
}
}
}
}
v___jp_1142_:
{
lean_object* v___x_1151_; double v___x_1152_; double v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1151_ = lean_io_get_num_heartbeats();
v___x_1152_ = lean_float_of_nat(v___y_1144_);
v___x_1153_ = lean_float_of_nat(v___x_1151_);
v___x_1154_ = lean_box_float(v___x_1152_);
v___x_1155_ = lean_box_float(v___x_1153_);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_a_1150_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1146_, v___y_1143_, v___y_1149_, v___y_1148_, v___y_1145_, v___y_1147_, v___x_1157_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1149_);
return v___x_1158_;
}
v___jp_1159_:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_a_1167_);
v___y_1143_ = v___y_1161_;
v___y_1144_ = v___y_1160_;
v___y_1145_ = v___y_1162_;
v___y_1146_ = v___y_1163_;
v___y_1147_ = v___y_1164_;
v___y_1148_ = v___y_1166_;
v___y_1149_ = v___y_1165_;
v_a_1150_ = v___x_1168_;
goto v___jp_1142_;
}
v___jp_1169_:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_a_1177_);
v___y_1143_ = v___y_1171_;
v___y_1144_ = v___y_1170_;
v___y_1145_ = v___y_1172_;
v___y_1146_ = v___y_1173_;
v___y_1147_ = v___y_1174_;
v___y_1148_ = v___y_1176_;
v___y_1149_ = v___y_1175_;
v_a_1150_ = v___x_1178_;
goto v___jp_1142_;
}
v___jp_1179_:
{
if (lean_obj_tag(v___y_1187_) == 0)
{
lean_object* v_a_1188_; 
v_a_1188_ = lean_ctor_get(v___y_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v___y_1187_);
v___y_1160_ = v___y_1181_;
v___y_1161_ = v___y_1180_;
v___y_1162_ = v___y_1182_;
v___y_1163_ = v___y_1183_;
v___y_1164_ = v___y_1184_;
v___y_1165_ = v___y_1186_;
v___y_1166_ = v___y_1185_;
v_a_1167_ = v_a_1188_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1189_; 
v_a_1189_ = lean_ctor_get(v___y_1187_, 0);
lean_inc(v_a_1189_);
lean_dec_ref(v___y_1187_);
v___y_1170_ = v___y_1181_;
v___y_1171_ = v___y_1180_;
v___y_1172_ = v___y_1182_;
v___y_1173_ = v___y_1183_;
v___y_1174_ = v___y_1184_;
v___y_1175_ = v___y_1186_;
v___y_1176_ = v___y_1185_;
v_a_1177_ = v_a_1189_;
goto v___jp_1169_;
}
}
v___jp_1190_:
{
lean_object* v___x_1199_; double v___x_1200_; double v___x_1201_; double v___x_1202_; double v___x_1203_; double v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1199_ = lean_io_mono_nanos_now();
v___x_1200_ = lean_float_of_nat(v___y_1194_);
v___x_1201_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1202_ = lean_float_div(v___x_1200_, v___x_1201_);
v___x_1203_ = lean_float_of_nat(v___x_1199_);
v___x_1204_ = lean_float_div(v___x_1203_, v___x_1201_);
v___x_1205_ = lean_box_float(v___x_1202_);
v___x_1206_ = lean_box_float(v___x_1204_);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1205_);
lean_ctor_set(v___x_1207_, 1, v___x_1206_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_a_1198_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_1046_, v___y_1193_, v___y_1191_, v___y_1197_, v___y_1196_, v___y_1192_, v___y_1195_, v___x_1208_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
lean_dec_ref(v___y_1197_);
return v___x_1209_;
}
v___jp_1210_:
{
lean_object* v___x_1219_; 
v___x_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1219_, 0, v_a_1218_);
v___y_1191_ = v___y_1211_;
v___y_1192_ = v___y_1212_;
v___y_1193_ = v___y_1213_;
v___y_1194_ = v___y_1214_;
v___y_1195_ = v___y_1215_;
v___y_1196_ = v___y_1217_;
v___y_1197_ = v___y_1216_;
v_a_1198_ = v___x_1219_;
goto v___jp_1190_;
}
v___jp_1220_:
{
lean_object* v___x_1229_; 
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1228_);
v___y_1191_ = v___y_1221_;
v___y_1192_ = v___y_1222_;
v___y_1193_ = v___y_1223_;
v___y_1194_ = v___y_1224_;
v___y_1195_ = v___y_1225_;
v___y_1196_ = v___y_1227_;
v___y_1197_ = v___y_1226_;
v_a_1198_ = v___x_1229_;
goto v___jp_1190_;
}
v___jp_1230_:
{
if (lean_obj_tag(v___y_1238_) == 0)
{
lean_object* v_a_1239_; 
v_a_1239_ = lean_ctor_get(v___y_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___y_1238_);
v___y_1211_ = v___y_1231_;
v___y_1212_ = v___y_1232_;
v___y_1213_ = v___y_1233_;
v___y_1214_ = v___y_1234_;
v___y_1215_ = v___y_1235_;
v___y_1216_ = v___y_1237_;
v___y_1217_ = v___y_1236_;
v_a_1218_ = v_a_1239_;
goto v___jp_1210_;
}
else
{
lean_object* v_a_1240_; 
v_a_1240_ = lean_ctor_get(v___y_1238_, 0);
lean_inc(v_a_1240_);
lean_dec_ref(v___y_1238_);
v___y_1221_ = v___y_1231_;
v___y_1222_ = v___y_1232_;
v___y_1223_ = v___y_1233_;
v___y_1224_ = v___y_1234_;
v___y_1225_ = v___y_1235_;
v___y_1226_ = v___y_1237_;
v___y_1227_ = v___y_1236_;
v_a_1228_ = v_a_1240_;
goto v___jp_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2487_, lean_object* v_trace_2488_, lean_object* v_next_2489_, lean_object* v_goals_2490_, lean_object* v_n_2491_, lean_object* v_curr_2492_, lean_object* v_acc_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2487_, v_trace_2488_, v_next_2489_, v_goals_2490_, v_n_2491_, v_curr_2492_, v_acc_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object* v_tail_2500_, lean_object* v_cfg_2501_, lean_object* v_trace_2502_, lean_object* v_next_2503_, lean_object* v_goals_2504_, lean_object* v_n_2505_, lean_object* v_acc_2506_, lean_object* v_r_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = l_List_appendTR___redArg(v_r_2507_, v_tail_2500_);
v___x_2514_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2514_, 0, v_cfg_2501_);
lean_closure_set(v___x_2514_, 1, v_trace_2502_);
lean_closure_set(v___x_2514_, 2, v_next_2503_);
lean_closure_set(v___x_2514_, 3, v_goals_2504_);
lean_closure_set(v___x_2514_, 4, v_n_2505_);
lean_closure_set(v___x_2514_, 5, v___x_2513_);
lean_closure_set(v___x_2514_, 6, v_acc_2506_);
v___x_2515_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg(v___x_2514_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2516_, lean_object* v_msg_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2524_, lean_object* v_msg_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2524_, v_msg_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(lean_object* v_00_u03b1_2532_, lean_object* v_x_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(v_x_2533_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2540_, lean_object* v_x_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(v_00_u03b1_2540_, v_x_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec_ref(v___y_2542_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_mvarId_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(v_mvarId_2548_, v___y_2550_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_mvarId_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_mvarId_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v_mvarId_2555_);
return v_res_2561_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11(lean_object* v_00_u03b2_2562_, lean_object* v_x_2563_, lean_object* v_x_2564_){
_start:
{
uint8_t v___x_2565_; 
v___x_2565_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(v_x_2563_, v_x_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___boxed(lean_object* v_00_u03b2_2566_, lean_object* v_x_2567_, lean_object* v_x_2568_){
_start:
{
uint8_t v_res_2569_; lean_object* v_r_2570_; 
v_res_2569_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11(v_00_u03b2_2566_, v_x_2567_, v_x_2568_);
lean_dec(v_x_2568_);
v_r_2570_ = lean_box(v_res_2569_);
return v_r_2570_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13(lean_object* v_00_u03b2_2571_, lean_object* v_x_2572_, size_t v_x_2573_, lean_object* v_x_2574_){
_start:
{
uint8_t v___x_2575_; 
v___x_2575_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(v_x_2572_, v_x_2573_, v_x_2574_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___boxed(lean_object* v_00_u03b2_2576_, lean_object* v_x_2577_, lean_object* v_x_2578_, lean_object* v_x_2579_){
_start:
{
size_t v_x_75468__boxed_2580_; uint8_t v_res_2581_; lean_object* v_r_2582_; 
v_x_75468__boxed_2580_ = lean_unbox_usize(v_x_2578_);
lean_dec(v_x_2578_);
v_res_2581_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13(v_00_u03b2_2576_, v_x_2577_, v_x_75468__boxed_2580_, v_x_2579_);
lean_dec(v_x_2579_);
v_r_2582_ = lean_box(v_res_2581_);
return v_r_2582_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16(lean_object* v_00_u03b2_2583_, lean_object* v_keys_2584_, lean_object* v_vals_2585_, lean_object* v_heq_2586_, lean_object* v_i_2587_, lean_object* v_k_2588_){
_start:
{
uint8_t v___x_2589_; 
v___x_2589_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(v_keys_2584_, v_i_2587_, v_k_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___boxed(lean_object* v_00_u03b2_2590_, lean_object* v_keys_2591_, lean_object* v_vals_2592_, lean_object* v_heq_2593_, lean_object* v_i_2594_, lean_object* v_k_2595_){
_start:
{
uint8_t v_res_2596_; lean_object* v_r_2597_; 
v_res_2596_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16(v_00_u03b2_2590_, v_keys_2591_, v_vals_2592_, v_heq_2593_, v_i_2594_, v_k_2595_);
lean_dec(v_k_2595_);
lean_dec_ref(v_vals_2592_);
lean_dec_ref(v_keys_2591_);
v_r_2597_ = lean_box(v_res_2596_);
return v_r_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2598_, lean_object* v_h__1_2599_, lean_object* v_h__2_2600_){
_start:
{
lean_object* v_zero_2601_; uint8_t v_isZero_2602_; 
v_zero_2601_ = lean_unsigned_to_nat(0u);
v_isZero_2602_ = lean_nat_dec_eq(v_n_2598_, v_zero_2601_);
if (v_isZero_2602_ == 1)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec(v_h__2_2600_);
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_apply_1(v_h__1_2599_, v___x_2603_);
return v___x_2604_;
}
else
{
lean_object* v_one_2605_; lean_object* v_n_2606_; lean_object* v___x_2607_; 
lean_dec(v_h__1_2599_);
v_one_2605_ = lean_unsigned_to_nat(1u);
v_n_2606_ = lean_nat_sub(v_n_2598_, v_one_2605_);
v___x_2607_ = lean_apply_1(v_h__2_2600_, v_n_2606_);
return v___x_2607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2608_, lean_object* v_h__1_2609_, lean_object* v_h__2_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2608_, v_h__1_2609_, v_h__2_2610_);
lean_dec(v_n_2608_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2612_, lean_object* v_n_2613_, lean_object* v_h__1_2614_, lean_object* v_h__2_2615_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2613_, v_h__1_2614_, v_h__2_2615_);
return v___x_2616_;
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
lean_object* v___x_2633_; 
v___x_2633_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(v_procResult_x3f_2630_, v_h__1_2631_, v_h__2_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2634_, lean_object* v_h__1_2635_, lean_object* v_h__2_2636_){
_start:
{
if (lean_obj_tag(v_curr_2634_) == 0)
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_dec(v_h__2_2636_);
v___x_2637_ = lean_box(0);
v___x_2638_ = lean_apply_1(v_h__1_2635_, v___x_2637_);
return v___x_2638_;
}
else
{
lean_object* v_head_2639_; lean_object* v_tail_2640_; lean_object* v___x_2641_; 
lean_dec(v_h__1_2635_);
v_head_2639_ = lean_ctor_get(v_curr_2634_, 0);
lean_inc(v_head_2639_);
v_tail_2640_ = lean_ctor_get(v_curr_2634_, 1);
lean_inc(v_tail_2640_);
lean_dec_ref(v_curr_2634_);
v___x_2641_ = lean_apply_2(v_h__2_2636_, v_head_2639_, v_tail_2640_);
return v___x_2641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2642_, lean_object* v_curr_2643_, lean_object* v_h__1_2644_, lean_object* v_h__2_2645_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(v_curr_2643_, v_h__1_2644_, v_h__2_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2647_, lean_object* v_h__1_2648_, lean_object* v_h__2_2649_){
_start:
{
if (lean_obj_tag(v_____do__lift_2647_) == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_dec(v_h__2_2649_);
v___x_2650_ = lean_box(0);
v___x_2651_ = lean_apply_1(v_h__1_2648_, v___x_2650_);
return v___x_2651_;
}
else
{
lean_object* v_val_2652_; lean_object* v___x_2653_; 
lean_dec(v_h__1_2648_);
v_val_2652_ = lean_ctor_get(v_____do__lift_2647_, 0);
lean_inc(v_val_2652_);
lean_dec_ref(v_____do__lift_2647_);
v___x_2653_ = lean_apply_1(v_h__2_2649_, v_val_2652_);
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_2654_, lean_object* v_____do__lift_2655_, lean_object* v_h__1_2656_, lean_object* v_h__2_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(v_____do__lift_2655_, v_h__1_2656_, v_h__2_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_2659_, lean_object* v_trace_2660_, lean_object* v_next_2661_, lean_object* v_orig_2662_, lean_object* v_g_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_maxDepth_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_maxDepth_2669_ = lean_ctor_get(v_cfg_2659_, 0);
lean_inc(v_maxDepth_2669_);
v___x_2670_ = lean_box(0);
v___x_2671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_g_2663_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2659_, v_trace_2660_, v_next_2661_, v_orig_2662_, v_maxDepth_2669_, v___x_2671_, v___x_2670_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_2673_, lean_object* v_trace_2674_, lean_object* v_next_2675_, lean_object* v_orig_2676_, lean_object* v_g_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2673_, v_trace_2674_, v_next_2675_, v_orig_2676_, v_g_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
if (lean_obj_tag(v_a_2684_) == 0)
{
lean_object* v___x_2686_; 
v___x_2686_ = l_List_reverse___redArg(v_a_2685_);
return v___x_2686_;
}
else
{
lean_object* v_head_2687_; lean_object* v_tail_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2697_; 
v_head_2687_ = lean_ctor_get(v_a_2684_, 0);
v_tail_2688_ = lean_ctor_get(v_a_2684_, 1);
v_isSharedCheck_2697_ = !lean_is_exclusive(v_a_2684_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2690_ = v_a_2684_;
v_isShared_2691_ = v_isSharedCheck_2697_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_tail_2688_);
lean_inc(v_head_2687_);
lean_dec(v_a_2684_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2697_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2692_ = l_Lean_MessageData_ofFormat(v_head_2687_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 1, v_a_2685_);
lean_ctor_set(v___x_2690_, 0, v___x_2692_);
v___x_2694_ = v___x_2690_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_a_2685_);
v___x_2694_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
v_a_2684_ = v_tail_2688_;
v_a_2685_ = v___x_2694_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_2700_ = l_Lean_stringToMessageData(v___x_2699_);
return v___x_2700_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_2703_ = l_Lean_stringToMessageData(v___x_2702_);
return v___x_2703_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_2706_ = l_Lean_stringToMessageData(v___x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_2707_, lean_object* v_snd_2708_, lean_object* v_x_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2707_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref(v___x_2715_);
v___x_2717_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_2708_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2737_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2737_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2737_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2722_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_2723_ = lean_box(0);
v___x_2724_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2716_, v___x_2723_);
v___x_2725_ = l_Lean_MessageData_ofList(v___x_2724_);
v___x_2726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2722_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_2728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2726_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_2730_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2718_, v___x_2723_);
v___x_2731_ = l_Lean_MessageData_ofList(v___x_2730_);
v___x_2732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2729_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
v___x_2733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2728_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2733_);
v___x_2735_ = v___x_2720_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_a_2716_);
v_a_2738_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2717_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2717_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_snd_2708_);
v_a_2746_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2715_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2715_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_2754_, lean_object* v_snd_2755_, lean_object* v_x_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2754_, v_snd_2755_, v_x_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec_ref(v_x_2756_);
return v_res_2762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_2765_ = l_Lean_stringToMessageData(v___x_2764_);
return v___x_2765_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_2768_ = l_Lean_stringToMessageData(v___x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_2769_, lean_object* v___x_2770_, lean_object* v_x_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2769_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2779_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref(v___x_2777_);
v___x_2779_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_2770_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2797_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2782_ = v___x_2779_;
v_isShared_2783_ = v_isSharedCheck_2797_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2779_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2797_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2784_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_2785_ = lean_box(0);
v___x_2786_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2778_, v___x_2785_);
v___x_2787_ = l_Lean_MessageData_ofList(v___x_2786_);
v___x_2788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2784_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
v___x_2789_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_2790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2780_, v___x_2785_);
v___x_2792_ = l_Lean_MessageData_ofList(v___x_2791_);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2790_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2793_);
v___x_2795_ = v___x_2782_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec(v_a_2778_);
v_a_2798_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2779_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2779_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec(v___x_2770_);
v_a_2806_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2777_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2777_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_2814_, lean_object* v___x_2815_, lean_object* v_x_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2814_, v___x_2815_, v_x_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v_x_2816_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t v___x_2823_, lean_object* v_x_2824_, lean_object* v_x_2825_, lean_object* v___y_2826_){
_start:
{
if (lean_obj_tag(v_x_2824_) == 0)
{
lean_object* v___x_2828_; 
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v_x_2825_);
return v___x_2828_;
}
else
{
lean_object* v_head_2829_; lean_object* v_tail_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2845_; 
v_head_2829_ = lean_ctor_get(v_x_2824_, 0);
v_tail_2830_ = lean_ctor_get(v_x_2824_, 1);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_x_2824_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2832_ = v_x_2824_;
v_isShared_2833_ = v_isSharedCheck_2845_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_tail_2830_);
lean_inc(v_head_2829_);
lean_dec(v_x_2824_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2845_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
uint8_t v_a_2840_; lean_object* v___x_2842_; lean_object* v_a_2843_; uint8_t v___x_2844_; 
v___x_2842_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(v_head_2829_, v___y_2826_);
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref(v___x_2842_);
v___x_2844_ = lean_unbox(v_a_2843_);
lean_dec(v_a_2843_);
if (v___x_2844_ == 0)
{
goto v___jp_2834_;
}
else
{
v_a_2840_ = v___x_2823_;
goto v___jp_2839_;
}
v___jp_2834_:
{
lean_object* v___x_2836_; 
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 1, v_x_2825_);
v___x_2836_ = v___x_2832_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_head_2829_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_x_2825_);
v___x_2836_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
v_x_2824_ = v_tail_2830_;
v_x_2825_ = v___x_2836_;
goto _start;
}
}
v___jp_2839_:
{
if (v_a_2840_ == 0)
{
lean_del_object(v___x_2832_);
lean_dec(v_head_2829_);
v_x_2824_ = v_tail_2830_;
goto _start;
}
else
{
goto v___jp_2834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v___x_2846_, lean_object* v_x_2847_, lean_object* v_x_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
uint8_t v___x_51076__boxed_2851_; lean_object* v_res_2852_; 
v___x_51076__boxed_2851_ = lean_unbox(v___x_2846_);
v_res_2852_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_51076__boxed_2851_, v_x_2847_, v_x_2848_, v___y_2849_);
lean_dec(v___y_2849_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_2853_, lean_object* v_a_2854_){
_start:
{
if (lean_obj_tag(v_a_2853_) == 0)
{
lean_object* v___x_2855_; 
v___x_2855_ = lean_array_to_list(v_a_2854_);
return v___x_2855_;
}
else
{
lean_object* v_head_2856_; lean_object* v_tail_2857_; lean_object* v___x_2858_; 
v_head_2856_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_head_2856_);
v_tail_2857_ = lean_ctor_get(v_a_2853_, 1);
lean_inc(v_tail_2857_);
lean_dec_ref(v_a_2853_);
v___x_2858_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2854_, v_head_2856_);
v_a_2853_ = v_tail_2857_;
v_a_2854_ = v___x_2858_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
if (lean_obj_tag(v_a_2861_) == 0)
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v_goals_2860_);
v___x_2869_ = lean_array_to_list(v_a_2862_);
v___x_2870_ = lean_array_to_list(v_a_2863_);
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
else
{
lean_object* v_head_2873_; lean_object* v_tail_2874_; lean_object* v___x_2875_; 
v_head_2873_ = lean_ctor_get(v_a_2861_, 0);
lean_inc(v_head_2873_);
v_tail_2874_ = lean_ctor_get(v_a_2861_, 1);
lean_inc(v_tail_2874_);
lean_dec_ref(v_a_2861_);
lean_inc(v___y_2867_);
lean_inc_ref(v___y_2866_);
lean_inc(v___y_2865_);
lean_inc_ref(v___y_2864_);
lean_inc(v_head_2873_);
lean_inc(v_goals_2860_);
v___x_2875_ = l_Lean_MVarId_isIndependentOf(v_goals_2860_, v_head_2873_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; uint8_t v___x_2877_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = lean_unbox(v_a_2876_);
lean_dec(v_a_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
v___x_2878_ = lean_array_push(v_a_2863_, v_head_2873_);
v_a_2861_ = v_tail_2874_;
v_a_2863_ = v___x_2878_;
goto _start;
}
else
{
lean_object* v___x_2880_; 
v___x_2880_ = lean_array_push(v_a_2862_, v_head_2873_);
v_a_2861_ = v_tail_2874_;
v_a_2862_ = v___x_2880_;
goto _start;
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_tail_2874_);
lean_dec(v_head_2873_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_a_2863_);
lean_dec_ref(v_a_2862_);
lean_dec(v_goals_2860_);
v_a_2882_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2875_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2875_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
if (lean_obj_tag(v_a_2900_) == 0)
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_array_to_list(v_a_2901_);
return v___x_2902_;
}
else
{
lean_object* v_head_2903_; 
v_head_2903_ = lean_ctor_get(v_a_2900_, 0);
if (lean_obj_tag(v_head_2903_) == 0)
{
lean_object* v_tail_2904_; lean_object* v_val_2905_; lean_object* v___x_2906_; 
lean_inc_ref(v_head_2903_);
v_tail_2904_ = lean_ctor_get(v_a_2900_, 1);
lean_inc(v_tail_2904_);
lean_dec_ref(v_a_2900_);
v_val_2905_ = lean_ctor_get(v_head_2903_, 0);
lean_inc(v_val_2905_);
lean_dec_ref(v_head_2903_);
v___x_2906_ = lean_array_push(v_a_2901_, v_val_2905_);
v_a_2900_ = v_tail_2904_;
v_a_2901_ = v___x_2906_;
goto _start;
}
else
{
lean_object* v_tail_2908_; 
v_tail_2908_ = lean_ctor_get(v_a_2900_, 1);
lean_inc(v_tail_2908_);
lean_dec_ref(v_a_2900_);
v_a_2900_ = v_tail_2908_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
if (lean_obj_tag(v_x_2911_) == 0)
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec_ref(v_f_2910_);
v___x_2918_ = l_List_reverse___redArg(v_x_2912_);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
else
{
lean_object* v_head_2920_; lean_object* v_tail_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2966_; 
v_head_2920_ = lean_ctor_get(v_x_2911_, 0);
v_tail_2921_ = lean_ctor_get(v_x_2911_, 1);
v_isSharedCheck_2966_ = !lean_is_exclusive(v_x_2911_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2923_ = v_x_2911_;
v_isShared_2924_ = v_isSharedCheck_2966_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_tail_2921_);
lean_inc(v_head_2920_);
lean_dec(v_x_2911_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2966_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v_a_2926_; lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_Meta_saveState___redArg(v___y_2914_, v___y_2916_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2933_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v___x_2931_);
lean_inc_ref(v_f_2910_);
lean_inc(v___y_2916_);
lean_inc_ref(v___y_2915_);
lean_inc(v___y_2914_);
lean_inc_ref(v___y_2913_);
lean_inc(v_head_2920_);
v___x_2933_ = lean_apply_6(v_f_2910_, v_head_2920_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, lean_box(0));
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2935_; 
lean_dec(v_a_2932_);
lean_dec(v_head_2920_);
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref(v___x_2933_);
v___x_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_a_2934_);
v_a_2926_ = v___x_2935_;
goto v___jp_2925_;
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2957_; 
v_a_2936_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2938_ = v___x_2933_;
v_isShared_2939_ = v_isSharedCheck_2957_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2933_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2957_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
uint8_t v___y_2941_; uint8_t v___x_2955_; 
v___x_2955_ = l_Lean_Exception_isInterrupt(v_a_2936_);
if (v___x_2955_ == 0)
{
uint8_t v___x_2956_; 
lean_inc(v_a_2936_);
v___x_2956_ = l_Lean_Exception_isRuntime(v_a_2936_);
v___y_2941_ = v___x_2956_;
goto v___jp_2940_;
}
else
{
v___y_2941_ = v___x_2955_;
goto v___jp_2940_;
}
v___jp_2940_:
{
if (v___y_2941_ == 0)
{
lean_object* v___x_2942_; 
lean_del_object(v___x_2938_);
lean_dec(v_a_2936_);
v___x_2942_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2932_, v___y_2914_, v___y_2916_);
lean_dec(v_a_2932_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v___x_2943_; 
lean_dec_ref(v___x_2942_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_head_2920_);
v_a_2926_ = v___x_2943_;
goto v___jp_2925_;
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_del_object(v___x_2923_);
lean_dec(v_tail_2921_);
lean_dec(v_head_2920_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v_x_2912_);
lean_dec_ref(v_f_2910_);
v_a_2944_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2942_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2942_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
else
{
lean_object* v___x_2953_; 
lean_dec(v_a_2932_);
lean_del_object(v___x_2923_);
lean_dec(v_tail_2921_);
lean_dec(v_head_2920_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v_x_2912_);
lean_dec_ref(v_f_2910_);
if (v_isShared_2939_ == 0)
{
v___x_2953_ = v___x_2938_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2936_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_del_object(v___x_2923_);
lean_dec(v_tail_2921_);
lean_dec(v_head_2920_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v_x_2912_);
lean_dec_ref(v_f_2910_);
v_a_2958_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2931_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2931_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
v___jp_2925_:
{
lean_object* v___x_2928_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v_x_2912_);
lean_ctor_set(v___x_2923_, 0, v_a_2926_);
v___x_2928_ = v___x_2923_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2926_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_x_2912_);
v___x_2928_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
v_x_2911_ = v_tail_2921_;
v_x_2912_ = v___x_2928_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_2967_, lean_object* v_x_2968_, lean_object* v_x_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2967_, v_x_2968_, v_x_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_2976_, lean_object* v_a_2977_){
_start:
{
if (lean_obj_tag(v_a_2976_) == 0)
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_array_to_list(v_a_2977_);
return v___x_2978_;
}
else
{
lean_object* v_head_2979_; 
v_head_2979_ = lean_ctor_get(v_a_2976_, 0);
if (lean_obj_tag(v_head_2979_) == 1)
{
lean_object* v_tail_2980_; lean_object* v_val_2981_; lean_object* v___x_2982_; 
lean_inc_ref(v_head_2979_);
v_tail_2980_ = lean_ctor_get(v_a_2976_, 1);
lean_inc(v_tail_2980_);
lean_dec_ref(v_a_2976_);
v_val_2981_ = lean_ctor_get(v_head_2979_, 0);
lean_inc(v_val_2981_);
lean_dec_ref(v_head_2979_);
v___x_2982_ = lean_array_push(v_a_2977_, v_val_2981_);
v_a_2976_ = v_tail_2980_;
v_a_2977_ = v___x_2982_;
goto _start;
}
else
{
lean_object* v_tail_2984_; 
v_tail_2984_ = lean_ctor_get(v_a_2976_, 1);
lean_inc(v_tail_2984_);
lean_dec_ref(v_a_2976_);
v_a_2976_ = v_tail_2984_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_2986_, lean_object* v_f_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_box(0);
v___x_2994_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2987_, v_L_2986_, v___x_2993_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3006_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3006_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3006_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_2999_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_2995_);
v___x_3000_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_2995_, v___x_2999_);
v___x_3001_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_2995_, v___x_2999_);
v___x_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3000_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_3002_);
v___x_3004_ = v___x_2997_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
v_a_3007_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2994_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2994_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* v_L_3015_, lean_object* v_f_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_3015_, v_f_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t v___x_3023_, uint8_t v___x_3024_, lean_object* v_x_3025_, lean_object* v_x_3026_, lean_object* v___y_3027_){
_start:
{
if (lean_obj_tag(v_x_3025_) == 0)
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_x_3026_);
return v___x_3029_;
}
else
{
lean_object* v_head_3030_; lean_object* v_tail_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3045_; 
v_head_3030_ = lean_ctor_get(v_x_3025_, 0);
v_tail_3031_ = lean_ctor_get(v_x_3025_, 1);
v_isSharedCheck_3045_ = !lean_is_exclusive(v_x_3025_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3033_ = v_x_3025_;
v_isShared_3034_ = v_isSharedCheck_3045_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_tail_3031_);
lean_inc(v_head_3030_);
lean_dec(v_x_3025_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3045_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
uint8_t v_a_3036_; lean_object* v___x_3042_; lean_object* v_a_3043_; uint8_t v___x_3044_; 
v___x_3042_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(v_head_3030_, v___y_3027_);
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3042_);
v___x_3044_ = lean_unbox(v_a_3043_);
lean_dec(v_a_3043_);
if (v___x_3044_ == 0)
{
v_a_3036_ = v___x_3023_;
goto v___jp_3035_;
}
else
{
v_a_3036_ = v___x_3024_;
goto v___jp_3035_;
}
v___jp_3035_:
{
if (v_a_3036_ == 0)
{
lean_del_object(v___x_3033_);
lean_dec(v_head_3030_);
v_x_3025_ = v_tail_3031_;
goto _start;
}
else
{
lean_object* v___x_3039_; 
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 1, v_x_3026_);
v___x_3039_ = v___x_3033_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_head_3030_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v_x_3026_);
v___x_3039_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
v_x_3025_ = v_tail_3031_;
v_x_3026_ = v___x_3039_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* v___x_3046_, lean_object* v___x_3047_, lean_object* v_x_3048_, lean_object* v_x_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
uint8_t v___x_51430__boxed_3052_; uint8_t v___x_51431__boxed_3053_; lean_object* v_res_3054_; 
v___x_51430__boxed_3052_ = lean_unbox(v___x_3046_);
v___x_51431__boxed_3053_ = lean_unbox(v___x_3047_);
v_res_3054_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_51430__boxed_3052_, v___x_51431__boxed_3053_, v_x_3048_, v_x_3049_, v___y_3050_);
lean_dec(v___y_3050_);
return v_res_3054_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
v___x_3057_ = l_Lean_stringToMessageData(v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_3060_, lean_object* v_trace_3061_, lean_object* v_next_3062_, lean_object* v_orig_3063_, lean_object* v_goals_3064_, lean_object* v_remaining_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2));
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_remaining_3065_);
lean_inc(v_goals_3064_);
v___x_3075_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_3064_, v_remaining_3065_, v___x_3074_, v___x_3074_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v_fst_3077_; lean_object* v_snd_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_4320_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref(v___x_3075_);
v_fst_3077_ = lean_ctor_get(v_a_3076_, 0);
v_snd_3078_ = lean_ctor_get(v_a_3076_, 1);
v_isSharedCheck_4320_ = !lean_is_exclusive(v_a_3076_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_3080_ = v_a_3076_;
v_isShared_3081_ = v_isSharedCheck_4320_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_snd_3078_);
lean_inc(v_fst_3077_);
lean_dec(v_a_3076_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_4320_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
uint8_t v___x_3082_; 
v___x_3082_ = l_List_isEmpty___redArg(v_fst_3077_);
if (v___x_3082_ == 0)
{
lean_object* v_options_3083_; uint8_t v_hasTrace_3084_; lean_object* v___f_3085_; 
lean_dec(v_remaining_3065_);
v_options_3083_ = lean_ctor_get(v_a_3068_, 2);
v_hasTrace_3084_ = lean_ctor_get_uint8(v_options_3083_, sizeof(void*)*1);
lean_inc(v_orig_3063_);
lean_inc_ref(v_next_3062_);
lean_inc(v_trace_3061_);
lean_inc_ref(v_cfg_3060_);
v___f_3085_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3085_, 0, v_cfg_3060_);
lean_closure_set(v___f_3085_, 1, v_trace_3061_);
lean_closure_set(v___f_3085_, 2, v_next_3062_);
lean_closure_set(v___f_3085_, 3, v_orig_3063_);
if (v_hasTrace_3084_ == 0)
{
lean_object* v___x_3086_; 
lean_del_object(v___x_3080_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
v___x_3086_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3077_, v___f_3085_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3156_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3089_ = v___x_3086_;
v_isShared_3090_ = v_isSharedCheck_3156_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3156_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v_fst_3091_; lean_object* v_snd_3092_; lean_object* v___x_3093_; lean_object* v_a_3095_; lean_object* v___y_3102_; lean_object* v___y_3105_; lean_object* v___y_3106_; uint8_t v___y_3107_; lean_object* v___y_3118_; lean_object* v_a_3133_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v_fst_3091_ = lean_ctor_get(v_a_3087_, 0);
lean_inc(v_fst_3091_);
v_snd_3092_ = lean_ctor_get(v_a_3087_, 1);
lean_inc(v_snd_3092_);
lean_dec(v_a_3087_);
v___x_3093_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3092_, v___x_3074_);
v___x_3151_ = lean_box(0);
v___x_3152_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_hasTrace_3084_, v_goals_3064_, v___x_3151_, v_a_3067_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3154_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref(v___x_3152_);
v___x_3154_ = l_List_reverse___redArg(v_a_3153_);
v_a_3133_ = v___x_3154_;
goto v___jp_3132_;
}
else
{
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3155_; 
v_a_3155_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3155_);
lean_dec_ref(v___x_3152_);
v_a_3133_ = v_a_3155_;
goto v___jp_3132_;
}
else
{
lean_dec(v___x_3093_);
lean_dec(v_fst_3091_);
lean_del_object(v___x_3089_);
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
return v___x_3152_;
}
}
v___jp_3094_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3099_; 
v___x_3096_ = l_List_appendTR___redArg(v___x_3093_, v_fst_3091_);
v___x_3097_ = l_List_appendTR___redArg(v___x_3096_, v_a_3095_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3097_);
v___x_3099_ = v___x_3089_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
v___jp_3101_:
{
if (lean_obj_tag(v___y_3102_) == 0)
{
lean_object* v_a_3103_; 
v_a_3103_ = lean_ctor_get(v___y_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref(v___y_3102_);
v_a_3095_ = v_a_3103_;
goto v___jp_3094_;
}
else
{
lean_dec(v___x_3093_);
lean_dec(v_fst_3091_);
lean_del_object(v___x_3089_);
return v___y_3102_;
}
}
v___jp_3104_:
{
if (v___y_3107_ == 0)
{
lean_object* v___x_3108_; 
lean_dec_ref(v___y_3105_);
v___x_3108_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3106_, v_a_3067_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec(v_a_3067_);
lean_dec_ref(v___y_3106_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_dec_ref(v___x_3108_);
v_a_3095_ = v_snd_3078_;
goto v___jp_3094_;
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec(v___x_3093_);
lean_dec(v_fst_3091_);
lean_del_object(v___x_3089_);
lean_dec(v_snd_3078_);
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3108_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_dec_ref(v___y_3106_);
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec(v_a_3067_);
v___y_3102_ = v___y_3105_;
goto v___jp_3101_;
}
}
v___jp_3117_:
{
uint8_t v___x_3119_; 
v___x_3119_ = l_List_isEmpty___redArg(v_fst_3091_);
lean_dec(v_fst_3091_);
if (v___x_3119_ == 0)
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
lean_dec(v___y_3118_);
lean_dec(v___x_3093_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
v___x_3120_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3121_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3120_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; 
v___x_3122_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3118_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3131_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3131_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3131_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
v___x_3127_ = l_List_appendTR___redArg(v___x_3093_, v_a_3123_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v___x_3127_);
v___x_3129_ = v___x_3125_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
else
{
lean_dec(v___x_3093_);
return v___x_3122_;
}
}
}
v___jp_3132_:
{
uint8_t v_commitIndependentGoals_3134_; lean_object* v___x_3135_; 
v_commitIndependentGoals_3134_ = lean_ctor_get_uint8(v_cfg_3060_, sizeof(void*)*4);
lean_inc(v___x_3093_);
v___x_3135_ = l_List_appendTR___redArg(v_a_3133_, v___x_3093_);
if (v_commitIndependentGoals_3134_ == 0)
{
lean_del_object(v___x_3089_);
v___y_3118_ = v___x_3135_;
goto v___jp_3117_;
}
else
{
uint8_t v___x_3136_; 
v___x_3136_ = l_List_isEmpty___redArg(v___x_3093_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_Meta_saveState___redArg(v_a_3067_, v_a_3069_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3139_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref(v___x_3137_);
lean_inc(v_a_3069_);
lean_inc(v_a_3067_);
lean_inc(v_snd_3078_);
v___x_3139_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___x_3135_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_dec(v_a_3138_);
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec(v_a_3067_);
v___y_3102_ = v___x_3139_;
goto v___jp_3101_;
}
else
{
lean_object* v_a_3140_; uint8_t v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
v___x_3141_ = l_Lean_Exception_isInterrupt(v_a_3140_);
if (v___x_3141_ == 0)
{
uint8_t v___x_3142_; 
v___x_3142_ = l_Lean_Exception_isRuntime(v_a_3140_);
v___y_3105_ = v___x_3139_;
v___y_3106_ = v_a_3138_;
v___y_3107_ = v___x_3142_;
goto v___jp_3104_;
}
else
{
lean_dec(v_a_3140_);
v___y_3105_ = v___x_3139_;
v___y_3106_ = v_a_3138_;
v___y_3107_ = v___x_3141_;
goto v___jp_3104_;
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec(v___x_3135_);
lean_dec(v___x_3093_);
lean_dec(v_fst_3091_);
lean_del_object(v___x_3089_);
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
v_a_3143_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3137_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3137_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
else
{
lean_del_object(v___x_3089_);
v___y_3118_ = v___x_3135_;
goto v___jp_3117_;
}
}
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
v_a_3157_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3086_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3086_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
else
{
lean_object* v___x_3165_; 
lean_inc(v_trace_3061_);
v___x_3165_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_3061_, v_a_3068_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___f_3167_; lean_object* v___x_3168_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v_a_3172_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v_a_3190_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v_a_3195_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v_a_3202_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; uint8_t v___y_3220_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3243_; lean_object* v___y_3244_; uint8_t v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v_a_3249_; lean_object* v___y_3259_; lean_object* v___y_3260_; uint8_t v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v_a_3265_; lean_object* v___y_3268_; lean_object* v___y_3269_; uint8_t v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v_a_3274_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; uint8_t v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v_a_3285_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; uint8_t v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; uint8_t v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; uint8_t v___y_3311_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; uint8_t v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3332_; lean_object* v___y_3333_; uint8_t v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; uint8_t v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; uint8_t v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; uint8_t v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v_a_3363_; lean_object* v___y_3370_; uint8_t v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v_a_3376_; lean_object* v___y_3389_; uint8_t v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v_a_3395_; lean_object* v___y_3398_; lean_object* v___y_3399_; uint8_t v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v_a_3406_; lean_object* v___y_3410_; uint8_t v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v_a_3416_; lean_object* v___y_3419_; uint8_t v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3429_; uint8_t v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; uint8_t v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; uint8_t v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3453_; lean_object* v___y_3454_; uint8_t v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3465_; lean_object* v___y_3466_; uint8_t v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; uint8_t v___y_3475_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; uint8_t v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; uint8_t v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; uint8_t v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v_a_3505_; uint8_t v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; uint8_t v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3535_; lean_object* v___y_3536_; uint8_t v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; uint8_t v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v_a_3556_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v_a_3563_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v_a_3576_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v_a_3583_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v_a_3589_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3598_; uint8_t v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v_a_3604_; uint8_t v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v_a_3623_; lean_object* v___y_3626_; lean_object* v___y_3627_; uint8_t v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v_a_3634_; uint8_t v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v_a_3644_; lean_object* v___y_3647_; uint8_t v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; uint8_t v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; uint8_t v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; uint8_t v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3681_; uint8_t v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3693_; lean_object* v___y_3694_; uint8_t v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; uint8_t v___y_3703_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; uint8_t v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; uint8_t v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; uint8_t v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v_a_3733_; lean_object* v___y_3738_; uint8_t v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v_a_3744_; lean_object* v___y_3754_; uint8_t v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v_a_3760_; lean_object* v___y_3763_; lean_object* v___y_3764_; uint8_t v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v_a_3771_; lean_object* v___y_3775_; uint8_t v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v_a_3781_; lean_object* v___y_3784_; uint8_t v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3794_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; uint8_t v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; uint8_t v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3820_; lean_object* v___y_3821_; uint8_t v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; uint8_t v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; uint8_t v___y_3842_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; uint8_t v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; uint8_t v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; uint8_t v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v_a_3872_; uint8_t v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; uint8_t v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3907_; uint8_t v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; uint8_t v___y_3932_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; uint8_t v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v_a_3954_; uint8_t v___x_4015_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref(v___x_3165_);
lean_inc(v_snd_3078_);
lean_inc(v_fst_3077_);
v___f_3167_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3167_, 0, v_fst_3077_);
lean_closure_set(v___f_3167_, 1, v_snd_3078_);
v___x_3168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
v___x_4015_ = lean_unbox(v_a_3166_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; uint8_t v___x_4017_; 
v___x_4016_ = l_Lean_trace_profiler;
v___x_4017_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_3083_, v___x_4016_);
if (v___x_4017_ == 0)
{
lean_object* v___x_4018_; 
lean_dec_ref(v___f_3167_);
lean_dec(v_a_3166_);
lean_del_object(v___x_3080_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
v___x_4018_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3077_, v___f_3085_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v_fst_4020_; lean_object* v_snd_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4300_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_a_4019_);
lean_dec_ref(v___x_4018_);
v_fst_4020_ = lean_ctor_get(v_a_4019_, 0);
v_snd_4021_ = lean_ctor_get(v_a_4019_, 1);
v_isSharedCheck_4300_ = !lean_is_exclusive(v_a_4019_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4023_ = v_a_4019_;
v_isShared_4024_ = v_isSharedCheck_4300_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_snd_4021_);
lean_inc(v_fst_4020_);
lean_dec(v_a_4019_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4300_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4025_; 
lean_inc(v_trace_3061_);
v___x_4025_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_3061_, v_a_3068_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4291_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4028_ = v___x_4025_;
v_isShared_4029_ = v_isSharedCheck_4291_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_4025_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4291_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4030_; lean_object* v___y_4032_; lean_object* v_a_4045_; lean_object* v___y_4052_; lean_object* v___y_4055_; lean_object* v___y_4056_; uint8_t v___y_4057_; lean_object* v___y_4068_; lean_object* v_a_4084_; lean_object* v___f_4088_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v_a_4092_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v_a_4107_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v_a_4112_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v_a_4118_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; uint8_t v___y_4130_; uint8_t v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; uint8_t v___y_4153_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; uint8_t v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v_a_4171_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v_a_4178_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v_a_4194_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v_a_4199_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v_a_4205_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4214_; lean_object* v___y_4215_; uint8_t v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; uint8_t v___y_4238_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; uint8_t v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v_a_4256_; lean_object* v___x_4260_; uint8_t v___x_4286_; 
v___x_4030_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_4021_, v___x_3074_);
lean_inc(v___x_4030_);
lean_inc(v_fst_4020_);
v___f_4088_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_4088_, 0, v_fst_4020_);
lean_closure_set(v___f_4088_, 1, v___x_4030_);
v___x_4260_ = lean_box(0);
v___x_4286_ = lean_unbox(v_a_4026_);
if (v___x_4286_ == 0)
{
if (v___x_4017_ == 0)
{
lean_object* v___x_4287_; 
lean_dec_ref(v___f_4088_);
lean_dec(v_a_4026_);
lean_del_object(v___x_4023_);
v___x_4287_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3084_, v___x_4017_, v_goals_3064_, v___x_4260_, v_a_3067_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4289_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref(v___x_4287_);
v___x_4289_ = l_List_reverse___redArg(v_a_4288_);
v_a_4084_ = v___x_4289_;
goto v___jp_4083_;
}
else
{
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4290_; 
v_a_4290_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4290_);
lean_dec_ref(v___x_4287_);
v_a_4084_ = v_a_4290_;
goto v___jp_4083_;
}
else
{
lean_dec(v___x_4030_);
lean_del_object(v___x_4028_);
lean_dec(v_fst_4020_);
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
return v___x_4287_;
}
}
}
else
{
lean_inc_ref(v_options_3083_);
lean_del_object(v___x_4028_);
goto v___jp_4261_;
}
}
else
{
lean_inc_ref(v_options_3083_);
lean_del_object(v___x_4028_);
goto v___jp_4261_;
}
v___jp_4031_:
{
uint8_t v___x_4033_; 
v___x_4033_ = l_List_isEmpty___redArg(v_fst_4020_);
lean_dec(v_fst_4020_);
if (v___x_4033_ == 0)
{
lean_dec(v___y_4032_);
lean_dec(v___x_4030_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
goto v___jp_3071_;
}
else
{
if (v___x_4017_ == 0)
{
lean_object* v___x_4034_; 
v___x_4034_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_4032_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4043_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4037_ = v___x_4034_;
v_isShared_4038_ = v_isSharedCheck_4043_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4034_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4043_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4039_; lean_object* v___x_4041_; 
v___x_4039_ = l_List_appendTR___redArg(v___x_4030_, v_a_4035_);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 0, v___x_4039_);
v___x_4041_ = v___x_4037_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v___x_4039_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
else
{
lean_dec(v___x_4030_);
return v___x_4034_;
}
}
else
{
lean_dec(v___y_4032_);
lean_dec(v___x_4030_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
goto v___jp_3071_;
}
}
}
v___jp_4044_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4049_; 
v___x_4046_ = l_List_appendTR___redArg(v___x_4030_, v_fst_4020_);
v___x_4047_ = l_List_appendTR___redArg(v___x_4046_, v_a_4045_);
if (v_isShared_4029_ == 0)
{
lean_ctor_set(v___x_4028_, 0, v___x_4047_);
v___x_4049_ = v___x_4028_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_4047_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
v___jp_4051_:
{
if (lean_obj_tag(v___y_4052_) == 0)
{
lean_object* v_a_4053_; 
v_a_4053_ = lean_ctor_get(v___y_4052_, 0);
lean_inc(v_a_4053_);
lean_dec_ref(v___y_4052_);
v_a_4045_ = v_a_4053_;
goto v___jp_4044_;
}
else
{
lean_dec(v___x_4030_);
lean_del_object(v___x_4028_);
lean_dec(v_fst_4020_);
return v___y_4052_;
}
}
v___jp_4054_:
{
if (v___y_4057_ == 0)
{
lean_object* v___x_4058_; 
lean_dec_ref(v___y_4055_);
v___x_4058_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4056_, v_a_3067_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec(v_a_3067_);
lean_dec_ref(v___y_4056_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_dec_ref(v___x_4058_);
v_a_4045_ = v_snd_3078_;
goto v___jp_4044_;
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
lean_dec(v___x_4030_);
lean_del_object(v___x_4028_);
lean_dec(v_fst_4020_);
lean_dec(v_snd_3078_);
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4058_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4058_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
else
{
lean_dec_ref(v___y_4056_);
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec(v_a_3067_);
v___y_4052_ = v___y_4055_;
goto v___jp_4051_;
}
}
v___jp_4067_:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_Meta_saveState___redArg(v_a_3067_, v_a_3069_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4071_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref(v___x_4069_);
lean_inc(v_a_3069_);
lean_inc(v_a_3067_);
lean_inc(v_snd_3078_);
v___x_4071_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_4068_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_dec(v_a_4070_);
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec(v_a_3067_);
v___y_4052_ = v___x_4071_;
goto v___jp_4051_;
}
else
{
lean_object* v_a_4072_; uint8_t v___x_4073_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
v___x_4073_ = l_Lean_Exception_isInterrupt(v_a_4072_);
if (v___x_4073_ == 0)
{
uint8_t v___x_4074_; 
v___x_4074_ = l_Lean_Exception_isRuntime(v_a_4072_);
v___y_4055_ = v___x_4071_;
v___y_4056_ = v_a_4070_;
v___y_4057_ = v___x_4074_;
goto v___jp_4054_;
}
else
{
lean_dec(v_a_4072_);
v___y_4055_ = v___x_4071_;
v___y_4056_ = v_a_4070_;
v___y_4057_ = v___x_4073_;
goto v___jp_4054_;
}
}
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
lean_dec(v___y_4068_);
lean_dec(v___x_4030_);
lean_del_object(v___x_4028_);
lean_dec(v_fst_4020_);
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
v_a_4075_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4069_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4069_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
v___jp_4083_:
{
uint8_t v_commitIndependentGoals_4085_; lean_object* v___x_4086_; 
v_commitIndependentGoals_4085_ = lean_ctor_get_uint8(v_cfg_3060_, sizeof(void*)*4);
lean_inc(v___x_4030_);
v___x_4086_ = l_List_appendTR___redArg(v_a_4084_, v___x_4030_);
if (v_commitIndependentGoals_4085_ == 0)
{
lean_del_object(v___x_4028_);
v___y_4032_ = v___x_4086_;
goto v___jp_4031_;
}
else
{
uint8_t v___x_4087_; 
v___x_4087_ = l_List_isEmpty___redArg(v___x_4030_);
if (v___x_4087_ == 0)
{
v___y_4068_ = v___x_4086_;
goto v___jp_4067_;
}
else
{
if (v___x_4017_ == 0)
{
lean_del_object(v___x_4028_);
v___y_4032_ = v___x_4086_;
goto v___jp_4031_;
}
else
{
v___y_4068_ = v___x_4086_;
goto v___jp_4067_;
}
}
}
}
v___jp_4089_:
{
lean_object* v___x_4093_; double v___x_4094_; double v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4099_; 
v___x_4093_ = lean_io_get_num_heartbeats();
v___x_4094_ = lean_float_of_nat(v___y_4091_);
v___x_4095_ = lean_float_of_nat(v___x_4093_);
v___x_4096_ = lean_box_float(v___x_4094_);
v___x_4097_ = lean_box_float(v___x_4095_);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 1, v___x_4097_);
lean_ctor_set(v___x_4023_, 0, v___x_4096_);
v___x_4099_ = v___x_4023_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4096_);
lean_ctor_set(v_reuseFailAlloc_4103_, 1, v___x_4097_);
v___x_4099_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
lean_object* v___x_4100_; uint8_t v___x_4101_; lean_object* v___x_4102_; 
v___x_4100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4100_, 0, v_a_4092_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
v___x_4101_ = lean_unbox(v_a_4026_);
lean_dec(v_a_4026_);
v___x_4102_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3061_, v_hasTrace_3084_, v___x_3168_, v_options_3083_, v___x_4101_, v___y_4090_, v___f_4088_, v___x_4100_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec_ref(v_options_3083_);
return v___x_4102_;
}
}
v___jp_4104_:
{
lean_object* v___x_4108_; 
v___x_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4108_, 0, v_a_4107_);
v___y_4090_ = v___y_4105_;
v___y_4091_ = v___y_4106_;
v_a_4092_ = v___x_4108_;
goto v___jp_4089_;
}
v___jp_4109_:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4113_ = l_List_appendTR___redArg(v___x_4030_, v_fst_4020_);
v___x_4114_ = l_List_appendTR___redArg(v___x_4113_, v_a_4112_);
v___y_4105_ = v___y_4110_;
v___y_4106_ = v___y_4111_;
v_a_4107_ = v___x_4114_;
goto v___jp_4104_;
}
v___jp_4115_:
{
lean_object* v___x_4119_; 
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v_a_4118_);
v___y_4090_ = v___y_4116_;
v___y_4091_ = v___y_4117_;
v_a_4092_ = v___x_4119_;
goto v___jp_4089_;
}
v___jp_4120_:
{
if (lean_obj_tag(v___y_4123_) == 0)
{
lean_object* v_a_4124_; 
v_a_4124_ = lean_ctor_get(v___y_4123_, 0);
lean_inc(v_a_4124_);
lean_dec_ref(v___y_4123_);
v___y_4105_ = v___y_4121_;
v___y_4106_ = v___y_4122_;
v_a_4107_ = v_a_4124_;
goto v___jp_4104_;
}
else
{
lean_object* v_a_4125_; 
v_a_4125_ = lean_ctor_get(v___y_4123_, 0);
lean_inc(v_a_4125_);
lean_dec_ref(v___y_4123_);
v___y_4116_ = v___y_4121_;
v___y_4117_ = v___y_4122_;
v_a_4118_ = v_a_4125_;
goto v___jp_4115_;
}
}
v___jp_4126_:
{
if (v___y_4130_ == 0)
{
lean_object* v___x_4131_; 
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_4131_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_4127_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v___x_4133_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref(v___x_4131_);
v___x_4133_ = l_List_appendTR___redArg(v___x_4030_, v_a_4132_);
v___y_4105_ = v___y_4128_;
v___y_4106_ = v___y_4129_;
v_a_4107_ = v___x_4133_;
goto v___jp_4104_;
}
else
{
lean_dec(v___x_4030_);
v___y_4121_ = v___y_4128_;
v___y_4122_ = v___y_4129_;
v___y_4123_ = v___x_4131_;
goto v___jp_4120_;
}
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
lean_dec(v___y_4127_);
lean_dec(v___x_4030_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___x_4134_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4135_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4134_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_4121_ = v___y_4128_;
v___y_4122_ = v___y_4129_;
v___y_4123_ = v___x_4135_;
goto v___jp_4120_;
}
}
v___jp_4136_:
{
uint8_t v___x_4141_; 
v___x_4141_ = l_List_isEmpty___redArg(v_fst_4020_);
lean_dec(v_fst_4020_);
if (v___x_4141_ == 0)
{
v___y_4127_ = v___y_4138_;
v___y_4128_ = v___y_4139_;
v___y_4129_ = v___y_4140_;
v___y_4130_ = v___y_4137_;
goto v___jp_4126_;
}
else
{
v___y_4127_ = v___y_4138_;
v___y_4128_ = v___y_4139_;
v___y_4129_ = v___y_4140_;
v___y_4130_ = v___x_4017_;
goto v___jp_4126_;
}
}
v___jp_4142_:
{
if (lean_obj_tag(v___y_4145_) == 0)
{
lean_object* v_a_4146_; 
v_a_4146_ = lean_ctor_get(v___y_4145_, 0);
lean_inc(v_a_4146_);
lean_dec_ref(v___y_4145_);
v___y_4110_ = v___y_4143_;
v___y_4111_ = v___y_4144_;
v_a_4112_ = v_a_4146_;
goto v___jp_4109_;
}
else
{
lean_object* v_a_4147_; 
lean_dec(v___x_4030_);
lean_dec(v_fst_4020_);
v_a_4147_ = lean_ctor_get(v___y_4145_, 0);
lean_inc(v_a_4147_);
lean_dec_ref(v___y_4145_);
v___y_4116_ = v___y_4143_;
v___y_4117_ = v___y_4144_;
v_a_4118_ = v_a_4147_;
goto v___jp_4115_;
}
}
v___jp_4148_:
{
if (v___y_4153_ == 0)
{
lean_object* v___x_4154_; 
lean_dec_ref(v___y_4149_);
v___x_4154_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4151_, v_a_3067_, v_a_3069_);
lean_dec_ref(v___y_4151_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_dec_ref(v___x_4154_);
v___y_4110_ = v___y_4150_;
v___y_4111_ = v___y_4152_;
v_a_4112_ = v_snd_3078_;
goto v___jp_4109_;
}
else
{
lean_object* v_a_4155_; 
lean_dec(v___x_4030_);
lean_dec(v_fst_4020_);
lean_dec(v_snd_3078_);
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref(v___x_4154_);
v___y_4116_ = v___y_4150_;
v___y_4117_ = v___y_4152_;
v_a_4118_ = v_a_4155_;
goto v___jp_4115_;
}
}
else
{
lean_dec_ref(v___y_4151_);
lean_dec(v_snd_3078_);
v___y_4143_ = v___y_4150_;
v___y_4144_ = v___y_4152_;
v___y_4145_ = v___y_4149_;
goto v___jp_4142_;
}
}
v___jp_4156_:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Lean_Meta_saveState___redArg(v_a_3067_, v_a_3069_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4162_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref(v___x_4160_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_snd_3078_);
lean_inc(v_trace_3061_);
v___x_4162_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_4157_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_dec(v_a_4161_);
lean_dec(v_snd_3078_);
v___y_4143_ = v___y_4158_;
v___y_4144_ = v___y_4159_;
v___y_4145_ = v___x_4162_;
goto v___jp_4142_;
}
else
{
lean_object* v_a_4163_; uint8_t v___x_4164_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
v___x_4164_ = l_Lean_Exception_isInterrupt(v_a_4163_);
if (v___x_4164_ == 0)
{
uint8_t v___x_4165_; 
v___x_4165_ = l_Lean_Exception_isRuntime(v_a_4163_);
v___y_4149_ = v___x_4162_;
v___y_4150_ = v___y_4158_;
v___y_4151_ = v_a_4161_;
v___y_4152_ = v___y_4159_;
v___y_4153_ = v___x_4165_;
goto v___jp_4148_;
}
else
{
lean_dec(v_a_4163_);
v___y_4149_ = v___x_4162_;
v___y_4150_ = v___y_4158_;
v___y_4151_ = v_a_4161_;
v___y_4152_ = v___y_4159_;
v___y_4153_ = v___x_4164_;
goto v___jp_4148_;
}
}
}
else
{
lean_object* v_a_4166_; 
lean_dec(v___y_4157_);
lean_dec(v___x_4030_);
lean_dec(v_fst_4020_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_4166_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4166_);
lean_dec_ref(v___x_4160_);
v___y_4116_ = v___y_4158_;
v___y_4117_ = v___y_4159_;
v_a_4118_ = v_a_4166_;
goto v___jp_4115_;
}
}
v___jp_4167_:
{
uint8_t v_commitIndependentGoals_4172_; lean_object* v___x_4173_; 
v_commitIndependentGoals_4172_ = lean_ctor_get_uint8(v_cfg_3060_, sizeof(void*)*4);
lean_inc(v___x_4030_);
v___x_4173_ = l_List_appendTR___redArg(v_a_4171_, v___x_4030_);
if (v_commitIndependentGoals_4172_ == 0)
{
v___y_4137_ = v___y_4168_;
v___y_4138_ = v___x_4173_;
v___y_4139_ = v___y_4169_;
v___y_4140_ = v___y_4170_;
goto v___jp_4136_;
}
else
{
uint8_t v___x_4174_; 
v___x_4174_ = l_List_isEmpty___redArg(v___x_4030_);
if (v___x_4174_ == 0)
{
v___y_4157_ = v___x_4173_;
v___y_4158_ = v___y_4169_;
v___y_4159_ = v___y_4170_;
goto v___jp_4156_;
}
else
{
if (v___x_4017_ == 0)
{
v___y_4137_ = v___y_4168_;
v___y_4138_ = v___x_4173_;
v___y_4139_ = v___y_4169_;
v___y_4140_ = v___y_4170_;
goto v___jp_4136_;
}
else
{
v___y_4157_ = v___x_4173_;
v___y_4158_ = v___y_4169_;
v___y_4159_ = v___y_4170_;
goto v___jp_4156_;
}
}
}
}
v___jp_4175_:
{
lean_object* v___x_4179_; double v___x_4180_; double v___x_4181_; double v___x_4182_; double v___x_4183_; double v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; lean_object* v___x_4190_; 
v___x_4179_ = lean_io_mono_nanos_now();
v___x_4180_ = lean_float_of_nat(v___y_4177_);
v___x_4181_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_4182_ = lean_float_div(v___x_4180_, v___x_4181_);
v___x_4183_ = lean_float_of_nat(v___x_4179_);
v___x_4184_ = lean_float_div(v___x_4183_, v___x_4181_);
v___x_4185_ = lean_box_float(v___x_4182_);
v___x_4186_ = lean_box_float(v___x_4184_);
v___x_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4185_);
lean_ctor_set(v___x_4187_, 1, v___x_4186_);
v___x_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4188_, 0, v_a_4178_);
lean_ctor_set(v___x_4188_, 1, v___x_4187_);
v___x_4189_ = lean_unbox(v_a_4026_);
lean_dec(v_a_4026_);
v___x_4190_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3061_, v_hasTrace_3084_, v___x_3168_, v_options_3083_, v___x_4189_, v___y_4176_, v___f_4088_, v___x_4188_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec_ref(v_options_3083_);
return v___x_4190_;
}
v___jp_4191_:
{
lean_object* v___x_4195_; 
v___x_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4195_, 0, v_a_4194_);
v___y_4176_ = v___y_4193_;
v___y_4177_ = v___y_4192_;
v_a_4178_ = v___x_4195_;
goto v___jp_4175_;
}
v___jp_4196_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = l_List_appendTR___redArg(v___x_4030_, v_fst_4020_);
v___x_4201_ = l_List_appendTR___redArg(v___x_4200_, v_a_4199_);
v___y_4192_ = v___y_4198_;
v___y_4193_ = v___y_4197_;
v_a_4194_ = v___x_4201_;
goto v___jp_4191_;
}
v___jp_4202_:
{
lean_object* v___x_4206_; 
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v_a_4205_);
v___y_4176_ = v___y_4204_;
v___y_4177_ = v___y_4203_;
v_a_4178_ = v___x_4206_;
goto v___jp_4175_;
}
v___jp_4207_:
{
if (lean_obj_tag(v___y_4210_) == 0)
{
lean_object* v_a_4211_; 
v_a_4211_ = lean_ctor_get(v___y_4210_, 0);
lean_inc(v_a_4211_);
lean_dec_ref(v___y_4210_);
v___y_4192_ = v___y_4209_;
v___y_4193_ = v___y_4208_;
v_a_4194_ = v_a_4211_;
goto v___jp_4191_;
}
else
{
lean_object* v_a_4212_; 
v_a_4212_ = lean_ctor_get(v___y_4210_, 0);
lean_inc(v_a_4212_);
lean_dec_ref(v___y_4210_);
v___y_4203_ = v___y_4209_;
v___y_4204_ = v___y_4208_;
v_a_4205_ = v_a_4212_;
goto v___jp_4202_;
}
}
v___jp_4213_:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4216_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4217_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4216_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_4208_ = v___y_4215_;
v___y_4209_ = v___y_4214_;
v___y_4210_ = v___x_4217_;
goto v___jp_4207_;
}
v___jp_4218_:
{
uint8_t v___x_4223_; 
v___x_4223_ = l_List_isEmpty___redArg(v_fst_4020_);
lean_dec(v_fst_4020_);
if (v___x_4223_ == 0)
{
lean_dec(v___y_4220_);
lean_dec(v___x_4030_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___y_4214_ = v___y_4222_;
v___y_4215_ = v___y_4221_;
goto v___jp_4213_;
}
else
{
if (v___y_4219_ == 0)
{
lean_object* v___x_4224_; 
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_4224_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_4220_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4226_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref(v___x_4224_);
v___x_4226_ = l_List_appendTR___redArg(v___x_4030_, v_a_4225_);
v___y_4192_ = v___y_4222_;
v___y_4193_ = v___y_4221_;
v_a_4194_ = v___x_4226_;
goto v___jp_4191_;
}
else
{
lean_dec(v___x_4030_);
v___y_4208_ = v___y_4221_;
v___y_4209_ = v___y_4222_;
v___y_4210_ = v___x_4224_;
goto v___jp_4207_;
}
}
else
{
lean_dec(v___y_4220_);
lean_dec(v___x_4030_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___y_4214_ = v___y_4222_;
v___y_4215_ = v___y_4221_;
goto v___jp_4213_;
}
}
}
v___jp_4227_:
{
if (lean_obj_tag(v___y_4230_) == 0)
{
lean_object* v_a_4231_; 
v_a_4231_ = lean_ctor_get(v___y_4230_, 0);
lean_inc(v_a_4231_);
lean_dec_ref(v___y_4230_);
v___y_4197_ = v___y_4229_;
v___y_4198_ = v___y_4228_;
v_a_4199_ = v_a_4231_;
goto v___jp_4196_;
}
else
{
lean_object* v_a_4232_; 
lean_dec(v___x_4030_);
lean_dec(v_fst_4020_);
v_a_4232_ = lean_ctor_get(v___y_4230_, 0);
lean_inc(v_a_4232_);
lean_dec_ref(v___y_4230_);
v___y_4203_ = v___y_4228_;
v___y_4204_ = v___y_4229_;
v_a_4205_ = v_a_4232_;
goto v___jp_4202_;
}
}
v___jp_4233_:
{
if (v___y_4238_ == 0)
{
lean_object* v___x_4239_; 
lean_dec_ref(v___y_4235_);
v___x_4239_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4234_, v_a_3067_, v_a_3069_);
lean_dec_ref(v___y_4234_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_dec_ref(v___x_4239_);
v___y_4197_ = v___y_4237_;
v___y_4198_ = v___y_4236_;
v_a_4199_ = v_snd_3078_;
goto v___jp_4196_;
}
else
{
lean_object* v_a_4240_; 
lean_dec(v___x_4030_);
lean_dec(v_fst_4020_);
lean_dec(v_snd_3078_);
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref(v___x_4239_);
v___y_4203_ = v___y_4236_;
v___y_4204_ = v___y_4237_;
v_a_4205_ = v_a_4240_;
goto v___jp_4202_;
}
}
else
{
lean_dec_ref(v___y_4234_);
lean_dec(v_snd_3078_);
v___y_4228_ = v___y_4236_;
v___y_4229_ = v___y_4237_;
v___y_4230_ = v___y_4235_;
goto v___jp_4227_;
}
}
v___jp_4241_:
{
lean_object* v___x_4245_; 
v___x_4245_ = l_Lean_Meta_saveState___redArg(v_a_3067_, v_a_3069_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; lean_object* v___x_4247_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4246_);
lean_dec_ref(v___x_4245_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_snd_3078_);
lean_inc(v_trace_3061_);
v___x_4247_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_4242_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_dec(v_a_4246_);
lean_dec(v_snd_3078_);
v___y_4228_ = v___y_4244_;
v___y_4229_ = v___y_4243_;
v___y_4230_ = v___x_4247_;
goto v___jp_4227_;
}
else
{
lean_object* v_a_4248_; uint8_t v___x_4249_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4248_);
v___x_4249_ = l_Lean_Exception_isInterrupt(v_a_4248_);
if (v___x_4249_ == 0)
{
uint8_t v___x_4250_; 
v___x_4250_ = l_Lean_Exception_isRuntime(v_a_4248_);
v___y_4234_ = v_a_4246_;
v___y_4235_ = v___x_4247_;
v___y_4236_ = v___y_4244_;
v___y_4237_ = v___y_4243_;
v___y_4238_ = v___x_4250_;
goto v___jp_4233_;
}
else
{
lean_dec(v_a_4248_);
v___y_4234_ = v_a_4246_;
v___y_4235_ = v___x_4247_;
v___y_4236_ = v___y_4244_;
v___y_4237_ = v___y_4243_;
v___y_4238_ = v___x_4249_;
goto v___jp_4233_;
}
}
}
else
{
lean_object* v_a_4251_; 
lean_dec(v___y_4242_);
lean_dec(v___x_4030_);
lean_dec(v_fst_4020_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_4251_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4251_);
lean_dec_ref(v___x_4245_);
v___y_4203_ = v___y_4244_;
v___y_4204_ = v___y_4243_;
v_a_4205_ = v_a_4251_;
goto v___jp_4202_;
}
}
v___jp_4252_:
{
uint8_t v_commitIndependentGoals_4257_; lean_object* v___x_4258_; 
v_commitIndependentGoals_4257_ = lean_ctor_get_uint8(v_cfg_3060_, sizeof(void*)*4);
lean_inc(v___x_4030_);
v___x_4258_ = l_List_appendTR___redArg(v_a_4256_, v___x_4030_);
if (v_commitIndependentGoals_4257_ == 0)
{
v___y_4219_ = v___y_4253_;
v___y_4220_ = v___x_4258_;
v___y_4221_ = v___y_4254_;
v___y_4222_ = v___y_4255_;
goto v___jp_4218_;
}
else
{
uint8_t v___x_4259_; 
v___x_4259_ = l_List_isEmpty___redArg(v___x_4030_);
if (v___x_4259_ == 0)
{
v___y_4242_ = v___x_4258_;
v___y_4243_ = v___y_4254_;
v___y_4244_ = v___y_4255_;
goto v___jp_4241_;
}
else
{
if (v___y_4253_ == 0)
{
v___y_4219_ = v___y_4253_;
v___y_4220_ = v___x_4258_;
v___y_4221_ = v___y_4254_;
v___y_4222_ = v___y_4255_;
goto v___jp_4218_;
}
else
{
v___y_4242_ = v___x_4258_;
v___y_4243_ = v___y_4254_;
v___y_4244_ = v___y_4255_;
goto v___jp_4241_;
}
}
}
}
v___jp_4261_:
{
lean_object* v___x_4262_; 
v___x_4262_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_3069_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref(v___x_4262_);
v___x_4264_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4265_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_3083_, v___x_4264_);
if (v___x_4265_ == 0)
{
lean_object* v___x_4266_; lean_object* v___x_4267_; 
lean_del_object(v___x_4023_);
v___x_4266_ = lean_io_mono_nanos_now();
v___x_4267_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3084_, v___x_4017_, v_goals_3064_, v___x_4260_, v_a_3067_);
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v_a_4268_; lean_object* v___x_4269_; 
v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
lean_inc(v_a_4268_);
lean_dec_ref(v___x_4267_);
v___x_4269_ = l_List_reverse___redArg(v_a_4268_);
v___y_4253_ = v___x_4265_;
v___y_4254_ = v_a_4263_;
v___y_4255_ = v___x_4266_;
v_a_4256_ = v___x_4269_;
goto v___jp_4252_;
}
else
{
if (lean_obj_tag(v___x_4267_) == 0)
{
lean_object* v_a_4270_; 
v_a_4270_ = lean_ctor_get(v___x_4267_, 0);
lean_inc(v_a_4270_);
lean_dec_ref(v___x_4267_);
v___y_4253_ = v___x_4265_;
v___y_4254_ = v_a_4263_;
v___y_4255_ = v___x_4266_;
v_a_4256_ = v_a_4270_;
goto v___jp_4252_;
}
else
{
lean_object* v_a_4271_; 
lean_dec(v___x_4030_);
lean_dec(v_fst_4020_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_4271_ = lean_ctor_get(v___x_4267_, 0);
lean_inc(v_a_4271_);
lean_dec_ref(v___x_4267_);
v___y_4203_ = v___x_4266_;
v___y_4204_ = v_a_4263_;
v_a_4205_ = v_a_4271_;
goto v___jp_4202_;
}
}
}
else
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = lean_io_get_num_heartbeats();
v___x_4273_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3084_, v___x_4017_, v_goals_3064_, v___x_4260_, v_a_3067_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4275_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref(v___x_4273_);
v___x_4275_ = l_List_reverse___redArg(v_a_4274_);
v___y_4168_ = v___x_4265_;
v___y_4169_ = v_a_4263_;
v___y_4170_ = v___x_4272_;
v_a_4171_ = v___x_4275_;
goto v___jp_4167_;
}
else
{
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4276_; 
v_a_4276_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4276_);
lean_dec_ref(v___x_4273_);
v___y_4168_ = v___x_4265_;
v___y_4169_ = v_a_4263_;
v___y_4170_ = v___x_4272_;
v_a_4171_ = v_a_4276_;
goto v___jp_4167_;
}
else
{
lean_object* v_a_4277_; 
lean_dec(v___x_4030_);
lean_dec(v_fst_4020_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_4277_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4277_);
lean_dec_ref(v___x_4273_);
v___y_4116_ = v_a_4263_;
v___y_4117_ = v___x_4272_;
v_a_4118_ = v_a_4277_;
goto v___jp_4115_;
}
}
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_dec_ref(v___f_4088_);
lean_dec(v___x_4030_);
lean_dec(v_a_4026_);
lean_del_object(v___x_4023_);
lean_dec(v_fst_4020_);
lean_dec_ref(v_options_3083_);
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
v_a_4278_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4262_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4262_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_del_object(v___x_4023_);
lean_dec(v_snd_4021_);
lean_dec(v_fst_4020_);
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
v_a_4292_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4025_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4025_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v_snd_3078_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
v_a_4301_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4018_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4018_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
else
{
lean_inc_ref(v_options_3083_);
goto v___jp_3958_;
}
}
else
{
lean_inc_ref(v_options_3083_);
goto v___jp_3958_;
}
v___jp_3169_:
{
lean_object* v___x_3173_; double v___x_3174_; double v___x_3175_; double v___x_3176_; double v___x_3177_; double v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3173_ = lean_io_mono_nanos_now();
v___x_3174_ = lean_float_of_nat(v___y_3170_);
v___x_3175_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3176_ = lean_float_div(v___x_3174_, v___x_3175_);
v___x_3177_ = lean_float_of_nat(v___x_3173_);
v___x_3178_ = lean_float_div(v___x_3177_, v___x_3175_);
v___x_3179_ = lean_box_float(v___x_3176_);
v___x_3180_ = lean_box_float(v___x_3178_);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 1, v___x_3180_);
lean_ctor_set(v___x_3080_, 0, v___x_3179_);
v___x_3182_ = v___x_3080_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3183_; uint8_t v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v_a_3172_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_unbox(v_a_3166_);
lean_dec(v_a_3166_);
v___x_3185_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3061_, v_hasTrace_3084_, v___x_3168_, v_options_3083_, v___x_3184_, v___y_3171_, v___f_3167_, v___x_3183_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec_ref(v_options_3083_);
return v___x_3185_;
}
}
v___jp_3187_:
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v_a_3190_);
v___y_3170_ = v___y_3188_;
v___y_3171_ = v___y_3189_;
v_a_3172_ = v___x_3191_;
goto v___jp_3169_;
}
v___jp_3192_:
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3196_, 0, v_a_3195_);
v___y_3170_ = v___y_3193_;
v___y_3171_ = v___y_3194_;
v_a_3172_ = v___x_3196_;
goto v___jp_3169_;
}
v___jp_3197_:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = l_List_appendTR___redArg(v___y_3198_, v___y_3201_);
v___x_3204_ = l_List_appendTR___redArg(v___x_3203_, v_a_3202_);
v___y_3193_ = v___y_3199_;
v___y_3194_ = v___y_3200_;
v_a_3195_ = v___x_3204_;
goto v___jp_3192_;
}
v___jp_3205_:
{
if (lean_obj_tag(v___y_3210_) == 0)
{
lean_object* v_a_3211_; 
v_a_3211_ = lean_ctor_get(v___y_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref(v___y_3210_);
v___y_3198_ = v___y_3206_;
v___y_3199_ = v___y_3207_;
v___y_3200_ = v___y_3208_;
v___y_3201_ = v___y_3209_;
v_a_3202_ = v_a_3211_;
goto v___jp_3197_;
}
else
{
lean_object* v_a_3212_; 
lean_dec(v___y_3209_);
lean_dec(v___y_3206_);
v_a_3212_ = lean_ctor_get(v___y_3210_, 0);
lean_inc(v_a_3212_);
lean_dec_ref(v___y_3210_);
v___y_3188_ = v___y_3207_;
v___y_3189_ = v___y_3208_;
v_a_3190_ = v_a_3212_;
goto v___jp_3187_;
}
}
v___jp_3213_:
{
if (v___y_3220_ == 0)
{
lean_object* v___x_3221_; 
lean_dec_ref(v___y_3216_);
v___x_3221_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3219_, v_a_3067_, v_a_3069_);
lean_dec_ref(v___y_3219_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_dec_ref(v___x_3221_);
v___y_3198_ = v___y_3214_;
v___y_3199_ = v___y_3215_;
v___y_3200_ = v___y_3217_;
v___y_3201_ = v___y_3218_;
v_a_3202_ = v_snd_3078_;
goto v___jp_3197_;
}
else
{
lean_object* v_a_3222_; 
lean_dec(v___y_3218_);
lean_dec(v___y_3214_);
lean_dec(v_snd_3078_);
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref(v___x_3221_);
v___y_3188_ = v___y_3215_;
v___y_3189_ = v___y_3217_;
v_a_3190_ = v_a_3222_;
goto v___jp_3187_;
}
}
else
{
lean_dec_ref(v___y_3219_);
lean_dec(v_snd_3078_);
v___y_3206_ = v___y_3214_;
v___y_3207_ = v___y_3215_;
v___y_3208_ = v___y_3217_;
v___y_3209_ = v___y_3218_;
v___y_3210_ = v___y_3216_;
goto v___jp_3205_;
}
}
v___jp_3223_:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_Meta_saveState___redArg(v_a_3067_, v_a_3069_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3231_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref(v___x_3229_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_snd_3078_);
lean_inc(v_trace_3061_);
v___x_3231_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3225_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_dec(v_a_3230_);
lean_dec(v_snd_3078_);
v___y_3206_ = v___y_3224_;
v___y_3207_ = v___y_3226_;
v___y_3208_ = v___y_3227_;
v___y_3209_ = v___y_3228_;
v___y_3210_ = v___x_3231_;
goto v___jp_3205_;
}
else
{
lean_object* v_a_3232_; uint8_t v___x_3233_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
v___x_3233_ = l_Lean_Exception_isInterrupt(v_a_3232_);
if (v___x_3233_ == 0)
{
uint8_t v___x_3234_; 
v___x_3234_ = l_Lean_Exception_isRuntime(v_a_3232_);
v___y_3214_ = v___y_3224_;
v___y_3215_ = v___y_3226_;
v___y_3216_ = v___x_3231_;
v___y_3217_ = v___y_3227_;
v___y_3218_ = v___y_3228_;
v___y_3219_ = v_a_3230_;
v___y_3220_ = v___x_3234_;
goto v___jp_3213_;
}
else
{
lean_dec(v_a_3232_);
v___y_3214_ = v___y_3224_;
v___y_3215_ = v___y_3226_;
v___y_3216_ = v___x_3231_;
v___y_3217_ = v___y_3227_;
v___y_3218_ = v___y_3228_;
v___y_3219_ = v_a_3230_;
v___y_3220_ = v___x_3233_;
goto v___jp_3213_;
}
}
}
else
{
lean_object* v_a_3235_; 
lean_dec(v___y_3228_);
lean_dec(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3235_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3235_);
lean_dec_ref(v___x_3229_);
v___y_3188_ = v___y_3226_;
v___y_3189_ = v___y_3227_;
v_a_3190_ = v_a_3235_;
goto v___jp_3187_;
}
}
v___jp_3236_:
{
if (lean_obj_tag(v___y_3239_) == 0)
{
lean_object* v_a_3240_; 
v_a_3240_ = lean_ctor_get(v___y_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref(v___y_3239_);
v___y_3193_ = v___y_3237_;
v___y_3194_ = v___y_3238_;
v_a_3195_ = v_a_3240_;
goto v___jp_3192_;
}
else
{
lean_object* v_a_3241_; 
v_a_3241_ = lean_ctor_get(v___y_3239_, 0);
lean_inc(v_a_3241_);
lean_dec_ref(v___y_3239_);
v___y_3188_ = v___y_3237_;
v___y_3189_ = v___y_3238_;
v_a_3190_ = v_a_3241_;
goto v___jp_3187_;
}
}
v___jp_3242_:
{
lean_object* v___x_3250_; double v___x_3251_; double v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3250_ = lean_io_get_num_heartbeats();
v___x_3251_ = lean_float_of_nat(v___y_3244_);
v___x_3252_ = lean_float_of_nat(v___x_3250_);
v___x_3253_ = lean_box_float(v___x_3251_);
v___x_3254_ = lean_box_float(v___x_3252_);
v___x_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3256_, 0, v_a_3249_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_3257_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3061_, v_hasTrace_3084_, v___x_3168_, v_options_3083_, v___y_3245_, v___y_3248_, v___y_3243_, v___x_3256_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_3237_ = v___y_3246_;
v___y_3238_ = v___y_3247_;
v___y_3239_ = v___x_3257_;
goto v___jp_3236_;
}
v___jp_3258_:
{
lean_object* v___x_3266_; 
v___x_3266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3266_, 0, v_a_3265_);
v___y_3243_ = v___y_3259_;
v___y_3244_ = v___y_3260_;
v___y_3245_ = v___y_3261_;
v___y_3246_ = v___y_3262_;
v___y_3247_ = v___y_3263_;
v___y_3248_ = v___y_3264_;
v_a_3249_ = v___x_3266_;
goto v___jp_3242_;
}
v___jp_3267_:
{
lean_object* v___x_3275_; 
v___x_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3275_, 0, v_a_3274_);
v___y_3243_ = v___y_3268_;
v___y_3244_ = v___y_3269_;
v___y_3245_ = v___y_3270_;
v___y_3246_ = v___y_3271_;
v___y_3247_ = v___y_3272_;
v___y_3248_ = v___y_3273_;
v_a_3249_ = v___x_3275_;
goto v___jp_3242_;
}
v___jp_3276_:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3286_ = l_List_appendTR___redArg(v___y_3278_, v___y_3283_);
v___x_3287_ = l_List_appendTR___redArg(v___x_3286_, v_a_3285_);
v___y_3268_ = v___y_3277_;
v___y_3269_ = v___y_3279_;
v___y_3270_ = v___y_3280_;
v___y_3271_ = v___y_3281_;
v___y_3272_ = v___y_3282_;
v___y_3273_ = v___y_3284_;
v_a_3274_ = v___x_3287_;
goto v___jp_3267_;
}
v___jp_3288_:
{
if (lean_obj_tag(v___y_3297_) == 0)
{
lean_object* v_a_3298_; 
v_a_3298_ = lean_ctor_get(v___y_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref(v___y_3297_);
v___y_3277_ = v___y_3289_;
v___y_3278_ = v___y_3290_;
v___y_3279_ = v___y_3291_;
v___y_3280_ = v___y_3292_;
v___y_3281_ = v___y_3293_;
v___y_3282_ = v___y_3294_;
v___y_3283_ = v___y_3295_;
v___y_3284_ = v___y_3296_;
v_a_3285_ = v_a_3298_;
goto v___jp_3276_;
}
else
{
lean_object* v_a_3299_; 
lean_dec(v___y_3295_);
lean_dec(v___y_3290_);
v_a_3299_ = lean_ctor_get(v___y_3297_, 0);
lean_inc(v_a_3299_);
lean_dec_ref(v___y_3297_);
v___y_3259_ = v___y_3289_;
v___y_3260_ = v___y_3291_;
v___y_3261_ = v___y_3292_;
v___y_3262_ = v___y_3293_;
v___y_3263_ = v___y_3294_;
v___y_3264_ = v___y_3296_;
v_a_3265_ = v_a_3299_;
goto v___jp_3258_;
}
}
v___jp_3300_:
{
if (v___y_3311_ == 0)
{
lean_object* v___x_3312_; 
lean_dec_ref(v___y_3308_);
v___x_3312_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3303_, v_a_3067_, v_a_3069_);
lean_dec_ref(v___y_3303_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_dec_ref(v___x_3312_);
v___y_3277_ = v___y_3301_;
v___y_3278_ = v___y_3302_;
v___y_3279_ = v___y_3304_;
v___y_3280_ = v___y_3305_;
v___y_3281_ = v___y_3306_;
v___y_3282_ = v___y_3307_;
v___y_3283_ = v___y_3309_;
v___y_3284_ = v___y_3310_;
v_a_3285_ = v_snd_3078_;
goto v___jp_3276_;
}
else
{
lean_object* v_a_3313_; 
lean_dec(v___y_3309_);
lean_dec(v___y_3302_);
lean_dec(v_snd_3078_);
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref(v___x_3312_);
v___y_3259_ = v___y_3301_;
v___y_3260_ = v___y_3304_;
v___y_3261_ = v___y_3305_;
v___y_3262_ = v___y_3306_;
v___y_3263_ = v___y_3307_;
v___y_3264_ = v___y_3310_;
v_a_3265_ = v_a_3313_;
goto v___jp_3258_;
}
}
else
{
lean_dec_ref(v___y_3303_);
lean_dec(v_snd_3078_);
v___y_3289_ = v___y_3301_;
v___y_3290_ = v___y_3302_;
v___y_3291_ = v___y_3304_;
v___y_3292_ = v___y_3305_;
v___y_3293_ = v___y_3306_;
v___y_3294_ = v___y_3307_;
v___y_3295_ = v___y_3309_;
v___y_3296_ = v___y_3310_;
v___y_3297_ = v___y_3308_;
goto v___jp_3288_;
}
}
v___jp_3314_:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Lean_Meta_saveState___redArg(v_a_3067_, v_a_3069_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3326_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref(v___x_3324_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_snd_3078_);
lean_inc(v_trace_3061_);
v___x_3326_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3318_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_dec(v_a_3325_);
lean_dec(v_snd_3078_);
v___y_3289_ = v___y_3315_;
v___y_3290_ = v___y_3316_;
v___y_3291_ = v___y_3317_;
v___y_3292_ = v___y_3319_;
v___y_3293_ = v___y_3320_;
v___y_3294_ = v___y_3321_;
v___y_3295_ = v___y_3322_;
v___y_3296_ = v___y_3323_;
v___y_3297_ = v___x_3326_;
goto v___jp_3288_;
}
else
{
lean_object* v_a_3327_; uint8_t v___x_3328_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
v___x_3328_ = l_Lean_Exception_isInterrupt(v_a_3327_);
if (v___x_3328_ == 0)
{
uint8_t v___x_3329_; 
v___x_3329_ = l_Lean_Exception_isRuntime(v_a_3327_);
v___y_3301_ = v___y_3315_;
v___y_3302_ = v___y_3316_;
v___y_3303_ = v_a_3325_;
v___y_3304_ = v___y_3317_;
v___y_3305_ = v___y_3319_;
v___y_3306_ = v___y_3320_;
v___y_3307_ = v___y_3321_;
v___y_3308_ = v___x_3326_;
v___y_3309_ = v___y_3322_;
v___y_3310_ = v___y_3323_;
v___y_3311_ = v___x_3329_;
goto v___jp_3300_;
}
else
{
lean_dec(v_a_3327_);
v___y_3301_ = v___y_3315_;
v___y_3302_ = v___y_3316_;
v___y_3303_ = v_a_3325_;
v___y_3304_ = v___y_3317_;
v___y_3305_ = v___y_3319_;
v___y_3306_ = v___y_3320_;
v___y_3307_ = v___y_3321_;
v___y_3308_ = v___x_3326_;
v___y_3309_ = v___y_3322_;
v___y_3310_ = v___y_3323_;
v___y_3311_ = v___x_3328_;
goto v___jp_3300_;
}
}
}
else
{
lean_object* v_a_3330_; 
lean_dec(v___y_3322_);
lean_dec(v___y_3318_);
lean_dec(v___y_3316_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3330_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3330_);
lean_dec_ref(v___x_3324_);
v___y_3259_ = v___y_3315_;
v___y_3260_ = v___y_3317_;
v___y_3261_ = v___y_3319_;
v___y_3262_ = v___y_3320_;
v___y_3263_ = v___y_3321_;
v___y_3264_ = v___y_3323_;
v_a_3265_ = v_a_3330_;
goto v___jp_3258_;
}
}
v___jp_3331_:
{
if (lean_obj_tag(v___y_3338_) == 0)
{
lean_object* v_a_3339_; 
v_a_3339_ = lean_ctor_get(v___y_3338_, 0);
lean_inc(v_a_3339_);
lean_dec_ref(v___y_3338_);
v___y_3268_ = v___y_3332_;
v___y_3269_ = v___y_3333_;
v___y_3270_ = v___y_3334_;
v___y_3271_ = v___y_3335_;
v___y_3272_ = v___y_3336_;
v___y_3273_ = v___y_3337_;
v_a_3274_ = v_a_3339_;
goto v___jp_3267_;
}
else
{
lean_object* v_a_3340_; 
v_a_3340_ = lean_ctor_get(v___y_3338_, 0);
lean_inc(v_a_3340_);
lean_dec_ref(v___y_3338_);
v___y_3259_ = v___y_3332_;
v___y_3260_ = v___y_3333_;
v___y_3261_ = v___y_3334_;
v___y_3262_ = v___y_3335_;
v___y_3263_ = v___y_3336_;
v___y_3264_ = v___y_3337_;
v_a_3265_ = v_a_3340_;
goto v___jp_3258_;
}
}
v___jp_3341_:
{
lean_object* v___x_3350_; 
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_3350_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3345_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3352_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref(v___x_3350_);
v___x_3352_ = l_List_appendTR___redArg(v___y_3343_, v_a_3351_);
v___y_3268_ = v___y_3342_;
v___y_3269_ = v___y_3344_;
v___y_3270_ = v___y_3346_;
v___y_3271_ = v___y_3347_;
v___y_3272_ = v___y_3348_;
v___y_3273_ = v___y_3349_;
v_a_3274_ = v___x_3352_;
goto v___jp_3267_;
}
else
{
lean_dec(v___y_3343_);
v___y_3332_ = v___y_3342_;
v___y_3333_ = v___y_3344_;
v___y_3334_ = v___y_3346_;
v___y_3335_ = v___y_3347_;
v___y_3336_ = v___y_3348_;
v___y_3337_ = v___y_3349_;
v___y_3338_ = v___x_3350_;
goto v___jp_3331_;
}
}
v___jp_3353_:
{
uint8_t v_commitIndependentGoals_3364_; lean_object* v___x_3365_; 
v_commitIndependentGoals_3364_ = lean_ctor_get_uint8(v_cfg_3060_, sizeof(void*)*4);
lean_inc(v___y_3356_);
v___x_3365_ = l_List_appendTR___redArg(v_a_3363_, v___y_3356_);
if (v_commitIndependentGoals_3364_ == 0)
{
lean_dec(v___y_3361_);
if (v___y_3354_ == 0)
{
v___y_3342_ = v___y_3355_;
v___y_3343_ = v___y_3356_;
v___y_3344_ = v___y_3357_;
v___y_3345_ = v___x_3365_;
v___y_3346_ = v___y_3358_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3360_;
v___y_3349_ = v___y_3362_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec(v___x_3365_);
lean_dec(v___y_3356_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___x_3366_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3367_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3366_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_3332_ = v___y_3355_;
v___y_3333_ = v___y_3357_;
v___y_3334_ = v___y_3358_;
v___y_3335_ = v___y_3359_;
v___y_3336_ = v___y_3360_;
v___y_3337_ = v___y_3362_;
v___y_3338_ = v___x_3367_;
goto v___jp_3331_;
}
}
else
{
uint8_t v___x_3368_; 
v___x_3368_ = l_List_isEmpty___redArg(v___y_3356_);
if (v___x_3368_ == 0)
{
v___y_3315_ = v___y_3355_;
v___y_3316_ = v___y_3356_;
v___y_3317_ = v___y_3357_;
v___y_3318_ = v___x_3365_;
v___y_3319_ = v___y_3358_;
v___y_3320_ = v___y_3359_;
v___y_3321_ = v___y_3360_;
v___y_3322_ = v___y_3361_;
v___y_3323_ = v___y_3362_;
goto v___jp_3314_;
}
else
{
if (v___y_3354_ == 0)
{
lean_dec(v___y_3361_);
v___y_3342_ = v___y_3355_;
v___y_3343_ = v___y_3356_;
v___y_3344_ = v___y_3357_;
v___y_3345_ = v___x_3365_;
v___y_3346_ = v___y_3358_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3360_;
v___y_3349_ = v___y_3362_;
goto v___jp_3341_;
}
else
{
v___y_3315_ = v___y_3355_;
v___y_3316_ = v___y_3356_;
v___y_3317_ = v___y_3357_;
v___y_3318_ = v___x_3365_;
v___y_3319_ = v___y_3358_;
v___y_3320_ = v___y_3359_;
v___y_3321_ = v___y_3360_;
v___y_3322_ = v___y_3361_;
v___y_3323_ = v___y_3362_;
goto v___jp_3314_;
}
}
}
}
v___jp_3369_:
{
lean_object* v___x_3377_; double v___x_3378_; double v___x_3379_; double v___x_3380_; double v___x_3381_; double v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3377_ = lean_io_mono_nanos_now();
v___x_3378_ = lean_float_of_nat(v___y_3375_);
v___x_3379_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3380_ = lean_float_div(v___x_3378_, v___x_3379_);
v___x_3381_ = lean_float_of_nat(v___x_3377_);
v___x_3382_ = lean_float_div(v___x_3381_, v___x_3379_);
v___x_3383_ = lean_box_float(v___x_3380_);
v___x_3384_ = lean_box_float(v___x_3382_);
v___x_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v_a_3376_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_3387_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3061_, v_hasTrace_3084_, v___x_3168_, v_options_3083_, v___y_3371_, v___y_3374_, v___y_3370_, v___x_3386_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_3237_ = v___y_3372_;
v___y_3238_ = v___y_3373_;
v___y_3239_ = v___x_3387_;
goto v___jp_3236_;
}
v___jp_3388_:
{
lean_object* v___x_3396_; 
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v_a_3395_);
v___y_3370_ = v___y_3389_;
v___y_3371_ = v___y_3390_;
v___y_3372_ = v___y_3391_;
v___y_3373_ = v___y_3392_;
v___y_3374_ = v___y_3393_;
v___y_3375_ = v___y_3394_;
v_a_3376_ = v___x_3396_;
goto v___jp_3369_;
}
v___jp_3397_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = l_List_appendTR___redArg(v___y_3399_, v___y_3403_);
v___x_3408_ = l_List_appendTR___redArg(v___x_3407_, v_a_3406_);
v___y_3389_ = v___y_3398_;
v___y_3390_ = v___y_3400_;
v___y_3391_ = v___y_3401_;
v___y_3392_ = v___y_3402_;
v___y_3393_ = v___y_3404_;
v___y_3394_ = v___y_3405_;
v_a_3395_ = v___x_3408_;
goto v___jp_3388_;
}
v___jp_3409_:
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3417_, 0, v_a_3416_);
v___y_3370_ = v___y_3410_;
v___y_3371_ = v___y_3411_;
v___y_3372_ = v___y_3412_;
v___y_3373_ = v___y_3413_;
v___y_3374_ = v___y_3414_;
v___y_3375_ = v___y_3415_;
v_a_3376_ = v___x_3417_;
goto v___jp_3369_;
}
v___jp_3418_:
{
if (lean_obj_tag(v___y_3425_) == 0)
{
lean_object* v_a_3426_; 
v_a_3426_ = lean_ctor_get(v___y_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref(v___y_3425_);
v___y_3389_ = v___y_3419_;
v___y_3390_ = v___y_3420_;
v___y_3391_ = v___y_3421_;
v___y_3392_ = v___y_3422_;
v___y_3393_ = v___y_3423_;
v___y_3394_ = v___y_3424_;
v_a_3395_ = v_a_3426_;
goto v___jp_3388_;
}
else
{
lean_object* v_a_3427_; 
v_a_3427_ = lean_ctor_get(v___y_3425_, 0);
lean_inc(v_a_3427_);
lean_dec_ref(v___y_3425_);
v___y_3410_ = v___y_3419_;
v___y_3411_ = v___y_3420_;
v___y_3412_ = v___y_3421_;
v___y_3413_ = v___y_3422_;
v___y_3414_ = v___y_3423_;
v___y_3415_ = v___y_3424_;
v_a_3416_ = v_a_3427_;
goto v___jp_3409_;
}
}
v___jp_3428_:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3436_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3435_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_3419_ = v___y_3429_;
v___y_3420_ = v___y_3430_;
v___y_3421_ = v___y_3431_;
v___y_3422_ = v___y_3432_;
v___y_3423_ = v___y_3433_;
v___y_3424_ = v___y_3434_;
v___y_3425_ = v___x_3436_;
goto v___jp_3418_;
}
v___jp_3437_:
{
uint8_t v___x_3448_; 
v___x_3448_ = l_List_isEmpty___redArg(v___y_3445_);
lean_dec(v___y_3445_);
if (v___x_3448_ == 0)
{
lean_dec(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___y_3429_ = v___y_3439_;
v___y_3430_ = v___y_3442_;
v___y_3431_ = v___y_3443_;
v___y_3432_ = v___y_3444_;
v___y_3433_ = v___y_3446_;
v___y_3434_ = v___y_3447_;
goto v___jp_3428_;
}
else
{
if (v___y_3438_ == 0)
{
lean_object* v___x_3449_; 
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_3449_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3441_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3451_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref(v___x_3449_);
v___x_3451_ = l_List_appendTR___redArg(v___y_3440_, v_a_3450_);
v___y_3389_ = v___y_3439_;
v___y_3390_ = v___y_3442_;
v___y_3391_ = v___y_3443_;
v___y_3392_ = v___y_3444_;
v___y_3393_ = v___y_3446_;
v___y_3394_ = v___y_3447_;
v_a_3395_ = v___x_3451_;
goto v___jp_3388_;
}
else
{
lean_dec(v___y_3440_);
v___y_3419_ = v___y_3439_;
v___y_3420_ = v___y_3442_;
v___y_3421_ = v___y_3443_;
v___y_3422_ = v___y_3444_;
v___y_3423_ = v___y_3446_;
v___y_3424_ = v___y_3447_;
v___y_3425_ = v___x_3449_;
goto v___jp_3418_;
}
}
else
{
lean_dec(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___y_3429_ = v___y_3439_;
v___y_3430_ = v___y_3442_;
v___y_3431_ = v___y_3443_;
v___y_3432_ = v___y_3444_;
v___y_3433_ = v___y_3446_;
v___y_3434_ = v___y_3447_;
goto v___jp_3428_;
}
}
}
v___jp_3452_:
{
if (lean_obj_tag(v___y_3461_) == 0)
{
lean_object* v_a_3462_; 
v_a_3462_ = lean_ctor_get(v___y_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___y_3461_);
v___y_3398_ = v___y_3453_;
v___y_3399_ = v___y_3454_;
v___y_3400_ = v___y_3455_;
v___y_3401_ = v___y_3456_;
v___y_3402_ = v___y_3457_;
v___y_3403_ = v___y_3458_;
v___y_3404_ = v___y_3459_;
v___y_3405_ = v___y_3460_;
v_a_3406_ = v_a_3462_;
goto v___jp_3397_;
}
else
{
lean_object* v_a_3463_; 
lean_dec(v___y_3458_);
lean_dec(v___y_3454_);
v_a_3463_ = lean_ctor_get(v___y_3461_, 0);
lean_inc(v_a_3463_);
lean_dec_ref(v___y_3461_);
v___y_3410_ = v___y_3453_;
v___y_3411_ = v___y_3455_;
v___y_3412_ = v___y_3456_;
v___y_3413_ = v___y_3457_;
v___y_3414_ = v___y_3459_;
v___y_3415_ = v___y_3460_;
v_a_3416_ = v_a_3463_;
goto v___jp_3409_;
}
}
v___jp_3464_:
{
if (v___y_3475_ == 0)
{
lean_object* v___x_3476_; 
lean_dec_ref(v___y_3471_);
v___x_3476_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3472_, v_a_3067_, v_a_3069_);
lean_dec_ref(v___y_3472_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_dec_ref(v___x_3476_);
v___y_3398_ = v___y_3465_;
v___y_3399_ = v___y_3466_;
v___y_3400_ = v___y_3467_;
v___y_3401_ = v___y_3468_;
v___y_3402_ = v___y_3469_;
v___y_3403_ = v___y_3470_;
v___y_3404_ = v___y_3473_;
v___y_3405_ = v___y_3474_;
v_a_3406_ = v_snd_3078_;
goto v___jp_3397_;
}
else
{
lean_object* v_a_3477_; 
lean_dec(v___y_3470_);
lean_dec(v___y_3466_);
lean_dec(v_snd_3078_);
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
lean_inc(v_a_3477_);
lean_dec_ref(v___x_3476_);
v___y_3410_ = v___y_3465_;
v___y_3411_ = v___y_3467_;
v___y_3412_ = v___y_3468_;
v___y_3413_ = v___y_3469_;
v___y_3414_ = v___y_3473_;
v___y_3415_ = v___y_3474_;
v_a_3416_ = v_a_3477_;
goto v___jp_3409_;
}
}
else
{
lean_dec_ref(v___y_3472_);
lean_dec(v_snd_3078_);
v___y_3453_ = v___y_3465_;
v___y_3454_ = v___y_3466_;
v___y_3455_ = v___y_3467_;
v___y_3456_ = v___y_3468_;
v___y_3457_ = v___y_3469_;
v___y_3458_ = v___y_3470_;
v___y_3459_ = v___y_3473_;
v___y_3460_ = v___y_3474_;
v___y_3461_ = v___y_3471_;
goto v___jp_3452_;
}
}
v___jp_3478_:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_Meta_saveState___redArg(v_a_3067_, v_a_3069_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3490_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3489_);
lean_dec_ref(v___x_3488_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_snd_3078_);
lean_inc(v_trace_3061_);
v___x_3490_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3481_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_dec(v_a_3489_);
lean_dec(v_snd_3078_);
v___y_3453_ = v___y_3479_;
v___y_3454_ = v___y_3480_;
v___y_3455_ = v___y_3482_;
v___y_3456_ = v___y_3483_;
v___y_3457_ = v___y_3484_;
v___y_3458_ = v___y_3485_;
v___y_3459_ = v___y_3486_;
v___y_3460_ = v___y_3487_;
v___y_3461_ = v___x_3490_;
goto v___jp_3452_;
}
else
{
lean_object* v_a_3491_; uint8_t v___x_3492_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
v___x_3492_ = l_Lean_Exception_isInterrupt(v_a_3491_);
if (v___x_3492_ == 0)
{
uint8_t v___x_3493_; 
v___x_3493_ = l_Lean_Exception_isRuntime(v_a_3491_);
v___y_3465_ = v___y_3479_;
v___y_3466_ = v___y_3480_;
v___y_3467_ = v___y_3482_;
v___y_3468_ = v___y_3483_;
v___y_3469_ = v___y_3484_;
v___y_3470_ = v___y_3485_;
v___y_3471_ = v___x_3490_;
v___y_3472_ = v_a_3489_;
v___y_3473_ = v___y_3486_;
v___y_3474_ = v___y_3487_;
v___y_3475_ = v___x_3493_;
goto v___jp_3464_;
}
else
{
lean_dec(v_a_3491_);
v___y_3465_ = v___y_3479_;
v___y_3466_ = v___y_3480_;
v___y_3467_ = v___y_3482_;
v___y_3468_ = v___y_3483_;
v___y_3469_ = v___y_3484_;
v___y_3470_ = v___y_3485_;
v___y_3471_ = v___x_3490_;
v___y_3472_ = v_a_3489_;
v___y_3473_ = v___y_3486_;
v___y_3474_ = v___y_3487_;
v___y_3475_ = v___x_3492_;
goto v___jp_3464_;
}
}
}
else
{
lean_object* v_a_3494_; 
lean_dec(v___y_3485_);
lean_dec(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3494_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_a_3494_);
lean_dec_ref(v___x_3488_);
v___y_3410_ = v___y_3479_;
v___y_3411_ = v___y_3482_;
v___y_3412_ = v___y_3483_;
v___y_3413_ = v___y_3484_;
v___y_3414_ = v___y_3486_;
v___y_3415_ = v___y_3487_;
v_a_3416_ = v_a_3494_;
goto v___jp_3409_;
}
}
v___jp_3495_:
{
uint8_t v_commitIndependentGoals_3506_; lean_object* v___x_3507_; 
v_commitIndependentGoals_3506_ = lean_ctor_get_uint8(v_cfg_3060_, sizeof(void*)*4);
lean_inc(v___y_3498_);
v___x_3507_ = l_List_appendTR___redArg(v_a_3505_, v___y_3498_);
if (v_commitIndependentGoals_3506_ == 0)
{
v___y_3438_ = v___y_3496_;
v___y_3439_ = v___y_3497_;
v___y_3440_ = v___y_3498_;
v___y_3441_ = v___x_3507_;
v___y_3442_ = v___y_3499_;
v___y_3443_ = v___y_3500_;
v___y_3444_ = v___y_3501_;
v___y_3445_ = v___y_3502_;
v___y_3446_ = v___y_3503_;
v___y_3447_ = v___y_3504_;
goto v___jp_3437_;
}
else
{
uint8_t v___x_3508_; 
v___x_3508_ = l_List_isEmpty___redArg(v___y_3498_);
if (v___x_3508_ == 0)
{
v___y_3479_ = v___y_3497_;
v___y_3480_ = v___y_3498_;
v___y_3481_ = v___x_3507_;
v___y_3482_ = v___y_3499_;
v___y_3483_ = v___y_3500_;
v___y_3484_ = v___y_3501_;
v___y_3485_ = v___y_3502_;
v___y_3486_ = v___y_3503_;
v___y_3487_ = v___y_3504_;
goto v___jp_3478_;
}
else
{
if (v___y_3496_ == 0)
{
v___y_3438_ = v___y_3496_;
v___y_3439_ = v___y_3497_;
v___y_3440_ = v___y_3498_;
v___y_3441_ = v___x_3507_;
v___y_3442_ = v___y_3499_;
v___y_3443_ = v___y_3500_;
v___y_3444_ = v___y_3501_;
v___y_3445_ = v___y_3502_;
v___y_3446_ = v___y_3503_;
v___y_3447_ = v___y_3504_;
goto v___jp_3437_;
}
else
{
v___y_3479_ = v___y_3497_;
v___y_3480_ = v___y_3498_;
v___y_3481_ = v___x_3507_;
v___y_3482_ = v___y_3499_;
v___y_3483_ = v___y_3500_;
v___y_3484_ = v___y_3501_;
v___y_3485_ = v___y_3502_;
v___y_3486_ = v___y_3503_;
v___y_3487_ = v___y_3504_;
goto v___jp_3478_;
}
}
}
}
v___jp_3509_:
{
lean_object* v___x_3518_; 
v___x_3518_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_3069_);
if (lean_obj_tag(v___x_3518_) == 0)
{
if (v___y_3510_ == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref(v___x_3518_);
v___x_3520_ = lean_io_mono_nanos_now();
v___x_3521_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3084_, v___y_3510_, v_goals_3064_, v___y_3516_, v_a_3067_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3523_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref(v___x_3521_);
v___x_3523_ = l_List_reverse___redArg(v_a_3522_);
v___y_3496_ = v___y_3510_;
v___y_3497_ = v___y_3511_;
v___y_3498_ = v___y_3512_;
v___y_3499_ = v___y_3513_;
v___y_3500_ = v___y_3514_;
v___y_3501_ = v___y_3515_;
v___y_3502_ = v___y_3517_;
v___y_3503_ = v_a_3519_;
v___y_3504_ = v___x_3520_;
v_a_3505_ = v___x_3523_;
goto v___jp_3495_;
}
else
{
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3524_; 
v_a_3524_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3524_);
lean_dec_ref(v___x_3521_);
v___y_3496_ = v___y_3510_;
v___y_3497_ = v___y_3511_;
v___y_3498_ = v___y_3512_;
v___y_3499_ = v___y_3513_;
v___y_3500_ = v___y_3514_;
v___y_3501_ = v___y_3515_;
v___y_3502_ = v___y_3517_;
v___y_3503_ = v_a_3519_;
v___y_3504_ = v___x_3520_;
v_a_3505_ = v_a_3524_;
goto v___jp_3495_;
}
else
{
lean_object* v_a_3525_; 
lean_dec(v___y_3517_);
lean_dec(v___y_3512_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3525_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3525_);
lean_dec_ref(v___x_3521_);
v___y_3410_ = v___y_3511_;
v___y_3411_ = v___y_3513_;
v___y_3412_ = v___y_3514_;
v___y_3413_ = v___y_3515_;
v___y_3414_ = v_a_3519_;
v___y_3415_ = v___x_3520_;
v_a_3416_ = v_a_3525_;
goto v___jp_3409_;
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v_a_3526_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3526_);
lean_dec_ref(v___x_3518_);
v___x_3527_ = lean_io_get_num_heartbeats();
v___x_3528_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3084_, v___y_3510_, v_goals_3064_, v___y_3516_, v_a_3067_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3530_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref(v___x_3528_);
v___x_3530_ = l_List_reverse___redArg(v_a_3529_);
v___y_3354_ = v___y_3510_;
v___y_3355_ = v___y_3511_;
v___y_3356_ = v___y_3512_;
v___y_3357_ = v___x_3527_;
v___y_3358_ = v___y_3513_;
v___y_3359_ = v___y_3514_;
v___y_3360_ = v___y_3515_;
v___y_3361_ = v___y_3517_;
v___y_3362_ = v_a_3526_;
v_a_3363_ = v___x_3530_;
goto v___jp_3353_;
}
else
{
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3531_; 
v_a_3531_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3531_);
lean_dec_ref(v___x_3528_);
v___y_3354_ = v___y_3510_;
v___y_3355_ = v___y_3511_;
v___y_3356_ = v___y_3512_;
v___y_3357_ = v___x_3527_;
v___y_3358_ = v___y_3513_;
v___y_3359_ = v___y_3514_;
v___y_3360_ = v___y_3515_;
v___y_3361_ = v___y_3517_;
v___y_3362_ = v_a_3526_;
v_a_3363_ = v_a_3531_;
goto v___jp_3353_;
}
else
{
lean_object* v_a_3532_; 
lean_dec(v___y_3517_);
lean_dec(v___y_3512_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3532_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3532_);
lean_dec_ref(v___x_3528_);
v___y_3259_ = v___y_3511_;
v___y_3260_ = v___x_3527_;
v___y_3261_ = v___y_3513_;
v___y_3262_ = v___y_3514_;
v___y_3263_ = v___y_3515_;
v___y_3264_ = v_a_3526_;
v_a_3265_ = v_a_3532_;
goto v___jp_3258_;
}
}
}
}
else
{
lean_object* v_a_3533_; 
lean_dec(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v_snd_3078_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3533_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3533_);
lean_dec_ref(v___x_3518_);
v___y_3188_ = v___y_3514_;
v___y_3189_ = v___y_3515_;
v_a_3190_ = v_a_3533_;
goto v___jp_3187_;
}
}
v___jp_3534_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3538_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3537_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_3237_ = v___y_3535_;
v___y_3238_ = v___y_3536_;
v___y_3239_ = v___x_3538_;
goto v___jp_3236_;
}
v___jp_3539_:
{
uint8_t v___x_3546_; 
v___x_3546_ = l_List_isEmpty___redArg(v___y_3545_);
lean_dec(v___y_3545_);
if (v___x_3546_ == 0)
{
lean_dec(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___y_3535_ = v___y_3543_;
v___y_3536_ = v___y_3544_;
goto v___jp_3534_;
}
else
{
if (v___y_3540_ == 0)
{
lean_object* v___x_3547_; 
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_3547_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3542_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___x_3549_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref(v___x_3547_);
v___x_3549_ = l_List_appendTR___redArg(v___y_3541_, v_a_3548_);
v___y_3193_ = v___y_3543_;
v___y_3194_ = v___y_3544_;
v_a_3195_ = v___x_3549_;
goto v___jp_3192_;
}
else
{
lean_dec(v___y_3541_);
v___y_3237_ = v___y_3543_;
v___y_3238_ = v___y_3544_;
v___y_3239_ = v___x_3547_;
goto v___jp_3236_;
}
}
else
{
lean_dec(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___y_3535_ = v___y_3543_;
v___y_3536_ = v___y_3544_;
goto v___jp_3534_;
}
}
}
v___jp_3550_:
{
uint8_t v_commitIndependentGoals_3557_; lean_object* v___x_3558_; 
v_commitIndependentGoals_3557_ = lean_ctor_get_uint8(v_cfg_3060_, sizeof(void*)*4);
lean_inc(v___y_3552_);
v___x_3558_ = l_List_appendTR___redArg(v_a_3556_, v___y_3552_);
if (v_commitIndependentGoals_3557_ == 0)
{
v___y_3540_ = v___y_3551_;
v___y_3541_ = v___y_3552_;
v___y_3542_ = v___x_3558_;
v___y_3543_ = v___y_3553_;
v___y_3544_ = v___y_3554_;
v___y_3545_ = v___y_3555_;
goto v___jp_3539_;
}
else
{
uint8_t v___x_3559_; 
v___x_3559_ = l_List_isEmpty___redArg(v___y_3552_);
if (v___x_3559_ == 0)
{
v___y_3224_ = v___y_3552_;
v___y_3225_ = v___x_3558_;
v___y_3226_ = v___y_3553_;
v___y_3227_ = v___y_3554_;
v___y_3228_ = v___y_3555_;
goto v___jp_3223_;
}
else
{
if (v___y_3551_ == 0)
{
v___y_3540_ = v___y_3551_;
v___y_3541_ = v___y_3552_;
v___y_3542_ = v___x_3558_;
v___y_3543_ = v___y_3553_;
v___y_3544_ = v___y_3554_;
v___y_3545_ = v___y_3555_;
goto v___jp_3539_;
}
else
{
v___y_3224_ = v___y_3552_;
v___y_3225_ = v___x_3558_;
v___y_3226_ = v___y_3553_;
v___y_3227_ = v___y_3554_;
v___y_3228_ = v___y_3555_;
goto v___jp_3223_;
}
}
}
}
v___jp_3560_:
{
lean_object* v___x_3564_; double v___x_3565_; double v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; lean_object* v___x_3572_; 
v___x_3564_ = lean_io_get_num_heartbeats();
v___x_3565_ = lean_float_of_nat(v___y_3562_);
v___x_3566_ = lean_float_of_nat(v___x_3564_);
v___x_3567_ = lean_box_float(v___x_3565_);
v___x_3568_ = lean_box_float(v___x_3566_);
v___x_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3567_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_a_3563_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = lean_unbox(v_a_3166_);
lean_dec(v_a_3166_);
v___x_3572_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3061_, v_hasTrace_3084_, v___x_3168_, v_options_3083_, v___x_3571_, v___y_3561_, v___f_3167_, v___x_3570_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec_ref(v_options_3083_);
return v___x_3572_;
}
v___jp_3573_:
{
lean_object* v___x_3577_; 
v___x_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3577_, 0, v_a_3576_);
v___y_3561_ = v___y_3574_;
v___y_3562_ = v___y_3575_;
v_a_3563_ = v___x_3577_;
goto v___jp_3560_;
}
v___jp_3578_:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = l_List_appendTR___redArg(v___y_3581_, v___y_3579_);
v___x_3585_ = l_List_appendTR___redArg(v___x_3584_, v_a_3583_);
v___y_3574_ = v___y_3580_;
v___y_3575_ = v___y_3582_;
v_a_3576_ = v___x_3585_;
goto v___jp_3573_;
}
v___jp_3586_:
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3590_, 0, v_a_3589_);
v___y_3561_ = v___y_3587_;
v___y_3562_ = v___y_3588_;
v_a_3563_ = v___x_3590_;
goto v___jp_3560_;
}
v___jp_3591_:
{
if (lean_obj_tag(v___y_3594_) == 0)
{
lean_object* v_a_3595_; 
v_a_3595_ = lean_ctor_get(v___y_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref(v___y_3594_);
v___y_3574_ = v___y_3592_;
v___y_3575_ = v___y_3593_;
v_a_3576_ = v_a_3595_;
goto v___jp_3573_;
}
else
{
lean_object* v_a_3596_; 
v_a_3596_ = lean_ctor_get(v___y_3594_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___y_3594_);
v___y_3587_ = v___y_3592_;
v___y_3588_ = v___y_3593_;
v_a_3589_ = v_a_3596_;
goto v___jp_3586_;
}
}
v___jp_3597_:
{
lean_object* v___x_3605_; double v___x_3606_; double v___x_3607_; double v___x_3608_; double v___x_3609_; double v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3605_ = lean_io_mono_nanos_now();
v___x_3606_ = lean_float_of_nat(v___y_3601_);
v___x_3607_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3608_ = lean_float_div(v___x_3606_, v___x_3607_);
v___x_3609_ = lean_float_of_nat(v___x_3605_);
v___x_3610_ = lean_float_div(v___x_3609_, v___x_3607_);
v___x_3611_ = lean_box_float(v___x_3608_);
v___x_3612_ = lean_box_float(v___x_3610_);
v___x_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3611_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3614_, 0, v_a_3604_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_3615_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3061_, v_hasTrace_3084_, v___x_3168_, v_options_3083_, v___y_3599_, v___y_3600_, v___y_3603_, v___x_3614_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_3592_ = v___y_3598_;
v___y_3593_ = v___y_3602_;
v___y_3594_ = v___x_3615_;
goto v___jp_3591_;
}
v___jp_3616_:
{
lean_object* v___x_3624_; 
v___x_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3624_, 0, v_a_3623_);
v___y_3598_ = v___y_3618_;
v___y_3599_ = v___y_3617_;
v___y_3600_ = v___y_3620_;
v___y_3601_ = v___y_3619_;
v___y_3602_ = v___y_3622_;
v___y_3603_ = v___y_3621_;
v_a_3604_ = v___x_3624_;
goto v___jp_3597_;
}
v___jp_3625_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = l_List_appendTR___redArg(v___y_3631_, v___y_3626_);
v___x_3636_ = l_List_appendTR___redArg(v___x_3635_, v_a_3634_);
v___y_3617_ = v___y_3628_;
v___y_3618_ = v___y_3627_;
v___y_3619_ = v___y_3630_;
v___y_3620_ = v___y_3629_;
v___y_3621_ = v___y_3633_;
v___y_3622_ = v___y_3632_;
v_a_3623_ = v___x_3636_;
goto v___jp_3616_;
}
v___jp_3637_:
{
lean_object* v___x_3645_; 
v___x_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3645_, 0, v_a_3644_);
v___y_3598_ = v___y_3639_;
v___y_3599_ = v___y_3638_;
v___y_3600_ = v___y_3641_;
v___y_3601_ = v___y_3640_;
v___y_3602_ = v___y_3643_;
v___y_3603_ = v___y_3642_;
v_a_3604_ = v___x_3645_;
goto v___jp_3597_;
}
v___jp_3646_:
{
if (lean_obj_tag(v___y_3653_) == 0)
{
lean_object* v_a_3654_; 
v_a_3654_ = lean_ctor_get(v___y_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref(v___y_3653_);
v___y_3617_ = v___y_3648_;
v___y_3618_ = v___y_3647_;
v___y_3619_ = v___y_3650_;
v___y_3620_ = v___y_3649_;
v___y_3621_ = v___y_3652_;
v___y_3622_ = v___y_3651_;
v_a_3623_ = v_a_3654_;
goto v___jp_3616_;
}
else
{
lean_object* v_a_3655_; 
v_a_3655_ = lean_ctor_get(v___y_3653_, 0);
lean_inc(v_a_3655_);
lean_dec_ref(v___y_3653_);
v___y_3638_ = v___y_3648_;
v___y_3639_ = v___y_3647_;
v___y_3640_ = v___y_3650_;
v___y_3641_ = v___y_3649_;
v___y_3642_ = v___y_3652_;
v___y_3643_ = v___y_3651_;
v_a_3644_ = v_a_3655_;
goto v___jp_3637_;
}
}
v___jp_3656_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3664_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3663_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_3647_ = v___y_3658_;
v___y_3648_ = v___y_3657_;
v___y_3649_ = v___y_3660_;
v___y_3650_ = v___y_3659_;
v___y_3651_ = v___y_3662_;
v___y_3652_ = v___y_3661_;
v___y_3653_ = v___x_3664_;
goto v___jp_3646_;
}
v___jp_3665_:
{
uint8_t v___x_3676_; 
v___x_3676_ = l_List_isEmpty___redArg(v___y_3667_);
lean_dec(v___y_3667_);
if (v___x_3676_ == 0)
{
lean_dec(v___y_3673_);
lean_dec(v___y_3668_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___y_3657_ = v___y_3670_;
v___y_3658_ = v___y_3669_;
v___y_3659_ = v___y_3672_;
v___y_3660_ = v___y_3671_;
v___y_3661_ = v___y_3675_;
v___y_3662_ = v___y_3674_;
goto v___jp_3656_;
}
else
{
if (v___y_3666_ == 0)
{
lean_object* v___x_3677_; 
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_3677_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3668_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3679_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref(v___x_3677_);
v___x_3679_ = l_List_appendTR___redArg(v___y_3673_, v_a_3678_);
v___y_3617_ = v___y_3670_;
v___y_3618_ = v___y_3669_;
v___y_3619_ = v___y_3672_;
v___y_3620_ = v___y_3671_;
v___y_3621_ = v___y_3675_;
v___y_3622_ = v___y_3674_;
v_a_3623_ = v___x_3679_;
goto v___jp_3616_;
}
else
{
lean_dec(v___y_3673_);
v___y_3647_ = v___y_3669_;
v___y_3648_ = v___y_3670_;
v___y_3649_ = v___y_3671_;
v___y_3650_ = v___y_3672_;
v___y_3651_ = v___y_3674_;
v___y_3652_ = v___y_3675_;
v___y_3653_ = v___x_3677_;
goto v___jp_3646_;
}
}
else
{
lean_dec(v___y_3673_);
lean_dec(v___y_3668_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___y_3657_ = v___y_3670_;
v___y_3658_ = v___y_3669_;
v___y_3659_ = v___y_3672_;
v___y_3660_ = v___y_3671_;
v___y_3661_ = v___y_3675_;
v___y_3662_ = v___y_3674_;
goto v___jp_3656_;
}
}
}
v___jp_3680_:
{
if (lean_obj_tag(v___y_3689_) == 0)
{
lean_object* v_a_3690_; 
v_a_3690_ = lean_ctor_get(v___y_3689_, 0);
lean_inc(v_a_3690_);
lean_dec_ref(v___y_3689_);
v___y_3626_ = v___y_3681_;
v___y_3627_ = v___y_3683_;
v___y_3628_ = v___y_3682_;
v___y_3629_ = v___y_3685_;
v___y_3630_ = v___y_3684_;
v___y_3631_ = v___y_3686_;
v___y_3632_ = v___y_3688_;
v___y_3633_ = v___y_3687_;
v_a_3634_ = v_a_3690_;
goto v___jp_3625_;
}
else
{
lean_object* v_a_3691_; 
lean_dec(v___y_3686_);
lean_dec(v___y_3681_);
v_a_3691_ = lean_ctor_get(v___y_3689_, 0);
lean_inc(v_a_3691_);
lean_dec_ref(v___y_3689_);
v___y_3638_ = v___y_3682_;
v___y_3639_ = v___y_3683_;
v___y_3640_ = v___y_3684_;
v___y_3641_ = v___y_3685_;
v___y_3642_ = v___y_3687_;
v___y_3643_ = v___y_3688_;
v_a_3644_ = v_a_3691_;
goto v___jp_3637_;
}
}
v___jp_3692_:
{
if (v___y_3703_ == 0)
{
lean_object* v___x_3704_; 
lean_dec_ref(v___y_3693_);
v___x_3704_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3702_, v_a_3067_, v_a_3069_);
lean_dec_ref(v___y_3702_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_dec_ref(v___x_3704_);
v___y_3626_ = v___y_3694_;
v___y_3627_ = v___y_3696_;
v___y_3628_ = v___y_3695_;
v___y_3629_ = v___y_3698_;
v___y_3630_ = v___y_3697_;
v___y_3631_ = v___y_3699_;
v___y_3632_ = v___y_3701_;
v___y_3633_ = v___y_3700_;
v_a_3634_ = v_snd_3078_;
goto v___jp_3625_;
}
else
{
lean_object* v_a_3705_; 
lean_dec(v___y_3699_);
lean_dec(v___y_3694_);
lean_dec(v_snd_3078_);
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref(v___x_3704_);
v___y_3638_ = v___y_3695_;
v___y_3639_ = v___y_3696_;
v___y_3640_ = v___y_3697_;
v___y_3641_ = v___y_3698_;
v___y_3642_ = v___y_3700_;
v___y_3643_ = v___y_3701_;
v_a_3644_ = v_a_3705_;
goto v___jp_3637_;
}
}
else
{
lean_dec_ref(v___y_3702_);
lean_dec(v_snd_3078_);
v___y_3681_ = v___y_3694_;
v___y_3682_ = v___y_3695_;
v___y_3683_ = v___y_3696_;
v___y_3684_ = v___y_3697_;
v___y_3685_ = v___y_3698_;
v___y_3686_ = v___y_3699_;
v___y_3687_ = v___y_3700_;
v___y_3688_ = v___y_3701_;
v___y_3689_ = v___y_3693_;
goto v___jp_3680_;
}
}
v___jp_3706_:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_Meta_saveState___redArg(v_a_3067_, v_a_3069_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3718_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3717_);
lean_dec_ref(v___x_3716_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_snd_3078_);
lean_inc(v_trace_3061_);
v___x_3718_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3708_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_dec(v_a_3717_);
lean_dec(v_snd_3078_);
v___y_3681_ = v___y_3707_;
v___y_3682_ = v___y_3710_;
v___y_3683_ = v___y_3709_;
v___y_3684_ = v___y_3712_;
v___y_3685_ = v___y_3711_;
v___y_3686_ = v___y_3713_;
v___y_3687_ = v___y_3715_;
v___y_3688_ = v___y_3714_;
v___y_3689_ = v___x_3718_;
goto v___jp_3680_;
}
else
{
lean_object* v_a_3719_; uint8_t v___x_3720_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
v___x_3720_ = l_Lean_Exception_isInterrupt(v_a_3719_);
if (v___x_3720_ == 0)
{
uint8_t v___x_3721_; 
v___x_3721_ = l_Lean_Exception_isRuntime(v_a_3719_);
v___y_3693_ = v___x_3718_;
v___y_3694_ = v___y_3707_;
v___y_3695_ = v___y_3710_;
v___y_3696_ = v___y_3709_;
v___y_3697_ = v___y_3712_;
v___y_3698_ = v___y_3711_;
v___y_3699_ = v___y_3713_;
v___y_3700_ = v___y_3715_;
v___y_3701_ = v___y_3714_;
v___y_3702_ = v_a_3717_;
v___y_3703_ = v___x_3721_;
goto v___jp_3692_;
}
else
{
lean_dec(v_a_3719_);
v___y_3693_ = v___x_3718_;
v___y_3694_ = v___y_3707_;
v___y_3695_ = v___y_3710_;
v___y_3696_ = v___y_3709_;
v___y_3697_ = v___y_3712_;
v___y_3698_ = v___y_3711_;
v___y_3699_ = v___y_3713_;
v___y_3700_ = v___y_3715_;
v___y_3701_ = v___y_3714_;
v___y_3702_ = v_a_3717_;
v___y_3703_ = v___x_3720_;
goto v___jp_3692_;
}
}
}
else
{
lean_object* v_a_3722_; 
lean_dec(v___y_3713_);
lean_dec(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3722_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3722_);
lean_dec_ref(v___x_3716_);
v___y_3638_ = v___y_3710_;
v___y_3639_ = v___y_3709_;
v___y_3640_ = v___y_3712_;
v___y_3641_ = v___y_3711_;
v___y_3642_ = v___y_3715_;
v___y_3643_ = v___y_3714_;
v_a_3644_ = v_a_3722_;
goto v___jp_3637_;
}
}
v___jp_3723_:
{
uint8_t v_commitIndependentGoals_3734_; lean_object* v___x_3735_; 
v_commitIndependentGoals_3734_ = lean_ctor_get_uint8(v_cfg_3060_, sizeof(void*)*4);
lean_inc(v___y_3730_);
v___x_3735_ = l_List_appendTR___redArg(v_a_3733_, v___y_3730_);
if (v_commitIndependentGoals_3734_ == 0)
{
v___y_3666_ = v___y_3724_;
v___y_3667_ = v___y_3725_;
v___y_3668_ = v___x_3735_;
v___y_3669_ = v___y_3726_;
v___y_3670_ = v___y_3727_;
v___y_3671_ = v___y_3728_;
v___y_3672_ = v___y_3729_;
v___y_3673_ = v___y_3730_;
v___y_3674_ = v___y_3731_;
v___y_3675_ = v___y_3732_;
goto v___jp_3665_;
}
else
{
uint8_t v___x_3736_; 
v___x_3736_ = l_List_isEmpty___redArg(v___y_3730_);
if (v___x_3736_ == 0)
{
v___y_3707_ = v___y_3725_;
v___y_3708_ = v___x_3735_;
v___y_3709_ = v___y_3726_;
v___y_3710_ = v___y_3727_;
v___y_3711_ = v___y_3728_;
v___y_3712_ = v___y_3729_;
v___y_3713_ = v___y_3730_;
v___y_3714_ = v___y_3731_;
v___y_3715_ = v___y_3732_;
goto v___jp_3706_;
}
else
{
if (v___y_3724_ == 0)
{
v___y_3666_ = v___y_3724_;
v___y_3667_ = v___y_3725_;
v___y_3668_ = v___x_3735_;
v___y_3669_ = v___y_3726_;
v___y_3670_ = v___y_3727_;
v___y_3671_ = v___y_3728_;
v___y_3672_ = v___y_3729_;
v___y_3673_ = v___y_3730_;
v___y_3674_ = v___y_3731_;
v___y_3675_ = v___y_3732_;
goto v___jp_3665_;
}
else
{
v___y_3707_ = v___y_3725_;
v___y_3708_ = v___x_3735_;
v___y_3709_ = v___y_3726_;
v___y_3710_ = v___y_3727_;
v___y_3711_ = v___y_3728_;
v___y_3712_ = v___y_3729_;
v___y_3713_ = v___y_3730_;
v___y_3714_ = v___y_3731_;
v___y_3715_ = v___y_3732_;
goto v___jp_3706_;
}
}
}
}
v___jp_3737_:
{
lean_object* v___x_3745_; double v___x_3746_; double v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3745_ = lean_io_get_num_heartbeats();
v___x_3746_ = lean_float_of_nat(v___y_3740_);
v___x_3747_ = lean_float_of_nat(v___x_3745_);
v___x_3748_ = lean_box_float(v___x_3746_);
v___x_3749_ = lean_box_float(v___x_3747_);
v___x_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3751_, 0, v_a_3744_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_3752_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_trace_3061_, v_hasTrace_3084_, v___x_3168_, v_options_3083_, v___y_3739_, v___y_3741_, v___y_3743_, v___x_3751_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_3592_ = v___y_3738_;
v___y_3593_ = v___y_3742_;
v___y_3594_ = v___x_3752_;
goto v___jp_3591_;
}
v___jp_3753_:
{
lean_object* v___x_3761_; 
v___x_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3761_, 0, v_a_3760_);
v___y_3738_ = v___y_3756_;
v___y_3739_ = v___y_3755_;
v___y_3740_ = v___y_3754_;
v___y_3741_ = v___y_3757_;
v___y_3742_ = v___y_3759_;
v___y_3743_ = v___y_3758_;
v_a_3744_ = v___x_3761_;
goto v___jp_3737_;
}
v___jp_3762_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = l_List_appendTR___redArg(v___y_3768_, v___y_3763_);
v___x_3773_ = l_List_appendTR___redArg(v___x_3772_, v_a_3771_);
v___y_3754_ = v___y_3766_;
v___y_3755_ = v___y_3765_;
v___y_3756_ = v___y_3764_;
v___y_3757_ = v___y_3767_;
v___y_3758_ = v___y_3770_;
v___y_3759_ = v___y_3769_;
v_a_3760_ = v___x_3773_;
goto v___jp_3753_;
}
v___jp_3774_:
{
lean_object* v___x_3782_; 
v___x_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3782_, 0, v_a_3781_);
v___y_3738_ = v___y_3777_;
v___y_3739_ = v___y_3776_;
v___y_3740_ = v___y_3775_;
v___y_3741_ = v___y_3778_;
v___y_3742_ = v___y_3780_;
v___y_3743_ = v___y_3779_;
v_a_3744_ = v___x_3782_;
goto v___jp_3737_;
}
v___jp_3783_:
{
if (lean_obj_tag(v___y_3790_) == 0)
{
lean_object* v_a_3791_; 
v_a_3791_ = lean_ctor_get(v___y_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref(v___y_3790_);
v___y_3754_ = v___y_3786_;
v___y_3755_ = v___y_3785_;
v___y_3756_ = v___y_3784_;
v___y_3757_ = v___y_3787_;
v___y_3758_ = v___y_3789_;
v___y_3759_ = v___y_3788_;
v_a_3760_ = v_a_3791_;
goto v___jp_3753_;
}
else
{
lean_object* v_a_3792_; 
v_a_3792_ = lean_ctor_get(v___y_3790_, 0);
lean_inc(v_a_3792_);
lean_dec_ref(v___y_3790_);
v___y_3775_ = v___y_3786_;
v___y_3776_ = v___y_3785_;
v___y_3777_ = v___y_3784_;
v___y_3778_ = v___y_3787_;
v___y_3779_ = v___y_3789_;
v___y_3780_ = v___y_3788_;
v_a_3781_ = v_a_3792_;
goto v___jp_3774_;
}
}
v___jp_3793_:
{
lean_object* v___x_3802_; 
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_3802_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3794_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3804_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref(v___x_3802_);
v___x_3804_ = l_List_appendTR___redArg(v___y_3799_, v_a_3803_);
v___y_3754_ = v___y_3797_;
v___y_3755_ = v___y_3796_;
v___y_3756_ = v___y_3795_;
v___y_3757_ = v___y_3798_;
v___y_3758_ = v___y_3801_;
v___y_3759_ = v___y_3800_;
v_a_3760_ = v___x_3804_;
goto v___jp_3753_;
}
else
{
lean_dec(v___y_3799_);
v___y_3784_ = v___y_3795_;
v___y_3785_ = v___y_3796_;
v___y_3786_ = v___y_3797_;
v___y_3787_ = v___y_3798_;
v___y_3788_ = v___y_3800_;
v___y_3789_ = v___y_3801_;
v___y_3790_ = v___x_3802_;
goto v___jp_3783_;
}
}
v___jp_3805_:
{
uint8_t v___x_3816_; 
v___x_3816_ = l_List_isEmpty___redArg(v___y_3807_);
lean_dec(v___y_3807_);
if (v___x_3816_ == 0)
{
if (v___y_3806_ == 0)
{
v___y_3794_ = v___y_3808_;
v___y_3795_ = v___y_3811_;
v___y_3796_ = v___y_3810_;
v___y_3797_ = v___y_3809_;
v___y_3798_ = v___y_3812_;
v___y_3799_ = v___y_3813_;
v___y_3800_ = v___y_3815_;
v___y_3801_ = v___y_3814_;
goto v___jp_3793_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
lean_dec(v___y_3813_);
lean_dec(v___y_3808_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___x_3817_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3818_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3817_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_3784_ = v___y_3811_;
v___y_3785_ = v___y_3810_;
v___y_3786_ = v___y_3809_;
v___y_3787_ = v___y_3812_;
v___y_3788_ = v___y_3815_;
v___y_3789_ = v___y_3814_;
v___y_3790_ = v___x_3818_;
goto v___jp_3783_;
}
}
else
{
v___y_3794_ = v___y_3808_;
v___y_3795_ = v___y_3811_;
v___y_3796_ = v___y_3810_;
v___y_3797_ = v___y_3809_;
v___y_3798_ = v___y_3812_;
v___y_3799_ = v___y_3813_;
v___y_3800_ = v___y_3815_;
v___y_3801_ = v___y_3814_;
goto v___jp_3793_;
}
}
v___jp_3819_:
{
if (lean_obj_tag(v___y_3828_) == 0)
{
lean_object* v_a_3829_; 
v_a_3829_ = lean_ctor_get(v___y_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref(v___y_3828_);
v___y_3763_ = v___y_3820_;
v___y_3764_ = v___y_3823_;
v___y_3765_ = v___y_3822_;
v___y_3766_ = v___y_3821_;
v___y_3767_ = v___y_3824_;
v___y_3768_ = v___y_3825_;
v___y_3769_ = v___y_3827_;
v___y_3770_ = v___y_3826_;
v_a_3771_ = v_a_3829_;
goto v___jp_3762_;
}
else
{
lean_object* v_a_3830_; 
lean_dec(v___y_3825_);
lean_dec(v___y_3820_);
v_a_3830_ = lean_ctor_get(v___y_3828_, 0);
lean_inc(v_a_3830_);
lean_dec_ref(v___y_3828_);
v___y_3775_ = v___y_3821_;
v___y_3776_ = v___y_3822_;
v___y_3777_ = v___y_3823_;
v___y_3778_ = v___y_3824_;
v___y_3779_ = v___y_3826_;
v___y_3780_ = v___y_3827_;
v_a_3781_ = v_a_3830_;
goto v___jp_3774_;
}
}
v___jp_3831_:
{
if (v___y_3842_ == 0)
{
lean_object* v___x_3843_; 
lean_dec_ref(v___y_3839_);
v___x_3843_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3833_, v_a_3067_, v_a_3069_);
lean_dec_ref(v___y_3833_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_dec_ref(v___x_3843_);
v___y_3763_ = v___y_3832_;
v___y_3764_ = v___y_3836_;
v___y_3765_ = v___y_3835_;
v___y_3766_ = v___y_3834_;
v___y_3767_ = v___y_3837_;
v___y_3768_ = v___y_3838_;
v___y_3769_ = v___y_3841_;
v___y_3770_ = v___y_3840_;
v_a_3771_ = v_snd_3078_;
goto v___jp_3762_;
}
else
{
lean_object* v_a_3844_; 
lean_dec(v___y_3838_);
lean_dec(v___y_3832_);
lean_dec(v_snd_3078_);
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref(v___x_3843_);
v___y_3775_ = v___y_3834_;
v___y_3776_ = v___y_3835_;
v___y_3777_ = v___y_3836_;
v___y_3778_ = v___y_3837_;
v___y_3779_ = v___y_3840_;
v___y_3780_ = v___y_3841_;
v_a_3781_ = v_a_3844_;
goto v___jp_3774_;
}
}
else
{
lean_dec_ref(v___y_3833_);
lean_dec(v_snd_3078_);
v___y_3820_ = v___y_3832_;
v___y_3821_ = v___y_3834_;
v___y_3822_ = v___y_3835_;
v___y_3823_ = v___y_3836_;
v___y_3824_ = v___y_3837_;
v___y_3825_ = v___y_3838_;
v___y_3826_ = v___y_3840_;
v___y_3827_ = v___y_3841_;
v___y_3828_ = v___y_3839_;
goto v___jp_3819_;
}
}
v___jp_3845_:
{
lean_object* v___x_3855_; 
v___x_3855_ = l_Lean_Meta_saveState___redArg(v_a_3067_, v_a_3069_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3857_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref(v___x_3855_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_snd_3078_);
lean_inc(v_trace_3061_);
v___x_3857_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3847_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_dec(v_a_3856_);
lean_dec(v_snd_3078_);
v___y_3820_ = v___y_3846_;
v___y_3821_ = v___y_3850_;
v___y_3822_ = v___y_3849_;
v___y_3823_ = v___y_3848_;
v___y_3824_ = v___y_3851_;
v___y_3825_ = v___y_3852_;
v___y_3826_ = v___y_3854_;
v___y_3827_ = v___y_3853_;
v___y_3828_ = v___x_3857_;
goto v___jp_3819_;
}
else
{
lean_object* v_a_3858_; uint8_t v___x_3859_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
v___x_3859_ = l_Lean_Exception_isInterrupt(v_a_3858_);
if (v___x_3859_ == 0)
{
uint8_t v___x_3860_; 
v___x_3860_ = l_Lean_Exception_isRuntime(v_a_3858_);
v___y_3832_ = v___y_3846_;
v___y_3833_ = v_a_3856_;
v___y_3834_ = v___y_3850_;
v___y_3835_ = v___y_3849_;
v___y_3836_ = v___y_3848_;
v___y_3837_ = v___y_3851_;
v___y_3838_ = v___y_3852_;
v___y_3839_ = v___x_3857_;
v___y_3840_ = v___y_3854_;
v___y_3841_ = v___y_3853_;
v___y_3842_ = v___x_3860_;
goto v___jp_3831_;
}
else
{
lean_dec(v_a_3858_);
v___y_3832_ = v___y_3846_;
v___y_3833_ = v_a_3856_;
v___y_3834_ = v___y_3850_;
v___y_3835_ = v___y_3849_;
v___y_3836_ = v___y_3848_;
v___y_3837_ = v___y_3851_;
v___y_3838_ = v___y_3852_;
v___y_3839_ = v___x_3857_;
v___y_3840_ = v___y_3854_;
v___y_3841_ = v___y_3853_;
v___y_3842_ = v___x_3859_;
goto v___jp_3831_;
}
}
}
else
{
lean_object* v_a_3861_; 
lean_dec(v___y_3852_);
lean_dec(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3861_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3861_);
lean_dec_ref(v___x_3855_);
v___y_3775_ = v___y_3850_;
v___y_3776_ = v___y_3849_;
v___y_3777_ = v___y_3848_;
v___y_3778_ = v___y_3851_;
v___y_3779_ = v___y_3854_;
v___y_3780_ = v___y_3853_;
v_a_3781_ = v_a_3861_;
goto v___jp_3774_;
}
}
v___jp_3862_:
{
uint8_t v_commitIndependentGoals_3873_; lean_object* v___x_3874_; 
v_commitIndependentGoals_3873_ = lean_ctor_get_uint8(v_cfg_3060_, sizeof(void*)*4);
lean_inc(v___y_3869_);
v___x_3874_ = l_List_appendTR___redArg(v_a_3872_, v___y_3869_);
if (v_commitIndependentGoals_3873_ == 0)
{
v___y_3806_ = v___y_3863_;
v___y_3807_ = v___y_3864_;
v___y_3808_ = v___x_3874_;
v___y_3809_ = v___y_3865_;
v___y_3810_ = v___y_3866_;
v___y_3811_ = v___y_3867_;
v___y_3812_ = v___y_3868_;
v___y_3813_ = v___y_3869_;
v___y_3814_ = v___y_3870_;
v___y_3815_ = v___y_3871_;
goto v___jp_3805_;
}
else
{
uint8_t v___x_3875_; 
v___x_3875_ = l_List_isEmpty___redArg(v___y_3869_);
if (v___x_3875_ == 0)
{
v___y_3846_ = v___y_3864_;
v___y_3847_ = v___x_3874_;
v___y_3848_ = v___y_3867_;
v___y_3849_ = v___y_3866_;
v___y_3850_ = v___y_3865_;
v___y_3851_ = v___y_3868_;
v___y_3852_ = v___y_3869_;
v___y_3853_ = v___y_3871_;
v___y_3854_ = v___y_3870_;
goto v___jp_3845_;
}
else
{
if (v___x_3082_ == 0)
{
v___y_3806_ = v___y_3863_;
v___y_3807_ = v___y_3864_;
v___y_3808_ = v___x_3874_;
v___y_3809_ = v___y_3865_;
v___y_3810_ = v___y_3866_;
v___y_3811_ = v___y_3867_;
v___y_3812_ = v___y_3868_;
v___y_3813_ = v___y_3869_;
v___y_3814_ = v___y_3870_;
v___y_3815_ = v___y_3871_;
goto v___jp_3805_;
}
else
{
v___y_3846_ = v___y_3864_;
v___y_3847_ = v___x_3874_;
v___y_3848_ = v___y_3867_;
v___y_3849_ = v___y_3866_;
v___y_3850_ = v___y_3865_;
v___y_3851_ = v___y_3868_;
v___y_3852_ = v___y_3869_;
v___y_3853_ = v___y_3871_;
v___y_3854_ = v___y_3870_;
goto v___jp_3845_;
}
}
}
}
v___jp_3876_:
{
lean_object* v___x_3885_; 
v___x_3885_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_3069_);
if (lean_obj_tag(v___x_3885_) == 0)
{
if (v___y_3877_ == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref(v___x_3885_);
v___x_3887_ = lean_io_mono_nanos_now();
v___x_3888_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3877_, v___x_3082_, v_goals_3064_, v___y_3879_, v_a_3067_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; lean_object* v___x_3890_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref(v___x_3888_);
v___x_3890_ = l_List_reverse___redArg(v_a_3889_);
v___y_3724_ = v___y_3877_;
v___y_3725_ = v___y_3878_;
v___y_3726_ = v___y_3881_;
v___y_3727_ = v___y_3880_;
v___y_3728_ = v_a_3886_;
v___y_3729_ = v___x_3887_;
v___y_3730_ = v___y_3882_;
v___y_3731_ = v___y_3884_;
v___y_3732_ = v___y_3883_;
v_a_3733_ = v___x_3890_;
goto v___jp_3723_;
}
else
{
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3891_; 
v_a_3891_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3891_);
lean_dec_ref(v___x_3888_);
v___y_3724_ = v___y_3877_;
v___y_3725_ = v___y_3878_;
v___y_3726_ = v___y_3881_;
v___y_3727_ = v___y_3880_;
v___y_3728_ = v_a_3886_;
v___y_3729_ = v___x_3887_;
v___y_3730_ = v___y_3882_;
v___y_3731_ = v___y_3884_;
v___y_3732_ = v___y_3883_;
v_a_3733_ = v_a_3891_;
goto v___jp_3723_;
}
else
{
lean_object* v_a_3892_; 
lean_dec(v___y_3882_);
lean_dec(v___y_3878_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3892_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3892_);
lean_dec_ref(v___x_3888_);
v___y_3638_ = v___y_3880_;
v___y_3639_ = v___y_3881_;
v___y_3640_ = v___x_3887_;
v___y_3641_ = v_a_3886_;
v___y_3642_ = v___y_3883_;
v___y_3643_ = v___y_3884_;
v_a_3644_ = v_a_3892_;
goto v___jp_3637_;
}
}
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v_a_3893_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3893_);
lean_dec_ref(v___x_3885_);
v___x_3894_ = lean_io_get_num_heartbeats();
v___x_3895_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3877_, v___x_3082_, v_goals_3064_, v___y_3879_, v_a_3067_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3897_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref(v___x_3895_);
v___x_3897_ = l_List_reverse___redArg(v_a_3896_);
v___y_3863_ = v___y_3877_;
v___y_3864_ = v___y_3878_;
v___y_3865_ = v___x_3894_;
v___y_3866_ = v___y_3880_;
v___y_3867_ = v___y_3881_;
v___y_3868_ = v_a_3893_;
v___y_3869_ = v___y_3882_;
v___y_3870_ = v___y_3883_;
v___y_3871_ = v___y_3884_;
v_a_3872_ = v___x_3897_;
goto v___jp_3862_;
}
else
{
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3898_; 
v_a_3898_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3898_);
lean_dec_ref(v___x_3895_);
v___y_3863_ = v___y_3877_;
v___y_3864_ = v___y_3878_;
v___y_3865_ = v___x_3894_;
v___y_3866_ = v___y_3880_;
v___y_3867_ = v___y_3881_;
v___y_3868_ = v_a_3893_;
v___y_3869_ = v___y_3882_;
v___y_3870_ = v___y_3883_;
v___y_3871_ = v___y_3884_;
v_a_3872_ = v_a_3898_;
goto v___jp_3862_;
}
else
{
lean_object* v_a_3899_; 
lean_dec(v___y_3882_);
lean_dec(v___y_3878_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3899_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3899_);
lean_dec_ref(v___x_3895_);
v___y_3775_ = v___x_3894_;
v___y_3776_ = v___y_3880_;
v___y_3777_ = v___y_3881_;
v___y_3778_ = v_a_3893_;
v___y_3779_ = v___y_3883_;
v___y_3780_ = v___y_3884_;
v_a_3781_ = v_a_3899_;
goto v___jp_3774_;
}
}
}
}
else
{
lean_object* v_a_3900_; 
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec(v_snd_3078_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3900_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3900_);
lean_dec_ref(v___x_3885_);
v___y_3587_ = v___y_3881_;
v___y_3588_ = v___y_3884_;
v_a_3589_ = v_a_3900_;
goto v___jp_3586_;
}
}
v___jp_3901_:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3905_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3904_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
v___y_3592_ = v___y_3902_;
v___y_3593_ = v___y_3903_;
v___y_3594_ = v___x_3905_;
goto v___jp_3591_;
}
v___jp_3906_:
{
uint8_t v___x_3913_; 
v___x_3913_ = l_List_isEmpty___redArg(v___y_3909_);
lean_dec(v___y_3909_);
if (v___x_3913_ == 0)
{
lean_dec(v___y_3911_);
lean_dec(v___y_3907_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___y_3902_ = v___y_3910_;
v___y_3903_ = v___y_3912_;
goto v___jp_3901_;
}
else
{
if (v___y_3908_ == 0)
{
lean_object* v___x_3914_; 
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_trace_3061_);
v___x_3914_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3907_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref(v___x_3914_);
v___x_3916_ = l_List_appendTR___redArg(v___y_3911_, v_a_3915_);
v___y_3574_ = v___y_3910_;
v___y_3575_ = v___y_3912_;
v_a_3576_ = v___x_3916_;
goto v___jp_3573_;
}
else
{
lean_dec(v___y_3911_);
v___y_3592_ = v___y_3910_;
v___y_3593_ = v___y_3912_;
v___y_3594_ = v___x_3914_;
goto v___jp_3591_;
}
}
else
{
lean_dec(v___y_3911_);
lean_dec(v___y_3907_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v___y_3902_ = v___y_3910_;
v___y_3903_ = v___y_3912_;
goto v___jp_3901_;
}
}
}
v___jp_3917_:
{
if (lean_obj_tag(v___y_3922_) == 0)
{
lean_object* v_a_3923_; 
v_a_3923_ = lean_ctor_get(v___y_3922_, 0);
lean_inc(v_a_3923_);
lean_dec_ref(v___y_3922_);
v___y_3579_ = v___y_3918_;
v___y_3580_ = v___y_3919_;
v___y_3581_ = v___y_3920_;
v___y_3582_ = v___y_3921_;
v_a_3583_ = v_a_3923_;
goto v___jp_3578_;
}
else
{
lean_object* v_a_3924_; 
lean_dec(v___y_3920_);
lean_dec(v___y_3918_);
v_a_3924_ = lean_ctor_get(v___y_3922_, 0);
lean_inc(v_a_3924_);
lean_dec_ref(v___y_3922_);
v___y_3587_ = v___y_3919_;
v___y_3588_ = v___y_3921_;
v_a_3589_ = v_a_3924_;
goto v___jp_3586_;
}
}
v___jp_3925_:
{
if (v___y_3932_ == 0)
{
lean_object* v___x_3933_; 
lean_dec_ref(v___y_3926_);
v___x_3933_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3928_, v_a_3067_, v_a_3069_);
lean_dec_ref(v___y_3928_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_dec_ref(v___x_3933_);
v___y_3579_ = v___y_3927_;
v___y_3580_ = v___y_3929_;
v___y_3581_ = v___y_3930_;
v___y_3582_ = v___y_3931_;
v_a_3583_ = v_snd_3078_;
goto v___jp_3578_;
}
else
{
lean_object* v_a_3934_; 
lean_dec(v___y_3930_);
lean_dec(v___y_3927_);
lean_dec(v_snd_3078_);
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref(v___x_3933_);
v___y_3587_ = v___y_3929_;
v___y_3588_ = v___y_3931_;
v_a_3589_ = v_a_3934_;
goto v___jp_3586_;
}
}
else
{
lean_dec_ref(v___y_3928_);
lean_dec(v_snd_3078_);
v___y_3918_ = v___y_3927_;
v___y_3919_ = v___y_3929_;
v___y_3920_ = v___y_3930_;
v___y_3921_ = v___y_3931_;
v___y_3922_ = v___y_3926_;
goto v___jp_3917_;
}
}
v___jp_3935_:
{
lean_object* v___x_3941_; 
v___x_3941_ = l_Lean_Meta_saveState___redArg(v_a_3067_, v_a_3069_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3943_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref(v___x_3941_);
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
lean_inc(v_snd_3078_);
lean_inc(v_trace_3061_);
v___x_3943_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v___y_3936_, v_snd_3078_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_dec(v_a_3942_);
lean_dec(v_snd_3078_);
v___y_3918_ = v___y_3937_;
v___y_3919_ = v___y_3938_;
v___y_3920_ = v___y_3939_;
v___y_3921_ = v___y_3940_;
v___y_3922_ = v___x_3943_;
goto v___jp_3917_;
}
else
{
lean_object* v_a_3944_; uint8_t v___x_3945_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
v___x_3945_ = l_Lean_Exception_isInterrupt(v_a_3944_);
if (v___x_3945_ == 0)
{
uint8_t v___x_3946_; 
v___x_3946_ = l_Lean_Exception_isRuntime(v_a_3944_);
v___y_3926_ = v___x_3943_;
v___y_3927_ = v___y_3937_;
v___y_3928_ = v_a_3942_;
v___y_3929_ = v___y_3938_;
v___y_3930_ = v___y_3939_;
v___y_3931_ = v___y_3940_;
v___y_3932_ = v___x_3946_;
goto v___jp_3925_;
}
else
{
lean_dec(v_a_3944_);
v___y_3926_ = v___x_3943_;
v___y_3927_ = v___y_3937_;
v___y_3928_ = v_a_3942_;
v___y_3929_ = v___y_3938_;
v___y_3930_ = v___y_3939_;
v___y_3931_ = v___y_3940_;
v___y_3932_ = v___x_3945_;
goto v___jp_3925_;
}
}
}
else
{
lean_object* v_a_3947_; 
lean_dec(v___y_3939_);
lean_dec(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3947_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3947_);
lean_dec_ref(v___x_3941_);
v___y_3587_ = v___y_3938_;
v___y_3588_ = v___y_3940_;
v_a_3589_ = v_a_3947_;
goto v___jp_3586_;
}
}
v___jp_3948_:
{
uint8_t v_commitIndependentGoals_3955_; lean_object* v___x_3956_; 
v_commitIndependentGoals_3955_ = lean_ctor_get_uint8(v_cfg_3060_, sizeof(void*)*4);
lean_inc(v___y_3952_);
v___x_3956_ = l_List_appendTR___redArg(v_a_3954_, v___y_3952_);
if (v_commitIndependentGoals_3955_ == 0)
{
v___y_3907_ = v___x_3956_;
v___y_3908_ = v___y_3949_;
v___y_3909_ = v___y_3950_;
v___y_3910_ = v___y_3951_;
v___y_3911_ = v___y_3952_;
v___y_3912_ = v___y_3953_;
goto v___jp_3906_;
}
else
{
uint8_t v___x_3957_; 
v___x_3957_ = l_List_isEmpty___redArg(v___y_3952_);
if (v___x_3957_ == 0)
{
v___y_3936_ = v___x_3956_;
v___y_3937_ = v___y_3950_;
v___y_3938_ = v___y_3951_;
v___y_3939_ = v___y_3952_;
v___y_3940_ = v___y_3953_;
goto v___jp_3935_;
}
else
{
if (v___y_3949_ == 0)
{
v___y_3907_ = v___x_3956_;
v___y_3908_ = v___y_3949_;
v___y_3909_ = v___y_3950_;
v___y_3910_ = v___y_3951_;
v___y_3911_ = v___y_3952_;
v___y_3912_ = v___y_3953_;
goto v___jp_3906_;
}
else
{
v___y_3936_ = v___x_3956_;
v___y_3937_ = v___y_3950_;
v___y_3938_ = v___y_3951_;
v___y_3939_ = v___y_3952_;
v___y_3940_ = v___y_3953_;
goto v___jp_3935_;
}
}
}
}
v___jp_3958_:
{
lean_object* v___x_3959_; 
v___x_3959_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(v_a_3069_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v___x_3961_; uint8_t v___x_3962_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref(v___x_3959_);
v___x_3961_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3962_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_3083_, v___x_3961_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_io_mono_nanos_now();
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
v___x_3964_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3077_, v___f_3085_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v_fst_3966_; lean_object* v_snd_3967_; lean_object* v___x_3968_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref(v___x_3964_);
v_fst_3966_ = lean_ctor_get(v_a_3965_, 0);
lean_inc(v_fst_3966_);
v_snd_3967_ = lean_ctor_get(v_a_3965_, 1);
lean_inc(v_snd_3967_);
lean_dec(v_a_3965_);
lean_inc(v_trace_3061_);
v___x_3968_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_3061_, v_a_3068_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3970_; lean_object* v___f_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref(v___x_3968_);
v___x_3970_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3967_, v___x_3074_);
lean_inc(v___x_3970_);
lean_inc(v_fst_3966_);
v___f_3971_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3971_, 0, v_fst_3966_);
lean_closure_set(v___f_3971_, 1, v___x_3970_);
v___x_3972_ = lean_box(0);
v___x_3973_ = lean_unbox(v_a_3969_);
if (v___x_3973_ == 0)
{
lean_object* v___x_3974_; uint8_t v___x_3975_; 
v___x_3974_ = l_Lean_trace_profiler;
v___x_3975_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_3083_, v___x_3974_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; 
lean_dec_ref(v___f_3971_);
lean_dec(v_a_3969_);
v___x_3976_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3084_, v___x_3962_, v_goals_3064_, v___x_3972_, v_a_3067_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; lean_object* v___x_3978_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref(v___x_3976_);
v___x_3978_ = l_List_reverse___redArg(v_a_3977_);
v___y_3551_ = v___x_3975_;
v___y_3552_ = v___x_3970_;
v___y_3553_ = v___x_3963_;
v___y_3554_ = v_a_3960_;
v___y_3555_ = v_fst_3966_;
v_a_3556_ = v___x_3978_;
goto v___jp_3550_;
}
else
{
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3979_; 
v_a_3979_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3979_);
lean_dec_ref(v___x_3976_);
v___y_3551_ = v___x_3975_;
v___y_3552_ = v___x_3970_;
v___y_3553_ = v___x_3963_;
v___y_3554_ = v_a_3960_;
v___y_3555_ = v_fst_3966_;
v_a_3556_ = v_a_3979_;
goto v___jp_3550_;
}
else
{
lean_object* v_a_3980_; 
lean_dec(v___x_3970_);
lean_dec(v_fst_3966_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3980_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3980_);
lean_dec_ref(v___x_3976_);
v___y_3188_ = v___x_3963_;
v___y_3189_ = v_a_3960_;
v_a_3190_ = v_a_3980_;
goto v___jp_3187_;
}
}
}
else
{
uint8_t v___x_3981_; 
v___x_3981_ = lean_unbox(v_a_3969_);
lean_dec(v_a_3969_);
v___y_3510_ = v___x_3962_;
v___y_3511_ = v___f_3971_;
v___y_3512_ = v___x_3970_;
v___y_3513_ = v___x_3981_;
v___y_3514_ = v___x_3963_;
v___y_3515_ = v_a_3960_;
v___y_3516_ = v___x_3972_;
v___y_3517_ = v_fst_3966_;
goto v___jp_3509_;
}
}
else
{
uint8_t v___x_3982_; 
v___x_3982_ = lean_unbox(v_a_3969_);
lean_dec(v_a_3969_);
v___y_3510_ = v___x_3962_;
v___y_3511_ = v___f_3971_;
v___y_3512_ = v___x_3970_;
v___y_3513_ = v___x_3982_;
v___y_3514_ = v___x_3963_;
v___y_3515_ = v_a_3960_;
v___y_3516_ = v___x_3972_;
v___y_3517_ = v_fst_3966_;
goto v___jp_3509_;
}
}
else
{
lean_object* v_a_3983_; 
lean_dec(v_snd_3967_);
lean_dec(v_fst_3966_);
lean_dec(v_snd_3078_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3983_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3983_);
lean_dec_ref(v___x_3968_);
v___y_3188_ = v___x_3963_;
v___y_3189_ = v_a_3960_;
v_a_3190_ = v_a_3983_;
goto v___jp_3187_;
}
}
else
{
lean_object* v_a_3984_; 
lean_dec(v_snd_3078_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_3984_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3984_);
lean_dec_ref(v___x_3964_);
v___y_3188_ = v___x_3963_;
v___y_3189_ = v_a_3960_;
v_a_3190_ = v_a_3984_;
goto v___jp_3187_;
}
}
else
{
lean_object* v___x_3985_; lean_object* v___x_3986_; 
lean_del_object(v___x_3080_);
v___x_3985_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3069_);
lean_inc_ref(v_a_3068_);
lean_inc(v_a_3067_);
lean_inc_ref(v_a_3066_);
v___x_3986_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3077_, v___f_3085_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v_a_3987_; lean_object* v_fst_3988_; lean_object* v_snd_3989_; lean_object* v___x_3990_; 
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_3987_);
lean_dec_ref(v___x_3986_);
v_fst_3988_ = lean_ctor_get(v_a_3987_, 0);
lean_inc(v_fst_3988_);
v_snd_3989_ = lean_ctor_get(v_a_3987_, 1);
lean_inc(v_snd_3989_);
lean_dec(v_a_3987_);
lean_inc(v_trace_3061_);
v___x_3990_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_trace_3061_, v_a_3068_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3992_; lean_object* v___f_3993_; lean_object* v___x_3994_; uint8_t v___x_3995_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_3991_);
lean_dec_ref(v___x_3990_);
v___x_3992_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3989_, v___x_3074_);
lean_inc(v___x_3992_);
lean_inc(v_fst_3988_);
v___f_3993_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3993_, 0, v_fst_3988_);
lean_closure_set(v___f_3993_, 1, v___x_3992_);
v___x_3994_ = lean_box(0);
v___x_3995_ = lean_unbox(v_a_3991_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3996_; uint8_t v___x_3997_; 
v___x_3996_ = l_Lean_trace_profiler;
v___x_3997_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_options_3083_, v___x_3996_);
if (v___x_3997_ == 0)
{
lean_object* v___x_3998_; 
lean_dec_ref(v___f_3993_);
lean_dec(v_a_3991_);
v___x_3998_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3962_, v___x_3082_, v_goals_3064_, v___x_3994_, v_a_3067_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4000_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref(v___x_3998_);
v___x_4000_ = l_List_reverse___redArg(v_a_3999_);
v___y_3949_ = v___x_3997_;
v___y_3950_ = v_fst_3988_;
v___y_3951_ = v_a_3960_;
v___y_3952_ = v___x_3992_;
v___y_3953_ = v___x_3985_;
v_a_3954_ = v___x_4000_;
goto v___jp_3948_;
}
else
{
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_4001_; 
v_a_4001_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v___x_3998_);
v___y_3949_ = v___x_3997_;
v___y_3950_ = v_fst_3988_;
v___y_3951_ = v_a_3960_;
v___y_3952_ = v___x_3992_;
v___y_3953_ = v___x_3985_;
v_a_3954_ = v_a_4001_;
goto v___jp_3948_;
}
else
{
lean_object* v_a_4002_; 
lean_dec(v___x_3992_);
lean_dec(v_fst_3988_);
lean_dec(v_snd_3078_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_4002_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_4002_);
lean_dec_ref(v___x_3998_);
v___y_3587_ = v_a_3960_;
v___y_3588_ = v___x_3985_;
v_a_3589_ = v_a_4002_;
goto v___jp_3586_;
}
}
}
else
{
uint8_t v___x_4003_; 
v___x_4003_ = lean_unbox(v_a_3991_);
lean_dec(v_a_3991_);
v___y_3877_ = v___x_3962_;
v___y_3878_ = v_fst_3988_;
v___y_3879_ = v___x_3994_;
v___y_3880_ = v___x_4003_;
v___y_3881_ = v_a_3960_;
v___y_3882_ = v___x_3992_;
v___y_3883_ = v___f_3993_;
v___y_3884_ = v___x_3985_;
goto v___jp_3876_;
}
}
else
{
uint8_t v___x_4004_; 
v___x_4004_ = lean_unbox(v_a_3991_);
lean_dec(v_a_3991_);
v___y_3877_ = v___x_3962_;
v___y_3878_ = v_fst_3988_;
v___y_3879_ = v___x_3994_;
v___y_3880_ = v___x_4004_;
v___y_3881_ = v_a_3960_;
v___y_3882_ = v___x_3992_;
v___y_3883_ = v___f_3993_;
v___y_3884_ = v___x_3985_;
goto v___jp_3876_;
}
}
else
{
lean_object* v_a_4005_; 
lean_dec(v_snd_3989_);
lean_dec(v_fst_3988_);
lean_dec(v_snd_3078_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_4005_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_4005_);
lean_dec_ref(v___x_3990_);
v___y_3587_ = v_a_3960_;
v___y_3588_ = v___x_3985_;
v_a_3589_ = v_a_4005_;
goto v___jp_3586_;
}
}
else
{
lean_object* v_a_4006_; 
lean_dec(v_snd_3078_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec_ref(v_cfg_3060_);
v_a_4006_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_a_4006_);
lean_dec_ref(v___x_3986_);
v___y_3587_ = v_a_3960_;
v___y_3588_ = v___x_3985_;
v_a_3589_ = v_a_4006_;
goto v___jp_3586_;
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec_ref(v___f_3167_);
lean_dec(v_a_3166_);
lean_dec_ref(v___f_3085_);
lean_dec_ref(v_options_3083_);
lean_del_object(v___x_3080_);
lean_dec(v_snd_3078_);
lean_dec(v_fst_3077_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
v_a_4007_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3959_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3959_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec_ref(v___f_3085_);
lean_del_object(v___x_3080_);
lean_dec(v_snd_3078_);
lean_dec(v_fst_3077_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
v_a_4309_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_3165_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_3165_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
}
else
{
lean_object* v_maxDepth_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
lean_del_object(v___x_3080_);
lean_dec(v_snd_3078_);
lean_dec(v_fst_3077_);
lean_dec(v_goals_3064_);
v_maxDepth_4317_ = lean_ctor_get(v_cfg_3060_, 0);
lean_inc(v_maxDepth_4317_);
v___x_4318_ = lean_box(0);
v___x_4319_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_3060_, v_trace_3061_, v_next_3062_, v_orig_3063_, v_maxDepth_4317_, v_remaining_3065_, v___x_4318_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
return v___x_4319_;
}
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_remaining_3065_);
lean_dec(v_goals_3064_);
lean_dec(v_orig_3063_);
lean_dec_ref(v_next_3062_);
lean_dec(v_trace_3061_);
lean_dec_ref(v_cfg_3060_);
v_a_4321_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_3075_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_3075_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
v___jp_3071_:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3073_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3072_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
lean_dec(v_a_3069_);
lean_dec_ref(v_a_3068_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
return v___x_3073_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_4329_, lean_object* v_trace_4330_, lean_object* v_next_4331_, lean_object* v_orig_4332_, lean_object* v_goals_4333_, lean_object* v_remaining_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4329_, v_trace_4330_, v_next_4331_, v_orig_4332_, v_goals_4333_, v_remaining_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_4341_, lean_object* v_00_u03b2_4342_, lean_object* v_L_4343_, lean_object* v_f_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v___x_4350_; 
v___x_4350_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_4343_, v_f_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_4351_, lean_object* v_00_u03b2_4352_, lean_object* v_L_4353_, lean_object* v_f_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_4351_, v_00_u03b2_4352_, v_L_4353_, v_f_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_4361_, lean_object* v_x_4362_, lean_object* v_x_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_4361_, v_x_4362_, v_x_4363_, v___y_4365_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_4370_, lean_object* v_x_4371_, lean_object* v_x_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
uint8_t v___x_54090__boxed_4378_; lean_object* v_res_4379_; 
v___x_54090__boxed_4378_ = lean_unbox(v___x_4370_);
v_res_4379_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_54090__boxed_4378_, v_x_4371_, v_x_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_4380_, uint8_t v___x_4381_, lean_object* v_x_4382_, lean_object* v_x_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
lean_object* v___x_4389_; 
v___x_4389_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_4380_, v___x_4381_, v_x_4382_, v_x_4383_, v___y_4385_);
return v___x_4389_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_4390_, lean_object* v___x_4391_, lean_object* v_x_4392_, lean_object* v_x_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
uint8_t v___x_54116__boxed_4399_; uint8_t v___x_54117__boxed_4400_; lean_object* v_res_4401_; 
v___x_54116__boxed_4399_ = lean_unbox(v___x_4390_);
v___x_54117__boxed_4400_ = lean_unbox(v___x_4391_);
v_res_4401_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_54116__boxed_4399_, v___x_54117__boxed_4400_, v_x_4392_, v_x_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_4402_, lean_object* v_00_u03b2_4403_, lean_object* v_f_4404_, lean_object* v_x_4405_, lean_object* v_x_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
lean_object* v___x_4412_; 
v___x_4412_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_4404_, v_x_4405_, v_x_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
return v___x_4412_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4413_, lean_object* v_00_u03b2_4414_, lean_object* v_f_4415_, lean_object* v_x_4416_, lean_object* v_x_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_4413_, v_00_u03b2_4414_, v_f_4415_, v_x_4416_, v_x_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_4424_, lean_object* v_00_u03b2_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_){
_start:
{
lean_object* v___x_4428_; 
v___x_4428_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_4426_, v_a_4427_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_4429_, lean_object* v_00_u03b2_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_){
_start:
{
lean_object* v___x_4433_; 
v___x_4433_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_4431_, v_a_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_4434_, lean_object* v_g_4435_, lean_object* v_f_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v___x_4442_; 
lean_inc(v___y_4440_);
lean_inc_ref(v___y_4439_);
lean_inc(v___y_4438_);
lean_inc_ref(v___y_4437_);
v___x_4442_ = lean_apply_6(v_next_4434_, v_g_4435_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, lean_box(0));
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v___x_4444_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
lean_dec_ref(v___x_4442_);
v___x_4444_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_4443_, v_f_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
return v___x_4444_;
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v_f_4436_);
v_a_4445_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4442_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4442_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_4453_, lean_object* v_g_4454_, lean_object* v_f_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_4453_, v_g_4454_, v_f_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_4462_, lean_object* v_trace_4463_, lean_object* v_next_4464_, lean_object* v_goals_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_resolve_4471_; lean_object* v___x_4472_; 
v_resolve_4471_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_4471_, 0, v_next_4464_);
lean_inc_n(v_goals_4465_, 2);
v___x_4472_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4462_, v_trace_4463_, v_resolve_4471_, v_goals_4465_, v_goals_4465_, v_goals_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_4473_, lean_object* v_trace_4474_, lean_object* v_next_4475_, lean_object* v_goals_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_4473_, v_trace_4474_, v_next_4475_, v_goals_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_);
return v_res_4482_;
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

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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isIndependentOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "success!"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 42, .m_data = "⏭️ deemed acceptable, returning as subgoal"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 35, .m_data = "⏬ discharger generated new subgoals"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 45, .m_data = "⏸️ suspending search and returning as subgoal"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "BacktrackConfig.proc failed: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "discarding already assigned goal "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_n(v_toPure_137_, 2);
lean_dec_ref(v_toApplicative_133_);
v___f_138_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__0));
v___f_139_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__1));
v___f_140_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__2));
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_unsigned_to_nat(32u);
v___x_155_ = lean_mk_empty_array_with_capacity(v___x_154_);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_157_ = ((size_t)5ULL);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_unsigned_to_nat(32u);
v___x_160_ = lean_mk_empty_array_with_capacity(v___x_159_);
v___x_161_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0);
v___x_162_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
lean_ctor_set(v___x_162_, 2, v___x_158_);
lean_ctor_set(v___x_162_, 3, v___x_158_);
lean_ctor_set_usize(v___x_162_, 4, v___x_157_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; lean_object* v_traceState_166_; lean_object* v_traces_167_; lean_object* v___x_168_; lean_object* v_traceState_169_; lean_object* v_env_170_; lean_object* v_nextMacroScope_171_; lean_object* v_ngen_172_; lean_object* v_auxDeclNGen_173_; lean_object* v_cache_174_; lean_object* v_messages_175_; lean_object* v_infoState_176_; lean_object* v_snapshotTasks_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_196_; 
v___x_165_ = lean_st_ref_get(v___y_163_);
v_traceState_166_ = lean_ctor_get(v___x_165_, 4);
lean_inc_ref(v_traceState_166_);
lean_dec(v___x_165_);
v_traces_167_ = lean_ctor_get(v_traceState_166_, 0);
lean_inc_ref(v_traces_167_);
lean_dec_ref(v_traceState_166_);
v___x_168_ = lean_st_ref_take(v___y_163_);
v_traceState_169_ = lean_ctor_get(v___x_168_, 4);
v_env_170_ = lean_ctor_get(v___x_168_, 0);
v_nextMacroScope_171_ = lean_ctor_get(v___x_168_, 1);
v_ngen_172_ = lean_ctor_get(v___x_168_, 2);
v_auxDeclNGen_173_ = lean_ctor_get(v___x_168_, 3);
v_cache_174_ = lean_ctor_get(v___x_168_, 5);
v_messages_175_ = lean_ctor_get(v___x_168_, 6);
v_infoState_176_ = lean_ctor_get(v___x_168_, 7);
v_snapshotTasks_177_ = lean_ctor_get(v___x_168_, 8);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_196_ == 0)
{
v___x_179_ = v___x_168_;
v_isShared_180_ = v_isSharedCheck_196_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_snapshotTasks_177_);
lean_inc(v_infoState_176_);
lean_inc(v_messages_175_);
lean_inc(v_cache_174_);
lean_inc(v_traceState_169_);
lean_inc(v_auxDeclNGen_173_);
lean_inc(v_ngen_172_);
lean_inc(v_nextMacroScope_171_);
lean_inc(v_env_170_);
lean_dec(v___x_168_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_196_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
uint64_t v_tid_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_194_; 
v_tid_181_ = lean_ctor_get_uint64(v_traceState_169_, sizeof(void*)*1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_traceState_169_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v_traceState_169_, 0);
lean_dec(v_unused_195_);
v___x_183_ = v_traceState_169_;
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
else
{
lean_dec(v_traceState_169_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_185_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_185_);
v___x_187_ = v___x_183_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_185_);
lean_ctor_set_uint64(v_reuseFailAlloc_193_, sizeof(void*)*1, v_tid_181_);
v___x_187_ = v_reuseFailAlloc_193_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 4, v___x_187_);
v___x_189_ = v___x_179_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_env_170_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_nextMacroScope_171_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_ngen_172_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_auxDeclNGen_173_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_192_, 5, v_cache_174_);
lean_ctor_set(v_reuseFailAlloc_192_, 6, v_messages_175_);
lean_ctor_set(v_reuseFailAlloc_192_, 7, v_infoState_176_);
lean_ctor_set(v_reuseFailAlloc_192_, 8, v_snapshotTasks_177_);
v___x_189_ = v_reuseFailAlloc_192_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_st_ref_set(v___y_163_, v___x_189_);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v_traces_167_);
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___boxed(lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v___y_197_);
lean_dec(v___y_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v___y_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___boxed(lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(lean_object* v_opts_212_, lean_object* v_opt_213_){
_start:
{
lean_object* v_name_214_; lean_object* v_defValue_215_; lean_object* v_map_216_; lean_object* v___x_217_; 
v_name_214_ = lean_ctor_get(v_opt_213_, 0);
v_defValue_215_ = lean_ctor_get(v_opt_213_, 1);
v_map_216_ = lean_ctor_get(v_opts_212_, 0);
v___x_217_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_216_, v_name_214_);
if (lean_obj_tag(v___x_217_) == 0)
{
uint8_t v___x_218_; 
v___x_218_ = lean_unbox(v_defValue_215_);
return v___x_218_;
}
else
{
lean_object* v_val_219_; 
v_val_219_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_val_219_);
lean_dec_ref(v___x_217_);
if (lean_obj_tag(v_val_219_) == 1)
{
uint8_t v_v_220_; 
v_v_220_ = lean_ctor_get_uint8(v_val_219_, 0);
lean_dec_ref(v_val_219_);
return v_v_220_;
}
else
{
uint8_t v___x_221_; 
lean_dec(v_val_219_);
v___x_221_ = lean_unbox(v_defValue_215_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___boxed(lean_object* v_opts_222_, lean_object* v_opt_223_){
_start:
{
uint8_t v_res_224_; lean_object* v_r_225_; 
v_res_224_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_222_, v_opt_223_);
lean_dec_ref(v_opt_223_);
lean_dec_ref(v_opts_222_);
v_r_225_ = lean_box(v_res_224_);
return v_r_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(lean_object* v_x_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_saveState___redArg(v___y_228_, v___y_230_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_234_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref(v___x_232_);
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
lean_inc(v___y_228_);
lean_inc_ref(v___y_227_);
v___x_234_ = lean_apply_5(v_x_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, lean_box(0));
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_a_233_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v_a_235_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_273_; 
v_a_244_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_273_ == 0)
{
v___x_246_ = v___x_234_;
v_isShared_247_ = v_isSharedCheck_273_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_234_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_273_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v___y_249_; uint8_t v___x_271_; 
v___x_271_ = l_Lean_Exception_isInterrupt(v_a_244_);
if (v___x_271_ == 0)
{
uint8_t v___x_272_; 
lean_inc(v_a_244_);
v___x_272_ = l_Lean_Exception_isRuntime(v_a_244_);
v___y_249_ = v___x_272_;
goto v___jp_248_;
}
else
{
v___y_249_ = v___x_271_;
goto v___jp_248_;
}
v___jp_248_:
{
if (v___y_249_ == 0)
{
lean_object* v___x_250_; 
lean_del_object(v___x_246_);
lean_dec(v_a_244_);
v___x_250_ = l_Lean_Meta_SavedState_restore___redArg(v_a_233_, v___y_228_, v___y_230_);
lean_dec(v_a_233_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_258_; 
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v___x_250_, 0);
lean_dec(v_unused_259_);
v___x_252_ = v___x_250_;
v_isShared_253_ = v_isSharedCheck_258_;
goto v_resetjp_251_;
}
else
{
lean_dec(v___x_250_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_258_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = lean_box(0);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_254_);
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
v_a_260_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_250_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_250_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
else
{
lean_object* v___x_269_; 
lean_dec(v_a_233_);
if (v_isShared_247_ == 0)
{
v___x_269_ = v___x_246_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_244_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v_x_226_);
v_a_274_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_232_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_232_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___boxed(lean_object* v_x_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v_x_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object* v_00_u03b1_289_, lean_object* v_x_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v_x_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object* v_00_u03b1_297_, lean_object* v_x_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_00_u03b1_297_, v_x_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(lean_object* v_msgData_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; lean_object* v_env_312_; lean_object* v___x_313_; lean_object* v_mctx_314_; lean_object* v_lctx_315_; lean_object* v_options_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_311_ = lean_st_ref_get(v___y_309_);
v_env_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_env_312_);
lean_dec(v___x_311_);
v___x_313_ = lean_st_ref_get(v___y_307_);
v_mctx_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_mctx_314_);
lean_dec(v___x_313_);
v_lctx_315_ = lean_ctor_get(v___y_306_, 2);
v_options_316_ = lean_ctor_get(v___y_308_, 2);
lean_inc_ref(v_options_316_);
lean_inc_ref(v_lctx_315_);
v___x_317_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_317_, 0, v_env_312_);
lean_ctor_set(v___x_317_, 1, v_mctx_314_);
lean_ctor_set(v___x_317_, 2, v_lctx_315_);
lean_ctor_set(v___x_317_, 3, v_options_316_);
v___x_318_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v_msgData_305_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___boxed(lean_object* v_msgData_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msgData_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0));
v___x_329_ = l_Lean_stringToMessageData(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object* v_x_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object* v_x_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(v_x_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec_ref(v_x_338_);
return v_res_344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0));
v___x_347_ = l_Lean_stringToMessageData(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object* v_x_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object* v_x_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(v_x_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec_ref(v_x_356_);
return v_res_362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0));
v___x_365_ = l_Lean_stringToMessageData(v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object* v_x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec_ref(v_x_374_);
return v_res_380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object* v_x_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec_ref(v_x_392_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(lean_object* v_opts_399_, lean_object* v_opt_400_){
_start:
{
lean_object* v_name_401_; lean_object* v_defValue_402_; lean_object* v_map_403_; lean_object* v___x_404_; 
v_name_401_ = lean_ctor_get(v_opt_400_, 0);
v_defValue_402_ = lean_ctor_get(v_opt_400_, 1);
v_map_403_ = lean_ctor_get(v_opts_399_, 0);
v___x_404_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_403_, v_name_401_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_inc(v_defValue_402_);
return v_defValue_402_;
}
else
{
lean_object* v_val_405_; 
v_val_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_val_405_);
lean_dec_ref(v___x_404_);
if (lean_obj_tag(v_val_405_) == 3)
{
lean_object* v_v_406_; 
v_v_406_ = lean_ctor_get(v_val_405_, 0);
lean_inc(v_v_406_);
lean_dec_ref(v_val_405_);
return v_v_406_;
}
else
{
lean_dec(v_val_405_);
lean_inc(v_defValue_402_);
return v_defValue_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6___boxed(lean_object* v_opts_407_, lean_object* v_opt_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_407_, v_opt_408_);
lean_dec_ref(v_opt_408_);
lean_dec_ref(v_opts_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4_spec__7(size_t v_sz_410_, size_t v_i_411_, lean_object* v_bs_412_){
_start:
{
uint8_t v___x_413_; 
v___x_413_ = lean_usize_dec_lt(v_i_411_, v_sz_410_);
if (v___x_413_ == 0)
{
return v_bs_412_;
}
else
{
lean_object* v_v_414_; lean_object* v_msg_415_; lean_object* v___x_416_; lean_object* v_bs_x27_417_; size_t v___x_418_; size_t v___x_419_; lean_object* v___x_420_; 
v_v_414_ = lean_array_uget_borrowed(v_bs_412_, v_i_411_);
v_msg_415_ = lean_ctor_get(v_v_414_, 1);
lean_inc_ref(v_msg_415_);
v___x_416_ = lean_unsigned_to_nat(0u);
v_bs_x27_417_ = lean_array_uset(v_bs_412_, v_i_411_, v___x_416_);
v___x_418_ = ((size_t)1ULL);
v___x_419_ = lean_usize_add(v_i_411_, v___x_418_);
v___x_420_ = lean_array_uset(v_bs_x27_417_, v_i_411_, v_msg_415_);
v_i_411_ = v___x_419_;
v_bs_412_ = v___x_420_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4_spec__7___boxed(lean_object* v_sz_422_, lean_object* v_i_423_, lean_object* v_bs_424_){
_start:
{
size_t v_sz_boxed_425_; size_t v_i_boxed_426_; lean_object* v_res_427_; 
v_sz_boxed_425_ = lean_unbox_usize(v_sz_422_);
lean_dec(v_sz_422_);
v_i_boxed_426_ = lean_unbox_usize(v_i_423_);
lean_dec(v_i_423_);
v_res_427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4_spec__7(v_sz_boxed_425_, v_i_boxed_426_, v_bs_424_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object* v_oldTraces_428_, lean_object* v_data_429_, lean_object* v_ref_430_, lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_fileName_437_; lean_object* v_fileMap_438_; lean_object* v_options_439_; lean_object* v_currRecDepth_440_; lean_object* v_maxRecDepth_441_; lean_object* v_ref_442_; lean_object* v_currNamespace_443_; lean_object* v_openDecls_444_; lean_object* v_initHeartbeats_445_; lean_object* v_maxHeartbeats_446_; lean_object* v_quotContext_447_; lean_object* v_currMacroScope_448_; uint8_t v_diag_449_; lean_object* v_cancelTk_x3f_450_; uint8_t v_suppressElabErrors_451_; lean_object* v_inheritedTraceOptions_452_; lean_object* v___x_453_; lean_object* v_traceState_454_; lean_object* v_traces_455_; lean_object* v_ref_456_; lean_object* v___x_457_; lean_object* v___x_458_; size_t v_sz_459_; size_t v___x_460_; lean_object* v___x_461_; lean_object* v_msg_462_; lean_object* v___x_463_; lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_501_; 
v_fileName_437_ = lean_ctor_get(v___y_434_, 0);
v_fileMap_438_ = lean_ctor_get(v___y_434_, 1);
v_options_439_ = lean_ctor_get(v___y_434_, 2);
v_currRecDepth_440_ = lean_ctor_get(v___y_434_, 3);
v_maxRecDepth_441_ = lean_ctor_get(v___y_434_, 4);
v_ref_442_ = lean_ctor_get(v___y_434_, 5);
v_currNamespace_443_ = lean_ctor_get(v___y_434_, 6);
v_openDecls_444_ = lean_ctor_get(v___y_434_, 7);
v_initHeartbeats_445_ = lean_ctor_get(v___y_434_, 8);
v_maxHeartbeats_446_ = lean_ctor_get(v___y_434_, 9);
v_quotContext_447_ = lean_ctor_get(v___y_434_, 10);
v_currMacroScope_448_ = lean_ctor_get(v___y_434_, 11);
v_diag_449_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*14);
v_cancelTk_x3f_450_ = lean_ctor_get(v___y_434_, 12);
v_suppressElabErrors_451_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_452_ = lean_ctor_get(v___y_434_, 13);
v___x_453_ = lean_st_ref_get(v___y_435_);
v_traceState_454_ = lean_ctor_get(v___x_453_, 4);
lean_inc_ref(v_traceState_454_);
lean_dec(v___x_453_);
v_traces_455_ = lean_ctor_get(v_traceState_454_, 0);
lean_inc_ref(v_traces_455_);
lean_dec_ref(v_traceState_454_);
v_ref_456_ = l_Lean_replaceRef(v_ref_430_, v_ref_442_);
lean_inc_ref(v_inheritedTraceOptions_452_);
lean_inc(v_cancelTk_x3f_450_);
lean_inc(v_currMacroScope_448_);
lean_inc(v_quotContext_447_);
lean_inc(v_maxHeartbeats_446_);
lean_inc(v_initHeartbeats_445_);
lean_inc(v_openDecls_444_);
lean_inc(v_currNamespace_443_);
lean_inc(v_maxRecDepth_441_);
lean_inc(v_currRecDepth_440_);
lean_inc_ref(v_options_439_);
lean_inc_ref(v_fileMap_438_);
lean_inc_ref(v_fileName_437_);
v___x_457_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_457_, 0, v_fileName_437_);
lean_ctor_set(v___x_457_, 1, v_fileMap_438_);
lean_ctor_set(v___x_457_, 2, v_options_439_);
lean_ctor_set(v___x_457_, 3, v_currRecDepth_440_);
lean_ctor_set(v___x_457_, 4, v_maxRecDepth_441_);
lean_ctor_set(v___x_457_, 5, v_ref_456_);
lean_ctor_set(v___x_457_, 6, v_currNamespace_443_);
lean_ctor_set(v___x_457_, 7, v_openDecls_444_);
lean_ctor_set(v___x_457_, 8, v_initHeartbeats_445_);
lean_ctor_set(v___x_457_, 9, v_maxHeartbeats_446_);
lean_ctor_set(v___x_457_, 10, v_quotContext_447_);
lean_ctor_set(v___x_457_, 11, v_currMacroScope_448_);
lean_ctor_set(v___x_457_, 12, v_cancelTk_x3f_450_);
lean_ctor_set(v___x_457_, 13, v_inheritedTraceOptions_452_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*14, v_diag_449_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*14 + 1, v_suppressElabErrors_451_);
v___x_458_ = l_Lean_PersistentArray_toArray___redArg(v_traces_455_);
lean_dec_ref(v_traces_455_);
v_sz_459_ = lean_array_size(v___x_458_);
v___x_460_ = ((size_t)0ULL);
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4_spec__7(v_sz_459_, v___x_460_, v___x_458_);
v_msg_462_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_462_, 0, v_data_429_);
lean_ctor_set(v_msg_462_, 1, v_msg_431_);
lean_ctor_set(v_msg_462_, 2, v___x_461_);
v___x_463_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_462_, v___y_432_, v___y_433_, v___x_457_, v___y_435_);
lean_dec_ref(v___x_457_);
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_501_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_501_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_501_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v_traceState_469_; lean_object* v_env_470_; lean_object* v_nextMacroScope_471_; lean_object* v_ngen_472_; lean_object* v_auxDeclNGen_473_; lean_object* v_cache_474_; lean_object* v_messages_475_; lean_object* v_infoState_476_; lean_object* v_snapshotTasks_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_500_; 
v___x_468_ = lean_st_ref_take(v___y_435_);
v_traceState_469_ = lean_ctor_get(v___x_468_, 4);
v_env_470_ = lean_ctor_get(v___x_468_, 0);
v_nextMacroScope_471_ = lean_ctor_get(v___x_468_, 1);
v_ngen_472_ = lean_ctor_get(v___x_468_, 2);
v_auxDeclNGen_473_ = lean_ctor_get(v___x_468_, 3);
v_cache_474_ = lean_ctor_get(v___x_468_, 5);
v_messages_475_ = lean_ctor_get(v___x_468_, 6);
v_infoState_476_ = lean_ctor_get(v___x_468_, 7);
v_snapshotTasks_477_ = lean_ctor_get(v___x_468_, 8);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_500_ == 0)
{
v___x_479_ = v___x_468_;
v_isShared_480_ = v_isSharedCheck_500_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_snapshotTasks_477_);
lean_inc(v_infoState_476_);
lean_inc(v_messages_475_);
lean_inc(v_cache_474_);
lean_inc(v_traceState_469_);
lean_inc(v_auxDeclNGen_473_);
lean_inc(v_ngen_472_);
lean_inc(v_nextMacroScope_471_);
lean_inc(v_env_470_);
lean_dec(v___x_468_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_500_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
uint64_t v_tid_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_498_; 
v_tid_481_ = lean_ctor_get_uint64(v_traceState_469_, sizeof(void*)*1);
v_isSharedCheck_498_ = !lean_is_exclusive(v_traceState_469_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v_traceState_469_, 0);
lean_dec(v_unused_499_);
v___x_483_ = v_traceState_469_;
v_isShared_484_ = v_isSharedCheck_498_;
goto v_resetjp_482_;
}
else
{
lean_dec(v_traceState_469_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_498_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_ref_430_);
lean_ctor_set(v___x_485_, 1, v_a_464_);
v___x_486_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_428_, v___x_485_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_486_);
lean_ctor_set_uint64(v_reuseFailAlloc_497_, sizeof(void*)*1, v_tid_481_);
v___x_488_ = v_reuseFailAlloc_497_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 4, v___x_488_);
v___x_490_ = v___x_479_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_env_470_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_nextMacroScope_471_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_ngen_472_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_auxDeclNGen_473_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v_cache_474_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_messages_475_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_infoState_476_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v_snapshotTasks_477_);
v___x_490_ = v_reuseFailAlloc_496_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_491_ = lean_st_ref_set(v___y_435_, v___x_490_);
v___x_492_ = lean_box(0);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_492_);
v___x_494_ = v___x_466_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object* v_oldTraces_502_, lean_object* v_data_503_, lean_object* v_ref_504_, lean_object* v_msg_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_oldTraces_502_, v_data_503_, v_ref_504_, v_msg_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(lean_object* v_x_512_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
v_a_514_ = lean_ctor_get(v_x_512_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v_x_512_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v_x_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 1);
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_a_522_ = lean_ctor_get(v_x_512_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v_x_512_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v_x_512_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 0);
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg___boxed(lean_object* v_x_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_x_530_);
return v_res_532_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object* v_e_533_){
_start:
{
if (lean_obj_tag(v_e_533_) == 0)
{
uint8_t v___x_534_; 
v___x_534_ = 2;
return v___x_534_;
}
else
{
lean_object* v_a_535_; 
v_a_535_ = lean_ctor_get(v_e_533_, 0);
if (lean_obj_tag(v_a_535_) == 0)
{
uint8_t v___x_536_; 
v___x_536_ = 1;
return v___x_536_;
}
else
{
uint8_t v___x_537_; 
v___x_537_ = 0;
return v___x_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object* v_e_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_e_538_);
lean_dec_ref(v_e_538_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2(void){
_start:
{
lean_object* v___x_544_; double v___x_545_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_float_of_nat(v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3));
v___x_548_ = l_Lean_stringToMessageData(v___x_547_);
return v___x_548_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5(void){
_start:
{
lean_object* v___x_549_; double v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(1000u);
v___x_550_ = lean_float_of_nat(v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_cls_551_, uint8_t v_collapsed_552_, lean_object* v_tag_553_, lean_object* v_opts_554_, uint8_t v_clsEnabled_555_, lean_object* v_oldTraces_556_, lean_object* v_msg_557_, lean_object* v_resStartStop_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_fst_564_; lean_object* v_snd_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_663_; 
v_fst_564_ = lean_ctor_get(v_resStartStop_558_, 0);
v_snd_565_ = lean_ctor_get(v_resStartStop_558_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_resStartStop_558_);
if (v_isSharedCheck_663_ == 0)
{
v___x_567_ = v_resStartStop_558_;
v_isShared_568_ = v_isSharedCheck_663_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_snd_565_);
lean_inc(v_fst_564_);
lean_dec(v_resStartStop_558_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_663_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v_data_572_; lean_object* v_fst_583_; lean_object* v_snd_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_662_; 
v_fst_583_ = lean_ctor_get(v_snd_565_, 0);
v_snd_584_ = lean_ctor_get(v_snd_565_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_snd_565_);
if (v_isSharedCheck_662_ == 0)
{
v___x_586_ = v_snd_565_;
v_isShared_587_ = v_isSharedCheck_662_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_snd_584_);
lean_inc(v_fst_583_);
lean_dec(v_snd_565_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_662_;
goto v_resetjp_585_;
}
v___jp_569_:
{
lean_object* v___x_573_; 
lean_inc(v___y_570_);
v___x_573_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_oldTraces_556_, v_data_572_, v___y_570_, v___y_571_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v___x_574_; 
lean_dec_ref(v___x_573_);
v___x_574_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_fst_564_);
return v___x_574_;
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec(v_fst_564_);
v_a_575_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_573_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
v_resetjp_585_:
{
lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___y_591_; lean_object* v_a_592_; uint8_t v___y_616_; double v___y_647_; 
v___x_588_ = l_Lean_trace_profiler;
v___x_589_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_554_, v___x_588_);
if (v___x_589_ == 0)
{
v___y_616_ = v___x_589_;
goto v___jp_615_;
}
else
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = l_Lean_trace_profiler_useHeartbeats;
v___x_653_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_554_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; double v___x_656_; double v___x_657_; double v___x_658_; 
v___x_654_ = l_Lean_trace_profiler_threshold;
v___x_655_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_554_, v___x_654_);
v___x_656_ = lean_float_of_nat(v___x_655_);
v___x_657_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5);
v___x_658_ = lean_float_div(v___x_656_, v___x_657_);
v___y_647_ = v___x_658_;
goto v___jp_646_;
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; double v___x_661_; 
v___x_659_ = l_Lean_trace_profiler_threshold;
v___x_660_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_554_, v___x_659_);
v___x_661_ = lean_float_of_nat(v___x_660_);
v___y_647_ = v___x_661_;
goto v___jp_646_;
}
}
v___jp_590_:
{
uint8_t v_result_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v_result_593_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_fst_564_);
v___x_594_ = l_Lean_TraceResult_toEmoji(v_result_593_);
v___x_595_ = l_Lean_stringToMessageData(v___x_594_);
v___x_596_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 7);
lean_ctor_set(v___x_586_, 1, v___x_596_);
lean_ctor_set(v___x_586_, 0, v___x_595_);
v___x_598_ = v___x_586_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_595_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_596_);
v___x_598_ = v_reuseFailAlloc_609_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v_m_600_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 7);
lean_ctor_set(v___x_567_, 1, v_a_592_);
lean_ctor_set(v___x_567_, 0, v___x_598_);
v_m_600_ = v___x_567_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_a_592_);
v_m_600_ = v_reuseFailAlloc_608_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; double v___x_603_; lean_object* v_data_604_; 
v___x_601_ = lean_box(v_result_593_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
lean_inc_ref(v_tag_553_);
lean_inc_ref(v___x_602_);
lean_inc(v_cls_551_);
v_data_604_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_604_, 0, v_cls_551_);
lean_ctor_set(v_data_604_, 1, v___x_602_);
lean_ctor_set(v_data_604_, 2, v_tag_553_);
lean_ctor_set_float(v_data_604_, sizeof(void*)*3, v___x_603_);
lean_ctor_set_float(v_data_604_, sizeof(void*)*3 + 8, v___x_603_);
lean_ctor_set_uint8(v_data_604_, sizeof(void*)*3 + 16, v_collapsed_552_);
if (v___x_589_ == 0)
{
lean_dec_ref(v___x_602_);
lean_dec(v_snd_584_);
lean_dec(v_fst_583_);
lean_dec_ref(v_tag_553_);
lean_dec(v_cls_551_);
v___y_570_ = v___y_591_;
v___y_571_ = v_m_600_;
v_data_572_ = v_data_604_;
goto v___jp_569_;
}
else
{
lean_object* v_data_605_; double v___x_606_; double v___x_607_; 
lean_dec_ref(v_data_604_);
v_data_605_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_605_, 0, v_cls_551_);
lean_ctor_set(v_data_605_, 1, v___x_602_);
lean_ctor_set(v_data_605_, 2, v_tag_553_);
v___x_606_ = lean_unbox_float(v_fst_583_);
lean_dec(v_fst_583_);
lean_ctor_set_float(v_data_605_, sizeof(void*)*3, v___x_606_);
v___x_607_ = lean_unbox_float(v_snd_584_);
lean_dec(v_snd_584_);
lean_ctor_set_float(v_data_605_, sizeof(void*)*3 + 8, v___x_607_);
lean_ctor_set_uint8(v_data_605_, sizeof(void*)*3 + 16, v_collapsed_552_);
v___y_570_ = v___y_591_;
v___y_571_ = v_m_600_;
v_data_572_ = v_data_605_;
goto v___jp_569_;
}
}
}
}
v___jp_610_:
{
lean_object* v_ref_611_; lean_object* v___x_612_; 
v_ref_611_ = lean_ctor_get(v___y_561_, 5);
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
lean_inc(v___y_560_);
lean_inc_ref(v___y_559_);
lean_inc(v_fst_564_);
v___x_612_ = lean_apply_6(v_msg_557_, v_fst_564_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, lean_box(0));
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref(v___x_612_);
v___y_591_ = v_ref_611_;
v_a_592_ = v_a_613_;
goto v___jp_590_;
}
else
{
lean_object* v___x_614_; 
lean_dec_ref(v___x_612_);
v___x_614_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4);
v___y_591_ = v_ref_611_;
v_a_592_ = v___x_614_;
goto v___jp_590_;
}
}
v___jp_615_:
{
if (v_clsEnabled_555_ == 0)
{
if (v___y_616_ == 0)
{
lean_object* v___x_617_; lean_object* v_traceState_618_; lean_object* v_env_619_; lean_object* v_nextMacroScope_620_; lean_object* v_ngen_621_; lean_object* v_auxDeclNGen_622_; lean_object* v_cache_623_; lean_object* v_messages_624_; lean_object* v_infoState_625_; lean_object* v_snapshotTasks_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_645_; 
lean_del_object(v___x_586_);
lean_dec(v_snd_584_);
lean_dec(v_fst_583_);
lean_del_object(v___x_567_);
lean_dec_ref(v_msg_557_);
lean_dec_ref(v_tag_553_);
lean_dec(v_cls_551_);
v___x_617_ = lean_st_ref_take(v___y_562_);
v_traceState_618_ = lean_ctor_get(v___x_617_, 4);
v_env_619_ = lean_ctor_get(v___x_617_, 0);
v_nextMacroScope_620_ = lean_ctor_get(v___x_617_, 1);
v_ngen_621_ = lean_ctor_get(v___x_617_, 2);
v_auxDeclNGen_622_ = lean_ctor_get(v___x_617_, 3);
v_cache_623_ = lean_ctor_get(v___x_617_, 5);
v_messages_624_ = lean_ctor_get(v___x_617_, 6);
v_infoState_625_ = lean_ctor_get(v___x_617_, 7);
v_snapshotTasks_626_ = lean_ctor_get(v___x_617_, 8);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_645_ == 0)
{
v___x_628_ = v___x_617_;
v_isShared_629_ = v_isSharedCheck_645_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_snapshotTasks_626_);
lean_inc(v_infoState_625_);
lean_inc(v_messages_624_);
lean_inc(v_cache_623_);
lean_inc(v_traceState_618_);
lean_inc(v_auxDeclNGen_622_);
lean_inc(v_ngen_621_);
lean_inc(v_nextMacroScope_620_);
lean_inc(v_env_619_);
lean_dec(v___x_617_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_645_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
uint64_t v_tid_630_; lean_object* v_traces_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_644_; 
v_tid_630_ = lean_ctor_get_uint64(v_traceState_618_, sizeof(void*)*1);
v_traces_631_ = lean_ctor_get(v_traceState_618_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_traceState_618_);
if (v_isSharedCheck_644_ == 0)
{
v___x_633_ = v_traceState_618_;
v_isShared_634_ = v_isSharedCheck_644_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_traces_631_);
lean_dec(v_traceState_618_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_644_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_556_, v_traces_631_);
lean_dec_ref(v_traces_631_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_635_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_635_);
lean_ctor_set_uint64(v_reuseFailAlloc_643_, sizeof(void*)*1, v_tid_630_);
v___x_637_ = v_reuseFailAlloc_643_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 4, v___x_637_);
v___x_639_ = v___x_628_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_env_619_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_nextMacroScope_620_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_ngen_621_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v_auxDeclNGen_622_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_642_, 5, v_cache_623_);
lean_ctor_set(v_reuseFailAlloc_642_, 6, v_messages_624_);
lean_ctor_set(v_reuseFailAlloc_642_, 7, v_infoState_625_);
lean_ctor_set(v_reuseFailAlloc_642_, 8, v_snapshotTasks_626_);
v___x_639_ = v_reuseFailAlloc_642_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_st_ref_set(v___y_562_, v___x_639_);
v___x_641_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_fst_564_);
return v___x_641_;
}
}
}
}
}
else
{
goto v___jp_610_;
}
}
else
{
goto v___jp_610_;
}
}
v___jp_646_:
{
double v___x_648_; double v___x_649_; double v___x_650_; uint8_t v___x_651_; 
v___x_648_ = lean_unbox_float(v_snd_584_);
v___x_649_ = lean_unbox_float(v_fst_583_);
v___x_650_ = lean_float_sub(v___x_648_, v___x_649_);
v___x_651_ = lean_float_decLt(v___y_647_, v___x_650_);
v___y_616_ = v___x_651_;
goto v___jp_615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_cls_664_, lean_object* v_collapsed_665_, lean_object* v_tag_666_, lean_object* v_opts_667_, lean_object* v_clsEnabled_668_, lean_object* v_oldTraces_669_, lean_object* v_msg_670_, lean_object* v_resStartStop_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
uint8_t v_collapsed_boxed_677_; uint8_t v_clsEnabled_boxed_678_; lean_object* v_res_679_; 
v_collapsed_boxed_677_ = lean_unbox(v_collapsed_665_);
v_clsEnabled_boxed_678_ = lean_unbox(v_clsEnabled_668_);
v_res_679_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_cls_664_, v_collapsed_boxed_677_, v_tag_666_, v_opts_667_, v_clsEnabled_boxed_678_, v_oldTraces_669_, v_msg_670_, v_resStartStop_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec_ref(v_opts_667_);
return v_res_679_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* v_a_683_, lean_object* v_x_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
v___x_691_ = l_Lean_Exception_toMessageData(v_a_683_);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* v_a_694_, lean_object* v_x_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_a_694_, v_x_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v_x_695_);
return v_res_701_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object* v_keys_702_, lean_object* v_i_703_, lean_object* v_k_704_){
_start:
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_array_get_size(v_keys_702_);
v___x_706_ = lean_nat_dec_lt(v_i_703_, v___x_705_);
if (v___x_706_ == 0)
{
lean_dec(v_i_703_);
return v___x_706_;
}
else
{
lean_object* v_k_x27_707_; uint8_t v___x_708_; 
v_k_x27_707_ = lean_array_fget_borrowed(v_keys_702_, v_i_703_);
v___x_708_ = l_Lean_instBEqMVarId_beq(v_k_704_, v_k_x27_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(1u);
v___x_710_ = lean_nat_add(v_i_703_, v___x_709_);
lean_dec(v_i_703_);
v_i_703_ = v___x_710_;
goto _start;
}
else
{
lean_dec(v_i_703_);
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object* v_keys_712_, lean_object* v_i_713_, lean_object* v_k_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_712_, v_i_713_, v_k_714_);
lean_dec(v_k_714_);
lean_dec_ref(v_keys_712_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0(void){
_start:
{
size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; 
v___x_717_ = ((size_t)5ULL);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_shift_left(v___x_718_, v___x_717_);
return v___x_719_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1(void){
_start:
{
size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; 
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0);
v___x_722_ = lean_usize_sub(v___x_721_, v___x_720_);
return v___x_722_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_723_, size_t v_x_724_, lean_object* v_x_725_){
_start:
{
if (lean_obj_tag(v_x_723_) == 0)
{
lean_object* v_es_726_; lean_object* v___x_727_; size_t v___x_728_; size_t v___x_729_; size_t v___x_730_; lean_object* v_j_731_; lean_object* v___x_732_; 
v_es_726_ = lean_ctor_get(v_x_723_, 0);
v___x_727_ = lean_box(2);
v___x_728_ = ((size_t)5ULL);
v___x_729_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1);
v___x_730_ = lean_usize_land(v_x_724_, v___x_729_);
v_j_731_ = lean_usize_to_nat(v___x_730_);
v___x_732_ = lean_array_get_borrowed(v___x_727_, v_es_726_, v_j_731_);
lean_dec(v_j_731_);
switch(lean_obj_tag(v___x_732_))
{
case 0:
{
lean_object* v_key_733_; uint8_t v___x_734_; 
v_key_733_ = lean_ctor_get(v___x_732_, 0);
v___x_734_ = l_Lean_instBEqMVarId_beq(v_x_725_, v_key_733_);
return v___x_734_;
}
case 1:
{
lean_object* v_node_735_; size_t v___x_736_; 
v_node_735_ = lean_ctor_get(v___x_732_, 0);
v___x_736_ = lean_usize_shift_right(v_x_724_, v___x_728_);
v_x_723_ = v_node_735_;
v_x_724_ = v___x_736_;
goto _start;
}
default: 
{
uint8_t v___x_738_; 
v___x_738_ = 0;
return v___x_738_;
}
}
}
else
{
lean_object* v_ks_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_ks_739_ = lean_ctor_get(v_x_723_, 0);
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_ks_739_, v___x_740_, v_x_725_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
size_t v_x_82175__boxed_745_; uint8_t v_res_746_; lean_object* v_r_747_; 
v_x_82175__boxed_745_ = lean_unbox_usize(v_x_743_);
lean_dec(v_x_743_);
v_res_746_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_742_, v_x_82175__boxed_745_, v_x_744_);
lean_dec(v_x_744_);
lean_dec_ref(v_x_742_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
uint64_t v___x_750_; size_t v___x_751_; uint8_t v___x_752_; 
v___x_750_ = l_Lean_instHashableMVarId_hash(v_x_749_);
v___x_751_ = lean_uint64_to_usize(v___x_750_);
v___x_752_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_748_, v___x_751_, v_x_749_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
uint8_t v_res_755_; lean_object* v_r_756_; 
v_res_755_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_753_, v_x_754_);
lean_dec(v_x_754_);
lean_dec_ref(v_x_753_);
v_r_756_ = lean_box(v_res_755_);
return v_r_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object* v_mvarId_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; lean_object* v_mctx_761_; lean_object* v_eAssignment_762_; uint8_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_760_ = lean_st_ref_get(v___y_758_);
v_mctx_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc_ref(v_mctx_761_);
lean_dec(v___x_760_);
v_eAssignment_762_ = lean_ctor_get(v_mctx_761_, 8);
lean_inc_ref(v_eAssignment_762_);
lean_dec_ref(v_mctx_761_);
v___x_763_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_eAssignment_762_, v_mvarId_757_);
lean_dec_ref(v_eAssignment_762_);
v___x_764_ = lean_box(v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object* v_mvarId_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec(v_mvarId_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_ref_776_; lean_object* v___x_777_; lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
v_ref_776_ = lean_ctor_get(v___y_773_, 5);
v___x_777_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_786_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
lean_inc(v_ref_776_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_ref_776_);
lean_ctor_set(v___x_782_, 1, v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 1);
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v_res_793_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object* v_e_794_){
_start:
{
if (lean_obj_tag(v_e_794_) == 0)
{
uint8_t v___x_795_; 
v___x_795_ = 2;
return v___x_795_;
}
else
{
uint8_t v___x_796_; 
v___x_796_ = 0;
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object* v_e_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_e_797_);
lean_dec_ref(v_e_797_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_800_, uint8_t v_collapsed_801_, lean_object* v_tag_802_, lean_object* v_opts_803_, uint8_t v_clsEnabled_804_, lean_object* v_oldTraces_805_, lean_object* v_msg_806_, lean_object* v_resStartStop_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_fst_813_; lean_object* v_snd_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_912_; 
v_fst_813_ = lean_ctor_get(v_resStartStop_807_, 0);
v_snd_814_ = lean_ctor_get(v_resStartStop_807_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_resStartStop_807_);
if (v_isSharedCheck_912_ == 0)
{
v___x_816_ = v_resStartStop_807_;
v_isShared_817_ = v_isSharedCheck_912_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_snd_814_);
lean_inc(v_fst_813_);
lean_dec(v_resStartStop_807_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_912_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v_data_821_; lean_object* v_fst_832_; lean_object* v_snd_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_911_; 
v_fst_832_ = lean_ctor_get(v_snd_814_, 0);
v_snd_833_ = lean_ctor_get(v_snd_814_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_snd_814_);
if (v_isSharedCheck_911_ == 0)
{
v___x_835_ = v_snd_814_;
v_isShared_836_ = v_isSharedCheck_911_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_snd_833_);
lean_inc(v_fst_832_);
lean_dec(v_snd_814_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_911_;
goto v_resetjp_834_;
}
v___jp_818_:
{
lean_object* v___x_822_; 
lean_inc(v___y_819_);
v___x_822_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_oldTraces_805_, v_data_821_, v___y_819_, v___y_820_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_823_; 
lean_dec_ref(v___x_822_);
v___x_823_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_fst_813_);
return v___x_823_;
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_fst_813_);
v_a_824_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_822_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_822_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
v_resetjp_834_:
{
lean_object* v___x_837_; uint8_t v___x_838_; lean_object* v___y_840_; lean_object* v_a_841_; uint8_t v___y_865_; double v___y_896_; 
v___x_837_ = l_Lean_trace_profiler;
v___x_838_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_803_, v___x_837_);
if (v___x_838_ == 0)
{
v___y_865_ = v___x_838_;
goto v___jp_864_;
}
else
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = l_Lean_trace_profiler_useHeartbeats;
v___x_902_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_803_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; double v___x_905_; double v___x_906_; double v___x_907_; 
v___x_903_ = l_Lean_trace_profiler_threshold;
v___x_904_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_803_, v___x_903_);
v___x_905_ = lean_float_of_nat(v___x_904_);
v___x_906_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5);
v___x_907_ = lean_float_div(v___x_905_, v___x_906_);
v___y_896_ = v___x_907_;
goto v___jp_895_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; double v___x_910_; 
v___x_908_ = l_Lean_trace_profiler_threshold;
v___x_909_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_803_, v___x_908_);
v___x_910_ = lean_float_of_nat(v___x_909_);
v___y_896_ = v___x_910_;
goto v___jp_895_;
}
}
v___jp_839_:
{
uint8_t v_result_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v_result_842_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_fst_813_);
v___x_843_ = l_Lean_TraceResult_toEmoji(v_result_842_);
v___x_844_ = l_Lean_stringToMessageData(v___x_843_);
v___x_845_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 7);
lean_ctor_set(v___x_835_, 1, v___x_845_);
lean_ctor_set(v___x_835_, 0, v___x_844_);
v___x_847_ = v___x_835_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_845_);
v___x_847_ = v_reuseFailAlloc_858_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v_m_849_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 7);
lean_ctor_set(v___x_816_, 1, v_a_841_);
lean_ctor_set(v___x_816_, 0, v___x_847_);
v_m_849_ = v___x_816_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_a_841_);
v_m_849_ = v_reuseFailAlloc_857_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; double v___x_852_; lean_object* v_data_853_; 
v___x_850_ = lean_box(v_result_842_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
v___x_852_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
lean_inc_ref(v_tag_802_);
lean_inc_ref(v___x_851_);
lean_inc(v_cls_800_);
v_data_853_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_853_, 0, v_cls_800_);
lean_ctor_set(v_data_853_, 1, v___x_851_);
lean_ctor_set(v_data_853_, 2, v_tag_802_);
lean_ctor_set_float(v_data_853_, sizeof(void*)*3, v___x_852_);
lean_ctor_set_float(v_data_853_, sizeof(void*)*3 + 8, v___x_852_);
lean_ctor_set_uint8(v_data_853_, sizeof(void*)*3 + 16, v_collapsed_801_);
if (v___x_838_ == 0)
{
lean_dec_ref(v___x_851_);
lean_dec(v_snd_833_);
lean_dec(v_fst_832_);
lean_dec_ref(v_tag_802_);
lean_dec(v_cls_800_);
v___y_819_ = v___y_840_;
v___y_820_ = v_m_849_;
v_data_821_ = v_data_853_;
goto v___jp_818_;
}
else
{
lean_object* v_data_854_; double v___x_855_; double v___x_856_; 
lean_dec_ref(v_data_853_);
v_data_854_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_854_, 0, v_cls_800_);
lean_ctor_set(v_data_854_, 1, v___x_851_);
lean_ctor_set(v_data_854_, 2, v_tag_802_);
v___x_855_ = lean_unbox_float(v_fst_832_);
lean_dec(v_fst_832_);
lean_ctor_set_float(v_data_854_, sizeof(void*)*3, v___x_855_);
v___x_856_ = lean_unbox_float(v_snd_833_);
lean_dec(v_snd_833_);
lean_ctor_set_float(v_data_854_, sizeof(void*)*3 + 8, v___x_856_);
lean_ctor_set_uint8(v_data_854_, sizeof(void*)*3 + 16, v_collapsed_801_);
v___y_819_ = v___y_840_;
v___y_820_ = v_m_849_;
v_data_821_ = v_data_854_;
goto v___jp_818_;
}
}
}
}
v___jp_859_:
{
lean_object* v_ref_860_; lean_object* v___x_861_; 
v_ref_860_ = lean_ctor_get(v___y_810_, 5);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
lean_inc(v_fst_813_);
v___x_861_ = lean_apply_6(v_msg_806_, v_fst_813_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, lean_box(0));
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v___x_861_);
v___y_840_ = v_ref_860_;
v_a_841_ = v_a_862_;
goto v___jp_839_;
}
else
{
lean_object* v___x_863_; 
lean_dec_ref(v___x_861_);
v___x_863_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4);
v___y_840_ = v_ref_860_;
v_a_841_ = v___x_863_;
goto v___jp_839_;
}
}
v___jp_864_:
{
if (v_clsEnabled_804_ == 0)
{
if (v___y_865_ == 0)
{
lean_object* v___x_866_; lean_object* v_traceState_867_; lean_object* v_env_868_; lean_object* v_nextMacroScope_869_; lean_object* v_ngen_870_; lean_object* v_auxDeclNGen_871_; lean_object* v_cache_872_; lean_object* v_messages_873_; lean_object* v_infoState_874_; lean_object* v_snapshotTasks_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_894_; 
lean_del_object(v___x_835_);
lean_dec(v_snd_833_);
lean_dec(v_fst_832_);
lean_del_object(v___x_816_);
lean_dec_ref(v_msg_806_);
lean_dec_ref(v_tag_802_);
lean_dec(v_cls_800_);
v___x_866_ = lean_st_ref_take(v___y_811_);
v_traceState_867_ = lean_ctor_get(v___x_866_, 4);
v_env_868_ = lean_ctor_get(v___x_866_, 0);
v_nextMacroScope_869_ = lean_ctor_get(v___x_866_, 1);
v_ngen_870_ = lean_ctor_get(v___x_866_, 2);
v_auxDeclNGen_871_ = lean_ctor_get(v___x_866_, 3);
v_cache_872_ = lean_ctor_get(v___x_866_, 5);
v_messages_873_ = lean_ctor_get(v___x_866_, 6);
v_infoState_874_ = lean_ctor_get(v___x_866_, 7);
v_snapshotTasks_875_ = lean_ctor_get(v___x_866_, 8);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_894_ == 0)
{
v___x_877_ = v___x_866_;
v_isShared_878_ = v_isSharedCheck_894_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_snapshotTasks_875_);
lean_inc(v_infoState_874_);
lean_inc(v_messages_873_);
lean_inc(v_cache_872_);
lean_inc(v_traceState_867_);
lean_inc(v_auxDeclNGen_871_);
lean_inc(v_ngen_870_);
lean_inc(v_nextMacroScope_869_);
lean_inc(v_env_868_);
lean_dec(v___x_866_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_894_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
uint64_t v_tid_879_; lean_object* v_traces_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_893_; 
v_tid_879_ = lean_ctor_get_uint64(v_traceState_867_, sizeof(void*)*1);
v_traces_880_ = lean_ctor_get(v_traceState_867_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v_traceState_867_);
if (v_isSharedCheck_893_ == 0)
{
v___x_882_ = v_traceState_867_;
v_isShared_883_ = v_isSharedCheck_893_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_traces_880_);
lean_dec(v_traceState_867_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_893_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_805_, v_traces_880_);
lean_dec_ref(v_traces_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_884_);
lean_ctor_set_uint64(v_reuseFailAlloc_892_, sizeof(void*)*1, v_tid_879_);
v___x_886_ = v_reuseFailAlloc_892_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 4, v___x_886_);
v___x_888_ = v___x_877_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_env_868_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_nextMacroScope_869_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_ngen_870_);
lean_ctor_set(v_reuseFailAlloc_891_, 3, v_auxDeclNGen_871_);
lean_ctor_set(v_reuseFailAlloc_891_, 4, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_891_, 5, v_cache_872_);
lean_ctor_set(v_reuseFailAlloc_891_, 6, v_messages_873_);
lean_ctor_set(v_reuseFailAlloc_891_, 7, v_infoState_874_);
lean_ctor_set(v_reuseFailAlloc_891_, 8, v_snapshotTasks_875_);
v___x_888_ = v_reuseFailAlloc_891_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_st_ref_set(v___y_811_, v___x_888_);
v___x_890_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_fst_813_);
return v___x_890_;
}
}
}
}
}
else
{
goto v___jp_859_;
}
}
else
{
goto v___jp_859_;
}
}
v___jp_895_:
{
double v___x_897_; double v___x_898_; double v___x_899_; uint8_t v___x_900_; 
v___x_897_ = lean_unbox_float(v_snd_833_);
v___x_898_ = lean_unbox_float(v_fst_832_);
v___x_899_ = lean_float_sub(v___x_897_, v___x_898_);
v___x_900_ = lean_float_decLt(v___y_896_, v___x_899_);
v___y_865_ = v___x_900_;
goto v___jp_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_913_, lean_object* v_collapsed_914_, lean_object* v_tag_915_, lean_object* v_opts_916_, lean_object* v_clsEnabled_917_, lean_object* v_oldTraces_918_, lean_object* v_msg_919_, lean_object* v_resStartStop_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
uint8_t v_collapsed_boxed_926_; uint8_t v_clsEnabled_boxed_927_; lean_object* v_res_928_; 
v_collapsed_boxed_926_ = lean_unbox(v_collapsed_914_);
v_clsEnabled_boxed_927_ = lean_unbox(v_clsEnabled_917_);
v_res_928_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_913_, v_collapsed_boxed_926_, v_tag_915_, v_opts_916_, v_clsEnabled_boxed_927_, v_oldTraces_918_, v_msg_919_, v_resStartStop_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec_ref(v_opts_916_);
return v_res_928_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_931_ = l_Lean_stringToMessageData(v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_head_932_, lean_object* v_x_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_940_, 0, v_head_932_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_head_943_, lean_object* v_x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_head_943_, v_x_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec_ref(v_x_944_);
return v_res_950_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object* v_head_954_, lean_object* v_x_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_972_; 
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v_head_954_);
v___x_962_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v___x_961_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_972_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v_a_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_968_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object* v_head_973_, lean_object* v_x_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(v_head_973_, v_x_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec_ref(v_x_974_);
return v_res_980_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_981_; double v___x_982_; 
v___x_981_ = lean_unsigned_to_nat(1000000000u);
v___x_982_ = lean_float_of_nat(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* v_tail_994_, lean_object* v_cfg_995_, lean_object* v_trace_996_, lean_object* v_next_997_, lean_object* v_goals_998_, lean_object* v_n_999_, lean_object* v_acc_1000_, lean_object* v_r_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_994_, v_cfg_995_, v_trace_996_, v_next_997_, v_goals_998_, v_n_999_, v_acc_1000_, v_r_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_1008_, lean_object* v_trace_1009_, lean_object* v_next_1010_, lean_object* v_goals_1011_, lean_object* v_n_1012_, lean_object* v_curr_1013_, lean_object* v_acc_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v___y_1021_; lean_object* v___y_1022_; uint8_t v___y_1023_; uint8_t v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v_a_1028_; lean_object* v___y_1038_; lean_object* v___y_1039_; uint8_t v___y_1040_; uint8_t v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v_a_1045_; lean_object* v___y_1058_; lean_object* v___y_1059_; uint8_t v___y_1060_; uint8_t v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; uint8_t v___y_1106_; uint8_t v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v_a_1113_; uint8_t v___y_1123_; uint8_t v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v_a_1130_; uint8_t v___y_1133_; uint8_t v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v_a_1140_; uint8_t v___y_1143_; uint8_t v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; uint8_t v___y_1154_; uint8_t v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v_a_1161_; uint8_t v___y_1174_; uint8_t v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v_a_1181_; uint8_t v___y_1184_; uint8_t v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v_a_1191_; uint8_t v___y_1194_; uint8_t v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v_zero_1204_; uint8_t v_isZero_1205_; 
v_zero_1204_ = lean_unsigned_to_nat(0u);
v_isZero_1205_ = lean_nat_dec_eq(v_n_1012_, v_zero_1204_);
if (v_isZero_1205_ == 1)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_dec(v_acc_1014_);
lean_dec(v_curr_1013_);
lean_dec(v_n_1012_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
v___x_1206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1207_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1206_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1207_;
}
else
{
lean_object* v_proc_1208_; lean_object* v_suspend_1209_; lean_object* v_discharge_1210_; lean_object* v___f_1211_; lean_object* v___y_1213_; uint8_t v___y_1214_; uint8_t v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___f_1253_; uint8_t v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; uint8_t v___y_1260_; lean_object* v_a_1261_; uint8_t v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; uint8_t v___y_1275_; lean_object* v___y_1276_; lean_object* v_a_1277_; uint8_t v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; uint8_t v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___f_1337_; uint8_t v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; uint8_t v___y_1344_; lean_object* v_a_1345_; uint8_t v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1363_; lean_object* v_a_1364_; lean_object* v___f_1373_; uint8_t v___y_1375_; uint8_t v___y_1376_; lean_object* v___y_1377_; uint8_t v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v_a_1385_; uint8_t v___y_1398_; uint8_t v___y_1399_; lean_object* v___y_1400_; uint8_t v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v_a_1408_; uint8_t v___y_1418_; uint8_t v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; uint8_t v___y_1425_; uint8_t v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1470_; uint8_t v___y_1471_; uint8_t v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; uint8_t v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v_a_1480_; lean_object* v___y_1493_; uint8_t v___y_1494_; uint8_t v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; uint8_t v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v_a_1503_; uint8_t v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; uint8_t v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; uint8_t v___y_1521_; uint8_t v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; uint8_t v___y_1565_; uint8_t v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; uint8_t v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v_a_1575_; uint8_t v___y_1585_; uint8_t v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; uint8_t v___y_1593_; lean_object* v___y_1594_; lean_object* v_a_1595_; uint8_t v___y_1608_; uint8_t v___y_1609_; lean_object* v___y_1610_; uint8_t v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v_a_1618_; uint8_t v___y_1628_; uint8_t v___y_1629_; uint8_t v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v_a_1638_; lean_object* v___y_1651_; uint8_t v___y_1652_; uint8_t v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; uint8_t v___y_1659_; uint8_t v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; uint8_t v___y_1703_; uint8_t v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; uint8_t v___y_1712_; lean_object* v_a_1713_; uint8_t v___y_1726_; lean_object* v___y_1727_; uint8_t v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; uint8_t v___y_1735_; lean_object* v_a_1736_; uint8_t v___y_1746_; uint8_t v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; uint8_t v___y_1755_; lean_object* v_a_1756_; uint8_t v___y_1769_; lean_object* v___y_1770_; uint8_t v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; uint8_t v___y_1778_; lean_object* v_a_1779_; uint8_t v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; uint8_t v___y_1794_; lean_object* v___y_1795_; uint8_t v___y_1796_; uint8_t v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; uint8_t v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; uint8_t v___y_1846_; lean_object* v_a_1847_; lean_object* v___y_1860_; uint8_t v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; uint8_t v___y_1865_; lean_object* v_a_1866_; uint8_t v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; uint8_t v___y_1881_; lean_object* v___y_1882_; lean_object* v_one_1923_; lean_object* v_n_1924_; uint8_t v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; uint8_t v___y_1930_; uint8_t v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; uint8_t v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; uint8_t v___y_1981_; uint8_t v___y_2005_; uint8_t v___y_2006_; uint8_t v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; uint8_t v___y_2013_; lean_object* v___y_2014_; uint8_t v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; uint8_t v___y_2062_; uint8_t v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; uint8_t v___y_2068_; uint8_t v___y_2089_; uint8_t v___y_2090_; uint8_t v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; uint8_t v___y_2097_; lean_object* v___y_2098_; uint8_t v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; uint8_t v___y_2147_; uint8_t v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; uint8_t v___y_2152_; uint8_t v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; uint8_t v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; uint8_t v___y_2230_; lean_object* v_a_2248_; lean_object* v___y_2339_; lean_object* v___x_2349_; 
v_proc_1208_ = lean_ctor_get(v_cfg_1008_, 1);
v_suspend_1209_ = lean_ctor_get(v_cfg_1008_, 2);
v_discharge_1210_ = lean_ctor_get(v_cfg_1008_, 3);
v___f_1211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1923_ = lean_unsigned_to_nat(1u);
v_n_1924_ = lean_nat_sub(v_n_1012_, v_one_1923_);
lean_dec(v_n_1012_);
lean_inc_ref(v_proc_1208_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v_curr_1013_);
lean_inc(v_goals_1011_);
v___x_2349_ = lean_apply_7(v_proc_1208_, v_goals_1011_, v_curr_1013_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
v_a_2248_ = v_a_2350_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2418_; 
v_a_2351_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2353_ = v___x_2349_;
v_isShared_2354_ = v_isSharedCheck_2418_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2349_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2418_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___f_2355_; uint8_t v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; uint8_t v___y_2360_; uint8_t v___y_2397_; uint8_t v___x_2416_; 
lean_inc(v_a_2351_);
v___f_2355_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(v___f_2355_, 0, v_a_2351_);
v___x_2416_ = l_Lean_Exception_isInterrupt(v_a_2351_);
if (v___x_2416_ == 0)
{
uint8_t v___x_2417_; 
lean_inc(v_a_2351_);
v___x_2417_ = l_Lean_Exception_isRuntime(v_a_2351_);
v___y_2397_ = v___x_2417_;
goto v___jp_2396_;
}
else
{
v___y_2397_ = v___x_2416_;
goto v___jp_2396_;
}
v___jp_2356_:
{
lean_object* v___x_2361_; lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2395_; 
v___x_2361_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2395_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2395_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; uint8_t v___x_2367_; 
v___x_2366_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2367_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2359_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2368_ = lean_io_mono_nanos_now();
v___x_2369_ = lean_io_mono_nanos_now();
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v_a_2351_);
v___x_2371_ = v___x_2364_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2351_);
v___x_2371_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
double v___x_2372_; double v___x_2373_; double v___x_2374_; double v___x_2375_; double v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2372_ = lean_float_of_nat(v___x_2368_);
v___x_2373_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2374_ = lean_float_div(v___x_2372_, v___x_2373_);
v___x_2375_ = lean_float_of_nat(v___x_2369_);
v___x_2376_ = lean_float_div(v___x_2375_, v___x_2373_);
v___x_2377_ = lean_box_float(v___x_2374_);
v___x_2378_ = lean_box_float(v___x_2376_);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2371_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
lean_inc_ref(v___y_2358_);
lean_inc(v_trace_1009_);
v___x_2381_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_1009_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v_a_2362_, v___f_2355_, v___x_2380_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_2339_ = v___x_2381_;
goto v___jp_2338_;
}
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2383_ = lean_io_get_num_heartbeats();
v___x_2384_ = lean_io_get_num_heartbeats();
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v_a_2351_);
v___x_2386_ = v___x_2364_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2351_);
v___x_2386_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
double v___x_2387_; double v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2387_ = lean_float_of_nat(v___x_2383_);
v___x_2388_ = lean_float_of_nat(v___x_2384_);
v___x_2389_ = lean_box_float(v___x_2387_);
v___x_2390_ = lean_box_float(v___x_2388_);
v___x_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2386_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
lean_inc_ref(v___y_2358_);
lean_inc(v_trace_1009_);
v___x_2393_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_1009_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v_a_2362_, v___f_2355_, v___x_2392_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_2339_ = v___x_2393_;
goto v___jp_2338_;
}
}
}
}
v___jp_2396_:
{
if (v___y_2397_ == 0)
{
lean_object* v_options_2398_; uint8_t v_hasTrace_2399_; 
v_options_2398_ = lean_ctor_get(v_a_1017_, 2);
v_hasTrace_2399_ = lean_ctor_get_uint8(v_options_2398_, sizeof(void*)*1);
if (v_hasTrace_2399_ == 0)
{
lean_object* v___x_2401_; 
lean_dec_ref(v___f_2355_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_curr_1013_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
if (v_isShared_2354_ == 0)
{
v___x_2401_ = v___x_2353_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2351_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v_inheritedTraceOptions_2403_ = lean_ctor_get(v_a_1017_, 13);
v___x_2404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1009_);
v___x_2406_ = l_Lean_Name_append(v___x_2405_, v_trace_1009_);
v___x_2407_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2403_, v_options_2398_, v___x_2406_);
lean_dec(v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = l_Lean_trace_profiler;
v___x_2409_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2398_, v___x_2408_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2411_; 
lean_dec_ref(v___f_2355_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_curr_1013_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
if (v_isShared_2354_ == 0)
{
v___x_2411_ = v___x_2353_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2351_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
else
{
lean_del_object(v___x_2353_);
v___y_2357_ = v_hasTrace_2399_;
v___y_2358_ = v___x_2404_;
v___y_2359_ = v_options_2398_;
v___y_2360_ = v___x_2407_;
goto v___jp_2356_;
}
}
else
{
lean_del_object(v___x_2353_);
v___y_2357_ = v_hasTrace_2399_;
v___y_2358_ = v___x_2404_;
v___y_2359_ = v_options_2398_;
v___y_2360_ = v___x_2407_;
goto v___jp_2356_;
}
}
}
else
{
lean_object* v___x_2414_; 
lean_dec_ref(v___f_2355_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_curr_1013_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
if (v_isShared_2354_ == 0)
{
v___x_2414_ = v___x_2353_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2351_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
}
v___jp_1212_:
{
lean_object* v___x_1218_; lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1252_; 
v___x_1218_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1252_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1252_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1224_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1216_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1225_ = lean_io_mono_nanos_now();
v___x_1226_ = lean_io_mono_nanos_now();
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 1);
lean_ctor_set(v___x_1221_, 0, v___y_1217_);
v___x_1228_ = v___x_1221_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___y_1217_);
v___x_1228_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
double v___x_1229_; double v___x_1230_; double v___x_1231_; double v___x_1232_; double v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1229_ = lean_float_of_nat(v___x_1225_);
v___x_1230_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1231_ = lean_float_div(v___x_1229_, v___x_1230_);
v___x_1232_ = lean_float_of_nat(v___x_1226_);
v___x_1233_ = lean_float_div(v___x_1232_, v___x_1230_);
v___x_1234_ = lean_box_float(v___x_1231_);
v___x_1235_ = lean_box_float(v___x_1233_);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1228_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
lean_inc_ref(v___y_1213_);
v___x_1238_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1215_, v___y_1213_, v___y_1216_, v___y_1214_, v_a_1219_, v___f_1211_, v___x_1237_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1238_;
}
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1240_ = lean_io_get_num_heartbeats();
v___x_1241_ = lean_io_get_num_heartbeats();
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 1);
lean_ctor_set(v___x_1221_, 0, v___y_1217_);
v___x_1243_ = v___x_1221_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___y_1217_);
v___x_1243_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
double v___x_1244_; double v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1244_ = lean_float_of_nat(v___x_1240_);
v___x_1245_ = lean_float_of_nat(v___x_1241_);
v___x_1246_ = lean_box_float(v___x_1244_);
v___x_1247_ = lean_box_float(v___x_1245_);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1246_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1243_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
lean_inc_ref(v___y_1213_);
v___x_1250_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1215_, v___y_1213_, v___y_1216_, v___y_1214_, v_a_1219_, v___f_1211_, v___x_1249_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1250_;
}
}
}
}
v___jp_1254_:
{
lean_object* v___x_1262_; double v___x_1263_; double v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1262_ = lean_io_get_num_heartbeats();
v___x_1263_ = lean_float_of_nat(v___y_1256_);
v___x_1264_ = lean_float_of_nat(v___x_1262_);
v___x_1265_ = lean_box_float(v___x_1263_);
v___x_1266_ = lean_box_float(v___x_1264_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v_a_1261_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
lean_inc_ref(v___y_1258_);
v___x_1269_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1255_, v___y_1258_, v___y_1257_, v___y_1260_, v___y_1259_, v___f_1253_, v___x_1268_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1269_;
}
v___jp_1270_:
{
lean_object* v___x_1278_; double v___x_1279_; double v___x_1280_; double v___x_1281_; double v___x_1282_; double v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1278_ = lean_io_mono_nanos_now();
v___x_1279_ = lean_float_of_nat(v___y_1276_);
v___x_1280_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1281_ = lean_float_div(v___x_1279_, v___x_1280_);
v___x_1282_ = lean_float_of_nat(v___x_1278_);
v___x_1283_ = lean_float_div(v___x_1282_, v___x_1280_);
v___x_1284_ = lean_box_float(v___x_1281_);
v___x_1285_ = lean_box_float(v___x_1283_);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v_a_1277_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
lean_inc_ref(v___y_1273_);
v___x_1288_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1271_, v___y_1273_, v___y_1272_, v___y_1275_, v___y_1274_, v___f_1253_, v___x_1287_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1288_;
}
v___jp_1289_:
{
lean_object* v___x_1297_; lean_object* v_a_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1297_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1297_);
v___x_1299_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1300_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1292_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1009_);
v___x_1302_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1296_, v___y_1291_, v___y_1295_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 1);
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
v___y_1271_ = v___y_1290_;
v___y_1272_ = v___y_1292_;
v___y_1273_ = v___y_1293_;
v___y_1274_ = v_a_1298_;
v___y_1275_ = v___y_1294_;
v___y_1276_ = v___x_1301_;
v_a_1277_ = v___x_1308_;
goto v___jp_1270_;
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_a_1311_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1302_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1302_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set_tag(v___x_1313_, 0);
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
v___y_1271_ = v___y_1290_;
v___y_1272_ = v___y_1292_;
v___y_1273_ = v___y_1293_;
v___y_1274_ = v_a_1298_;
v___y_1275_ = v___y_1294_;
v___y_1276_ = v___x_1301_;
v_a_1277_ = v___x_1316_;
goto v___jp_1270_;
}
}
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1009_);
v___x_1320_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1296_, v___y_1291_, v___y_1295_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set_tag(v___x_1323_, 1);
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
v___y_1255_ = v___y_1290_;
v___y_1256_ = v___x_1319_;
v___y_1257_ = v___y_1292_;
v___y_1258_ = v___y_1293_;
v___y_1259_ = v_a_1298_;
v___y_1260_ = v___y_1294_;
v_a_1261_ = v___x_1326_;
goto v___jp_1254_;
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1320_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1320_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
lean_ctor_set_tag(v___x_1331_, 0);
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
v___y_1255_ = v___y_1290_;
v___y_1256_ = v___x_1319_;
v___y_1257_ = v___y_1292_;
v___y_1258_ = v___y_1293_;
v___y_1259_ = v_a_1298_;
v___y_1260_ = v___y_1294_;
v_a_1261_ = v___x_1334_;
goto v___jp_1254_;
}
}
}
}
}
v___jp_1338_:
{
lean_object* v___x_1346_; double v___x_1347_; double v___x_1348_; double v___x_1349_; double v___x_1350_; double v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1346_ = lean_io_mono_nanos_now();
v___x_1347_ = lean_float_of_nat(v___y_1341_);
v___x_1348_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1349_ = lean_float_div(v___x_1347_, v___x_1348_);
v___x_1350_ = lean_float_of_nat(v___x_1346_);
v___x_1351_ = lean_float_div(v___x_1350_, v___x_1348_);
v___x_1352_ = lean_box_float(v___x_1349_);
v___x_1353_ = lean_box_float(v___x_1351_);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v_a_1345_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
lean_inc_ref(v___y_1342_);
v___x_1356_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1339_, v___y_1342_, v___y_1340_, v___y_1344_, v___y_1343_, v___f_1337_, v___x_1355_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1356_;
}
v___jp_1357_:
{
lean_object* v___x_1365_; double v___x_1366_; double v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1365_ = lean_io_get_num_heartbeats();
v___x_1366_ = lean_float_of_nat(v___y_1359_);
v___x_1367_ = lean_float_of_nat(v___x_1365_);
v___x_1368_ = lean_box_float(v___x_1366_);
v___x_1369_ = lean_box_float(v___x_1367_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_a_1364_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
lean_inc_ref(v___y_1361_);
v___x_1372_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1358_, v___y_1361_, v___y_1360_, v___y_1363_, v___y_1362_, v___f_1337_, v___x_1371_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1372_;
}
v___jp_1374_:
{
lean_object* v___x_1386_; double v___x_1387_; double v___x_1388_; double v___x_1389_; double v___x_1390_; double v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1386_ = lean_io_mono_nanos_now();
v___x_1387_ = lean_float_of_nat(v___y_1384_);
v___x_1388_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1389_ = lean_float_div(v___x_1387_, v___x_1388_);
v___x_1390_ = lean_float_of_nat(v___x_1386_);
v___x_1391_ = lean_float_div(v___x_1390_, v___x_1388_);
v___x_1392_ = lean_box_float(v___x_1389_);
v___x_1393_ = lean_box_float(v___x_1391_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v_a_1385_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
lean_inc_ref(v___y_1381_);
lean_inc(v_trace_1009_);
v___x_1396_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1375_, v___y_1381_, v___y_1380_, v___y_1378_, v___y_1377_, v___f_1373_, v___x_1395_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1143_ = v___y_1375_;
v___y_1144_ = v___y_1376_;
v___y_1145_ = v___y_1379_;
v___y_1146_ = v___y_1380_;
v___y_1147_ = v___y_1381_;
v___y_1148_ = v___y_1382_;
v___y_1149_ = v___y_1383_;
v___y_1150_ = v___x_1396_;
goto v___jp_1142_;
}
v___jp_1397_:
{
lean_object* v___x_1409_; double v___x_1410_; double v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1409_ = lean_io_get_num_heartbeats();
v___x_1410_ = lean_float_of_nat(v___y_1407_);
v___x_1411_ = lean_float_of_nat(v___x_1409_);
v___x_1412_ = lean_box_float(v___x_1410_);
v___x_1413_ = lean_box_float(v___x_1411_);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v_a_1408_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
lean_inc_ref(v___y_1404_);
lean_inc(v_trace_1009_);
v___x_1416_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1398_, v___y_1404_, v___y_1403_, v___y_1401_, v___y_1400_, v___f_1373_, v___x_1415_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1143_ = v___y_1398_;
v___y_1144_ = v___y_1399_;
v___y_1145_ = v___y_1402_;
v___y_1146_ = v___y_1403_;
v___y_1147_ = v___y_1404_;
v___y_1148_ = v___y_1405_;
v___y_1149_ = v___y_1406_;
v___y_1150_ = v___x_1416_;
goto v___jp_1142_;
}
v___jp_1417_:
{
lean_object* v___x_1430_; 
v___x_1430_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
if (v___y_1425_ == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1009_);
v___x_1433_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1420_, v___y_1422_, v___y_1424_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set_tag(v___x_1436_, 1);
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v___y_1375_ = v___y_1418_;
v___y_1376_ = v___y_1426_;
v___y_1377_ = v_a_1431_;
v___y_1378_ = v___y_1419_;
v___y_1379_ = v___y_1421_;
v___y_1380_ = v___y_1427_;
v___y_1381_ = v___y_1428_;
v___y_1382_ = v___y_1429_;
v___y_1383_ = v___y_1423_;
v___y_1384_ = v___x_1432_;
v_a_1385_ = v___x_1439_;
goto v___jp_1374_;
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_a_1442_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1433_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1433_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 0);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
v___y_1375_ = v___y_1418_;
v___y_1376_ = v___y_1426_;
v___y_1377_ = v_a_1431_;
v___y_1378_ = v___y_1419_;
v___y_1379_ = v___y_1421_;
v___y_1380_ = v___y_1427_;
v___y_1381_ = v___y_1428_;
v___y_1382_ = v___y_1429_;
v___y_1383_ = v___y_1423_;
v___y_1384_ = v___x_1432_;
v_a_1385_ = v___x_1447_;
goto v___jp_1374_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_a_1450_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1450_);
lean_dec_ref(v___x_1430_);
v___x_1451_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1009_);
v___x_1452_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1420_, v___y_1422_, v___y_1424_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set_tag(v___x_1455_, 1);
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
v___y_1398_ = v___y_1418_;
v___y_1399_ = v___y_1426_;
v___y_1400_ = v_a_1450_;
v___y_1401_ = v___y_1419_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1427_;
v___y_1404_ = v___y_1428_;
v___y_1405_ = v___y_1429_;
v___y_1406_ = v___y_1423_;
v___y_1407_ = v___x_1451_;
v_a_1408_ = v___x_1458_;
goto v___jp_1397_;
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_a_1461_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1452_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1452_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set_tag(v___x_1463_, 0);
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
v___y_1398_ = v___y_1418_;
v___y_1399_ = v___y_1426_;
v___y_1400_ = v_a_1450_;
v___y_1401_ = v___y_1419_;
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1427_;
v___y_1404_ = v___y_1428_;
v___y_1405_ = v___y_1429_;
v___y_1406_ = v___y_1423_;
v___y_1407_ = v___x_1451_;
v_a_1408_ = v___x_1466_;
goto v___jp_1397_;
}
}
}
}
}
v___jp_1469_:
{
lean_object* v___x_1481_; double v___x_1482_; double v___x_1483_; double v___x_1484_; double v___x_1485_; double v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1481_ = lean_io_mono_nanos_now();
v___x_1482_ = lean_float_of_nat(v___y_1479_);
v___x_1483_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1484_ = lean_float_div(v___x_1482_, v___x_1483_);
v___x_1485_ = lean_float_of_nat(v___x_1481_);
v___x_1486_ = lean_float_div(v___x_1485_, v___x_1483_);
v___x_1487_ = lean_box_float(v___x_1484_);
v___x_1488_ = lean_box_float(v___x_1486_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_a_1480_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
lean_inc_ref(v___y_1477_);
lean_inc(v_trace_1009_);
v___x_1491_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1471_, v___y_1477_, v___y_1474_, v___y_1476_, v___y_1470_, v___f_1253_, v___x_1490_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1194_ = v___y_1471_;
v___y_1195_ = v___y_1472_;
v___y_1196_ = v___y_1473_;
v___y_1197_ = v___y_1474_;
v___y_1198_ = v___y_1477_;
v___y_1199_ = v___y_1475_;
v___y_1200_ = v___y_1478_;
v___y_1201_ = v___x_1491_;
goto v___jp_1193_;
}
v___jp_1492_:
{
lean_object* v___x_1504_; double v___x_1505_; double v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1504_ = lean_io_get_num_heartbeats();
v___x_1505_ = lean_float_of_nat(v___y_1496_);
v___x_1506_ = lean_float_of_nat(v___x_1504_);
v___x_1507_ = lean_box_float(v___x_1505_);
v___x_1508_ = lean_box_float(v___x_1506_);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_a_1503_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
lean_inc_ref(v___y_1501_);
lean_inc(v_trace_1009_);
v___x_1511_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1494_, v___y_1501_, v___y_1498_, v___y_1500_, v___y_1493_, v___f_1253_, v___x_1510_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1194_ = v___y_1494_;
v___y_1195_ = v___y_1495_;
v___y_1196_ = v___y_1497_;
v___y_1197_ = v___y_1498_;
v___y_1198_ = v___y_1501_;
v___y_1199_ = v___y_1499_;
v___y_1200_ = v___y_1502_;
v___y_1201_ = v___x_1511_;
goto v___jp_1193_;
}
v___jp_1512_:
{
lean_object* v___x_1525_; 
v___x_1525_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
if (v___y_1521_ == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref(v___x_1525_);
v___x_1527_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1009_);
v___x_1528_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1519_, v___y_1515_, v___y_1520_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 1);
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
v___y_1470_ = v_a_1526_;
v___y_1471_ = v___y_1513_;
v___y_1472_ = v___y_1522_;
v___y_1473_ = v___y_1514_;
v___y_1474_ = v___y_1523_;
v___y_1475_ = v___y_1516_;
v___y_1476_ = v___y_1517_;
v___y_1477_ = v___y_1524_;
v___y_1478_ = v___y_1518_;
v___y_1479_ = v___x_1527_;
v_a_1480_ = v___x_1534_;
goto v___jp_1469_;
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_a_1537_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1528_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1528_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 0);
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
v___y_1470_ = v_a_1526_;
v___y_1471_ = v___y_1513_;
v___y_1472_ = v___y_1522_;
v___y_1473_ = v___y_1514_;
v___y_1474_ = v___y_1523_;
v___y_1475_ = v___y_1516_;
v___y_1476_ = v___y_1517_;
v___y_1477_ = v___y_1524_;
v___y_1478_ = v___y_1518_;
v___y_1479_ = v___x_1527_;
v_a_1480_ = v___x_1542_;
goto v___jp_1469_;
}
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_a_1545_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v___x_1525_);
v___x_1546_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1009_);
v___x_1547_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1519_, v___y_1515_, v___y_1520_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 1);
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
v___y_1493_ = v_a_1545_;
v___y_1494_ = v___y_1513_;
v___y_1495_ = v___y_1522_;
v___y_1496_ = v___x_1546_;
v___y_1497_ = v___y_1514_;
v___y_1498_ = v___y_1523_;
v___y_1499_ = v___y_1516_;
v___y_1500_ = v___y_1517_;
v___y_1501_ = v___y_1524_;
v___y_1502_ = v___y_1518_;
v_a_1503_ = v___x_1553_;
goto v___jp_1492_;
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
v_a_1556_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1547_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1547_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set_tag(v___x_1558_, 0);
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
v___y_1493_ = v_a_1545_;
v___y_1494_ = v___y_1513_;
v___y_1495_ = v___y_1522_;
v___y_1496_ = v___x_1546_;
v___y_1497_ = v___y_1514_;
v___y_1498_ = v___y_1523_;
v___y_1499_ = v___y_1516_;
v___y_1500_ = v___y_1517_;
v___y_1501_ = v___y_1524_;
v___y_1502_ = v___y_1518_;
v_a_1503_ = v___x_1561_;
goto v___jp_1492_;
}
}
}
}
}
v___jp_1564_:
{
lean_object* v___x_1576_; double v___x_1577_; double v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1576_ = lean_io_get_num_heartbeats();
v___x_1577_ = lean_float_of_nat(v___y_1574_);
v___x_1578_ = lean_float_of_nat(v___x_1576_);
v___x_1579_ = lean_box_float(v___x_1577_);
v___x_1580_ = lean_box_float(v___x_1578_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v_a_1575_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
lean_inc_ref(v___y_1570_);
lean_inc(v_trace_1009_);
v___x_1583_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1565_, v___y_1570_, v___y_1568_, v___y_1572_, v___y_1571_, v___f_1337_, v___x_1582_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1194_ = v___y_1565_;
v___y_1195_ = v___y_1566_;
v___y_1196_ = v___y_1567_;
v___y_1197_ = v___y_1568_;
v___y_1198_ = v___y_1570_;
v___y_1199_ = v___y_1569_;
v___y_1200_ = v___y_1573_;
v___y_1201_ = v___x_1583_;
goto v___jp_1193_;
}
v___jp_1584_:
{
lean_object* v___x_1596_; double v___x_1597_; double v___x_1598_; double v___x_1599_; double v___x_1600_; double v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1596_ = lean_io_mono_nanos_now();
v___x_1597_ = lean_float_of_nat(v___y_1591_);
v___x_1598_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1599_ = lean_float_div(v___x_1597_, v___x_1598_);
v___x_1600_ = lean_float_of_nat(v___x_1596_);
v___x_1601_ = lean_float_div(v___x_1600_, v___x_1598_);
v___x_1602_ = lean_box_float(v___x_1599_);
v___x_1603_ = lean_box_float(v___x_1601_);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v_a_1595_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
lean_inc_ref(v___y_1590_);
lean_inc(v_trace_1009_);
v___x_1606_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1585_, v___y_1590_, v___y_1588_, v___y_1593_, v___y_1592_, v___f_1337_, v___x_1605_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1194_ = v___y_1585_;
v___y_1195_ = v___y_1586_;
v___y_1196_ = v___y_1587_;
v___y_1197_ = v___y_1588_;
v___y_1198_ = v___y_1590_;
v___y_1199_ = v___y_1589_;
v___y_1200_ = v___y_1594_;
v___y_1201_ = v___x_1606_;
goto v___jp_1193_;
}
v___jp_1607_:
{
lean_object* v___x_1619_; double v___x_1620_; double v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1619_ = lean_io_get_num_heartbeats();
v___x_1620_ = lean_float_of_nat(v___y_1610_);
v___x_1621_ = lean_float_of_nat(v___x_1619_);
v___x_1622_ = lean_box_float(v___x_1620_);
v___x_1623_ = lean_box_float(v___x_1621_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v_a_1618_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
lean_inc_ref(v___y_1615_);
lean_inc(v_trace_1009_);
v___x_1626_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1608_, v___y_1615_, v___y_1613_, v___y_1611_, v___y_1617_, v___f_1373_, v___x_1625_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1194_ = v___y_1608_;
v___y_1195_ = v___y_1609_;
v___y_1196_ = v___y_1612_;
v___y_1197_ = v___y_1613_;
v___y_1198_ = v___y_1615_;
v___y_1199_ = v___y_1614_;
v___y_1200_ = v___y_1616_;
v___y_1201_ = v___x_1626_;
goto v___jp_1193_;
}
v___jp_1627_:
{
lean_object* v___x_1639_; double v___x_1640_; double v___x_1641_; double v___x_1642_; double v___x_1643_; double v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1639_ = lean_io_mono_nanos_now();
v___x_1640_ = lean_float_of_nat(v___y_1637_);
v___x_1641_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1642_ = lean_float_div(v___x_1640_, v___x_1641_);
v___x_1643_ = lean_float_of_nat(v___x_1639_);
v___x_1644_ = lean_float_div(v___x_1643_, v___x_1641_);
v___x_1645_ = lean_box_float(v___x_1642_);
v___x_1646_ = lean_box_float(v___x_1644_);
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_a_1638_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
lean_inc_ref(v___y_1634_);
lean_inc(v_trace_1009_);
v___x_1649_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1628_, v___y_1634_, v___y_1632_, v___y_1630_, v___y_1636_, v___f_1373_, v___x_1648_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1194_ = v___y_1628_;
v___y_1195_ = v___y_1629_;
v___y_1196_ = v___y_1631_;
v___y_1197_ = v___y_1632_;
v___y_1198_ = v___y_1634_;
v___y_1199_ = v___y_1633_;
v___y_1200_ = v___y_1635_;
v___y_1201_ = v___x_1649_;
goto v___jp_1193_;
}
v___jp_1650_:
{
lean_object* v___x_1663_; 
v___x_1663_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
if (v___y_1659_ == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1009_);
v___x_1666_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1651_, v___y_1655_, v___y_1657_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set_tag(v___x_1669_, 1);
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
v___y_1628_ = v___y_1652_;
v___y_1629_ = v___y_1660_;
v___y_1630_ = v___y_1653_;
v___y_1631_ = v___y_1654_;
v___y_1632_ = v___y_1661_;
v___y_1633_ = v___y_1656_;
v___y_1634_ = v___y_1662_;
v___y_1635_ = v___y_1658_;
v___y_1636_ = v_a_1664_;
v___y_1637_ = v___x_1665_;
v_a_1638_ = v___x_1672_;
goto v___jp_1627_;
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
v_a_1675_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1666_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1666_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set_tag(v___x_1677_, 0);
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
v___y_1628_ = v___y_1652_;
v___y_1629_ = v___y_1660_;
v___y_1630_ = v___y_1653_;
v___y_1631_ = v___y_1654_;
v___y_1632_ = v___y_1661_;
v___y_1633_ = v___y_1656_;
v___y_1634_ = v___y_1662_;
v___y_1635_ = v___y_1658_;
v___y_1636_ = v_a_1664_;
v___y_1637_ = v___x_1665_;
v_a_1638_ = v___x_1680_;
goto v___jp_1627_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_a_1683_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1683_);
lean_dec_ref(v___x_1663_);
v___x_1684_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1009_);
v___x_1685_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1651_, v___y_1655_, v___y_1657_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set_tag(v___x_1688_, 1);
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
v___y_1608_ = v___y_1652_;
v___y_1609_ = v___y_1660_;
v___y_1610_ = v___x_1684_;
v___y_1611_ = v___y_1653_;
v___y_1612_ = v___y_1654_;
v___y_1613_ = v___y_1661_;
v___y_1614_ = v___y_1656_;
v___y_1615_ = v___y_1662_;
v___y_1616_ = v___y_1658_;
v___y_1617_ = v_a_1683_;
v_a_1618_ = v___x_1691_;
goto v___jp_1607_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
v_a_1694_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1685_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1685_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 0);
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
v___y_1608_ = v___y_1652_;
v___y_1609_ = v___y_1660_;
v___y_1610_ = v___x_1684_;
v___y_1611_ = v___y_1653_;
v___y_1612_ = v___y_1654_;
v___y_1613_ = v___y_1661_;
v___y_1614_ = v___y_1656_;
v___y_1615_ = v___y_1662_;
v___y_1616_ = v___y_1658_;
v___y_1617_ = v_a_1683_;
v_a_1618_ = v___x_1699_;
goto v___jp_1607_;
}
}
}
}
}
v___jp_1702_:
{
lean_object* v___x_1714_; double v___x_1715_; double v___x_1716_; double v___x_1717_; double v___x_1718_; double v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1714_ = lean_io_mono_nanos_now();
v___x_1715_ = lean_float_of_nat(v___y_1705_);
v___x_1716_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1717_ = lean_float_div(v___x_1715_, v___x_1716_);
v___x_1718_ = lean_float_of_nat(v___x_1714_);
v___x_1719_ = lean_float_div(v___x_1718_, v___x_1716_);
v___x_1720_ = lean_box_float(v___x_1717_);
v___x_1721_ = lean_box_float(v___x_1719_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v_a_1713_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
lean_inc_ref(v___y_1709_);
lean_inc(v_trace_1009_);
v___x_1724_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1703_, v___y_1709_, v___y_1708_, v___y_1712_, v___y_1707_, v___f_1337_, v___x_1723_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1143_ = v___y_1703_;
v___y_1144_ = v___y_1704_;
v___y_1145_ = v___y_1706_;
v___y_1146_ = v___y_1708_;
v___y_1147_ = v___y_1709_;
v___y_1148_ = v___y_1710_;
v___y_1149_ = v___y_1711_;
v___y_1150_ = v___x_1724_;
goto v___jp_1142_;
}
v___jp_1725_:
{
lean_object* v___x_1737_; double v___x_1738_; double v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1737_ = lean_io_get_num_heartbeats();
v___x_1738_ = lean_float_of_nat(v___y_1727_);
v___x_1739_ = lean_float_of_nat(v___x_1737_);
v___x_1740_ = lean_box_float(v___x_1738_);
v___x_1741_ = lean_box_float(v___x_1739_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_a_1736_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
lean_inc_ref(v___y_1732_);
lean_inc(v_trace_1009_);
v___x_1744_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1726_, v___y_1732_, v___y_1731_, v___y_1735_, v___y_1730_, v___f_1337_, v___x_1743_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1143_ = v___y_1726_;
v___y_1144_ = v___y_1728_;
v___y_1145_ = v___y_1729_;
v___y_1146_ = v___y_1731_;
v___y_1147_ = v___y_1732_;
v___y_1148_ = v___y_1733_;
v___y_1149_ = v___y_1734_;
v___y_1150_ = v___x_1744_;
goto v___jp_1142_;
}
v___jp_1745_:
{
lean_object* v___x_1757_; double v___x_1758_; double v___x_1759_; double v___x_1760_; double v___x_1761_; double v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1757_ = lean_io_mono_nanos_now();
v___x_1758_ = lean_float_of_nat(v___y_1751_);
v___x_1759_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1760_ = lean_float_div(v___x_1758_, v___x_1759_);
v___x_1761_ = lean_float_of_nat(v___x_1757_);
v___x_1762_ = lean_float_div(v___x_1761_, v___x_1759_);
v___x_1763_ = lean_box_float(v___x_1760_);
v___x_1764_ = lean_box_float(v___x_1762_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_a_1756_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
lean_inc_ref(v___y_1750_);
lean_inc(v_trace_1009_);
v___x_1767_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1746_, v___y_1750_, v___y_1749_, v___y_1755_, v___y_1753_, v___f_1253_, v___x_1766_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1143_ = v___y_1746_;
v___y_1144_ = v___y_1747_;
v___y_1145_ = v___y_1748_;
v___y_1146_ = v___y_1749_;
v___y_1147_ = v___y_1750_;
v___y_1148_ = v___y_1752_;
v___y_1149_ = v___y_1754_;
v___y_1150_ = v___x_1767_;
goto v___jp_1142_;
}
v___jp_1768_:
{
lean_object* v___x_1780_; double v___x_1781_; double v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1780_ = lean_io_get_num_heartbeats();
v___x_1781_ = lean_float_of_nat(v___y_1770_);
v___x_1782_ = lean_float_of_nat(v___x_1780_);
v___x_1783_ = lean_box_float(v___x_1781_);
v___x_1784_ = lean_box_float(v___x_1782_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1783_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v_a_1779_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
lean_inc_ref(v___y_1774_);
lean_inc(v_trace_1009_);
v___x_1787_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1769_, v___y_1774_, v___y_1773_, v___y_1778_, v___y_1776_, v___f_1253_, v___x_1786_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1143_ = v___y_1769_;
v___y_1144_ = v___y_1771_;
v___y_1145_ = v___y_1772_;
v___y_1146_ = v___y_1773_;
v___y_1147_ = v___y_1774_;
v___y_1148_ = v___y_1775_;
v___y_1149_ = v___y_1777_;
v___y_1150_ = v___x_1787_;
goto v___jp_1142_;
}
v___jp_1788_:
{
lean_object* v___x_1801_; 
v___x_1801_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
if (v___y_1796_ == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref(v___x_1801_);
v___x_1803_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1009_);
v___x_1804_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1790_, v___y_1792_, v___y_1795_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 1);
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
v___y_1746_ = v___y_1789_;
v___y_1747_ = v___y_1797_;
v___y_1748_ = v___y_1791_;
v___y_1749_ = v___y_1798_;
v___y_1750_ = v___y_1799_;
v___y_1751_ = v___x_1803_;
v___y_1752_ = v___y_1800_;
v___y_1753_ = v_a_1802_;
v___y_1754_ = v___y_1793_;
v___y_1755_ = v___y_1794_;
v_a_1756_ = v___x_1810_;
goto v___jp_1745_;
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_a_1813_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1804_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1804_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set_tag(v___x_1815_, 0);
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
v___y_1746_ = v___y_1789_;
v___y_1747_ = v___y_1797_;
v___y_1748_ = v___y_1791_;
v___y_1749_ = v___y_1798_;
v___y_1750_ = v___y_1799_;
v___y_1751_ = v___x_1803_;
v___y_1752_ = v___y_1800_;
v___y_1753_ = v_a_1802_;
v___y_1754_ = v___y_1793_;
v___y_1755_ = v___y_1794_;
v_a_1756_ = v___x_1818_;
goto v___jp_1745_;
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_a_1821_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1821_);
lean_dec_ref(v___x_1801_);
v___x_1822_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1009_);
v___x_1823_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1790_, v___y_1792_, v___y_1795_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 1);
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
v___y_1769_ = v___y_1789_;
v___y_1770_ = v___x_1822_;
v___y_1771_ = v___y_1797_;
v___y_1772_ = v___y_1791_;
v___y_1773_ = v___y_1798_;
v___y_1774_ = v___y_1799_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v_a_1821_;
v___y_1777_ = v___y_1793_;
v___y_1778_ = v___y_1794_;
v_a_1779_ = v___x_1829_;
goto v___jp_1768_;
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
v_a_1832_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1823_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1823_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set_tag(v___x_1834_, 0);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
v___y_1769_ = v___y_1789_;
v___y_1770_ = v___x_1822_;
v___y_1771_ = v___y_1797_;
v___y_1772_ = v___y_1791_;
v___y_1773_ = v___y_1798_;
v___y_1774_ = v___y_1799_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v_a_1821_;
v___y_1777_ = v___y_1793_;
v___y_1778_ = v___y_1794_;
v_a_1779_ = v___x_1837_;
goto v___jp_1768_;
}
}
}
}
}
v___jp_1840_:
{
lean_object* v___x_1848_; double v___x_1849_; double v___x_1850_; double v___x_1851_; double v___x_1852_; double v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1848_ = lean_io_mono_nanos_now();
v___x_1849_ = lean_float_of_nat(v___y_1844_);
v___x_1850_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1851_ = lean_float_div(v___x_1849_, v___x_1850_);
v___x_1852_ = lean_float_of_nat(v___x_1848_);
v___x_1853_ = lean_float_div(v___x_1852_, v___x_1850_);
v___x_1854_ = lean_box_float(v___x_1851_);
v___x_1855_ = lean_box_float(v___x_1853_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_a_1847_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
lean_inc_ref(v___y_1845_);
v___x_1858_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1841_, v___y_1845_, v___y_1843_, v___y_1846_, v___y_1842_, v___f_1373_, v___x_1857_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1858_;
}
v___jp_1859_:
{
lean_object* v___x_1867_; double v___x_1868_; double v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1867_ = lean_io_get_num_heartbeats();
v___x_1868_ = lean_float_of_nat(v___y_1860_);
v___x_1869_ = lean_float_of_nat(v___x_1867_);
v___x_1870_ = lean_box_float(v___x_1868_);
v___x_1871_ = lean_box_float(v___x_1869_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v_a_1866_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
lean_inc_ref(v___y_1864_);
v___x_1874_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1861_, v___y_1864_, v___y_1863_, v___y_1865_, v___y_1862_, v___f_1373_, v___x_1873_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1874_;
}
v___jp_1875_:
{
lean_object* v___x_1883_; lean_object* v_a_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1883_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1886_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1879_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1009_);
v___x_1888_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1882_, v___y_1878_, v___y_1877_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 1);
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
v___y_1841_ = v___y_1876_;
v___y_1842_ = v_a_1884_;
v___y_1843_ = v___y_1879_;
v___y_1844_ = v___x_1887_;
v___y_1845_ = v___y_1880_;
v___y_1846_ = v___y_1881_;
v_a_1847_ = v___x_1894_;
goto v___jp_1840_;
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
v_a_1897_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1888_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1888_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 0);
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
v___y_1841_ = v___y_1876_;
v___y_1842_ = v_a_1884_;
v___y_1843_ = v___y_1879_;
v___y_1844_ = v___x_1887_;
v___y_1845_ = v___y_1880_;
v___y_1846_ = v___y_1881_;
v_a_1847_ = v___x_1902_;
goto v___jp_1840_;
}
}
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1009_);
v___x_1906_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1882_, v___y_1878_, v___y_1877_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 1);
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
v___y_1860_ = v___x_1905_;
v___y_1861_ = v___y_1876_;
v___y_1862_ = v_a_1884_;
v___y_1863_ = v___y_1879_;
v___y_1864_ = v___y_1880_;
v___y_1865_ = v___y_1881_;
v_a_1866_ = v___x_1912_;
goto v___jp_1859_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1906_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1906_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 0);
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
v___y_1860_ = v___x_1905_;
v___y_1861_ = v___y_1876_;
v___y_1862_ = v_a_1884_;
v___y_1863_ = v___y_1879_;
v___y_1864_ = v___y_1880_;
v___y_1865_ = v___y_1881_;
v_a_1866_ = v___x_1920_;
goto v___jp_1859_;
}
}
}
}
}
v___jp_1925_:
{
lean_object* v___x_1931_; lean_object* v_a_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1931_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
v___x_1933_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1934_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1928_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1009_);
v___x_1936_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v_n_1924_, v___y_1927_, v_acc_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set_tag(v___x_1939_, 1);
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v___y_1339_ = v___y_1926_;
v___y_1340_ = v___y_1928_;
v___y_1341_ = v___x_1935_;
v___y_1342_ = v___y_1929_;
v___y_1343_ = v_a_1932_;
v___y_1344_ = v___y_1930_;
v_a_1345_ = v___x_1942_;
goto v___jp_1338_;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_a_1945_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1936_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1936_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set_tag(v___x_1947_, 0);
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
v___y_1339_ = v___y_1926_;
v___y_1340_ = v___y_1928_;
v___y_1341_ = v___x_1935_;
v___y_1342_ = v___y_1929_;
v___y_1343_ = v_a_1932_;
v___y_1344_ = v___y_1930_;
v_a_1345_ = v___x_1950_;
goto v___jp_1338_;
}
}
}
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1009_);
v___x_1954_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v_n_1924_, v___y_1927_, v_acc_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set_tag(v___x_1957_, 1);
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
v___y_1358_ = v___y_1926_;
v___y_1359_ = v___x_1953_;
v___y_1360_ = v___y_1928_;
v___y_1361_ = v___y_1929_;
v___y_1362_ = v_a_1932_;
v___y_1363_ = v___y_1930_;
v_a_1364_ = v___x_1960_;
goto v___jp_1357_;
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
v_a_1963_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1954_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1954_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 0);
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
v___y_1358_ = v___y_1926_;
v___y_1359_ = v___x_1953_;
v___y_1360_ = v___y_1928_;
v___y_1361_ = v___y_1929_;
v___y_1362_ = v_a_1932_;
v___y_1363_ = v___y_1930_;
v_a_1364_ = v___x_1968_;
goto v___jp_1357_;
}
}
}
}
}
v___jp_1971_:
{
if (v___y_1981_ == 0)
{
lean_object* v___x_1982_; 
lean_dec_ref(v___y_1974_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v___y_1973_);
v___x_1982_ = lean_apply_6(v___y_1979_, v___y_1973_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref(v___x_1982_);
if (lean_obj_tag(v_a_1983_) == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1984_ = lean_nat_add(v_n_1924_, v_one_1923_);
lean_dec(v_n_1924_);
v___x_1985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___y_1973_);
lean_ctor_set(v___x_1985_, 1, v_acc_1014_);
v___x_1986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1009_);
v___x_1987_ = l_Lean_Name_append(v___x_1986_, v_trace_1009_);
v___x_1988_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1980_, v___y_1976_, v___x_1987_);
lean_dec(v___x_1987_);
if (v___x_1988_ == 0)
{
if (v___y_1977_ == 0)
{
v_n_1012_ = v___x_1984_;
v_curr_1013_ = v___y_1975_;
v_acc_1014_ = v___x_1985_;
goto _start;
}
else
{
v___y_1290_ = v___y_1972_;
v___y_1291_ = v___y_1975_;
v___y_1292_ = v___y_1976_;
v___y_1293_ = v___y_1978_;
v___y_1294_ = v___x_1988_;
v___y_1295_ = v___x_1985_;
v___y_1296_ = v___x_1984_;
goto v___jp_1289_;
}
}
else
{
v___y_1290_ = v___y_1972_;
v___y_1291_ = v___y_1975_;
v___y_1292_ = v___y_1976_;
v___y_1293_ = v___y_1978_;
v___y_1294_ = v___x_1988_;
v___y_1295_ = v___x_1985_;
v___y_1296_ = v___x_1984_;
goto v___jp_1289_;
}
}
else
{
lean_object* v_val_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
lean_dec(v___y_1973_);
v_val_1990_ = lean_ctor_get(v_a_1983_, 0);
lean_inc(v_val_1990_);
lean_dec_ref(v_a_1983_);
v___x_1991_ = l_List_appendTR___redArg(v_val_1990_, v___y_1975_);
v___x_1992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1009_);
v___x_1993_ = l_Lean_Name_append(v___x_1992_, v_trace_1009_);
v___x_1994_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1980_, v___y_1976_, v___x_1993_);
lean_dec(v___x_1993_);
if (v___x_1994_ == 0)
{
if (v___y_1977_ == 0)
{
v_n_1012_ = v_n_1924_;
v_curr_1013_ = v___x_1991_;
goto _start;
}
else
{
v___y_1926_ = v___y_1972_;
v___y_1927_ = v___x_1991_;
v___y_1928_ = v___y_1976_;
v___y_1929_ = v___y_1978_;
v___y_1930_ = v___x_1994_;
goto v___jp_1925_;
}
}
else
{
v___y_1926_ = v___y_1972_;
v___y_1927_ = v___x_1991_;
v___y_1928_ = v___y_1976_;
v___y_1929_ = v___y_1978_;
v___y_1930_ = v___x_1994_;
goto v___jp_1925_;
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v___y_1975_);
lean_dec(v___y_1973_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
v_a_1996_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1982_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1982_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1975_);
lean_dec(v___y_1973_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
return v___y_1974_;
}
}
v___jp_2004_:
{
lean_object* v___x_2015_; 
v___x_2015_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
if (v___y_2007_ == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_2015_);
v___x_2017_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1009_);
v___x_2018_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v_n_1924_, v___y_2008_, v_acc_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
lean_ctor_set_tag(v___x_2021_, 1);
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
v___y_1703_ = v___y_2005_;
v___y_1704_ = v___y_2006_;
v___y_1705_ = v___x_2017_;
v___y_1706_ = v___y_2010_;
v___y_1707_ = v_a_2016_;
v___y_1708_ = v___y_2009_;
v___y_1709_ = v___y_2011_;
v___y_1710_ = v___y_2012_;
v___y_1711_ = v___y_2014_;
v___y_1712_ = v___y_2013_;
v_a_1713_ = v___x_2024_;
goto v___jp_1702_;
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
v_a_2027_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2018_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2018_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set_tag(v___x_2029_, 0);
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
v___y_1703_ = v___y_2005_;
v___y_1704_ = v___y_2006_;
v___y_1705_ = v___x_2017_;
v___y_1706_ = v___y_2010_;
v___y_1707_ = v_a_2016_;
v___y_1708_ = v___y_2009_;
v___y_1709_ = v___y_2011_;
v___y_1710_ = v___y_2012_;
v___y_1711_ = v___y_2014_;
v___y_1712_ = v___y_2013_;
v_a_1713_ = v___x_2032_;
goto v___jp_1702_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_a_2035_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_2015_);
v___x_2036_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1009_);
v___x_2037_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v_n_1924_, v___y_2008_, v_acc_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 1);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
v___y_1726_ = v___y_2005_;
v___y_1727_ = v___x_2036_;
v___y_1728_ = v___y_2006_;
v___y_1729_ = v___y_2010_;
v___y_1730_ = v_a_2035_;
v___y_1731_ = v___y_2009_;
v___y_1732_ = v___y_2011_;
v___y_1733_ = v___y_2012_;
v___y_1734_ = v___y_2014_;
v___y_1735_ = v___y_2013_;
v_a_1736_ = v___x_2043_;
goto v___jp_1725_;
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
v_a_2046_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2037_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2037_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 0);
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
v___y_1726_ = v___y_2005_;
v___y_1727_ = v___x_2036_;
v___y_1728_ = v___y_2006_;
v___y_1729_ = v___y_2010_;
v___y_1730_ = v_a_2035_;
v___y_1731_ = v___y_2009_;
v___y_1732_ = v___y_2011_;
v___y_1733_ = v___y_2012_;
v___y_1734_ = v___y_2014_;
v___y_1735_ = v___y_2013_;
v_a_1736_ = v___x_2051_;
goto v___jp_1725_;
}
}
}
}
}
v___jp_2054_:
{
if (v___y_2068_ == 0)
{
lean_object* v___x_2069_; 
lean_dec_ref(v___y_2056_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v___y_2057_);
v___x_2069_ = lean_apply_6(v___y_2060_, v___y_2057_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref(v___x_2069_);
if (lean_obj_tag(v_a_2070_) == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2071_ = lean_nat_add(v_n_1924_, v_one_1923_);
lean_dec(v_n_1924_);
v___x_2072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___y_2057_);
lean_ctor_set(v___x_2072_, 1, v_acc_1014_);
v___x_2073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1009_);
v___x_2074_ = l_Lean_Name_append(v___x_2073_, v_trace_1009_);
v___x_2075_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2067_, v___y_2064_, v___x_2074_);
lean_dec(v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = l_Lean_trace_profiler;
v___x_2077_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2064_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
lean_inc(v_trace_1009_);
v___x_2078_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___x_2071_, v___y_2059_, v___x_2072_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1143_ = v___y_2055_;
v___y_1144_ = v___y_2063_;
v___y_1145_ = v___y_2058_;
v___y_1146_ = v___y_2064_;
v___y_1147_ = v___y_2065_;
v___y_1148_ = v___y_2066_;
v___y_1149_ = v___y_2061_;
v___y_1150_ = v___x_2078_;
goto v___jp_1142_;
}
else
{
v___y_1789_ = v___y_2055_;
v___y_1790_ = v___x_2071_;
v___y_1791_ = v___y_2058_;
v___y_1792_ = v___y_2059_;
v___y_1793_ = v___y_2061_;
v___y_1794_ = v___x_2075_;
v___y_1795_ = v___x_2072_;
v___y_1796_ = v___y_2062_;
v___y_1797_ = v___y_2063_;
v___y_1798_ = v___y_2064_;
v___y_1799_ = v___y_2065_;
v___y_1800_ = v___y_2066_;
goto v___jp_1788_;
}
}
else
{
v___y_1789_ = v___y_2055_;
v___y_1790_ = v___x_2071_;
v___y_1791_ = v___y_2058_;
v___y_1792_ = v___y_2059_;
v___y_1793_ = v___y_2061_;
v___y_1794_ = v___x_2075_;
v___y_1795_ = v___x_2072_;
v___y_1796_ = v___y_2062_;
v___y_1797_ = v___y_2063_;
v___y_1798_ = v___y_2064_;
v___y_1799_ = v___y_2065_;
v___y_1800_ = v___y_2066_;
goto v___jp_1788_;
}
}
else
{
lean_object* v_val_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
lean_dec(v___y_2057_);
v_val_2079_ = lean_ctor_get(v_a_2070_, 0);
lean_inc(v_val_2079_);
lean_dec_ref(v_a_2070_);
v___x_2080_ = l_List_appendTR___redArg(v_val_2079_, v___y_2059_);
v___x_2081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1009_);
v___x_2082_ = l_Lean_Name_append(v___x_2081_, v_trace_1009_);
v___x_2083_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2067_, v___y_2064_, v___x_2082_);
lean_dec(v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2084_ = l_Lean_trace_profiler;
v___x_2085_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2064_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
lean_inc(v_trace_1009_);
v___x_2086_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v_n_1924_, v___x_2080_, v_acc_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1143_ = v___y_2055_;
v___y_1144_ = v___y_2063_;
v___y_1145_ = v___y_2058_;
v___y_1146_ = v___y_2064_;
v___y_1147_ = v___y_2065_;
v___y_1148_ = v___y_2066_;
v___y_1149_ = v___y_2061_;
v___y_1150_ = v___x_2086_;
goto v___jp_1142_;
}
else
{
v___y_2005_ = v___y_2055_;
v___y_2006_ = v___y_2063_;
v___y_2007_ = v___y_2062_;
v___y_2008_ = v___x_2080_;
v___y_2009_ = v___y_2064_;
v___y_2010_ = v___y_2058_;
v___y_2011_ = v___y_2065_;
v___y_2012_ = v___y_2066_;
v___y_2013_ = v___x_2083_;
v___y_2014_ = v___y_2061_;
goto v___jp_2004_;
}
}
else
{
v___y_2005_ = v___y_2055_;
v___y_2006_ = v___y_2063_;
v___y_2007_ = v___y_2062_;
v___y_2008_ = v___x_2080_;
v___y_2009_ = v___y_2064_;
v___y_2010_ = v___y_2058_;
v___y_2011_ = v___y_2065_;
v___y_2012_ = v___y_2066_;
v___y_2013_ = v___x_2083_;
v___y_2014_ = v___y_2061_;
goto v___jp_2004_;
}
}
}
else
{
lean_object* v_a_2087_; 
lean_dec(v___y_2059_);
lean_dec(v___y_2057_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec_ref(v_cfg_1008_);
v_a_2087_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2087_);
lean_dec_ref(v___x_2069_);
v___y_1133_ = v___y_2055_;
v___y_1134_ = v___y_2063_;
v___y_1135_ = v___y_2064_;
v___y_1136_ = v___y_2058_;
v___y_1137_ = v___y_2065_;
v___y_1138_ = v___y_2066_;
v___y_1139_ = v___y_2061_;
v_a_1140_ = v_a_2087_;
goto v___jp_1132_;
}
}
else
{
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec(v___y_2057_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec_ref(v_cfg_1008_);
v___y_1133_ = v___y_2055_;
v___y_1134_ = v___y_2063_;
v___y_1135_ = v___y_2064_;
v___y_1136_ = v___y_2058_;
v___y_1137_ = v___y_2065_;
v___y_1138_ = v___y_2066_;
v___y_1139_ = v___y_2061_;
v_a_1140_ = v___y_2056_;
goto v___jp_1132_;
}
}
v___jp_2088_:
{
lean_object* v___x_2099_; 
v___x_2099_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
if (v___y_2091_ == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref(v___x_2099_);
v___x_2101_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1009_);
v___x_2102_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v_n_1924_, v___y_2096_, v_acc_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set_tag(v___x_2105_, 1);
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
v___y_1585_ = v___y_2089_;
v___y_1586_ = v___y_2090_;
v___y_1587_ = v___y_2093_;
v___y_1588_ = v___y_2092_;
v___y_1589_ = v___y_2095_;
v___y_1590_ = v___y_2094_;
v___y_1591_ = v___x_2101_;
v___y_1592_ = v_a_2100_;
v___y_1593_ = v___y_2097_;
v___y_1594_ = v___y_2098_;
v_a_1595_ = v___x_2108_;
goto v___jp_1584_;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2102_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2102_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set_tag(v___x_2113_, 0);
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
v___y_1585_ = v___y_2089_;
v___y_1586_ = v___y_2090_;
v___y_1587_ = v___y_2093_;
v___y_1588_ = v___y_2092_;
v___y_1589_ = v___y_2095_;
v___y_1590_ = v___y_2094_;
v___y_1591_ = v___x_2101_;
v___y_1592_ = v_a_2100_;
v___y_1593_ = v___y_2097_;
v___y_1594_ = v___y_2098_;
v_a_1595_ = v___x_2116_;
goto v___jp_1584_;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v_a_2119_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2119_);
lean_dec_ref(v___x_2099_);
v___x_2120_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1009_);
v___x_2121_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v_n_1924_, v___y_2096_, v_acc_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set_tag(v___x_2124_, 1);
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
v___y_1565_ = v___y_2089_;
v___y_1566_ = v___y_2090_;
v___y_1567_ = v___y_2093_;
v___y_1568_ = v___y_2092_;
v___y_1569_ = v___y_2095_;
v___y_1570_ = v___y_2094_;
v___y_1571_ = v_a_2119_;
v___y_1572_ = v___y_2097_;
v___y_1573_ = v___y_2098_;
v___y_1574_ = v___x_2120_;
v_a_1575_ = v___x_2127_;
goto v___jp_1564_;
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_a_2130_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2121_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2121_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set_tag(v___x_2132_, 0);
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
v___y_1565_ = v___y_2089_;
v___y_1566_ = v___y_2090_;
v___y_1567_ = v___y_2093_;
v___y_1568_ = v___y_2092_;
v___y_1569_ = v___y_2095_;
v___y_1570_ = v___y_2094_;
v___y_1571_ = v_a_2119_;
v___y_1572_ = v___y_2097_;
v___y_1573_ = v___y_2098_;
v___y_1574_ = v___x_2120_;
v_a_1575_ = v___x_2135_;
goto v___jp_1564_;
}
}
}
}
}
v___jp_2138_:
{
if (v___y_2152_ == 0)
{
lean_object* v___x_2153_; 
lean_dec_ref(v___y_2143_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v___y_2140_);
v___x_2153_ = lean_apply_6(v___y_2145_, v___y_2140_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref(v___x_2153_);
if (lean_obj_tag(v_a_2154_) == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2155_ = lean_nat_add(v_n_1924_, v_one_1923_);
lean_dec(v_n_1924_);
v___x_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___y_2140_);
lean_ctor_set(v___x_2156_, 1, v_acc_1014_);
v___x_2157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1009_);
v___x_2158_ = l_Lean_Name_append(v___x_2157_, v_trace_1009_);
v___x_2159_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2151_, v___y_2149_, v___x_2158_);
lean_dec(v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = l_Lean_trace_profiler;
v___x_2161_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2149_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; 
lean_inc(v_trace_1009_);
v___x_2162_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___x_2155_, v___y_2142_, v___x_2156_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1194_ = v___y_2139_;
v___y_1195_ = v___y_2148_;
v___y_1196_ = v___y_2141_;
v___y_1197_ = v___y_2149_;
v___y_1198_ = v___y_2150_;
v___y_1199_ = v___y_2144_;
v___y_1200_ = v___y_2146_;
v___y_1201_ = v___x_2162_;
goto v___jp_1193_;
}
else
{
v___y_1513_ = v___y_2139_;
v___y_1514_ = v___y_2141_;
v___y_1515_ = v___y_2142_;
v___y_1516_ = v___y_2144_;
v___y_1517_ = v___x_2159_;
v___y_1518_ = v___y_2146_;
v___y_1519_ = v___x_2155_;
v___y_1520_ = v___x_2156_;
v___y_1521_ = v___y_2147_;
v___y_1522_ = v___y_2148_;
v___y_1523_ = v___y_2149_;
v___y_1524_ = v___y_2150_;
goto v___jp_1512_;
}
}
else
{
v___y_1513_ = v___y_2139_;
v___y_1514_ = v___y_2141_;
v___y_1515_ = v___y_2142_;
v___y_1516_ = v___y_2144_;
v___y_1517_ = v___x_2159_;
v___y_1518_ = v___y_2146_;
v___y_1519_ = v___x_2155_;
v___y_1520_ = v___x_2156_;
v___y_1521_ = v___y_2147_;
v___y_1522_ = v___y_2148_;
v___y_1523_ = v___y_2149_;
v___y_1524_ = v___y_2150_;
goto v___jp_1512_;
}
}
else
{
lean_object* v_val_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
lean_dec(v___y_2140_);
v_val_2163_ = lean_ctor_get(v_a_2154_, 0);
lean_inc(v_val_2163_);
lean_dec_ref(v_a_2154_);
v___x_2164_ = l_List_appendTR___redArg(v_val_2163_, v___y_2142_);
v___x_2165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1009_);
v___x_2166_ = l_Lean_Name_append(v___x_2165_, v_trace_1009_);
v___x_2167_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2151_, v___y_2149_, v___x_2166_);
lean_dec(v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = l_Lean_trace_profiler;
v___x_2169_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2149_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; 
lean_inc(v_trace_1009_);
v___x_2170_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v_n_1924_, v___x_2164_, v_acc_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1194_ = v___y_2139_;
v___y_1195_ = v___y_2148_;
v___y_1196_ = v___y_2141_;
v___y_1197_ = v___y_2149_;
v___y_1198_ = v___y_2150_;
v___y_1199_ = v___y_2144_;
v___y_1200_ = v___y_2146_;
v___y_1201_ = v___x_2170_;
goto v___jp_1193_;
}
else
{
v___y_2089_ = v___y_2139_;
v___y_2090_ = v___y_2148_;
v___y_2091_ = v___y_2147_;
v___y_2092_ = v___y_2149_;
v___y_2093_ = v___y_2141_;
v___y_2094_ = v___y_2150_;
v___y_2095_ = v___y_2144_;
v___y_2096_ = v___x_2164_;
v___y_2097_ = v___x_2167_;
v___y_2098_ = v___y_2146_;
goto v___jp_2088_;
}
}
else
{
v___y_2089_ = v___y_2139_;
v___y_2090_ = v___y_2148_;
v___y_2091_ = v___y_2147_;
v___y_2092_ = v___y_2149_;
v___y_2093_ = v___y_2141_;
v___y_2094_ = v___y_2150_;
v___y_2095_ = v___y_2144_;
v___y_2096_ = v___x_2164_;
v___y_2097_ = v___x_2167_;
v___y_2098_ = v___y_2146_;
goto v___jp_2088_;
}
}
}
else
{
lean_object* v_a_2171_; 
lean_dec(v___y_2142_);
lean_dec(v___y_2140_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec_ref(v_cfg_1008_);
v_a_2171_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2171_);
lean_dec_ref(v___x_2153_);
v___y_1184_ = v___y_2139_;
v___y_1185_ = v___y_2148_;
v___y_1186_ = v___y_2149_;
v___y_1187_ = v___y_2141_;
v___y_1188_ = v___y_2144_;
v___y_1189_ = v___y_2150_;
v___y_1190_ = v___y_2146_;
v_a_1191_ = v_a_2171_;
goto v___jp_1183_;
}
}
else
{
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2142_);
lean_dec(v___y_2140_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec_ref(v_cfg_1008_);
v___y_1184_ = v___y_2139_;
v___y_1185_ = v___y_2148_;
v___y_1186_ = v___y_2149_;
v___y_1187_ = v___y_2141_;
v___y_1188_ = v___y_2144_;
v___y_1189_ = v___y_2150_;
v___y_1190_ = v___y_2146_;
v_a_1191_ = v___y_2143_;
goto v___jp_1183_;
}
}
v___jp_2172_:
{
lean_object* v___x_2185_; lean_object* v_a_2186_; lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2185_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref(v___x_2185_);
v___x_2187_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2188_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2181_, v___x_2187_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec_ref(v___y_2179_);
v___x_2189_ = lean_io_mono_nanos_now();
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v___y_2175_);
v___x_2190_ = lean_apply_6(v___y_2174_, v___y_2175_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; uint8_t v___x_2192_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v___x_2190_);
v___x_2192_ = lean_unbox(v_a_2191_);
lean_dec(v_a_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; 
lean_inc_ref(v_next_1010_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v___y_2175_);
v___x_2193_ = lean_apply_7(v_next_1010_, v___y_2175_, v___y_2183_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; 
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec(v___y_2175_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec_ref(v_cfg_1008_);
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref(v___x_2193_);
v___y_1174_ = v___y_2173_;
v___y_1175_ = v___y_2180_;
v___y_1176_ = v___y_2181_;
v___y_1177_ = v___y_2176_;
v___y_1178_ = v___x_2189_;
v___y_1179_ = v___y_2182_;
v___y_1180_ = v_a_2186_;
v_a_1181_ = v_a_2194_;
goto v___jp_1173_;
}
else
{
lean_object* v_a_2195_; uint8_t v___x_2196_; 
v_a_2195_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2195_);
lean_dec_ref(v___x_2193_);
v___x_2196_ = l_Lean_Exception_isInterrupt(v_a_2195_);
if (v___x_2196_ == 0)
{
uint8_t v___x_2197_; 
lean_inc(v_a_2195_);
v___x_2197_ = l_Lean_Exception_isRuntime(v_a_2195_);
v___y_2139_ = v___y_2173_;
v___y_2140_ = v___y_2175_;
v___y_2141_ = v___y_2176_;
v___y_2142_ = v___y_2177_;
v___y_2143_ = v_a_2195_;
v___y_2144_ = v___x_2189_;
v___y_2145_ = v___y_2178_;
v___y_2146_ = v_a_2186_;
v___y_2147_ = v___x_2188_;
v___y_2148_ = v___y_2180_;
v___y_2149_ = v___y_2181_;
v___y_2150_ = v___y_2182_;
v___y_2151_ = v___y_2184_;
v___y_2152_ = v___x_2197_;
goto v___jp_2138_;
}
else
{
v___y_2139_ = v___y_2173_;
v___y_2140_ = v___y_2175_;
v___y_2141_ = v___y_2176_;
v___y_2142_ = v___y_2177_;
v___y_2143_ = v_a_2195_;
v___y_2144_ = v___x_2189_;
v___y_2145_ = v___y_2178_;
v___y_2146_ = v_a_2186_;
v___y_2147_ = v___x_2188_;
v___y_2148_ = v___y_2180_;
v___y_2149_ = v___y_2181_;
v___y_2150_ = v___y_2182_;
v___y_2151_ = v___y_2184_;
v___y_2152_ = v___x_2196_;
goto v___jp_2138_;
}
}
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
lean_dec_ref(v___y_2183_);
lean_dec_ref(v___y_2178_);
v___x_2198_ = lean_nat_add(v_n_1924_, v_one_1923_);
lean_dec(v_n_1924_);
v___x_2199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___y_2175_);
lean_ctor_set(v___x_2199_, 1, v_acc_1014_);
v___x_2200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1009_);
v___x_2201_ = l_Lean_Name_append(v___x_2200_, v_trace_1009_);
v___x_2202_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2184_, v___y_2181_, v___x_2201_);
lean_dec(v___x_2201_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = l_Lean_trace_profiler;
v___x_2204_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2181_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; 
lean_inc(v_trace_1009_);
v___x_2205_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___x_2198_, v___y_2177_, v___x_2199_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1194_ = v___y_2173_;
v___y_1195_ = v___y_2180_;
v___y_1196_ = v___y_2176_;
v___y_1197_ = v___y_2181_;
v___y_1198_ = v___y_2182_;
v___y_1199_ = v___x_2189_;
v___y_1200_ = v_a_2186_;
v___y_1201_ = v___x_2205_;
goto v___jp_1193_;
}
else
{
v___y_1651_ = v___x_2198_;
v___y_1652_ = v___y_2173_;
v___y_1653_ = v___x_2202_;
v___y_1654_ = v___y_2176_;
v___y_1655_ = v___y_2177_;
v___y_1656_ = v___x_2189_;
v___y_1657_ = v___x_2199_;
v___y_1658_ = v_a_2186_;
v___y_1659_ = v___x_2188_;
v___y_1660_ = v___y_2180_;
v___y_1661_ = v___y_2181_;
v___y_1662_ = v___y_2182_;
goto v___jp_1650_;
}
}
else
{
v___y_1651_ = v___x_2198_;
v___y_1652_ = v___y_2173_;
v___y_1653_ = v___x_2202_;
v___y_1654_ = v___y_2176_;
v___y_1655_ = v___y_2177_;
v___y_1656_ = v___x_2189_;
v___y_1657_ = v___x_2199_;
v___y_1658_ = v_a_2186_;
v___y_1659_ = v___x_2188_;
v___y_1660_ = v___y_2180_;
v___y_1661_ = v___y_2181_;
v___y_1662_ = v___y_2182_;
goto v___jp_1650_;
}
}
}
else
{
lean_object* v_a_2206_; 
lean_dec_ref(v___y_2183_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec(v___y_2175_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec_ref(v_cfg_1008_);
v_a_2206_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2206_);
lean_dec_ref(v___x_2190_);
v___y_1184_ = v___y_2173_;
v___y_1185_ = v___y_2180_;
v___y_1186_ = v___y_2181_;
v___y_1187_ = v___y_2176_;
v___y_1188_ = v___x_2189_;
v___y_1189_ = v___y_2182_;
v___y_1190_ = v_a_2186_;
v_a_1191_ = v_a_2206_;
goto v___jp_1183_;
}
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec_ref(v___y_2183_);
v___x_2207_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v___y_2175_);
v___x_2208_ = lean_apply_6(v___y_2174_, v___y_2175_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; uint8_t v___x_2210_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref(v___x_2208_);
v___x_2210_ = lean_unbox(v_a_2209_);
lean_dec(v_a_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; 
lean_inc_ref(v_next_1010_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v___y_2175_);
v___x_2211_ = lean_apply_7(v_next_1010_, v___y_2175_, v___y_2179_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; 
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec(v___y_2175_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec_ref(v_cfg_1008_);
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref(v___x_2211_);
v___y_1123_ = v___y_2173_;
v___y_1124_ = v___y_2180_;
v___y_1125_ = v___y_2181_;
v___y_1126_ = v___y_2176_;
v___y_1127_ = v___y_2182_;
v___y_1128_ = v___x_2207_;
v___y_1129_ = v_a_2186_;
v_a_1130_ = v_a_2212_;
goto v___jp_1122_;
}
else
{
lean_object* v_a_2213_; uint8_t v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2213_);
lean_dec_ref(v___x_2211_);
v___x_2214_ = l_Lean_Exception_isInterrupt(v_a_2213_);
if (v___x_2214_ == 0)
{
uint8_t v___x_2215_; 
lean_inc(v_a_2213_);
v___x_2215_ = l_Lean_Exception_isRuntime(v_a_2213_);
v___y_2055_ = v___y_2173_;
v___y_2056_ = v_a_2213_;
v___y_2057_ = v___y_2175_;
v___y_2058_ = v___y_2176_;
v___y_2059_ = v___y_2177_;
v___y_2060_ = v___y_2178_;
v___y_2061_ = v_a_2186_;
v___y_2062_ = v___x_2188_;
v___y_2063_ = v___y_2180_;
v___y_2064_ = v___y_2181_;
v___y_2065_ = v___y_2182_;
v___y_2066_ = v___x_2207_;
v___y_2067_ = v___y_2184_;
v___y_2068_ = v___x_2215_;
goto v___jp_2054_;
}
else
{
v___y_2055_ = v___y_2173_;
v___y_2056_ = v_a_2213_;
v___y_2057_ = v___y_2175_;
v___y_2058_ = v___y_2176_;
v___y_2059_ = v___y_2177_;
v___y_2060_ = v___y_2178_;
v___y_2061_ = v_a_2186_;
v___y_2062_ = v___x_2188_;
v___y_2063_ = v___y_2180_;
v___y_2064_ = v___y_2181_;
v___y_2065_ = v___y_2182_;
v___y_2066_ = v___x_2207_;
v___y_2067_ = v___y_2184_;
v___y_2068_ = v___x_2214_;
goto v___jp_2054_;
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
lean_dec_ref(v___y_2179_);
lean_dec_ref(v___y_2178_);
v___x_2216_ = lean_nat_add(v_n_1924_, v_one_1923_);
lean_dec(v_n_1924_);
v___x_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___y_2175_);
lean_ctor_set(v___x_2217_, 1, v_acc_1014_);
v___x_2218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1009_);
v___x_2219_ = l_Lean_Name_append(v___x_2218_, v_trace_1009_);
v___x_2220_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2184_, v___y_2181_, v___x_2219_);
lean_dec(v___x_2219_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2221_ = l_Lean_trace_profiler;
v___x_2222_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2181_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
lean_inc(v_trace_1009_);
v___x_2223_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___x_2216_, v___y_2177_, v___x_2217_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
v___y_1143_ = v___y_2173_;
v___y_1144_ = v___y_2180_;
v___y_1145_ = v___y_2176_;
v___y_1146_ = v___y_2181_;
v___y_1147_ = v___y_2182_;
v___y_1148_ = v___x_2207_;
v___y_1149_ = v_a_2186_;
v___y_1150_ = v___x_2223_;
goto v___jp_1142_;
}
else
{
v___y_1418_ = v___y_2173_;
v___y_1419_ = v___x_2220_;
v___y_1420_ = v___x_2216_;
v___y_1421_ = v___y_2176_;
v___y_1422_ = v___y_2177_;
v___y_1423_ = v_a_2186_;
v___y_1424_ = v___x_2217_;
v___y_1425_ = v___x_2188_;
v___y_1426_ = v___y_2180_;
v___y_1427_ = v___y_2181_;
v___y_1428_ = v___y_2182_;
v___y_1429_ = v___x_2207_;
goto v___jp_1417_;
}
}
else
{
v___y_1418_ = v___y_2173_;
v___y_1419_ = v___x_2220_;
v___y_1420_ = v___x_2216_;
v___y_1421_ = v___y_2176_;
v___y_1422_ = v___y_2177_;
v___y_1423_ = v_a_2186_;
v___y_1424_ = v___x_2217_;
v___y_1425_ = v___x_2188_;
v___y_1426_ = v___y_2180_;
v___y_1427_ = v___y_2181_;
v___y_1428_ = v___y_2182_;
v___y_1429_ = v___x_2207_;
goto v___jp_1417_;
}
}
}
else
{
lean_object* v_a_2224_; 
lean_dec_ref(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec(v___y_2175_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec_ref(v_cfg_1008_);
v_a_2224_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2224_);
lean_dec_ref(v___x_2208_);
v___y_1133_ = v___y_2173_;
v___y_1134_ = v___y_2180_;
v___y_1135_ = v___y_2181_;
v___y_1136_ = v___y_2176_;
v___y_1137_ = v___y_2182_;
v___y_1138_ = v___x_2207_;
v___y_1139_ = v_a_2186_;
v_a_1140_ = v_a_2224_;
goto v___jp_1132_;
}
}
}
v___jp_2225_:
{
if (v___y_2230_ == 0)
{
lean_object* v___x_2231_; 
lean_dec_ref(v___y_2229_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v___y_2226_);
v___x_2231_ = lean_apply_6(v___y_2228_, v___y_2226_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref(v___x_2231_);
if (lean_obj_tag(v_a_2232_) == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_nat_add(v_n_1924_, v_one_1923_);
lean_dec(v_n_1924_);
v___x_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___y_2226_);
lean_ctor_set(v___x_2234_, 1, v_acc_1014_);
v_n_1012_ = v___x_2233_;
v_curr_1013_ = v___y_2227_;
v_acc_1014_ = v___x_2234_;
goto _start;
}
else
{
lean_object* v_val_2236_; lean_object* v___x_2237_; 
lean_dec(v___y_2226_);
v_val_2236_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_val_2236_);
lean_dec_ref(v_a_2232_);
v___x_2237_ = l_List_appendTR___redArg(v_val_2236_, v___y_2227_);
v_n_1012_ = v_n_1924_;
v_curr_1013_ = v___x_2237_;
goto _start;
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
v_a_2239_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2231_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2231_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
return v___y_2229_;
}
}
v___jp_2247_:
{
if (lean_obj_tag(v_a_2248_) == 0)
{
if (lean_obj_tag(v_curr_1013_) == 0)
{
lean_object* v_options_2249_; lean_object* v_inheritedTraceOptions_2250_; uint8_t v_hasTrace_2251_; lean_object* v___x_2252_; 
lean_dec(v_n_1924_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec_ref(v_cfg_1008_);
v_options_2249_ = lean_ctor_get(v_a_1017_, 2);
v_inheritedTraceOptions_2250_ = lean_ctor_get(v_a_1017_, 13);
v_hasTrace_2251_ = lean_ctor_get_uint8(v_options_2249_, sizeof(void*)*1);
v___x_2252_ = l_List_reverse___redArg(v_acc_1014_);
if (v_hasTrace_2251_ == 0)
{
lean_object* v___x_2253_; 
lean_dec(v_trace_1009_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1009_);
v___x_2256_ = l_Lean_Name_append(v___x_2255_, v_trace_1009_);
v___x_2257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2250_, v_options_2249_, v___x_2256_);
lean_dec(v___x_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; uint8_t v___x_2259_; 
v___x_2258_ = l_Lean_trace_profiler;
v___x_2259_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2249_, v___x_2258_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
lean_dec(v_trace_1009_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2252_);
return v___x_2260_;
}
else
{
v___y_1213_ = v___x_2254_;
v___y_1214_ = v___x_2257_;
v___y_1215_ = v_hasTrace_2251_;
v___y_1216_ = v_options_2249_;
v___y_1217_ = v___x_2252_;
goto v___jp_1212_;
}
}
else
{
v___y_1213_ = v___x_2254_;
v___y_1214_ = v___x_2257_;
v___y_1215_ = v_hasTrace_2251_;
v___y_1216_ = v_options_2249_;
v___y_1217_ = v___x_2252_;
goto v___jp_1212_;
}
}
}
else
{
lean_object* v_head_2261_; lean_object* v_tail_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2335_; 
v_head_2261_ = lean_ctor_get(v_curr_1013_, 0);
v_tail_2262_ = lean_ctor_get(v_curr_1013_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_curr_1013_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2264_ = v_curr_1013_;
v_isShared_2265_ = v_isSharedCheck_2335_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_tail_2262_);
lean_inc(v_head_2261_);
lean_dec(v_curr_1013_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2335_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; lean_object* v_a_2267_; uint8_t v___x_2268_; uint8_t v___x_2269_; 
v___x_2266_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2261_, v_a_1016_);
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref(v___x_2266_);
v___x_2268_ = 1;
v___x_2269_ = lean_unbox(v_a_2267_);
lean_dec(v_a_2267_);
if (v___x_2269_ == 0)
{
lean_object* v_options_2270_; uint8_t v_hasTrace_2271_; 
v_options_2270_ = lean_ctor_get(v_a_1017_, 2);
v_hasTrace_2271_ = lean_ctor_get_uint8(v_options_2270_, sizeof(void*)*1);
if (v_hasTrace_2271_ == 0)
{
lean_object* v___x_2272_; 
lean_inc_ref(v_suspend_1209_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v_head_2261_);
v___x_2272_ = lean_apply_6(v_suspend_1209_, v_head_2261_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; uint8_t v___x_2274_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref(v___x_2272_);
v___x_2274_ = lean_unbox(v_a_2273_);
lean_dec(v_a_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___f_2275_; lean_object* v___x_2276_; 
lean_del_object(v___x_2264_);
lean_inc(v_acc_1014_);
lean_inc(v_n_1924_);
lean_inc(v_goals_1011_);
lean_inc_ref_n(v_next_1010_, 2);
lean_inc(v_trace_1009_);
lean_inc_ref(v_cfg_1008_);
lean_inc(v_tail_2262_);
v___f_2275_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2275_, 0, v_tail_2262_);
lean_closure_set(v___f_2275_, 1, v_cfg_1008_);
lean_closure_set(v___f_2275_, 2, v_trace_1009_);
lean_closure_set(v___f_2275_, 3, v_next_1010_);
lean_closure_set(v___f_2275_, 4, v_goals_1011_);
lean_closure_set(v___f_2275_, 5, v_n_1924_);
lean_closure_set(v___f_2275_, 6, v_acc_1014_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v_head_2261_);
v___x_2276_ = lean_apply_7(v_next_1010_, v_head_2261_, v___f_2275_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_dec(v_tail_2262_);
lean_dec(v_head_2261_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
return v___x_2276_;
}
else
{
lean_object* v_a_2277_; uint8_t v___x_2278_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
v___x_2278_ = l_Lean_Exception_isInterrupt(v_a_2277_);
if (v___x_2278_ == 0)
{
uint8_t v___x_2279_; 
v___x_2279_ = l_Lean_Exception_isRuntime(v_a_2277_);
lean_inc_ref(v_discharge_1210_);
v___y_2226_ = v_head_2261_;
v___y_2227_ = v_tail_2262_;
v___y_2228_ = v_discharge_1210_;
v___y_2229_ = v___x_2276_;
v___y_2230_ = v___x_2279_;
goto v___jp_2225_;
}
else
{
lean_dec(v_a_2277_);
lean_inc_ref(v_discharge_1210_);
v___y_2226_ = v_head_2261_;
v___y_2227_ = v_tail_2262_;
v___y_2228_ = v_discharge_1210_;
v___y_2229_ = v___x_2276_;
v___y_2230_ = v___x_2278_;
goto v___jp_2225_;
}
}
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = lean_nat_add(v_n_1924_, v_one_1923_);
lean_dec(v_n_1924_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v_acc_1014_);
v___x_2282_ = v___x_2264_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_head_2261_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_acc_1014_);
v___x_2282_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
v_n_1012_ = v___x_2280_;
v_curr_1013_ = v_tail_2262_;
v_acc_1014_ = v___x_2282_;
goto _start;
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_del_object(v___x_2264_);
lean_dec(v_tail_2262_);
lean_dec(v_head_2261_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
v_a_2285_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2272_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2272_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2293_; lean_object* v___f_2294_; lean_object* v___f_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v_inheritedTraceOptions_2293_ = lean_ctor_get(v_a_1017_, 13);
lean_inc(v_acc_1014_);
lean_inc(v_n_1924_);
lean_inc(v_goals_1011_);
lean_inc_ref(v_next_1010_);
lean_inc_n(v_trace_1009_, 2);
lean_inc_ref(v_cfg_1008_);
lean_inc(v_tail_2262_);
v___f_2294_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2294_, 0, v_tail_2262_);
lean_closure_set(v___f_2294_, 1, v_cfg_1008_);
lean_closure_set(v___f_2294_, 2, v_trace_1009_);
lean_closure_set(v___f_2294_, 3, v_next_1010_);
lean_closure_set(v___f_2294_, 4, v_goals_1011_);
lean_closure_set(v___f_2294_, 5, v_n_1924_);
lean_closure_set(v___f_2294_, 6, v_acc_1014_);
lean_inc(v_head_2261_);
v___f_2295_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(v___f_2295_, 0, v_head_2261_);
v___x_2296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
v___x_2298_ = l_Lean_Name_append(v___x_2297_, v_trace_1009_);
v___x_2299_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2293_, v_options_2270_, v___x_2298_);
lean_dec(v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = l_Lean_trace_profiler;
v___x_2301_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2270_, v___x_2300_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; 
lean_dec_ref(v___f_2295_);
lean_inc_ref(v_suspend_1209_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v_head_2261_);
v___x_2302_ = lean_apply_6(v_suspend_1209_, v_head_2261_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; uint8_t v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref(v___x_2302_);
v___x_2304_ = lean_unbox(v_a_2303_);
lean_dec(v_a_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; 
lean_del_object(v___x_2264_);
lean_inc_ref(v_next_1010_);
lean_inc(v_a_1018_);
lean_inc_ref(v_a_1017_);
lean_inc(v_a_1016_);
lean_inc_ref(v_a_1015_);
lean_inc(v_head_2261_);
v___x_2305_ = lean_apply_7(v_next_1010_, v_head_2261_, v___f_2294_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, lean_box(0));
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_dec(v_tail_2262_);
lean_dec(v_head_2261_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
return v___x_2305_;
}
else
{
lean_object* v_a_2306_; uint8_t v___x_2307_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
v___x_2307_ = l_Lean_Exception_isInterrupt(v_a_2306_);
if (v___x_2307_ == 0)
{
uint8_t v___x_2308_; 
v___x_2308_ = l_Lean_Exception_isRuntime(v_a_2306_);
lean_inc_ref(v_discharge_1210_);
v___y_1972_ = v___x_2268_;
v___y_1973_ = v_head_2261_;
v___y_1974_ = v___x_2305_;
v___y_1975_ = v_tail_2262_;
v___y_1976_ = v_options_2270_;
v___y_1977_ = v___x_2301_;
v___y_1978_ = v___x_2296_;
v___y_1979_ = v_discharge_1210_;
v___y_1980_ = v_inheritedTraceOptions_2293_;
v___y_1981_ = v___x_2308_;
goto v___jp_1971_;
}
else
{
lean_dec(v_a_2306_);
lean_inc_ref(v_discharge_1210_);
v___y_1972_ = v___x_2268_;
v___y_1973_ = v_head_2261_;
v___y_1974_ = v___x_2305_;
v___y_1975_ = v_tail_2262_;
v___y_1976_ = v_options_2270_;
v___y_1977_ = v___x_2301_;
v___y_1978_ = v___x_2296_;
v___y_1979_ = v_discharge_1210_;
v___y_1980_ = v_inheritedTraceOptions_2293_;
v___y_1981_ = v___x_2307_;
goto v___jp_1971_;
}
}
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
lean_dec_ref(v___f_2294_);
v___x_2309_ = lean_nat_add(v_n_1924_, v_one_1923_);
lean_dec(v_n_1924_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v_acc_1014_);
v___x_2311_ = v___x_2264_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_head_2261_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v_acc_1014_);
v___x_2311_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
if (v___x_2299_ == 0)
{
if (v___x_2301_ == 0)
{
v_n_1012_ = v___x_2309_;
v_curr_1013_ = v_tail_2262_;
v_acc_1014_ = v___x_2311_;
goto _start;
}
else
{
v___y_1876_ = v___x_2268_;
v___y_1877_ = v___x_2311_;
v___y_1878_ = v_tail_2262_;
v___y_1879_ = v_options_2270_;
v___y_1880_ = v___x_2296_;
v___y_1881_ = v___x_2299_;
v___y_1882_ = v___x_2309_;
goto v___jp_1875_;
}
}
else
{
v___y_1876_ = v___x_2268_;
v___y_1877_ = v___x_2311_;
v___y_1878_ = v_tail_2262_;
v___y_1879_ = v_options_2270_;
v___y_1880_ = v___x_2296_;
v___y_1881_ = v___x_2299_;
v___y_1882_ = v___x_2309_;
goto v___jp_1875_;
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v___f_2294_);
lean_del_object(v___x_2264_);
lean_dec(v_tail_2262_);
lean_dec(v_head_2261_);
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
v_a_2314_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2302_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2302_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
else
{
lean_del_object(v___x_2264_);
lean_inc_ref(v___f_2294_);
lean_inc_ref(v_discharge_1210_);
lean_inc_ref(v_suspend_1209_);
v___y_2173_ = v___x_2268_;
v___y_2174_ = v_suspend_1209_;
v___y_2175_ = v_head_2261_;
v___y_2176_ = v___f_2295_;
v___y_2177_ = v_tail_2262_;
v___y_2178_ = v_discharge_1210_;
v___y_2179_ = v___f_2294_;
v___y_2180_ = v___x_2299_;
v___y_2181_ = v_options_2270_;
v___y_2182_ = v___x_2296_;
v___y_2183_ = v___f_2294_;
v___y_2184_ = v_inheritedTraceOptions_2293_;
goto v___jp_2172_;
}
}
else
{
lean_del_object(v___x_2264_);
lean_inc_ref(v___f_2294_);
lean_inc_ref(v_discharge_1210_);
lean_inc_ref(v_suspend_1209_);
v___y_2173_ = v___x_2268_;
v___y_2174_ = v_suspend_1209_;
v___y_2175_ = v_head_2261_;
v___y_2176_ = v___f_2295_;
v___y_2177_ = v_tail_2262_;
v___y_2178_ = v_discharge_1210_;
v___y_2179_ = v___f_2294_;
v___y_2180_ = v___x_2299_;
v___y_2181_ = v_options_2270_;
v___y_2182_ = v___x_2296_;
v___y_2183_ = v___f_2294_;
v___y_2184_ = v_inheritedTraceOptions_2293_;
goto v___jp_2172_;
}
}
}
else
{
lean_object* v_options_2322_; lean_object* v_inheritedTraceOptions_2323_; uint8_t v_hasTrace_2324_; lean_object* v___x_2325_; 
lean_del_object(v___x_2264_);
v_options_2322_ = lean_ctor_get(v_a_1017_, 2);
v_inheritedTraceOptions_2323_ = lean_ctor_get(v_a_1017_, 13);
v_hasTrace_2324_ = lean_ctor_get_uint8(v_options_2322_, sizeof(void*)*1);
v___x_2325_ = lean_nat_add(v_n_1924_, v_one_1923_);
lean_dec(v_n_1924_);
if (v_hasTrace_2324_ == 0)
{
lean_dec(v_head_2261_);
v_n_1012_ = v___x_2325_;
v_curr_1013_ = v_tail_2262_;
goto _start;
}
else
{
lean_object* v___f_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___f_2327_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2327_, 0, v_head_2261_);
v___x_2328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1009_);
v___x_2330_ = l_Lean_Name_append(v___x_2329_, v_trace_1009_);
v___x_2331_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2323_, v_options_2322_, v___x_2330_);
lean_dec(v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2332_ = l_Lean_trace_profiler;
v___x_2333_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2322_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_dec_ref(v___f_2327_);
v_n_1012_ = v___x_2325_;
v_curr_1013_ = v_tail_2262_;
goto _start;
}
else
{
v___y_1058_ = v___x_2328_;
v___y_1059_ = v___f_2327_;
v___y_1060_ = v___x_2268_;
v___y_1061_ = v___x_2331_;
v___y_1062_ = v_tail_2262_;
v___y_1063_ = v___x_2325_;
v___y_1064_ = v_options_2322_;
goto v___jp_1057_;
}
}
else
{
v___y_1058_ = v___x_2328_;
v___y_1059_ = v___f_2327_;
v___y_1060_ = v___x_2268_;
v___y_1061_ = v___x_2331_;
v___y_1062_ = v_tail_2262_;
v___y_1063_ = v___x_2325_;
v___y_1064_ = v_options_2322_;
goto v___jp_1057_;
}
}
}
}
}
}
else
{
lean_object* v_val_2336_; 
lean_dec(v_curr_1013_);
v_val_2336_ = lean_ctor_get(v_a_2248_, 0);
lean_inc(v_val_2336_);
lean_dec_ref(v_a_2248_);
v_n_1012_ = v_n_1924_;
v_curr_1013_ = v_val_2336_;
goto _start;
}
}
v___jp_2338_:
{
if (lean_obj_tag(v___y_2339_) == 0)
{
lean_object* v_a_2340_; 
v_a_2340_ = lean_ctor_get(v___y_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___y_2339_);
v_a_2248_ = v_a_2340_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_n_1924_);
lean_dec(v_acc_1014_);
lean_dec(v_curr_1013_);
lean_dec(v_goals_1011_);
lean_dec_ref(v_next_1010_);
lean_dec(v_trace_1009_);
lean_dec_ref(v_cfg_1008_);
v_a_2341_ = lean_ctor_get(v___y_2339_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___y_2339_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___y_2339_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___y_2339_);
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
}
v___jp_1020_:
{
lean_object* v___x_1029_; double v___x_1030_; double v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1029_ = lean_io_get_num_heartbeats();
v___x_1030_ = lean_float_of_nat(v___y_1027_);
v___x_1031_ = lean_float_of_nat(v___x_1029_);
v___x_1032_ = lean_box_float(v___x_1030_);
v___x_1033_ = lean_box_float(v___x_1031_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_a_1028_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
lean_inc_ref(v___y_1022_);
v___x_1036_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1023_, v___y_1022_, v___y_1026_, v___y_1024_, v___y_1025_, v___y_1021_, v___x_1035_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1036_;
}
v___jp_1037_:
{
lean_object* v___x_1046_; double v___x_1047_; double v___x_1048_; double v___x_1049_; double v___x_1050_; double v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1046_ = lean_io_mono_nanos_now();
v___x_1047_ = lean_float_of_nat(v___y_1042_);
v___x_1048_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1049_ = lean_float_div(v___x_1047_, v___x_1048_);
v___x_1050_ = lean_float_of_nat(v___x_1046_);
v___x_1051_ = lean_float_div(v___x_1050_, v___x_1048_);
v___x_1052_ = lean_box_float(v___x_1049_);
v___x_1053_ = lean_box_float(v___x_1051_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1045_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
lean_inc_ref(v___y_1039_);
v___x_1056_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1040_, v___y_1039_, v___y_1044_, v___y_1041_, v___y_1043_, v___y_1038_, v___x_1055_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1056_;
}
v___jp_1057_:
{
lean_object* v___x_1065_; lean_object* v_a_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1065_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1018_);
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1068_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1064_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1009_);
v___x_1070_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1063_, v___y_1062_, v_acc_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set_tag(v___x_1073_, 1);
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
v___y_1038_ = v___y_1059_;
v___y_1039_ = v___y_1058_;
v___y_1040_ = v___y_1060_;
v___y_1041_ = v___y_1061_;
v___y_1042_ = v___x_1069_;
v___y_1043_ = v_a_1066_;
v___y_1044_ = v___y_1064_;
v_a_1045_ = v___x_1076_;
goto v___jp_1037_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1070_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1070_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set_tag(v___x_1081_, 0);
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
v___y_1038_ = v___y_1059_;
v___y_1039_ = v___y_1058_;
v___y_1040_ = v___y_1060_;
v___y_1041_ = v___y_1061_;
v___y_1042_ = v___x_1069_;
v___y_1043_ = v_a_1066_;
v___y_1044_ = v___y_1064_;
v_a_1045_ = v___x_1084_;
goto v___jp_1037_;
}
}
}
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1009_);
v___x_1088_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1008_, v_trace_1009_, v_next_1010_, v_goals_1011_, v___y_1063_, v___y_1062_, v_acc_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 1);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
v___y_1021_ = v___y_1059_;
v___y_1022_ = v___y_1058_;
v___y_1023_ = v___y_1060_;
v___y_1024_ = v___y_1061_;
v___y_1025_ = v_a_1066_;
v___y_1026_ = v___y_1064_;
v___y_1027_ = v___x_1087_;
v_a_1028_ = v___x_1094_;
goto v___jp_1020_;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
v_a_1097_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1088_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1088_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set_tag(v___x_1099_, 0);
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
v___y_1021_ = v___y_1059_;
v___y_1022_ = v___y_1058_;
v___y_1023_ = v___y_1060_;
v___y_1024_ = v___y_1061_;
v___y_1025_ = v_a_1066_;
v___y_1026_ = v___y_1064_;
v___y_1027_ = v___x_1087_;
v_a_1028_ = v___x_1102_;
goto v___jp_1020_;
}
}
}
}
}
v___jp_1105_:
{
lean_object* v___x_1114_; double v___x_1115_; double v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1114_ = lean_io_get_num_heartbeats();
v___x_1115_ = lean_float_of_nat(v___y_1111_);
v___x_1116_ = lean_float_of_nat(v___x_1114_);
v___x_1117_ = lean_box_float(v___x_1115_);
v___x_1118_ = lean_box_float(v___x_1116_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v_a_1113_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
lean_inc_ref(v___y_1110_);
v___x_1121_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1106_, v___y_1110_, v___y_1109_, v___y_1107_, v___y_1112_, v___y_1108_, v___x_1120_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1121_;
}
v___jp_1122_:
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1131_, 0, v_a_1130_);
v___y_1106_ = v___y_1123_;
v___y_1107_ = v___y_1124_;
v___y_1108_ = v___y_1126_;
v___y_1109_ = v___y_1125_;
v___y_1110_ = v___y_1127_;
v___y_1111_ = v___y_1128_;
v___y_1112_ = v___y_1129_;
v_a_1113_ = v___x_1131_;
goto v___jp_1105_;
}
v___jp_1132_:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_a_1140_);
v___y_1106_ = v___y_1133_;
v___y_1107_ = v___y_1134_;
v___y_1108_ = v___y_1136_;
v___y_1109_ = v___y_1135_;
v___y_1110_ = v___y_1137_;
v___y_1111_ = v___y_1138_;
v___y_1112_ = v___y_1139_;
v_a_1113_ = v___x_1141_;
goto v___jp_1105_;
}
v___jp_1142_:
{
if (lean_obj_tag(v___y_1150_) == 0)
{
lean_object* v_a_1151_; 
v_a_1151_ = lean_ctor_get(v___y_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___y_1150_);
v___y_1123_ = v___y_1143_;
v___y_1124_ = v___y_1144_;
v___y_1125_ = v___y_1146_;
v___y_1126_ = v___y_1145_;
v___y_1127_ = v___y_1147_;
v___y_1128_ = v___y_1148_;
v___y_1129_ = v___y_1149_;
v_a_1130_ = v_a_1151_;
goto v___jp_1122_;
}
else
{
lean_object* v_a_1152_; 
v_a_1152_ = lean_ctor_get(v___y_1150_, 0);
lean_inc(v_a_1152_);
lean_dec_ref(v___y_1150_);
v___y_1133_ = v___y_1143_;
v___y_1134_ = v___y_1144_;
v___y_1135_ = v___y_1146_;
v___y_1136_ = v___y_1145_;
v___y_1137_ = v___y_1147_;
v___y_1138_ = v___y_1148_;
v___y_1139_ = v___y_1149_;
v_a_1140_ = v_a_1152_;
goto v___jp_1132_;
}
}
v___jp_1153_:
{
lean_object* v___x_1162_; double v___x_1163_; double v___x_1164_; double v___x_1165_; double v___x_1166_; double v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1162_ = lean_io_mono_nanos_now();
v___x_1163_ = lean_float_of_nat(v___y_1159_);
v___x_1164_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1165_ = lean_float_div(v___x_1163_, v___x_1164_);
v___x_1166_ = lean_float_of_nat(v___x_1162_);
v___x_1167_ = lean_float_div(v___x_1166_, v___x_1164_);
v___x_1168_ = lean_box_float(v___x_1165_);
v___x_1169_ = lean_box_float(v___x_1167_);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_a_1161_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
lean_inc_ref(v___y_1158_);
v___x_1172_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1009_, v___y_1154_, v___y_1158_, v___y_1157_, v___y_1155_, v___y_1160_, v___y_1156_, v___x_1171_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
return v___x_1172_;
}
v___jp_1173_:
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_a_1181_);
v___y_1154_ = v___y_1174_;
v___y_1155_ = v___y_1175_;
v___y_1156_ = v___y_1177_;
v___y_1157_ = v___y_1176_;
v___y_1158_ = v___y_1179_;
v___y_1159_ = v___y_1178_;
v___y_1160_ = v___y_1180_;
v_a_1161_ = v___x_1182_;
goto v___jp_1153_;
}
v___jp_1183_:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v_a_1191_);
v___y_1154_ = v___y_1184_;
v___y_1155_ = v___y_1185_;
v___y_1156_ = v___y_1187_;
v___y_1157_ = v___y_1186_;
v___y_1158_ = v___y_1189_;
v___y_1159_ = v___y_1188_;
v___y_1160_ = v___y_1190_;
v_a_1161_ = v___x_1192_;
goto v___jp_1153_;
}
v___jp_1193_:
{
if (lean_obj_tag(v___y_1201_) == 0)
{
lean_object* v_a_1202_; 
v_a_1202_ = lean_ctor_get(v___y_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref(v___y_1201_);
v___y_1174_ = v___y_1194_;
v___y_1175_ = v___y_1195_;
v___y_1176_ = v___y_1197_;
v___y_1177_ = v___y_1196_;
v___y_1178_ = v___y_1199_;
v___y_1179_ = v___y_1198_;
v___y_1180_ = v___y_1200_;
v_a_1181_ = v_a_1202_;
goto v___jp_1173_;
}
else
{
lean_object* v_a_1203_; 
v_a_1203_ = lean_ctor_get(v___y_1201_, 0);
lean_inc(v_a_1203_);
lean_dec_ref(v___y_1201_);
v___y_1184_ = v___y_1194_;
v___y_1185_ = v___y_1195_;
v___y_1186_ = v___y_1197_;
v___y_1187_ = v___y_1196_;
v___y_1188_ = v___y_1199_;
v___y_1189_ = v___y_1198_;
v___y_1190_ = v___y_1200_;
v_a_1191_ = v_a_1203_;
goto v___jp_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2419_, lean_object* v_trace_2420_, lean_object* v_next_2421_, lean_object* v_goals_2422_, lean_object* v_n_2423_, lean_object* v_curr_2424_, lean_object* v_acc_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2419_, v_trace_2420_, v_next_2421_, v_goals_2422_, v_n_2423_, v_curr_2424_, v_acc_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object* v_tail_2432_, lean_object* v_cfg_2433_, lean_object* v_trace_2434_, lean_object* v_next_2435_, lean_object* v_goals_2436_, lean_object* v_n_2437_, lean_object* v_acc_2438_, lean_object* v_r_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = l_List_appendTR___redArg(v_r_2439_, v_tail_2432_);
v___x_2446_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2446_, 0, v_cfg_2433_);
lean_closure_set(v___x_2446_, 1, v_trace_2434_);
lean_closure_set(v___x_2446_, 2, v_next_2435_);
lean_closure_set(v___x_2446_, 3, v_goals_2436_);
lean_closure_set(v___x_2446_, 4, v_n_2437_);
lean_closure_set(v___x_2446_, 5, v___x_2445_);
lean_closure_set(v___x_2446_, 6, v_acc_2438_);
v___x_2447_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v___x_2446_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2448_, lean_object* v_msg_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2456_, lean_object* v_msg_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2456_, v_msg_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_00_u03b1_2464_, lean_object* v_x_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_x_2465_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2472_, lean_object* v_x_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_00_u03b1_2472_, v_x_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* v_mvarId_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_2480_, v___y_2482_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* v_mvarId_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_mvarId_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v_mvarId_2487_);
return v_res_2493_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_object* v_00_u03b2_2494_, lean_object* v_x_2495_, lean_object* v_x_2496_){
_start:
{
uint8_t v___x_2497_; 
v___x_2497_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_2495_, v_x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2498_, lean_object* v_x_2499_, lean_object* v_x_2500_){
_start:
{
uint8_t v_res_2501_; lean_object* v_r_2502_; 
v_res_2501_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(v_00_u03b2_2498_, v_x_2499_, v_x_2500_);
lean_dec(v_x_2500_);
lean_dec_ref(v_x_2499_);
v_r_2502_ = lean_box(v_res_2501_);
return v_r_2502_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_2503_, lean_object* v_x_2504_, size_t v_x_2505_, lean_object* v_x_2506_){
_start:
{
uint8_t v___x_2507_; 
v___x_2507_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_2504_, v_x_2505_, v_x_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___boxed(lean_object* v_00_u03b2_2508_, lean_object* v_x_2509_, lean_object* v_x_2510_, lean_object* v_x_2511_){
_start:
{
size_t v_x_85549__boxed_2512_; uint8_t v_res_2513_; lean_object* v_r_2514_; 
v_x_85549__boxed_2512_ = lean_unbox_usize(v_x_2510_);
lean_dec(v_x_2510_);
v_res_2513_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2508_, v_x_2509_, v_x_85549__boxed_2512_, v_x_2511_);
lean_dec(v_x_2511_);
lean_dec_ref(v_x_2509_);
v_r_2514_ = lean_box(v_res_2513_);
return v_r_2514_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_object* v_00_u03b2_2515_, lean_object* v_keys_2516_, lean_object* v_vals_2517_, lean_object* v_heq_2518_, lean_object* v_i_2519_, lean_object* v_k_2520_){
_start:
{
uint8_t v___x_2521_; 
v___x_2521_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_2516_, v_i_2519_, v_k_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2522_, lean_object* v_keys_2523_, lean_object* v_vals_2524_, lean_object* v_heq_2525_, lean_object* v_i_2526_, lean_object* v_k_2527_){
_start:
{
uint8_t v_res_2528_; lean_object* v_r_2529_; 
v_res_2528_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(v_00_u03b2_2522_, v_keys_2523_, v_vals_2524_, v_heq_2525_, v_i_2526_, v_k_2527_);
lean_dec(v_k_2527_);
lean_dec_ref(v_vals_2524_);
lean_dec_ref(v_keys_2523_);
v_r_2529_ = lean_box(v_res_2528_);
return v_r_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2530_, lean_object* v_h__1_2531_, lean_object* v_h__2_2532_){
_start:
{
lean_object* v_zero_2533_; uint8_t v_isZero_2534_; 
v_zero_2533_ = lean_unsigned_to_nat(0u);
v_isZero_2534_ = lean_nat_dec_eq(v_n_2530_, v_zero_2533_);
if (v_isZero_2534_ == 1)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec(v_h__2_2532_);
v___x_2535_ = lean_box(0);
v___x_2536_ = lean_apply_1(v_h__1_2531_, v___x_2535_);
return v___x_2536_;
}
else
{
lean_object* v_one_2537_; lean_object* v_n_2538_; lean_object* v___x_2539_; 
lean_dec(v_h__1_2531_);
v_one_2537_ = lean_unsigned_to_nat(1u);
v_n_2538_ = lean_nat_sub(v_n_2530_, v_one_2537_);
v___x_2539_ = lean_apply_1(v_h__2_2532_, v_n_2538_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2540_, lean_object* v_h__1_2541_, lean_object* v_h__2_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2540_, v_h__1_2541_, v_h__2_2542_);
lean_dec(v_n_2540_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2544_, lean_object* v_n_2545_, lean_object* v_h__1_2546_, lean_object* v_h__2_2547_){
_start:
{
lean_object* v_zero_2548_; uint8_t v_isZero_2549_; 
v_zero_2548_ = lean_unsigned_to_nat(0u);
v_isZero_2549_ = lean_nat_dec_eq(v_n_2545_, v_zero_2548_);
if (v_isZero_2549_ == 1)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec(v_h__2_2547_);
v___x_2550_ = lean_box(0);
v___x_2551_ = lean_apply_1(v_h__1_2546_, v___x_2550_);
return v___x_2551_;
}
else
{
lean_object* v_one_2552_; lean_object* v_n_2553_; lean_object* v___x_2554_; 
lean_dec(v_h__1_2546_);
v_one_2552_ = lean_unsigned_to_nat(1u);
v_n_2553_ = lean_nat_sub(v_n_2545_, v_one_2552_);
v___x_2554_ = lean_apply_1(v_h__2_2547_, v_n_2553_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* v_motive_2555_, lean_object* v_n_2556_, lean_object* v_h__1_2557_, lean_object* v_h__2_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(v_motive_2555_, v_n_2556_, v_h__1_2557_, v_h__2_2558_);
lean_dec(v_n_2556_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* v_procResult_x3f_2560_, lean_object* v_h__1_2561_, lean_object* v_h__2_2562_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2560_) == 0)
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
lean_dec(v_h__1_2561_);
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_apply_1(v_h__2_2562_, v___x_2563_);
return v___x_2564_;
}
else
{
lean_object* v_val_2565_; lean_object* v___x_2566_; 
lean_dec(v_h__2_2562_);
v_val_2565_ = lean_ctor_get(v_procResult_x3f_2560_, 0);
lean_inc(v_val_2565_);
lean_dec_ref(v_procResult_x3f_2560_);
v___x_2566_ = lean_apply_1(v_h__1_2561_, v_val_2565_);
return v___x_2566_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* v_motive_2567_, lean_object* v_procResult_x3f_2568_, lean_object* v_h__1_2569_, lean_object* v_h__2_2570_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2568_) == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec(v_h__1_2569_);
v___x_2571_ = lean_box(0);
v___x_2572_ = lean_apply_1(v_h__2_2570_, v___x_2571_);
return v___x_2572_;
}
else
{
lean_object* v_val_2573_; lean_object* v___x_2574_; 
lean_dec(v_h__2_2570_);
v_val_2573_ = lean_ctor_get(v_procResult_x3f_2568_, 0);
lean_inc(v_val_2573_);
lean_dec_ref(v_procResult_x3f_2568_);
v___x_2574_ = lean_apply_1(v_h__1_2569_, v_val_2573_);
return v___x_2574_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2575_, lean_object* v_h__1_2576_, lean_object* v_h__2_2577_){
_start:
{
if (lean_obj_tag(v_curr_2575_) == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_dec(v_h__2_2577_);
v___x_2578_ = lean_box(0);
v___x_2579_ = lean_apply_1(v_h__1_2576_, v___x_2578_);
return v___x_2579_;
}
else
{
lean_object* v_head_2580_; lean_object* v_tail_2581_; lean_object* v___x_2582_; 
lean_dec(v_h__1_2576_);
v_head_2580_ = lean_ctor_get(v_curr_2575_, 0);
lean_inc(v_head_2580_);
v_tail_2581_ = lean_ctor_get(v_curr_2575_, 1);
lean_inc(v_tail_2581_);
lean_dec_ref(v_curr_2575_);
v___x_2582_ = lean_apply_2(v_h__2_2577_, v_head_2580_, v_tail_2581_);
return v___x_2582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2583_, lean_object* v_curr_2584_, lean_object* v_h__1_2585_, lean_object* v_h__2_2586_){
_start:
{
if (lean_obj_tag(v_curr_2584_) == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_dec(v_h__2_2586_);
v___x_2587_ = lean_box(0);
v___x_2588_ = lean_apply_1(v_h__1_2585_, v___x_2587_);
return v___x_2588_;
}
else
{
lean_object* v_head_2589_; lean_object* v_tail_2590_; lean_object* v___x_2591_; 
lean_dec(v_h__1_2585_);
v_head_2589_ = lean_ctor_get(v_curr_2584_, 0);
lean_inc(v_head_2589_);
v_tail_2590_ = lean_ctor_get(v_curr_2584_, 1);
lean_inc(v_tail_2590_);
lean_dec_ref(v_curr_2584_);
v___x_2591_ = lean_apply_2(v_h__2_2586_, v_head_2589_, v_tail_2590_);
return v___x_2591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2592_, lean_object* v_h__1_2593_, lean_object* v_h__2_2594_){
_start:
{
if (lean_obj_tag(v_____do__lift_2592_) == 0)
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
lean_dec(v_h__2_2594_);
v___x_2595_ = lean_box(0);
v___x_2596_ = lean_apply_1(v_h__1_2593_, v___x_2595_);
return v___x_2596_;
}
else
{
lean_object* v_val_2597_; lean_object* v___x_2598_; 
lean_dec(v_h__1_2593_);
v_val_2597_ = lean_ctor_get(v_____do__lift_2592_, 0);
lean_inc(v_val_2597_);
lean_dec_ref(v_____do__lift_2592_);
v___x_2598_ = lean_apply_1(v_h__2_2594_, v_val_2597_);
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_2599_, lean_object* v_____do__lift_2600_, lean_object* v_h__1_2601_, lean_object* v_h__2_2602_){
_start:
{
if (lean_obj_tag(v_____do__lift_2600_) == 0)
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec(v_h__2_2602_);
v___x_2603_ = lean_box(0);
v___x_2604_ = lean_apply_1(v_h__1_2601_, v___x_2603_);
return v___x_2604_;
}
else
{
lean_object* v_val_2605_; lean_object* v___x_2606_; 
lean_dec(v_h__1_2601_);
v_val_2605_ = lean_ctor_get(v_____do__lift_2600_, 0);
lean_inc(v_val_2605_);
lean_dec_ref(v_____do__lift_2600_);
v___x_2606_ = lean_apply_1(v_h__2_2602_, v_val_2605_);
return v___x_2606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_2607_, lean_object* v_trace_2608_, lean_object* v_next_2609_, lean_object* v_orig_2610_, lean_object* v_g_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_maxDepth_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v_maxDepth_2617_ = lean_ctor_get(v_cfg_2607_, 0);
lean_inc(v_maxDepth_2617_);
v___x_2618_ = lean_box(0);
v___x_2619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2619_, 0, v_g_2611_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2607_, v_trace_2608_, v_next_2609_, v_orig_2610_, v_maxDepth_2617_, v___x_2619_, v___x_2618_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_2621_, lean_object* v_trace_2622_, lean_object* v_next_2623_, lean_object* v_orig_2624_, lean_object* v_g_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2621_, v_trace_2622_, v_next_2623_, v_orig_2624_, v_g_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
if (lean_obj_tag(v_a_2632_) == 0)
{
lean_object* v___x_2634_; 
v___x_2634_ = l_List_reverse___redArg(v_a_2633_);
return v___x_2634_;
}
else
{
lean_object* v_head_2635_; lean_object* v_tail_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2645_; 
v_head_2635_ = lean_ctor_get(v_a_2632_, 0);
v_tail_2636_ = lean_ctor_get(v_a_2632_, 1);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_a_2632_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2638_ = v_a_2632_;
v_isShared_2639_ = v_isSharedCheck_2645_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_tail_2636_);
lean_inc(v_head_2635_);
lean_dec(v_a_2632_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2645_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
v___x_2640_ = l_Lean_MessageData_ofFormat(v_head_2635_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 1, v_a_2633_);
lean_ctor_set(v___x_2638_, 0, v___x_2640_);
v___x_2642_ = v___x_2638_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_a_2633_);
v___x_2642_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
v_a_2632_ = v_tail_2636_;
v_a_2633_ = v___x_2642_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_2648_ = l_Lean_stringToMessageData(v___x_2647_);
return v___x_2648_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_2651_ = l_Lean_stringToMessageData(v___x_2650_);
return v___x_2651_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_2654_ = l_Lean_stringToMessageData(v___x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_2655_, lean_object* v_snd_2656_, lean_object* v_x_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2655_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2665_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref(v___x_2663_);
v___x_2665_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_2656_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2685_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2685_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2685_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_2671_ = lean_box(0);
v___x_2672_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2664_, v___x_2671_);
v___x_2673_ = l_Lean_MessageData_ofList(v___x_2672_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2670_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_2678_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2666_, v___x_2671_);
v___x_2679_ = l_Lean_MessageData_ofList(v___x_2678_);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2677_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2676_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2681_);
v___x_2683_ = v___x_2668_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec(v_a_2664_);
v_a_2686_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2665_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2665_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v_snd_2656_);
v_a_2694_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2663_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2663_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_2702_, lean_object* v_snd_2703_, lean_object* v_x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2702_, v_snd_2703_, v_x_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec_ref(v_x_2704_);
return v_res_2710_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_2713_ = l_Lean_stringToMessageData(v___x_2712_);
return v___x_2713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_2716_ = l_Lean_stringToMessageData(v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_2717_, lean_object* v___x_2718_, lean_object* v_x_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
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
v___x_2727_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_2718_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2745_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2745_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2745_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_2733_ = lean_box(0);
v___x_2734_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2726_, v___x_2733_);
v___x_2735_ = l_Lean_MessageData_ofList(v___x_2734_);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2732_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2728_, v___x_2733_);
v___x_2740_ = l_Lean_MessageData_ofList(v___x_2739_);
v___x_2741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2738_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2741_);
v___x_2743_ = v___x_2730_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec(v_a_2726_);
v_a_2746_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2727_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2727_);
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
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v___x_2718_);
v_a_2754_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2725_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2725_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_2762_, lean_object* v___x_2763_, lean_object* v_x_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2762_, v___x_2763_, v_x_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec_ref(v_x_2764_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t v___x_2771_, lean_object* v_x_2772_, lean_object* v_x_2773_, lean_object* v___y_2774_){
_start:
{
if (lean_obj_tag(v_x_2772_) == 0)
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2776_, 0, v_x_2773_);
return v___x_2776_;
}
else
{
lean_object* v_head_2777_; lean_object* v_tail_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2793_; 
v_head_2777_ = lean_ctor_get(v_x_2772_, 0);
v_tail_2778_ = lean_ctor_get(v_x_2772_, 1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_x_2772_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2780_ = v_x_2772_;
v_isShared_2781_ = v_isSharedCheck_2793_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_tail_2778_);
lean_inc(v_head_2777_);
lean_dec(v_x_2772_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2793_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
uint8_t v_a_2788_; lean_object* v___x_2790_; lean_object* v_a_2791_; uint8_t v___x_2792_; 
v___x_2790_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2777_, v___y_2774_);
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
lean_dec_ref(v___x_2790_);
v___x_2792_ = lean_unbox(v_a_2791_);
lean_dec(v_a_2791_);
if (v___x_2792_ == 0)
{
goto v___jp_2782_;
}
else
{
v_a_2788_ = v___x_2771_;
goto v___jp_2787_;
}
v___jp_2782_:
{
lean_object* v___x_2784_; 
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 1, v_x_2773_);
v___x_2784_ = v___x_2780_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_head_2777_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_x_2773_);
v___x_2784_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
v_x_2772_ = v_tail_2778_;
v_x_2773_ = v___x_2784_;
goto _start;
}
}
v___jp_2787_:
{
if (v_a_2788_ == 0)
{
lean_del_object(v___x_2780_);
lean_dec(v_head_2777_);
v_x_2772_ = v_tail_2778_;
goto _start;
}
else
{
goto v___jp_2782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v___x_2794_, lean_object* v_x_2795_, lean_object* v_x_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
uint8_t v___x_57591__boxed_2799_; lean_object* v_res_2800_; 
v___x_57591__boxed_2799_ = lean_unbox(v___x_2794_);
v_res_2800_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_57591__boxed_2799_, v_x_2795_, v_x_2796_, v___y_2797_);
lean_dec(v___y_2797_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_2801_, lean_object* v_a_2802_){
_start:
{
if (lean_obj_tag(v_a_2801_) == 0)
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_array_to_list(v_a_2802_);
return v___x_2803_;
}
else
{
lean_object* v_head_2804_; lean_object* v_tail_2805_; lean_object* v___x_2806_; 
v_head_2804_ = lean_ctor_get(v_a_2801_, 0);
lean_inc(v_head_2804_);
v_tail_2805_ = lean_ctor_get(v_a_2801_, 1);
lean_inc(v_tail_2805_);
lean_dec_ref(v_a_2801_);
v___x_2806_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2802_, v_head_2804_);
v_a_2801_ = v_tail_2805_;
v_a_2802_ = v___x_2806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
if (lean_obj_tag(v_a_2809_) == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_dec(v_goals_2808_);
v___x_2817_ = lean_array_to_list(v_a_2810_);
v___x_2818_ = lean_array_to_list(v_a_2811_);
v___x_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
v___x_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
return v___x_2820_;
}
else
{
lean_object* v_head_2821_; lean_object* v_tail_2822_; lean_object* v___x_2823_; 
v_head_2821_ = lean_ctor_get(v_a_2809_, 0);
lean_inc_n(v_head_2821_, 2);
v_tail_2822_ = lean_ctor_get(v_a_2809_, 1);
lean_inc(v_tail_2822_);
lean_dec_ref(v_a_2809_);
lean_inc(v_goals_2808_);
v___x_2823_ = l_Lean_MVarId_isIndependentOf(v_goals_2808_, v_head_2821_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; uint8_t v___x_2825_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref(v___x_2823_);
v___x_2825_ = lean_unbox(v_a_2824_);
lean_dec(v_a_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; 
v___x_2826_ = lean_array_push(v_a_2811_, v_head_2821_);
v_a_2809_ = v_tail_2822_;
v_a_2811_ = v___x_2826_;
goto _start;
}
else
{
lean_object* v___x_2828_; 
v___x_2828_ = lean_array_push(v_a_2810_, v_head_2821_);
v_a_2809_ = v_tail_2822_;
v_a_2810_ = v___x_2828_;
goto _start;
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_tail_2822_);
lean_dec(v_head_2821_);
lean_dec_ref(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_goals_2808_);
v_a_2830_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2823_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2823_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
if (lean_obj_tag(v_a_2848_) == 0)
{
lean_object* v___x_2850_; 
v___x_2850_ = lean_array_to_list(v_a_2849_);
return v___x_2850_;
}
else
{
lean_object* v_head_2851_; 
v_head_2851_ = lean_ctor_get(v_a_2848_, 0);
if (lean_obj_tag(v_head_2851_) == 0)
{
lean_object* v_tail_2852_; lean_object* v_val_2853_; lean_object* v___x_2854_; 
lean_inc_ref(v_head_2851_);
v_tail_2852_ = lean_ctor_get(v_a_2848_, 1);
lean_inc(v_tail_2852_);
lean_dec_ref(v_a_2848_);
v_val_2853_ = lean_ctor_get(v_head_2851_, 0);
lean_inc(v_val_2853_);
lean_dec_ref(v_head_2851_);
v___x_2854_ = lean_array_push(v_a_2849_, v_val_2853_);
v_a_2848_ = v_tail_2852_;
v_a_2849_ = v___x_2854_;
goto _start;
}
else
{
lean_object* v_tail_2856_; 
v_tail_2856_ = lean_ctor_get(v_a_2848_, 1);
lean_inc(v_tail_2856_);
lean_dec_ref(v_a_2848_);
v_a_2848_ = v_tail_2856_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_2858_, lean_object* v_x_2859_, lean_object* v_x_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
if (lean_obj_tag(v_x_2859_) == 0)
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
lean_dec_ref(v_f_2858_);
v___x_2866_ = l_List_reverse___redArg(v_x_2860_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
return v___x_2867_;
}
else
{
lean_object* v_head_2868_; lean_object* v_tail_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2914_; 
v_head_2868_ = lean_ctor_get(v_x_2859_, 0);
v_tail_2869_ = lean_ctor_get(v_x_2859_, 1);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_x_2859_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2871_ = v_x_2859_;
v_isShared_2872_ = v_isSharedCheck_2914_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_tail_2869_);
lean_inc(v_head_2868_);
lean_dec(v_x_2859_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2914_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v_a_2874_; lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_Meta_saveState___redArg(v___y_2862_, v___y_2864_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref(v___x_2879_);
lean_inc_ref(v_f_2858_);
lean_inc(v___y_2864_);
lean_inc_ref(v___y_2863_);
lean_inc(v___y_2862_);
lean_inc_ref(v___y_2861_);
lean_inc(v_head_2868_);
v___x_2881_ = lean_apply_6(v_f_2858_, v_head_2868_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, lean_box(0));
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2883_; 
lean_dec(v_a_2880_);
lean_dec(v_head_2868_);
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref(v___x_2881_);
v___x_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2883_, 0, v_a_2882_);
v_a_2874_ = v___x_2883_;
goto v___jp_2873_;
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2905_; 
v_a_2884_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2886_ = v___x_2881_;
v_isShared_2887_ = v_isSharedCheck_2905_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2881_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2905_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
uint8_t v___y_2889_; uint8_t v___x_2903_; 
v___x_2903_ = l_Lean_Exception_isInterrupt(v_a_2884_);
if (v___x_2903_ == 0)
{
uint8_t v___x_2904_; 
lean_inc(v_a_2884_);
v___x_2904_ = l_Lean_Exception_isRuntime(v_a_2884_);
v___y_2889_ = v___x_2904_;
goto v___jp_2888_;
}
else
{
v___y_2889_ = v___x_2903_;
goto v___jp_2888_;
}
v___jp_2888_:
{
if (v___y_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_del_object(v___x_2886_);
lean_dec(v_a_2884_);
v___x_2890_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2880_, v___y_2862_, v___y_2864_);
lean_dec(v_a_2880_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v___x_2891_; 
lean_dec_ref(v___x_2890_);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v_head_2868_);
v_a_2874_ = v___x_2891_;
goto v___jp_2873_;
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_del_object(v___x_2871_);
lean_dec(v_tail_2869_);
lean_dec(v_head_2868_);
lean_dec(v_x_2860_);
lean_dec_ref(v_f_2858_);
v_a_2892_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2890_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2890_);
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
else
{
lean_object* v___x_2901_; 
lean_dec(v_a_2880_);
lean_del_object(v___x_2871_);
lean_dec(v_tail_2869_);
lean_dec(v_head_2868_);
lean_dec(v_x_2860_);
lean_dec_ref(v_f_2858_);
if (v_isShared_2887_ == 0)
{
v___x_2901_ = v___x_2886_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2884_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_del_object(v___x_2871_);
lean_dec(v_tail_2869_);
lean_dec(v_head_2868_);
lean_dec(v_x_2860_);
lean_dec_ref(v_f_2858_);
v_a_2906_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2879_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2879_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
v___jp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 1, v_x_2860_);
lean_ctor_set(v___x_2871_, 0, v_a_2874_);
v___x_2876_ = v___x_2871_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2874_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_x_2860_);
v___x_2876_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
v_x_2859_ = v_tail_2869_;
v_x_2860_ = v___x_2876_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_2915_, lean_object* v_x_2916_, lean_object* v_x_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2915_, v_x_2916_, v_x_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
if (lean_obj_tag(v_a_2924_) == 0)
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_array_to_list(v_a_2925_);
return v___x_2926_;
}
else
{
lean_object* v_head_2927_; 
v_head_2927_ = lean_ctor_get(v_a_2924_, 0);
if (lean_obj_tag(v_head_2927_) == 1)
{
lean_object* v_tail_2928_; lean_object* v_val_2929_; lean_object* v___x_2930_; 
lean_inc_ref(v_head_2927_);
v_tail_2928_ = lean_ctor_get(v_a_2924_, 1);
lean_inc(v_tail_2928_);
lean_dec_ref(v_a_2924_);
v_val_2929_ = lean_ctor_get(v_head_2927_, 0);
lean_inc(v_val_2929_);
lean_dec_ref(v_head_2927_);
v___x_2930_ = lean_array_push(v_a_2925_, v_val_2929_);
v_a_2924_ = v_tail_2928_;
v_a_2925_ = v___x_2930_;
goto _start;
}
else
{
lean_object* v_tail_2932_; 
v_tail_2932_ = lean_ctor_get(v_a_2924_, 1);
lean_inc(v_tail_2932_);
lean_dec_ref(v_a_2924_);
v_a_2924_ = v_tail_2932_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_2934_, lean_object* v_f_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_box(0);
v___x_2942_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2935_, v_L_2934_, v___x_2941_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2954_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2954_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2954_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2947_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_2943_);
v___x_2948_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_2943_, v___x_2947_);
v___x_2949_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_2943_, v___x_2947_);
v___x_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2948_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v___x_2950_);
v___x_2952_ = v___x_2945_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
v_a_2955_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2942_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2942_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* v_L_2963_, lean_object* v_f_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_2963_, v_f_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t v___x_2971_, uint8_t v___x_2972_, lean_object* v_x_2973_, lean_object* v_x_2974_, lean_object* v___y_2975_){
_start:
{
if (lean_obj_tag(v_x_2973_) == 0)
{
lean_object* v___x_2977_; 
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v_x_2974_);
return v___x_2977_;
}
else
{
lean_object* v_head_2978_; lean_object* v_tail_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2993_; 
v_head_2978_ = lean_ctor_get(v_x_2973_, 0);
v_tail_2979_ = lean_ctor_get(v_x_2973_, 1);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_x_2973_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2981_ = v_x_2973_;
v_isShared_2982_ = v_isSharedCheck_2993_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_tail_2979_);
lean_inc(v_head_2978_);
lean_dec(v_x_2973_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2993_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
uint8_t v_a_2984_; lean_object* v___x_2990_; lean_object* v_a_2991_; uint8_t v___x_2992_; 
v___x_2990_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2978_, v___y_2975_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref(v___x_2990_);
v___x_2992_ = lean_unbox(v_a_2991_);
lean_dec(v_a_2991_);
if (v___x_2992_ == 0)
{
v_a_2984_ = v___x_2971_;
goto v___jp_2983_;
}
else
{
v_a_2984_ = v___x_2972_;
goto v___jp_2983_;
}
v___jp_2983_:
{
if (v_a_2984_ == 0)
{
lean_del_object(v___x_2981_);
lean_dec(v_head_2978_);
v_x_2973_ = v_tail_2979_;
goto _start;
}
else
{
lean_object* v___x_2987_; 
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 1, v_x_2974_);
v___x_2987_ = v___x_2981_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_head_2978_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_x_2974_);
v___x_2987_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
v_x_2973_ = v_tail_2979_;
v_x_2974_ = v___x_2987_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* v___x_2994_, lean_object* v___x_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
uint8_t v___x_57945__boxed_3000_; uint8_t v___x_57946__boxed_3001_; lean_object* v_res_3002_; 
v___x_57945__boxed_3000_ = lean_unbox(v___x_2994_);
v___x_57946__boxed_3001_ = lean_unbox(v___x_2995_);
v_res_3002_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_57945__boxed_3000_, v___x_57946__boxed_3001_, v_x_2996_, v_x_2997_, v___y_2998_);
lean_dec(v___y_2998_);
return v_res_3002_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1(void){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
v___x_3005_ = l_Lean_stringToMessageData(v___x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_3008_, lean_object* v_trace_3009_, lean_object* v_next_3010_, lean_object* v_orig_3011_, lean_object* v_goals_3012_, lean_object* v_remaining_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2));
lean_inc(v_remaining_3013_);
lean_inc(v_goals_3012_);
v___x_3023_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_3012_, v_remaining_3013_, v___x_3022_, v___x_3022_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v_fst_3025_; lean_object* v_snd_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_4234_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref(v___x_3023_);
v_fst_3025_ = lean_ctor_get(v_a_3024_, 0);
v_snd_3026_ = lean_ctor_get(v_a_3024_, 1);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_a_3024_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_3028_ = v_a_3024_;
v_isShared_3029_ = v_isSharedCheck_4234_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_snd_3026_);
lean_inc(v_fst_3025_);
lean_dec(v_a_3024_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_4234_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
uint8_t v___x_3030_; 
v___x_3030_ = l_List_isEmpty___redArg(v_fst_3025_);
if (v___x_3030_ == 0)
{
lean_object* v_options_3031_; lean_object* v_inheritedTraceOptions_3032_; uint8_t v_hasTrace_3033_; lean_object* v___f_3034_; 
lean_dec(v_remaining_3013_);
v_options_3031_ = lean_ctor_get(v_a_3016_, 2);
v_inheritedTraceOptions_3032_ = lean_ctor_get(v_a_3016_, 13);
v_hasTrace_3033_ = lean_ctor_get_uint8(v_options_3031_, sizeof(void*)*1);
lean_inc(v_orig_3011_);
lean_inc_ref(v_next_3010_);
lean_inc(v_trace_3009_);
lean_inc_ref(v_cfg_3008_);
v___f_3034_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3034_, 0, v_cfg_3008_);
lean_closure_set(v___f_3034_, 1, v_trace_3009_);
lean_closure_set(v___f_3034_, 2, v_next_3010_);
lean_closure_set(v___f_3034_, 3, v_orig_3011_);
if (v_hasTrace_3033_ == 0)
{
lean_object* v___x_3035_; 
lean_del_object(v___x_3028_);
v___x_3035_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3025_, v___f_3034_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3105_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3105_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3105_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v_fst_3040_; lean_object* v_snd_3041_; lean_object* v___x_3042_; lean_object* v_a_3044_; lean_object* v___y_3051_; lean_object* v___y_3054_; lean_object* v___y_3055_; uint8_t v___y_3056_; lean_object* v___y_3067_; lean_object* v_a_3082_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v_fst_3040_ = lean_ctor_get(v_a_3036_, 0);
lean_inc(v_fst_3040_);
v_snd_3041_ = lean_ctor_get(v_a_3036_, 1);
lean_inc(v_snd_3041_);
lean_dec(v_a_3036_);
v___x_3042_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3041_, v___x_3022_);
v___x_3100_ = lean_box(0);
v___x_3101_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_hasTrace_3033_, v_goals_3012_, v___x_3100_, v_a_3015_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref(v___x_3101_);
v___x_3103_ = l_List_reverse___redArg(v_a_3102_);
v_a_3082_ = v___x_3103_;
goto v___jp_3081_;
}
else
{
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3104_; 
v_a_3104_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3104_);
lean_dec_ref(v___x_3101_);
v_a_3082_ = v_a_3104_;
goto v___jp_3081_;
}
else
{
lean_dec(v___x_3042_);
lean_dec(v_fst_3040_);
lean_del_object(v___x_3038_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
return v___x_3101_;
}
}
v___jp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3045_ = l_List_appendTR___redArg(v___x_3042_, v_fst_3040_);
v___x_3046_ = l_List_appendTR___redArg(v___x_3045_, v_a_3044_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3046_);
v___x_3048_ = v___x_3038_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
v___jp_3050_:
{
if (lean_obj_tag(v___y_3051_) == 0)
{
lean_object* v_a_3052_; 
v_a_3052_ = lean_ctor_get(v___y_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref(v___y_3051_);
v_a_3044_ = v_a_3052_;
goto v___jp_3043_;
}
else
{
lean_dec(v___x_3042_);
lean_dec(v_fst_3040_);
lean_del_object(v___x_3038_);
return v___y_3051_;
}
}
v___jp_3053_:
{
if (v___y_3056_ == 0)
{
lean_object* v___x_3057_; 
lean_dec_ref(v___y_3054_);
v___x_3057_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3055_, v_a_3015_, v_a_3017_);
lean_dec_ref(v___y_3055_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_dec_ref(v___x_3057_);
v_a_3044_ = v_snd_3026_;
goto v___jp_3043_;
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec(v___x_3042_);
lean_dec(v_fst_3040_);
lean_del_object(v___x_3038_);
lean_dec(v_snd_3026_);
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
lean_dec_ref(v___y_3055_);
lean_dec(v_snd_3026_);
v___y_3051_ = v___y_3054_;
goto v___jp_3050_;
}
}
v___jp_3066_:
{
uint8_t v___x_3068_; 
v___x_3068_ = l_List_isEmpty___redArg(v_fst_3040_);
lean_dec(v_fst_3040_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_dec(v___y_3067_);
lean_dec(v___x_3042_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
v___x_3069_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3070_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3069_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
return v___x_3070_;
}
else
{
lean_object* v___x_3071_; 
v___x_3071_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3067_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3080_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3074_ = v___x_3071_;
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3071_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = l_List_appendTR___redArg(v___x_3042_, v_a_3072_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 0, v___x_3076_);
v___x_3078_ = v___x_3074_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
else
{
lean_dec(v___x_3042_);
return v___x_3071_;
}
}
}
v___jp_3081_:
{
uint8_t v_commitIndependentGoals_3083_; lean_object* v___x_3084_; 
v_commitIndependentGoals_3083_ = lean_ctor_get_uint8(v_cfg_3008_, sizeof(void*)*4);
lean_inc(v___x_3042_);
v___x_3084_ = l_List_appendTR___redArg(v_a_3082_, v___x_3042_);
if (v_commitIndependentGoals_3083_ == 0)
{
lean_del_object(v___x_3038_);
v___y_3067_ = v___x_3084_;
goto v___jp_3066_;
}
else
{
uint8_t v___x_3085_; 
v___x_3085_ = l_List_isEmpty___redArg(v___x_3042_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; 
v___x_3086_ = l_Lean_Meta_saveState___redArg(v_a_3015_, v_a_3017_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3088_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref(v___x_3086_);
lean_inc(v_snd_3026_);
v___x_3088_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___x_3084_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_dec(v_a_3087_);
lean_dec(v_snd_3026_);
v___y_3051_ = v___x_3088_;
goto v___jp_3050_;
}
else
{
lean_object* v_a_3089_; uint8_t v___x_3090_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
v___x_3090_ = l_Lean_Exception_isInterrupt(v_a_3089_);
if (v___x_3090_ == 0)
{
uint8_t v___x_3091_; 
v___x_3091_ = l_Lean_Exception_isRuntime(v_a_3089_);
v___y_3054_ = v___x_3088_;
v___y_3055_ = v_a_3087_;
v___y_3056_ = v___x_3091_;
goto v___jp_3053_;
}
else
{
lean_dec(v_a_3089_);
v___y_3054_ = v___x_3088_;
v___y_3055_ = v_a_3087_;
v___y_3056_ = v___x_3090_;
goto v___jp_3053_;
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v___x_3084_);
lean_dec(v___x_3042_);
lean_dec(v_fst_3040_);
lean_del_object(v___x_3038_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
v_a_3092_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3086_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3086_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
lean_del_object(v___x_3038_);
v___y_3067_ = v___x_3084_;
goto v___jp_3066_;
}
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v_snd_3026_);
lean_dec(v_goals_3012_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
v_a_3106_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3035_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3035_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v___f_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v_a_3122_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v_a_3139_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v_a_3146_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v_a_3152_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; uint8_t v___y_3169_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; uint8_t v___y_3196_; lean_object* v___y_3197_; lean_object* v_a_3198_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; uint8_t v___y_3215_; lean_object* v___y_3216_; lean_object* v_a_3217_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; uint8_t v___y_3224_; lean_object* v___y_3225_; lean_object* v_a_3226_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; uint8_t v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v_a_3237_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; uint8_t v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; uint8_t v___y_3263_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; uint8_t v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; uint8_t v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; uint8_t v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; uint8_t v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; uint8_t v___y_3312_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; uint8_t v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; uint8_t v___y_3326_; lean_object* v_a_3327_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; uint8_t v___y_3336_; lean_object* v___y_3337_; lean_object* v_a_3338_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; uint8_t v___y_3352_; lean_object* v___y_3353_; lean_object* v_a_3354_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; uint8_t v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v_a_3365_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; uint8_t v___y_3373_; lean_object* v___y_3374_; lean_object* v_a_3375_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; uint8_t v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; uint8_t v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; uint8_t v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; uint8_t v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; uint8_t v___y_3422_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; uint8_t v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; uint8_t v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; uint8_t v___y_3451_; lean_object* v_a_3452_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; uint8_t v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; uint8_t v___y_3466_; lean_object* v___y_3484_; lean_object* v___y_3485_; uint8_t v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; uint8_t v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v_a_3505_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v_a_3512_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v_a_3524_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v_a_3529_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3538_; uint8_t v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v_a_3544_; uint8_t v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v_a_3563_; uint8_t v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v_a_3572_; lean_object* v___y_3575_; uint8_t v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v_a_3583_; uint8_t v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; uint8_t v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; uint8_t v___y_3609_; lean_object* v___y_3613_; uint8_t v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3630_; uint8_t v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; uint8_t v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3649_; uint8_t v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; uint8_t v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3664_; uint8_t v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; uint8_t v___y_3671_; lean_object* v___y_3672_; lean_object* v_a_3673_; lean_object* v___y_3678_; uint8_t v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v_a_3684_; uint8_t v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v_a_3700_; uint8_t v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v_a_3709_; lean_object* v___y_3712_; uint8_t v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v_a_3720_; uint8_t v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; uint8_t v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; uint8_t v___y_3746_; lean_object* v___y_3750_; uint8_t v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3767_; uint8_t v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3777_; uint8_t v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; uint8_t v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; uint8_t v___y_3798_; uint8_t v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; uint8_t v___y_3810_; lean_object* v___y_3811_; lean_object* v_a_3812_; uint8_t v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; uint8_t v___y_3824_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; uint8_t v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v_a_3862_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; uint8_t v___y_3880_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3897_; lean_object* v___y_3898_; uint8_t v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v_a_3902_; 
lean_inc(v_snd_3026_);
lean_inc(v_fst_3025_);
v___f_3114_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3114_, 0, v_fst_3025_);
lean_closure_set(v___f_3114_, 1, v_snd_3026_);
v___x_3115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_3116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_3009_);
v___x_3117_ = l_Lean_Name_append(v___x_3116_, v_trace_3009_);
v___x_3118_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3032_, v_options_3031_, v___x_3117_);
lean_dec(v___x_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3951_; uint8_t v___x_3952_; 
v___x_3951_ = l_Lean_trace_profiler;
v___x_3952_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3031_, v___x_3951_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3953_; 
lean_dec_ref(v___f_3114_);
lean_del_object(v___x_3028_);
v___x_3953_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3025_, v___f_3034_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_4222_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_3956_ = v___x_3953_;
v_isShared_3957_ = v_isSharedCheck_4222_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3953_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_4222_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v_fst_3958_; lean_object* v_snd_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_4221_; 
v_fst_3958_ = lean_ctor_get(v_a_3954_, 0);
v_snd_3959_ = lean_ctor_get(v_a_3954_, 1);
v_isSharedCheck_4221_ = !lean_is_exclusive(v_a_3954_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_3961_ = v_a_3954_;
v_isShared_3962_ = v_isSharedCheck_4221_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_snd_3959_);
lean_inc(v_fst_3958_);
lean_dec(v_a_3954_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_4221_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3963_; lean_object* v___y_3965_; lean_object* v_a_3978_; lean_object* v___y_3985_; lean_object* v___y_3988_; lean_object* v___y_3989_; uint8_t v___y_3990_; lean_object* v___y_4001_; lean_object* v_a_4017_; lean_object* v___f_4021_; lean_object* v___x_4022_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v_a_4026_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v_a_4043_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v_a_4048_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v_a_4053_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; uint8_t v___y_4067_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; uint8_t v___y_4096_; lean_object* v___y_4102_; lean_object* v___y_4103_; uint8_t v___y_4104_; lean_object* v_a_4105_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v_a_4112_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v_a_4124_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v_a_4129_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v_a_4135_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; uint8_t v___y_4147_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; uint8_t v___y_4157_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; uint8_t v___y_4170_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4185_; lean_object* v___y_4186_; uint8_t v___y_4187_; lean_object* v_a_4188_; 
v___x_3963_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3959_, v___x_3022_);
lean_inc(v___x_3963_);
lean_inc(v_fst_3958_);
v___f_4021_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_4021_, 0, v_fst_3958_);
lean_closure_set(v___f_4021_, 1, v___x_3963_);
v___x_4022_ = lean_box(0);
if (v___x_3118_ == 0)
{
if (v___x_3952_ == 0)
{
lean_object* v___x_4217_; 
lean_dec_ref(v___f_4021_);
lean_del_object(v___x_3961_);
v___x_4217_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3033_, v___x_3952_, v_goals_3012_, v___x_4022_, v_a_3015_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4219_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
lean_dec_ref(v___x_4217_);
v___x_4219_ = l_List_reverse___redArg(v_a_4218_);
v_a_4017_ = v___x_4219_;
goto v___jp_4016_;
}
else
{
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4220_; 
v_a_4220_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4220_);
lean_dec_ref(v___x_4217_);
v_a_4017_ = v_a_4220_;
goto v___jp_4016_;
}
else
{
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
lean_del_object(v___x_3956_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
return v___x_4217_;
}
}
}
else
{
lean_del_object(v___x_3956_);
goto v___jp_4192_;
}
}
else
{
lean_del_object(v___x_3956_);
goto v___jp_4192_;
}
v___jp_3964_:
{
uint8_t v___x_3966_; 
v___x_3966_ = l_List_isEmpty___redArg(v_fst_3958_);
lean_dec(v_fst_3958_);
if (v___x_3966_ == 0)
{
lean_dec(v___y_3965_);
lean_dec(v___x_3963_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
goto v___jp_3019_;
}
else
{
if (v___x_3952_ == 0)
{
lean_object* v___x_3967_; 
v___x_3967_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3965_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3976_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3970_ = v___x_3967_;
v_isShared_3971_ = v_isSharedCheck_3976_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3967_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3976_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3972_; lean_object* v___x_3974_; 
v___x_3972_ = l_List_appendTR___redArg(v___x_3963_, v_a_3968_);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 0, v___x_3972_);
v___x_3974_ = v___x_3970_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
else
{
lean_dec(v___x_3963_);
return v___x_3967_;
}
}
else
{
lean_dec(v___y_3965_);
lean_dec(v___x_3963_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
goto v___jp_3019_;
}
}
}
v___jp_3977_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3982_; 
v___x_3979_ = l_List_appendTR___redArg(v___x_3963_, v_fst_3958_);
v___x_3980_ = l_List_appendTR___redArg(v___x_3979_, v_a_3978_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 0, v___x_3980_);
v___x_3982_ = v___x_3956_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3980_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
v___jp_3984_:
{
if (lean_obj_tag(v___y_3985_) == 0)
{
lean_object* v_a_3986_; 
v_a_3986_ = lean_ctor_get(v___y_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref(v___y_3985_);
v_a_3978_ = v_a_3986_;
goto v___jp_3977_;
}
else
{
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
lean_del_object(v___x_3956_);
return v___y_3985_;
}
}
v___jp_3987_:
{
if (v___y_3990_ == 0)
{
lean_object* v___x_3991_; 
lean_dec_ref(v___y_3988_);
v___x_3991_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3989_, v_a_3015_, v_a_3017_);
lean_dec_ref(v___y_3989_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_dec_ref(v___x_3991_);
v_a_3978_ = v_snd_3026_;
goto v___jp_3977_;
}
else
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
lean_del_object(v___x_3956_);
lean_dec(v_snd_3026_);
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3991_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v___x_3991_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
else
{
lean_dec_ref(v___y_3989_);
lean_dec(v_snd_3026_);
v___y_3985_ = v___y_3988_;
goto v___jp_3984_;
}
}
v___jp_4000_:
{
lean_object* v___x_4002_; 
v___x_4002_ = l_Lean_Meta_saveState___redArg(v_a_3015_, v_a_3017_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; lean_object* v___x_4004_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_a_4003_);
lean_dec_ref(v___x_4002_);
lean_inc(v_snd_3026_);
v___x_4004_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_4001_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_dec(v_a_4003_);
lean_dec(v_snd_3026_);
v___y_3985_ = v___x_4004_;
goto v___jp_3984_;
}
else
{
lean_object* v_a_4005_; uint8_t v___x_4006_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
v___x_4006_ = l_Lean_Exception_isInterrupt(v_a_4005_);
if (v___x_4006_ == 0)
{
uint8_t v___x_4007_; 
v___x_4007_ = l_Lean_Exception_isRuntime(v_a_4005_);
v___y_3988_ = v___x_4004_;
v___y_3989_ = v_a_4003_;
v___y_3990_ = v___x_4007_;
goto v___jp_3987_;
}
else
{
lean_dec(v_a_4005_);
v___y_3988_ = v___x_4004_;
v___y_3989_ = v_a_4003_;
v___y_3990_ = v___x_4006_;
goto v___jp_3987_;
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec(v___y_4001_);
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
lean_del_object(v___x_3956_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
v_a_4008_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_4002_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_4002_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
v___jp_4016_:
{
uint8_t v_commitIndependentGoals_4018_; lean_object* v___x_4019_; 
v_commitIndependentGoals_4018_ = lean_ctor_get_uint8(v_cfg_3008_, sizeof(void*)*4);
lean_inc(v___x_3963_);
v___x_4019_ = l_List_appendTR___redArg(v_a_4017_, v___x_3963_);
if (v_commitIndependentGoals_4018_ == 0)
{
lean_del_object(v___x_3956_);
v___y_3965_ = v___x_4019_;
goto v___jp_3964_;
}
else
{
uint8_t v___x_4020_; 
v___x_4020_ = l_List_isEmpty___redArg(v___x_3963_);
if (v___x_4020_ == 0)
{
v___y_4001_ = v___x_4019_;
goto v___jp_4000_;
}
else
{
if (v___x_3952_ == 0)
{
lean_del_object(v___x_3956_);
v___y_3965_ = v___x_4019_;
goto v___jp_3964_;
}
else
{
v___y_4001_ = v___x_4019_;
goto v___jp_4000_;
}
}
}
}
v___jp_4023_:
{
lean_object* v___x_4027_; double v___x_4028_; double v___x_4029_; double v___x_4030_; double v___x_4031_; double v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4036_; 
v___x_4027_ = lean_io_mono_nanos_now();
v___x_4028_ = lean_float_of_nat(v___y_4025_);
v___x_4029_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_4030_ = lean_float_div(v___x_4028_, v___x_4029_);
v___x_4031_ = lean_float_of_nat(v___x_4027_);
v___x_4032_ = lean_float_div(v___x_4031_, v___x_4029_);
v___x_4033_ = lean_box_float(v___x_4030_);
v___x_4034_ = lean_box_float(v___x_4032_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v___x_4034_);
lean_ctor_set(v___x_3961_, 0, v___x_4033_);
v___x_4036_ = v___x_3961_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4033_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4037_, 0, v_a_4026_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3009_, v_hasTrace_3033_, v___x_3115_, v_options_3031_, v___x_3118_, v___y_4024_, v___f_4021_, v___x_4037_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
return v___x_4038_;
}
}
v___jp_4040_:
{
lean_object* v___x_4044_; 
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v_a_4043_);
v___y_4024_ = v___y_4041_;
v___y_4025_ = v___y_4042_;
v_a_4026_ = v___x_4044_;
goto v___jp_4023_;
}
v___jp_4045_:
{
lean_object* v___x_4049_; 
v___x_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4049_, 0, v_a_4048_);
v___y_4024_ = v___y_4046_;
v___y_4025_ = v___y_4047_;
v_a_4026_ = v___x_4049_;
goto v___jp_4023_;
}
v___jp_4050_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = l_List_appendTR___redArg(v___x_3963_, v_fst_3958_);
v___x_4055_ = l_List_appendTR___redArg(v___x_4054_, v_a_4053_);
v___y_4046_ = v___y_4051_;
v___y_4047_ = v___y_4052_;
v_a_4048_ = v___x_4055_;
goto v___jp_4045_;
}
v___jp_4056_:
{
if (lean_obj_tag(v___y_4059_) == 0)
{
lean_object* v_a_4060_; 
v_a_4060_ = lean_ctor_get(v___y_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref(v___y_4059_);
v___y_4051_ = v___y_4057_;
v___y_4052_ = v___y_4058_;
v_a_4053_ = v_a_4060_;
goto v___jp_4050_;
}
else
{
lean_object* v_a_4061_; 
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
v_a_4061_ = lean_ctor_get(v___y_4059_, 0);
lean_inc(v_a_4061_);
lean_dec_ref(v___y_4059_);
v___y_4041_ = v___y_4057_;
v___y_4042_ = v___y_4058_;
v_a_4043_ = v_a_4061_;
goto v___jp_4040_;
}
}
v___jp_4062_:
{
if (v___y_4067_ == 0)
{
lean_object* v___x_4068_; 
lean_dec_ref(v___y_4066_);
v___x_4068_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4064_, v_a_3015_, v_a_3017_);
lean_dec_ref(v___y_4064_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_dec_ref(v___x_4068_);
v___y_4051_ = v___y_4063_;
v___y_4052_ = v___y_4065_;
v_a_4053_ = v_snd_3026_;
goto v___jp_4050_;
}
else
{
lean_object* v_a_4069_; 
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
lean_dec(v_snd_3026_);
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4069_);
lean_dec_ref(v___x_4068_);
v___y_4041_ = v___y_4063_;
v___y_4042_ = v___y_4065_;
v_a_4043_ = v_a_4069_;
goto v___jp_4040_;
}
}
else
{
lean_dec_ref(v___y_4064_);
lean_dec(v_snd_3026_);
v___y_4057_ = v___y_4063_;
v___y_4058_ = v___y_4065_;
v___y_4059_ = v___y_4066_;
goto v___jp_4056_;
}
}
v___jp_4070_:
{
lean_object* v___x_4074_; 
v___x_4074_ = l_Lean_Meta_saveState___redArg(v_a_3015_, v_a_3017_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4076_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref(v___x_4074_);
lean_inc(v_snd_3026_);
lean_inc(v_trace_3009_);
v___x_4076_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_4072_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_dec(v_a_4075_);
lean_dec(v_snd_3026_);
v___y_4057_ = v___y_4071_;
v___y_4058_ = v___y_4073_;
v___y_4059_ = v___x_4076_;
goto v___jp_4056_;
}
else
{
lean_object* v_a_4077_; uint8_t v___x_4078_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
v___x_4078_ = l_Lean_Exception_isInterrupt(v_a_4077_);
if (v___x_4078_ == 0)
{
uint8_t v___x_4079_; 
v___x_4079_ = l_Lean_Exception_isRuntime(v_a_4077_);
v___y_4063_ = v___y_4071_;
v___y_4064_ = v_a_4075_;
v___y_4065_ = v___y_4073_;
v___y_4066_ = v___x_4076_;
v___y_4067_ = v___x_4079_;
goto v___jp_4062_;
}
else
{
lean_dec(v_a_4077_);
v___y_4063_ = v___y_4071_;
v___y_4064_ = v_a_4075_;
v___y_4065_ = v___y_4073_;
v___y_4066_ = v___x_4076_;
v___y_4067_ = v___x_4078_;
goto v___jp_4062_;
}
}
}
else
{
lean_object* v_a_4080_; 
lean_dec(v___y_4072_);
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_4080_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4080_);
lean_dec_ref(v___x_4074_);
v___y_4041_ = v___y_4071_;
v___y_4042_ = v___y_4073_;
v_a_4043_ = v_a_4080_;
goto v___jp_4040_;
}
}
v___jp_4081_:
{
if (lean_obj_tag(v___y_4084_) == 0)
{
lean_object* v_a_4085_; 
v_a_4085_ = lean_ctor_get(v___y_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref(v___y_4084_);
v___y_4046_ = v___y_4082_;
v___y_4047_ = v___y_4083_;
v_a_4048_ = v_a_4085_;
goto v___jp_4045_;
}
else
{
lean_object* v_a_4086_; 
v_a_4086_ = lean_ctor_get(v___y_4084_, 0);
lean_inc(v_a_4086_);
lean_dec_ref(v___y_4084_);
v___y_4041_ = v___y_4082_;
v___y_4042_ = v___y_4083_;
v_a_4043_ = v_a_4086_;
goto v___jp_4040_;
}
}
v___jp_4087_:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; 
v___x_4090_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4091_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4090_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_4082_ = v___y_4088_;
v___y_4083_ = v___y_4089_;
v___y_4084_ = v___x_4091_;
goto v___jp_4081_;
}
v___jp_4092_:
{
uint8_t v___x_4097_; 
v___x_4097_ = l_List_isEmpty___redArg(v_fst_3958_);
lean_dec(v_fst_3958_);
if (v___x_4097_ == 0)
{
lean_dec(v___y_4094_);
lean_dec(v___x_3963_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___y_4088_ = v___y_4093_;
v___y_4089_ = v___y_4095_;
goto v___jp_4087_;
}
else
{
if (v___y_4096_ == 0)
{
lean_object* v___x_4098_; 
lean_inc(v_trace_3009_);
v___x_4098_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_4094_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4100_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref(v___x_4098_);
v___x_4100_ = l_List_appendTR___redArg(v___x_3963_, v_a_4099_);
v___y_4046_ = v___y_4093_;
v___y_4047_ = v___y_4095_;
v_a_4048_ = v___x_4100_;
goto v___jp_4045_;
}
else
{
lean_dec(v___x_3963_);
v___y_4082_ = v___y_4093_;
v___y_4083_ = v___y_4095_;
v___y_4084_ = v___x_4098_;
goto v___jp_4081_;
}
}
else
{
lean_dec(v___y_4094_);
lean_dec(v___x_3963_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___y_4088_ = v___y_4093_;
v___y_4089_ = v___y_4095_;
goto v___jp_4087_;
}
}
}
v___jp_4101_:
{
uint8_t v_commitIndependentGoals_4106_; lean_object* v___x_4107_; 
v_commitIndependentGoals_4106_ = lean_ctor_get_uint8(v_cfg_3008_, sizeof(void*)*4);
lean_inc(v___x_3963_);
v___x_4107_ = l_List_appendTR___redArg(v_a_4105_, v___x_3963_);
if (v_commitIndependentGoals_4106_ == 0)
{
v___y_4093_ = v___y_4102_;
v___y_4094_ = v___x_4107_;
v___y_4095_ = v___y_4103_;
v___y_4096_ = v___y_4104_;
goto v___jp_4092_;
}
else
{
uint8_t v___x_4108_; 
v___x_4108_ = l_List_isEmpty___redArg(v___x_3963_);
if (v___x_4108_ == 0)
{
v___y_4071_ = v___y_4102_;
v___y_4072_ = v___x_4107_;
v___y_4073_ = v___y_4103_;
goto v___jp_4070_;
}
else
{
if (v___y_4104_ == 0)
{
v___y_4093_ = v___y_4102_;
v___y_4094_ = v___x_4107_;
v___y_4095_ = v___y_4103_;
v___y_4096_ = v___y_4104_;
goto v___jp_4092_;
}
else
{
v___y_4071_ = v___y_4102_;
v___y_4072_ = v___x_4107_;
v___y_4073_ = v___y_4103_;
goto v___jp_4070_;
}
}
}
}
v___jp_4109_:
{
lean_object* v___x_4113_; double v___x_4114_; double v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4113_ = lean_io_get_num_heartbeats();
v___x_4114_ = lean_float_of_nat(v___y_4111_);
v___x_4115_ = lean_float_of_nat(v___x_4113_);
v___x_4116_ = lean_box_float(v___x_4114_);
v___x_4117_ = lean_box_float(v___x_4115_);
v___x_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4116_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
v___x_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4119_, 0, v_a_4112_);
lean_ctor_set(v___x_4119_, 1, v___x_4118_);
v___x_4120_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3009_, v_hasTrace_3033_, v___x_3115_, v_options_3031_, v___x_3118_, v___y_4110_, v___f_4021_, v___x_4119_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
return v___x_4120_;
}
v___jp_4121_:
{
lean_object* v___x_4125_; 
v___x_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4125_, 0, v_a_4124_);
v___y_4110_ = v___y_4122_;
v___y_4111_ = v___y_4123_;
v_a_4112_ = v___x_4125_;
goto v___jp_4109_;
}
v___jp_4126_:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = l_List_appendTR___redArg(v___x_3963_, v_fst_3958_);
v___x_4131_ = l_List_appendTR___redArg(v___x_4130_, v_a_4129_);
v___y_4122_ = v___y_4127_;
v___y_4123_ = v___y_4128_;
v_a_4124_ = v___x_4131_;
goto v___jp_4121_;
}
v___jp_4132_:
{
lean_object* v___x_4136_; 
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v_a_4135_);
v___y_4110_ = v___y_4133_;
v___y_4111_ = v___y_4134_;
v_a_4112_ = v___x_4136_;
goto v___jp_4109_;
}
v___jp_4137_:
{
if (lean_obj_tag(v___y_4140_) == 0)
{
lean_object* v_a_4141_; 
v_a_4141_ = lean_ctor_get(v___y_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref(v___y_4140_);
v___y_4122_ = v___y_4138_;
v___y_4123_ = v___y_4139_;
v_a_4124_ = v_a_4141_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4142_; 
v_a_4142_ = lean_ctor_get(v___y_4140_, 0);
lean_inc(v_a_4142_);
lean_dec_ref(v___y_4140_);
v___y_4133_ = v___y_4138_;
v___y_4134_ = v___y_4139_;
v_a_4135_ = v_a_4142_;
goto v___jp_4132_;
}
}
v___jp_4143_:
{
if (v___y_4147_ == 0)
{
lean_object* v___x_4148_; 
lean_inc(v_trace_3009_);
v___x_4148_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_4145_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4150_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref(v___x_4148_);
v___x_4150_ = l_List_appendTR___redArg(v___x_3963_, v_a_4149_);
v___y_4122_ = v___y_4144_;
v___y_4123_ = v___y_4146_;
v_a_4124_ = v___x_4150_;
goto v___jp_4121_;
}
else
{
lean_dec(v___x_3963_);
v___y_4138_ = v___y_4144_;
v___y_4139_ = v___y_4146_;
v___y_4140_ = v___x_4148_;
goto v___jp_4137_;
}
}
else
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
lean_dec(v___y_4145_);
lean_dec(v___x_3963_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___x_4151_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4152_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4151_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_4138_ = v___y_4144_;
v___y_4139_ = v___y_4146_;
v___y_4140_ = v___x_4152_;
goto v___jp_4137_;
}
}
v___jp_4153_:
{
uint8_t v___x_4158_; 
v___x_4158_ = l_List_isEmpty___redArg(v_fst_3958_);
lean_dec(v_fst_3958_);
if (v___x_4158_ == 0)
{
v___y_4144_ = v___y_4154_;
v___y_4145_ = v___y_4155_;
v___y_4146_ = v___y_4156_;
v___y_4147_ = v___y_4157_;
goto v___jp_4143_;
}
else
{
v___y_4144_ = v___y_4154_;
v___y_4145_ = v___y_4155_;
v___y_4146_ = v___y_4156_;
v___y_4147_ = v___x_3952_;
goto v___jp_4143_;
}
}
v___jp_4159_:
{
if (lean_obj_tag(v___y_4162_) == 0)
{
lean_object* v_a_4163_; 
v_a_4163_ = lean_ctor_get(v___y_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref(v___y_4162_);
v___y_4127_ = v___y_4160_;
v___y_4128_ = v___y_4161_;
v_a_4129_ = v_a_4163_;
goto v___jp_4126_;
}
else
{
lean_object* v_a_4164_; 
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
v_a_4164_ = lean_ctor_get(v___y_4162_, 0);
lean_inc(v_a_4164_);
lean_dec_ref(v___y_4162_);
v___y_4133_ = v___y_4160_;
v___y_4134_ = v___y_4161_;
v_a_4135_ = v_a_4164_;
goto v___jp_4132_;
}
}
v___jp_4165_:
{
if (v___y_4170_ == 0)
{
lean_object* v___x_4171_; 
lean_dec_ref(v___y_4167_);
v___x_4171_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4169_, v_a_3015_, v_a_3017_);
lean_dec_ref(v___y_4169_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_dec_ref(v___x_4171_);
v___y_4127_ = v___y_4166_;
v___y_4128_ = v___y_4168_;
v_a_4129_ = v_snd_3026_;
goto v___jp_4126_;
}
else
{
lean_object* v_a_4172_; 
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
lean_dec(v_snd_3026_);
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref(v___x_4171_);
v___y_4133_ = v___y_4166_;
v___y_4134_ = v___y_4168_;
v_a_4135_ = v_a_4172_;
goto v___jp_4132_;
}
}
else
{
lean_dec_ref(v___y_4169_);
lean_dec(v_snd_3026_);
v___y_4160_ = v___y_4166_;
v___y_4161_ = v___y_4168_;
v___y_4162_ = v___y_4167_;
goto v___jp_4159_;
}
}
v___jp_4173_:
{
lean_object* v___x_4177_; 
v___x_4177_ = l_Lean_Meta_saveState___redArg(v_a_3015_, v_a_3017_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4179_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref(v___x_4177_);
lean_inc(v_snd_3026_);
lean_inc(v_trace_3009_);
v___x_4179_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_4175_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_dec(v_a_4178_);
lean_dec(v_snd_3026_);
v___y_4160_ = v___y_4174_;
v___y_4161_ = v___y_4176_;
v___y_4162_ = v___x_4179_;
goto v___jp_4159_;
}
else
{
lean_object* v_a_4180_; uint8_t v___x_4181_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
v___x_4181_ = l_Lean_Exception_isInterrupt(v_a_4180_);
if (v___x_4181_ == 0)
{
uint8_t v___x_4182_; 
v___x_4182_ = l_Lean_Exception_isRuntime(v_a_4180_);
v___y_4166_ = v___y_4174_;
v___y_4167_ = v___x_4179_;
v___y_4168_ = v___y_4176_;
v___y_4169_ = v_a_4178_;
v___y_4170_ = v___x_4182_;
goto v___jp_4165_;
}
else
{
lean_dec(v_a_4180_);
v___y_4166_ = v___y_4174_;
v___y_4167_ = v___x_4179_;
v___y_4168_ = v___y_4176_;
v___y_4169_ = v_a_4178_;
v___y_4170_ = v___x_4181_;
goto v___jp_4165_;
}
}
}
else
{
lean_object* v_a_4183_; 
lean_dec(v___y_4175_);
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_4183_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4183_);
lean_dec_ref(v___x_4177_);
v___y_4133_ = v___y_4174_;
v___y_4134_ = v___y_4176_;
v_a_4135_ = v_a_4183_;
goto v___jp_4132_;
}
}
v___jp_4184_:
{
uint8_t v_commitIndependentGoals_4189_; lean_object* v___x_4190_; 
v_commitIndependentGoals_4189_ = lean_ctor_get_uint8(v_cfg_3008_, sizeof(void*)*4);
lean_inc(v___x_3963_);
v___x_4190_ = l_List_appendTR___redArg(v_a_4188_, v___x_3963_);
if (v_commitIndependentGoals_4189_ == 0)
{
v___y_4154_ = v___y_4185_;
v___y_4155_ = v___x_4190_;
v___y_4156_ = v___y_4186_;
v___y_4157_ = v___y_4187_;
goto v___jp_4153_;
}
else
{
uint8_t v___x_4191_; 
v___x_4191_ = l_List_isEmpty___redArg(v___x_3963_);
if (v___x_4191_ == 0)
{
v___y_4174_ = v___y_4185_;
v___y_4175_ = v___x_4190_;
v___y_4176_ = v___y_4186_;
goto v___jp_4173_;
}
else
{
if (v___x_3952_ == 0)
{
v___y_4154_ = v___y_4185_;
v___y_4155_ = v___x_4190_;
v___y_4156_ = v___y_4186_;
v___y_4157_ = v___y_4187_;
goto v___jp_4153_;
}
else
{
v___y_4174_ = v___y_4185_;
v___y_4175_ = v___x_4190_;
v___y_4176_ = v___y_4186_;
goto v___jp_4173_;
}
}
}
}
v___jp_4192_:
{
lean_object* v___x_4193_; 
v___x_4193_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3017_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; lean_object* v___x_4195_; uint8_t v___x_4196_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_a_4194_);
lean_dec_ref(v___x_4193_);
v___x_4195_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4196_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3031_, v___x_4195_);
if (v___x_4196_ == 0)
{
lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4197_ = lean_io_mono_nanos_now();
v___x_4198_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3033_, v___x_3952_, v_goals_3012_, v___x_4022_, v_a_3015_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v___x_4200_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref(v___x_4198_);
v___x_4200_ = l_List_reverse___redArg(v_a_4199_);
v___y_4102_ = v_a_4194_;
v___y_4103_ = v___x_4197_;
v___y_4104_ = v___x_4196_;
v_a_4105_ = v___x_4200_;
goto v___jp_4101_;
}
else
{
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4201_; 
v_a_4201_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4201_);
lean_dec_ref(v___x_4198_);
v___y_4102_ = v_a_4194_;
v___y_4103_ = v___x_4197_;
v___y_4104_ = v___x_4196_;
v_a_4105_ = v_a_4201_;
goto v___jp_4101_;
}
else
{
lean_object* v_a_4202_; 
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_4202_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4202_);
lean_dec_ref(v___x_4198_);
v___y_4041_ = v_a_4194_;
v___y_4042_ = v___x_4197_;
v_a_4043_ = v_a_4202_;
goto v___jp_4040_;
}
}
}
else
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_del_object(v___x_3961_);
v___x_4203_ = lean_io_get_num_heartbeats();
v___x_4204_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3033_, v___x_3952_, v_goals_3012_, v___x_4022_, v_a_3015_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4206_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
lean_dec_ref(v___x_4204_);
v___x_4206_ = l_List_reverse___redArg(v_a_4205_);
v___y_4185_ = v_a_4194_;
v___y_4186_ = v___x_4203_;
v___y_4187_ = v___x_4196_;
v_a_4188_ = v___x_4206_;
goto v___jp_4184_;
}
else
{
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4207_; 
v_a_4207_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4207_);
lean_dec_ref(v___x_4204_);
v___y_4185_ = v_a_4194_;
v___y_4186_ = v___x_4203_;
v___y_4187_ = v___x_4196_;
v_a_4188_ = v_a_4207_;
goto v___jp_4184_;
}
else
{
lean_object* v_a_4208_; 
lean_dec(v___x_3963_);
lean_dec(v_fst_3958_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_4208_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4208_);
lean_dec_ref(v___x_4204_);
v___y_4133_ = v_a_4194_;
v___y_4134_ = v___x_4203_;
v_a_4135_ = v_a_4208_;
goto v___jp_4132_;
}
}
}
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
lean_dec_ref(v___f_4021_);
lean_dec(v___x_3963_);
lean_del_object(v___x_3961_);
lean_dec(v_fst_3958_);
lean_dec(v_snd_3026_);
lean_dec(v_goals_3012_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
v_a_4209_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4193_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4193_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec(v_snd_3026_);
lean_dec(v_goals_3012_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
v_a_4223_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_3953_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_3953_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
}
}
else
{
goto v___jp_3906_;
}
}
else
{
goto v___jp_3906_;
}
v___jp_3119_:
{
lean_object* v___x_3123_; double v___x_3124_; double v___x_3125_; double v___x_3126_; double v___x_3127_; double v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3123_ = lean_io_mono_nanos_now();
v___x_3124_ = lean_float_of_nat(v___y_3121_);
v___x_3125_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3126_ = lean_float_div(v___x_3124_, v___x_3125_);
v___x_3127_ = lean_float_of_nat(v___x_3123_);
v___x_3128_ = lean_float_div(v___x_3127_, v___x_3125_);
v___x_3129_ = lean_box_float(v___x_3126_);
v___x_3130_ = lean_box_float(v___x_3128_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v___x_3130_);
lean_ctor_set(v___x_3028_, 0, v___x_3129_);
v___x_3132_ = v___x_3028_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3133_, 0, v_a_3122_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
v___x_3134_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3009_, v_hasTrace_3033_, v___x_3115_, v_options_3031_, v___x_3118_, v___y_3120_, v___f_3114_, v___x_3133_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
return v___x_3134_;
}
}
v___jp_3136_:
{
lean_object* v___x_3140_; 
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_a_3139_);
v___y_3120_ = v___y_3137_;
v___y_3121_ = v___y_3138_;
v_a_3122_ = v___x_3140_;
goto v___jp_3119_;
}
v___jp_3141_:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = l_List_appendTR___redArg(v___y_3145_, v___y_3144_);
v___x_3148_ = l_List_appendTR___redArg(v___x_3147_, v_a_3146_);
v___y_3137_ = v___y_3142_;
v___y_3138_ = v___y_3143_;
v_a_3139_ = v___x_3148_;
goto v___jp_3136_;
}
v___jp_3149_:
{
lean_object* v___x_3153_; 
v___x_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3153_, 0, v_a_3152_);
v___y_3120_ = v___y_3150_;
v___y_3121_ = v___y_3151_;
v_a_3122_ = v___x_3153_;
goto v___jp_3119_;
}
v___jp_3154_:
{
if (lean_obj_tag(v___y_3159_) == 0)
{
lean_object* v_a_3160_; 
v_a_3160_ = lean_ctor_get(v___y_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___y_3159_);
v___y_3142_ = v___y_3155_;
v___y_3143_ = v___y_3156_;
v___y_3144_ = v___y_3157_;
v___y_3145_ = v___y_3158_;
v_a_3146_ = v_a_3160_;
goto v___jp_3141_;
}
else
{
lean_object* v_a_3161_; 
lean_dec(v___y_3158_);
lean_dec(v___y_3157_);
v_a_3161_ = lean_ctor_get(v___y_3159_, 0);
lean_inc(v_a_3161_);
lean_dec_ref(v___y_3159_);
v___y_3150_ = v___y_3155_;
v___y_3151_ = v___y_3156_;
v_a_3152_ = v_a_3161_;
goto v___jp_3149_;
}
}
v___jp_3162_:
{
if (v___y_3169_ == 0)
{
lean_object* v___x_3170_; 
lean_dec_ref(v___y_3168_);
v___x_3170_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3164_, v_a_3015_, v_a_3017_);
lean_dec_ref(v___y_3164_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_dec_ref(v___x_3170_);
v___y_3142_ = v___y_3163_;
v___y_3143_ = v___y_3165_;
v___y_3144_ = v___y_3166_;
v___y_3145_ = v___y_3167_;
v_a_3146_ = v_snd_3026_;
goto v___jp_3141_;
}
else
{
lean_object* v_a_3171_; 
lean_dec(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec(v_snd_3026_);
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref(v___x_3170_);
v___y_3150_ = v___y_3163_;
v___y_3151_ = v___y_3165_;
v_a_3152_ = v_a_3171_;
goto v___jp_3149_;
}
}
else
{
lean_dec_ref(v___y_3164_);
lean_dec(v_snd_3026_);
v___y_3155_ = v___y_3163_;
v___y_3156_ = v___y_3165_;
v___y_3157_ = v___y_3166_;
v___y_3158_ = v___y_3167_;
v___y_3159_ = v___y_3168_;
goto v___jp_3154_;
}
}
v___jp_3172_:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_Meta_saveState___redArg(v_a_3015_, v_a_3017_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3180_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_a_3179_);
lean_dec_ref(v___x_3178_);
lean_inc(v_snd_3026_);
lean_inc(v_trace_3009_);
v___x_3180_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3176_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_dec(v_a_3179_);
lean_dec(v_snd_3026_);
v___y_3155_ = v___y_3173_;
v___y_3156_ = v___y_3174_;
v___y_3157_ = v___y_3175_;
v___y_3158_ = v___y_3177_;
v___y_3159_ = v___x_3180_;
goto v___jp_3154_;
}
else
{
lean_object* v_a_3181_; uint8_t v___x_3182_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3181_);
v___x_3182_ = l_Lean_Exception_isInterrupt(v_a_3181_);
if (v___x_3182_ == 0)
{
uint8_t v___x_3183_; 
v___x_3183_ = l_Lean_Exception_isRuntime(v_a_3181_);
v___y_3163_ = v___y_3173_;
v___y_3164_ = v_a_3179_;
v___y_3165_ = v___y_3174_;
v___y_3166_ = v___y_3175_;
v___y_3167_ = v___y_3177_;
v___y_3168_ = v___x_3180_;
v___y_3169_ = v___x_3183_;
goto v___jp_3162_;
}
else
{
lean_dec(v_a_3181_);
v___y_3163_ = v___y_3173_;
v___y_3164_ = v_a_3179_;
v___y_3165_ = v___y_3174_;
v___y_3166_ = v___y_3175_;
v___y_3167_ = v___y_3177_;
v___y_3168_ = v___x_3180_;
v___y_3169_ = v___x_3182_;
goto v___jp_3162_;
}
}
}
else
{
lean_object* v_a_3184_; 
lean_dec(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec(v___y_3175_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3184_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_a_3184_);
lean_dec_ref(v___x_3178_);
v___y_3150_ = v___y_3173_;
v___y_3151_ = v___y_3174_;
v_a_3152_ = v_a_3184_;
goto v___jp_3149_;
}
}
v___jp_3185_:
{
if (lean_obj_tag(v___y_3188_) == 0)
{
lean_object* v_a_3189_; 
v_a_3189_ = lean_ctor_get(v___y_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref(v___y_3188_);
v___y_3137_ = v___y_3186_;
v___y_3138_ = v___y_3187_;
v_a_3139_ = v_a_3189_;
goto v___jp_3136_;
}
else
{
lean_object* v_a_3190_; 
v_a_3190_ = lean_ctor_get(v___y_3188_, 0);
lean_inc(v_a_3190_);
lean_dec_ref(v___y_3188_);
v___y_3150_ = v___y_3186_;
v___y_3151_ = v___y_3187_;
v_a_3152_ = v_a_3190_;
goto v___jp_3149_;
}
}
v___jp_3191_:
{
lean_object* v___x_3199_; double v___x_3200_; double v___x_3201_; double v___x_3202_; double v___x_3203_; double v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3199_ = lean_io_mono_nanos_now();
v___x_3200_ = lean_float_of_nat(v___y_3197_);
v___x_3201_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3202_ = lean_float_div(v___x_3200_, v___x_3201_);
v___x_3203_ = lean_float_of_nat(v___x_3199_);
v___x_3204_ = lean_float_div(v___x_3203_, v___x_3201_);
v___x_3205_ = lean_box_float(v___x_3202_);
v___x_3206_ = lean_box_float(v___x_3204_);
v___x_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3205_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v_a_3198_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
lean_inc(v_trace_3009_);
v___x_3209_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3009_, v_hasTrace_3033_, v___x_3115_, v_options_3031_, v___y_3196_, v___y_3195_, v___y_3193_, v___x_3208_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_3186_ = v___y_3192_;
v___y_3187_ = v___y_3194_;
v___y_3188_ = v___x_3209_;
goto v___jp_3185_;
}
v___jp_3210_:
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3218_, 0, v_a_3217_);
v___y_3192_ = v___y_3212_;
v___y_3193_ = v___y_3211_;
v___y_3194_ = v___y_3214_;
v___y_3195_ = v___y_3213_;
v___y_3196_ = v___y_3215_;
v___y_3197_ = v___y_3216_;
v_a_3198_ = v___x_3218_;
goto v___jp_3191_;
}
v___jp_3219_:
{
lean_object* v___x_3227_; 
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_a_3226_);
v___y_3192_ = v___y_3221_;
v___y_3193_ = v___y_3220_;
v___y_3194_ = v___y_3223_;
v___y_3195_ = v___y_3222_;
v___y_3196_ = v___y_3224_;
v___y_3197_ = v___y_3225_;
v_a_3198_ = v___x_3227_;
goto v___jp_3191_;
}
v___jp_3228_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = l_List_appendTR___redArg(v___y_3235_, v___y_3234_);
v___x_3239_ = l_List_appendTR___redArg(v___x_3238_, v_a_3237_);
v___y_3220_ = v___y_3230_;
v___y_3221_ = v___y_3229_;
v___y_3222_ = v___y_3232_;
v___y_3223_ = v___y_3231_;
v___y_3224_ = v___y_3233_;
v___y_3225_ = v___y_3236_;
v_a_3226_ = v___x_3239_;
goto v___jp_3219_;
}
v___jp_3240_:
{
if (lean_obj_tag(v___y_3249_) == 0)
{
lean_object* v_a_3250_; 
v_a_3250_ = lean_ctor_get(v___y_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref(v___y_3249_);
v___y_3229_ = v___y_3242_;
v___y_3230_ = v___y_3241_;
v___y_3231_ = v___y_3244_;
v___y_3232_ = v___y_3243_;
v___y_3233_ = v___y_3245_;
v___y_3234_ = v___y_3246_;
v___y_3235_ = v___y_3247_;
v___y_3236_ = v___y_3248_;
v_a_3237_ = v_a_3250_;
goto v___jp_3228_;
}
else
{
lean_object* v_a_3251_; 
lean_dec(v___y_3247_);
lean_dec(v___y_3246_);
v_a_3251_ = lean_ctor_get(v___y_3249_, 0);
lean_inc(v_a_3251_);
lean_dec_ref(v___y_3249_);
v___y_3211_ = v___y_3241_;
v___y_3212_ = v___y_3242_;
v___y_3213_ = v___y_3243_;
v___y_3214_ = v___y_3244_;
v___y_3215_ = v___y_3245_;
v___y_3216_ = v___y_3248_;
v_a_3217_ = v_a_3251_;
goto v___jp_3210_;
}
}
v___jp_3252_:
{
if (v___y_3263_ == 0)
{
lean_object* v___x_3264_; 
lean_dec_ref(v___y_3261_);
v___x_3264_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3262_, v_a_3015_, v_a_3017_);
lean_dec_ref(v___y_3262_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_dec_ref(v___x_3264_);
v___y_3229_ = v___y_3254_;
v___y_3230_ = v___y_3253_;
v___y_3231_ = v___y_3256_;
v___y_3232_ = v___y_3255_;
v___y_3233_ = v___y_3257_;
v___y_3234_ = v___y_3258_;
v___y_3235_ = v___y_3259_;
v___y_3236_ = v___y_3260_;
v_a_3237_ = v_snd_3026_;
goto v___jp_3228_;
}
else
{
lean_object* v_a_3265_; 
lean_dec(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec(v_snd_3026_);
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref(v___x_3264_);
v___y_3211_ = v___y_3253_;
v___y_3212_ = v___y_3254_;
v___y_3213_ = v___y_3255_;
v___y_3214_ = v___y_3256_;
v___y_3215_ = v___y_3257_;
v___y_3216_ = v___y_3260_;
v_a_3217_ = v_a_3265_;
goto v___jp_3210_;
}
}
else
{
lean_dec_ref(v___y_3262_);
lean_dec(v_snd_3026_);
v___y_3241_ = v___y_3253_;
v___y_3242_ = v___y_3254_;
v___y_3243_ = v___y_3255_;
v___y_3244_ = v___y_3256_;
v___y_3245_ = v___y_3257_;
v___y_3246_ = v___y_3258_;
v___y_3247_ = v___y_3259_;
v___y_3248_ = v___y_3260_;
v___y_3249_ = v___y_3261_;
goto v___jp_3240_;
}
}
v___jp_3266_:
{
lean_object* v___x_3276_; 
v___x_3276_ = l_Lean_Meta_saveState___redArg(v_a_3015_, v_a_3017_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3278_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref(v___x_3276_);
lean_inc(v_snd_3026_);
lean_inc(v_trace_3009_);
v___x_3278_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3275_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_dec(v_a_3277_);
lean_dec(v_snd_3026_);
v___y_3241_ = v___y_3268_;
v___y_3242_ = v___y_3267_;
v___y_3243_ = v___y_3270_;
v___y_3244_ = v___y_3269_;
v___y_3245_ = v___y_3271_;
v___y_3246_ = v___y_3272_;
v___y_3247_ = v___y_3273_;
v___y_3248_ = v___y_3274_;
v___y_3249_ = v___x_3278_;
goto v___jp_3240_;
}
else
{
lean_object* v_a_3279_; uint8_t v___x_3280_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
v___x_3280_ = l_Lean_Exception_isInterrupt(v_a_3279_);
if (v___x_3280_ == 0)
{
uint8_t v___x_3281_; 
v___x_3281_ = l_Lean_Exception_isRuntime(v_a_3279_);
v___y_3253_ = v___y_3268_;
v___y_3254_ = v___y_3267_;
v___y_3255_ = v___y_3270_;
v___y_3256_ = v___y_3269_;
v___y_3257_ = v___y_3271_;
v___y_3258_ = v___y_3272_;
v___y_3259_ = v___y_3273_;
v___y_3260_ = v___y_3274_;
v___y_3261_ = v___x_3278_;
v___y_3262_ = v_a_3277_;
v___y_3263_ = v___x_3281_;
goto v___jp_3252_;
}
else
{
lean_dec(v_a_3279_);
v___y_3253_ = v___y_3268_;
v___y_3254_ = v___y_3267_;
v___y_3255_ = v___y_3270_;
v___y_3256_ = v___y_3269_;
v___y_3257_ = v___y_3271_;
v___y_3258_ = v___y_3272_;
v___y_3259_ = v___y_3273_;
v___y_3260_ = v___y_3274_;
v___y_3261_ = v___x_3278_;
v___y_3262_ = v_a_3277_;
v___y_3263_ = v___x_3280_;
goto v___jp_3252_;
}
}
}
else
{
lean_object* v_a_3282_; 
lean_dec(v___y_3275_);
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3282_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3282_);
lean_dec_ref(v___x_3276_);
v___y_3211_ = v___y_3268_;
v___y_3212_ = v___y_3267_;
v___y_3213_ = v___y_3270_;
v___y_3214_ = v___y_3269_;
v___y_3215_ = v___y_3271_;
v___y_3216_ = v___y_3274_;
v_a_3217_ = v_a_3282_;
goto v___jp_3210_;
}
}
v___jp_3283_:
{
if (lean_obj_tag(v___y_3290_) == 0)
{
lean_object* v_a_3291_; 
v_a_3291_ = lean_ctor_get(v___y_3290_, 0);
lean_inc(v_a_3291_);
lean_dec_ref(v___y_3290_);
v___y_3220_ = v___y_3285_;
v___y_3221_ = v___y_3284_;
v___y_3222_ = v___y_3287_;
v___y_3223_ = v___y_3286_;
v___y_3224_ = v___y_3288_;
v___y_3225_ = v___y_3289_;
v_a_3226_ = v_a_3291_;
goto v___jp_3219_;
}
else
{
lean_object* v_a_3292_; 
v_a_3292_ = lean_ctor_get(v___y_3290_, 0);
lean_inc(v_a_3292_);
lean_dec_ref(v___y_3290_);
v___y_3211_ = v___y_3285_;
v___y_3212_ = v___y_3284_;
v___y_3213_ = v___y_3287_;
v___y_3214_ = v___y_3286_;
v___y_3215_ = v___y_3288_;
v___y_3216_ = v___y_3289_;
v_a_3217_ = v_a_3292_;
goto v___jp_3210_;
}
}
v___jp_3293_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3301_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3300_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_3284_ = v___y_3295_;
v___y_3285_ = v___y_3294_;
v___y_3286_ = v___y_3297_;
v___y_3287_ = v___y_3296_;
v___y_3288_ = v___y_3298_;
v___y_3289_ = v___y_3299_;
v___y_3290_ = v___x_3301_;
goto v___jp_3283_;
}
v___jp_3302_:
{
uint8_t v___x_3313_; 
v___x_3313_ = l_List_isEmpty___redArg(v___y_3308_);
lean_dec(v___y_3308_);
if (v___x_3313_ == 0)
{
lean_dec(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___y_3294_ = v___y_3304_;
v___y_3295_ = v___y_3303_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3305_;
v___y_3298_ = v___y_3307_;
v___y_3299_ = v___y_3311_;
goto v___jp_3293_;
}
else
{
if (v___y_3312_ == 0)
{
lean_object* v___x_3314_; 
lean_inc(v_trace_3009_);
v___x_3314_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3310_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3316_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
lean_dec_ref(v___x_3314_);
v___x_3316_ = l_List_appendTR___redArg(v___y_3309_, v_a_3315_);
v___y_3220_ = v___y_3304_;
v___y_3221_ = v___y_3303_;
v___y_3222_ = v___y_3306_;
v___y_3223_ = v___y_3305_;
v___y_3224_ = v___y_3307_;
v___y_3225_ = v___y_3311_;
v_a_3226_ = v___x_3316_;
goto v___jp_3219_;
}
else
{
lean_dec(v___y_3309_);
v___y_3284_ = v___y_3303_;
v___y_3285_ = v___y_3304_;
v___y_3286_ = v___y_3305_;
v___y_3287_ = v___y_3306_;
v___y_3288_ = v___y_3307_;
v___y_3289_ = v___y_3311_;
v___y_3290_ = v___x_3314_;
goto v___jp_3283_;
}
}
else
{
lean_dec(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___y_3294_ = v___y_3304_;
v___y_3295_ = v___y_3303_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3305_;
v___y_3298_ = v___y_3307_;
v___y_3299_ = v___y_3311_;
goto v___jp_3293_;
}
}
}
v___jp_3317_:
{
uint8_t v_commitIndependentGoals_3328_; lean_object* v___x_3329_; 
v_commitIndependentGoals_3328_ = lean_ctor_get_uint8(v_cfg_3008_, sizeof(void*)*4);
lean_inc(v___y_3324_);
v___x_3329_ = l_List_appendTR___redArg(v_a_3327_, v___y_3324_);
if (v_commitIndependentGoals_3328_ == 0)
{
v___y_3303_ = v___y_3318_;
v___y_3304_ = v___y_3319_;
v___y_3305_ = v___y_3320_;
v___y_3306_ = v___y_3321_;
v___y_3307_ = v___y_3322_;
v___y_3308_ = v___y_3323_;
v___y_3309_ = v___y_3324_;
v___y_3310_ = v___x_3329_;
v___y_3311_ = v___y_3325_;
v___y_3312_ = v___y_3326_;
goto v___jp_3302_;
}
else
{
uint8_t v___x_3330_; 
v___x_3330_ = l_List_isEmpty___redArg(v___y_3324_);
if (v___x_3330_ == 0)
{
v___y_3267_ = v___y_3318_;
v___y_3268_ = v___y_3319_;
v___y_3269_ = v___y_3320_;
v___y_3270_ = v___y_3321_;
v___y_3271_ = v___y_3322_;
v___y_3272_ = v___y_3323_;
v___y_3273_ = v___y_3324_;
v___y_3274_ = v___y_3325_;
v___y_3275_ = v___x_3329_;
goto v___jp_3266_;
}
else
{
if (v___y_3326_ == 0)
{
v___y_3303_ = v___y_3318_;
v___y_3304_ = v___y_3319_;
v___y_3305_ = v___y_3320_;
v___y_3306_ = v___y_3321_;
v___y_3307_ = v___y_3322_;
v___y_3308_ = v___y_3323_;
v___y_3309_ = v___y_3324_;
v___y_3310_ = v___x_3329_;
v___y_3311_ = v___y_3325_;
v___y_3312_ = v___y_3326_;
goto v___jp_3302_;
}
else
{
v___y_3267_ = v___y_3318_;
v___y_3268_ = v___y_3319_;
v___y_3269_ = v___y_3320_;
v___y_3270_ = v___y_3321_;
v___y_3271_ = v___y_3322_;
v___y_3272_ = v___y_3323_;
v___y_3273_ = v___y_3324_;
v___y_3274_ = v___y_3325_;
v___y_3275_ = v___x_3329_;
goto v___jp_3266_;
}
}
}
}
v___jp_3331_:
{
lean_object* v___x_3339_; double v___x_3340_; double v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3339_ = lean_io_get_num_heartbeats();
v___x_3340_ = lean_float_of_nat(v___y_3337_);
v___x_3341_ = lean_float_of_nat(v___x_3339_);
v___x_3342_ = lean_box_float(v___x_3340_);
v___x_3343_ = lean_box_float(v___x_3341_);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v_a_3338_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
lean_inc(v_trace_3009_);
v___x_3346_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3009_, v_hasTrace_3033_, v___x_3115_, v_options_3031_, v___y_3336_, v___y_3335_, v___y_3333_, v___x_3345_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_3186_ = v___y_3332_;
v___y_3187_ = v___y_3334_;
v___y_3188_ = v___x_3346_;
goto v___jp_3185_;
}
v___jp_3347_:
{
lean_object* v___x_3355_; 
v___x_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3355_, 0, v_a_3354_);
v___y_3332_ = v___y_3349_;
v___y_3333_ = v___y_3348_;
v___y_3334_ = v___y_3351_;
v___y_3335_ = v___y_3350_;
v___y_3336_ = v___y_3352_;
v___y_3337_ = v___y_3353_;
v_a_3338_ = v___x_3355_;
goto v___jp_3331_;
}
v___jp_3356_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = l_List_appendTR___redArg(v___y_3364_, v___y_3363_);
v___x_3367_ = l_List_appendTR___redArg(v___x_3366_, v_a_3365_);
v___y_3348_ = v___y_3358_;
v___y_3349_ = v___y_3357_;
v___y_3350_ = v___y_3360_;
v___y_3351_ = v___y_3359_;
v___y_3352_ = v___y_3361_;
v___y_3353_ = v___y_3362_;
v_a_3354_ = v___x_3367_;
goto v___jp_3347_;
}
v___jp_3368_:
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3376_, 0, v_a_3375_);
v___y_3332_ = v___y_3370_;
v___y_3333_ = v___y_3369_;
v___y_3334_ = v___y_3372_;
v___y_3335_ = v___y_3371_;
v___y_3336_ = v___y_3373_;
v___y_3337_ = v___y_3374_;
v_a_3338_ = v___x_3376_;
goto v___jp_3331_;
}
v___jp_3377_:
{
if (lean_obj_tag(v___y_3384_) == 0)
{
lean_object* v_a_3385_; 
v_a_3385_ = lean_ctor_get(v___y_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref(v___y_3384_);
v___y_3348_ = v___y_3379_;
v___y_3349_ = v___y_3378_;
v___y_3350_ = v___y_3381_;
v___y_3351_ = v___y_3380_;
v___y_3352_ = v___y_3382_;
v___y_3353_ = v___y_3383_;
v_a_3354_ = v_a_3385_;
goto v___jp_3347_;
}
else
{
lean_object* v_a_3386_; 
v_a_3386_ = lean_ctor_get(v___y_3384_, 0);
lean_inc(v_a_3386_);
lean_dec_ref(v___y_3384_);
v___y_3369_ = v___y_3379_;
v___y_3370_ = v___y_3378_;
v___y_3371_ = v___y_3381_;
v___y_3372_ = v___y_3380_;
v___y_3373_ = v___y_3382_;
v___y_3374_ = v___y_3383_;
v_a_3375_ = v_a_3386_;
goto v___jp_3368_;
}
}
v___jp_3387_:
{
lean_object* v___x_3396_; 
lean_inc(v_trace_3009_);
v___x_3396_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3395_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3398_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref(v___x_3396_);
v___x_3398_ = l_List_appendTR___redArg(v___y_3394_, v_a_3397_);
v___y_3348_ = v___y_3389_;
v___y_3349_ = v___y_3388_;
v___y_3350_ = v___y_3391_;
v___y_3351_ = v___y_3390_;
v___y_3352_ = v___y_3392_;
v___y_3353_ = v___y_3393_;
v_a_3354_ = v___x_3398_;
goto v___jp_3347_;
}
else
{
lean_dec(v___y_3394_);
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___y_3389_;
v___y_3380_ = v___y_3390_;
v___y_3381_ = v___y_3391_;
v___y_3382_ = v___y_3392_;
v___y_3383_ = v___y_3393_;
v___y_3384_ = v___x_3396_;
goto v___jp_3377_;
}
}
v___jp_3399_:
{
if (lean_obj_tag(v___y_3408_) == 0)
{
lean_object* v_a_3409_; 
v_a_3409_ = lean_ctor_get(v___y_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref(v___y_3408_);
v___y_3357_ = v___y_3401_;
v___y_3358_ = v___y_3400_;
v___y_3359_ = v___y_3403_;
v___y_3360_ = v___y_3402_;
v___y_3361_ = v___y_3404_;
v___y_3362_ = v___y_3405_;
v___y_3363_ = v___y_3406_;
v___y_3364_ = v___y_3407_;
v_a_3365_ = v_a_3409_;
goto v___jp_3356_;
}
else
{
lean_object* v_a_3410_; 
lean_dec(v___y_3407_);
lean_dec(v___y_3406_);
v_a_3410_ = lean_ctor_get(v___y_3408_, 0);
lean_inc(v_a_3410_);
lean_dec_ref(v___y_3408_);
v___y_3369_ = v___y_3400_;
v___y_3370_ = v___y_3401_;
v___y_3371_ = v___y_3402_;
v___y_3372_ = v___y_3403_;
v___y_3373_ = v___y_3404_;
v___y_3374_ = v___y_3405_;
v_a_3375_ = v_a_3410_;
goto v___jp_3368_;
}
}
v___jp_3411_:
{
if (v___y_3422_ == 0)
{
lean_object* v___x_3423_; 
lean_dec_ref(v___y_3412_);
v___x_3423_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3418_, v_a_3015_, v_a_3017_);
lean_dec_ref(v___y_3418_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_dec_ref(v___x_3423_);
v___y_3357_ = v___y_3414_;
v___y_3358_ = v___y_3413_;
v___y_3359_ = v___y_3416_;
v___y_3360_ = v___y_3415_;
v___y_3361_ = v___y_3417_;
v___y_3362_ = v___y_3419_;
v___y_3363_ = v___y_3420_;
v___y_3364_ = v___y_3421_;
v_a_3365_ = v_snd_3026_;
goto v___jp_3356_;
}
else
{
lean_object* v_a_3424_; 
lean_dec(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec(v_snd_3026_);
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref(v___x_3423_);
v___y_3369_ = v___y_3413_;
v___y_3370_ = v___y_3414_;
v___y_3371_ = v___y_3415_;
v___y_3372_ = v___y_3416_;
v___y_3373_ = v___y_3417_;
v___y_3374_ = v___y_3419_;
v_a_3375_ = v_a_3424_;
goto v___jp_3368_;
}
}
else
{
lean_dec_ref(v___y_3418_);
lean_dec(v_snd_3026_);
v___y_3400_ = v___y_3413_;
v___y_3401_ = v___y_3414_;
v___y_3402_ = v___y_3415_;
v___y_3403_ = v___y_3416_;
v___y_3404_ = v___y_3417_;
v___y_3405_ = v___y_3419_;
v___y_3406_ = v___y_3420_;
v___y_3407_ = v___y_3421_;
v___y_3408_ = v___y_3412_;
goto v___jp_3399_;
}
}
v___jp_3425_:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Lean_Meta_saveState___redArg(v_a_3015_, v_a_3017_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3437_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3436_);
lean_dec_ref(v___x_3435_);
lean_inc(v_snd_3026_);
lean_inc(v_trace_3009_);
v___x_3437_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3434_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_dec(v_a_3436_);
lean_dec(v_snd_3026_);
v___y_3400_ = v___y_3427_;
v___y_3401_ = v___y_3426_;
v___y_3402_ = v___y_3429_;
v___y_3403_ = v___y_3428_;
v___y_3404_ = v___y_3430_;
v___y_3405_ = v___y_3431_;
v___y_3406_ = v___y_3432_;
v___y_3407_ = v___y_3433_;
v___y_3408_ = v___x_3437_;
goto v___jp_3399_;
}
else
{
lean_object* v_a_3438_; uint8_t v___x_3439_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
v___x_3439_ = l_Lean_Exception_isInterrupt(v_a_3438_);
if (v___x_3439_ == 0)
{
uint8_t v___x_3440_; 
v___x_3440_ = l_Lean_Exception_isRuntime(v_a_3438_);
v___y_3412_ = v___x_3437_;
v___y_3413_ = v___y_3427_;
v___y_3414_ = v___y_3426_;
v___y_3415_ = v___y_3429_;
v___y_3416_ = v___y_3428_;
v___y_3417_ = v___y_3430_;
v___y_3418_ = v_a_3436_;
v___y_3419_ = v___y_3431_;
v___y_3420_ = v___y_3432_;
v___y_3421_ = v___y_3433_;
v___y_3422_ = v___x_3440_;
goto v___jp_3411_;
}
else
{
lean_dec(v_a_3438_);
v___y_3412_ = v___x_3437_;
v___y_3413_ = v___y_3427_;
v___y_3414_ = v___y_3426_;
v___y_3415_ = v___y_3429_;
v___y_3416_ = v___y_3428_;
v___y_3417_ = v___y_3430_;
v___y_3418_ = v_a_3436_;
v___y_3419_ = v___y_3431_;
v___y_3420_ = v___y_3432_;
v___y_3421_ = v___y_3433_;
v___y_3422_ = v___x_3439_;
goto v___jp_3411_;
}
}
}
else
{
lean_object* v_a_3441_; 
lean_dec(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3441_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3441_);
lean_dec_ref(v___x_3435_);
v___y_3369_ = v___y_3427_;
v___y_3370_ = v___y_3426_;
v___y_3371_ = v___y_3429_;
v___y_3372_ = v___y_3428_;
v___y_3373_ = v___y_3430_;
v___y_3374_ = v___y_3431_;
v_a_3375_ = v_a_3441_;
goto v___jp_3368_;
}
}
v___jp_3442_:
{
uint8_t v_commitIndependentGoals_3453_; lean_object* v___x_3454_; 
v_commitIndependentGoals_3453_ = lean_ctor_get_uint8(v_cfg_3008_, sizeof(void*)*4);
lean_inc(v___y_3450_);
v___x_3454_ = l_List_appendTR___redArg(v_a_3452_, v___y_3450_);
if (v_commitIndependentGoals_3453_ == 0)
{
lean_dec(v___y_3449_);
if (v___y_3451_ == 0)
{
v___y_3388_ = v___y_3444_;
v___y_3389_ = v___y_3443_;
v___y_3390_ = v___y_3446_;
v___y_3391_ = v___y_3445_;
v___y_3392_ = v___y_3447_;
v___y_3393_ = v___y_3448_;
v___y_3394_ = v___y_3450_;
v___y_3395_ = v___x_3454_;
goto v___jp_3387_;
}
else
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
lean_dec(v___x_3454_);
lean_dec(v___y_3450_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___x_3455_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3456_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3455_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_3378_ = v___y_3444_;
v___y_3379_ = v___y_3443_;
v___y_3380_ = v___y_3446_;
v___y_3381_ = v___y_3445_;
v___y_3382_ = v___y_3447_;
v___y_3383_ = v___y_3448_;
v___y_3384_ = v___x_3456_;
goto v___jp_3377_;
}
}
else
{
uint8_t v___x_3457_; 
v___x_3457_ = l_List_isEmpty___redArg(v___y_3450_);
if (v___x_3457_ == 0)
{
v___y_3426_ = v___y_3444_;
v___y_3427_ = v___y_3443_;
v___y_3428_ = v___y_3446_;
v___y_3429_ = v___y_3445_;
v___y_3430_ = v___y_3447_;
v___y_3431_ = v___y_3448_;
v___y_3432_ = v___y_3449_;
v___y_3433_ = v___y_3450_;
v___y_3434_ = v___x_3454_;
goto v___jp_3425_;
}
else
{
if (v___y_3451_ == 0)
{
lean_dec(v___y_3449_);
v___y_3388_ = v___y_3444_;
v___y_3389_ = v___y_3443_;
v___y_3390_ = v___y_3446_;
v___y_3391_ = v___y_3445_;
v___y_3392_ = v___y_3447_;
v___y_3393_ = v___y_3448_;
v___y_3394_ = v___y_3450_;
v___y_3395_ = v___x_3454_;
goto v___jp_3387_;
}
else
{
v___y_3426_ = v___y_3444_;
v___y_3427_ = v___y_3443_;
v___y_3428_ = v___y_3446_;
v___y_3429_ = v___y_3445_;
v___y_3430_ = v___y_3447_;
v___y_3431_ = v___y_3448_;
v___y_3432_ = v___y_3449_;
v___y_3433_ = v___y_3450_;
v___y_3434_ = v___x_3454_;
goto v___jp_3425_;
}
}
}
}
v___jp_3458_:
{
lean_object* v___x_3467_; 
v___x_3467_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3017_);
if (lean_obj_tag(v___x_3467_) == 0)
{
if (v___y_3466_ == 0)
{
lean_object* v_a_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3468_);
lean_dec_ref(v___x_3467_);
v___x_3469_ = lean_io_mono_nanos_now();
v___x_3470_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3033_, v___y_3466_, v_goals_3012_, v___y_3463_, v_a_3015_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3472_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref(v___x_3470_);
v___x_3472_ = l_List_reverse___redArg(v_a_3471_);
v___y_3318_ = v___y_3460_;
v___y_3319_ = v___y_3459_;
v___y_3320_ = v___y_3461_;
v___y_3321_ = v_a_3468_;
v___y_3322_ = v___y_3462_;
v___y_3323_ = v___y_3464_;
v___y_3324_ = v___y_3465_;
v___y_3325_ = v___x_3469_;
v___y_3326_ = v___y_3466_;
v_a_3327_ = v___x_3472_;
goto v___jp_3317_;
}
else
{
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3473_; 
v_a_3473_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3473_);
lean_dec_ref(v___x_3470_);
v___y_3318_ = v___y_3460_;
v___y_3319_ = v___y_3459_;
v___y_3320_ = v___y_3461_;
v___y_3321_ = v_a_3468_;
v___y_3322_ = v___y_3462_;
v___y_3323_ = v___y_3464_;
v___y_3324_ = v___y_3465_;
v___y_3325_ = v___x_3469_;
v___y_3326_ = v___y_3466_;
v_a_3327_ = v_a_3473_;
goto v___jp_3317_;
}
else
{
lean_object* v_a_3474_; 
lean_dec(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3474_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3474_);
lean_dec_ref(v___x_3470_);
v___y_3211_ = v___y_3459_;
v___y_3212_ = v___y_3460_;
v___y_3213_ = v_a_3468_;
v___y_3214_ = v___y_3461_;
v___y_3215_ = v___y_3462_;
v___y_3216_ = v___x_3469_;
v_a_3217_ = v_a_3474_;
goto v___jp_3210_;
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_a_3475_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3475_);
lean_dec_ref(v___x_3467_);
v___x_3476_ = lean_io_get_num_heartbeats();
v___x_3477_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3033_, v___y_3466_, v_goals_3012_, v___y_3463_, v_a_3015_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3479_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3477_);
v___x_3479_ = l_List_reverse___redArg(v_a_3478_);
v___y_3443_ = v___y_3459_;
v___y_3444_ = v___y_3460_;
v___y_3445_ = v_a_3475_;
v___y_3446_ = v___y_3461_;
v___y_3447_ = v___y_3462_;
v___y_3448_ = v___x_3476_;
v___y_3449_ = v___y_3464_;
v___y_3450_ = v___y_3465_;
v___y_3451_ = v___y_3466_;
v_a_3452_ = v___x_3479_;
goto v___jp_3442_;
}
else
{
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3480_; 
v_a_3480_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3480_);
lean_dec_ref(v___x_3477_);
v___y_3443_ = v___y_3459_;
v___y_3444_ = v___y_3460_;
v___y_3445_ = v_a_3475_;
v___y_3446_ = v___y_3461_;
v___y_3447_ = v___y_3462_;
v___y_3448_ = v___x_3476_;
v___y_3449_ = v___y_3464_;
v___y_3450_ = v___y_3465_;
v___y_3451_ = v___y_3466_;
v_a_3452_ = v_a_3480_;
goto v___jp_3442_;
}
else
{
lean_object* v_a_3481_; 
lean_dec(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3481_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3481_);
lean_dec_ref(v___x_3477_);
v___y_3369_ = v___y_3459_;
v___y_3370_ = v___y_3460_;
v___y_3371_ = v_a_3475_;
v___y_3372_ = v___y_3461_;
v___y_3373_ = v___y_3462_;
v___y_3374_ = v___x_3476_;
v_a_3375_ = v_a_3481_;
goto v___jp_3368_;
}
}
}
}
else
{
lean_object* v_a_3482_; 
lean_dec(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3459_);
lean_dec(v_snd_3026_);
lean_dec(v_goals_3012_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3482_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_a_3482_);
lean_dec_ref(v___x_3467_);
v___y_3150_ = v___y_3460_;
v___y_3151_ = v___y_3461_;
v_a_3152_ = v_a_3482_;
goto v___jp_3149_;
}
}
v___jp_3483_:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3487_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3486_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_3186_ = v___y_3484_;
v___y_3187_ = v___y_3485_;
v___y_3188_ = v___x_3487_;
goto v___jp_3185_;
}
v___jp_3488_:
{
uint8_t v___x_3495_; 
v___x_3495_ = l_List_isEmpty___redArg(v___y_3492_);
lean_dec(v___y_3492_);
if (v___x_3495_ == 0)
{
lean_dec(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___y_3484_ = v___y_3490_;
v___y_3485_ = v___y_3491_;
goto v___jp_3483_;
}
else
{
if (v___y_3489_ == 0)
{
lean_object* v___x_3496_; 
lean_inc(v_trace_3009_);
v___x_3496_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3493_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3498_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref(v___x_3496_);
v___x_3498_ = l_List_appendTR___redArg(v___y_3494_, v_a_3497_);
v___y_3137_ = v___y_3490_;
v___y_3138_ = v___y_3491_;
v_a_3139_ = v___x_3498_;
goto v___jp_3136_;
}
else
{
lean_dec(v___y_3494_);
v___y_3186_ = v___y_3490_;
v___y_3187_ = v___y_3491_;
v___y_3188_ = v___x_3496_;
goto v___jp_3185_;
}
}
else
{
lean_dec(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___y_3484_ = v___y_3490_;
v___y_3485_ = v___y_3491_;
goto v___jp_3483_;
}
}
}
v___jp_3499_:
{
uint8_t v_commitIndependentGoals_3506_; lean_object* v___x_3507_; 
v_commitIndependentGoals_3506_ = lean_ctor_get_uint8(v_cfg_3008_, sizeof(void*)*4);
lean_inc(v___y_3504_);
v___x_3507_ = l_List_appendTR___redArg(v_a_3505_, v___y_3504_);
if (v_commitIndependentGoals_3506_ == 0)
{
v___y_3489_ = v___y_3500_;
v___y_3490_ = v___y_3501_;
v___y_3491_ = v___y_3502_;
v___y_3492_ = v___y_3503_;
v___y_3493_ = v___x_3507_;
v___y_3494_ = v___y_3504_;
goto v___jp_3488_;
}
else
{
uint8_t v___x_3508_; 
v___x_3508_ = l_List_isEmpty___redArg(v___y_3504_);
if (v___x_3508_ == 0)
{
v___y_3173_ = v___y_3501_;
v___y_3174_ = v___y_3502_;
v___y_3175_ = v___y_3503_;
v___y_3176_ = v___x_3507_;
v___y_3177_ = v___y_3504_;
goto v___jp_3172_;
}
else
{
if (v___y_3500_ == 0)
{
v___y_3489_ = v___y_3500_;
v___y_3490_ = v___y_3501_;
v___y_3491_ = v___y_3502_;
v___y_3492_ = v___y_3503_;
v___y_3493_ = v___x_3507_;
v___y_3494_ = v___y_3504_;
goto v___jp_3488_;
}
else
{
v___y_3173_ = v___y_3501_;
v___y_3174_ = v___y_3502_;
v___y_3175_ = v___y_3503_;
v___y_3176_ = v___x_3507_;
v___y_3177_ = v___y_3504_;
goto v___jp_3172_;
}
}
}
}
v___jp_3509_:
{
lean_object* v___x_3513_; double v___x_3514_; double v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3513_ = lean_io_get_num_heartbeats();
v___x_3514_ = lean_float_of_nat(v___y_3511_);
v___x_3515_ = lean_float_of_nat(v___x_3513_);
v___x_3516_ = lean_box_float(v___x_3514_);
v___x_3517_ = lean_box_float(v___x_3515_);
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3516_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
v___x_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3519_, 0, v_a_3512_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
v___x_3520_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3009_, v_hasTrace_3033_, v___x_3115_, v_options_3031_, v___x_3118_, v___y_3510_, v___f_3114_, v___x_3519_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
return v___x_3520_;
}
v___jp_3521_:
{
lean_object* v___x_3525_; 
v___x_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_a_3524_);
v___y_3510_ = v___y_3522_;
v___y_3511_ = v___y_3523_;
v_a_3512_ = v___x_3525_;
goto v___jp_3509_;
}
v___jp_3526_:
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3530_, 0, v_a_3529_);
v___y_3510_ = v___y_3527_;
v___y_3511_ = v___y_3528_;
v_a_3512_ = v___x_3530_;
goto v___jp_3509_;
}
v___jp_3531_:
{
if (lean_obj_tag(v___y_3534_) == 0)
{
lean_object* v_a_3535_; 
v_a_3535_ = lean_ctor_get(v___y_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref(v___y_3534_);
v___y_3527_ = v___y_3532_;
v___y_3528_ = v___y_3533_;
v_a_3529_ = v_a_3535_;
goto v___jp_3526_;
}
else
{
lean_object* v_a_3536_; 
v_a_3536_ = lean_ctor_get(v___y_3534_, 0);
lean_inc(v_a_3536_);
lean_dec_ref(v___y_3534_);
v___y_3522_ = v___y_3532_;
v___y_3523_ = v___y_3533_;
v_a_3524_ = v_a_3536_;
goto v___jp_3521_;
}
}
v___jp_3537_:
{
lean_object* v___x_3545_; double v___x_3546_; double v___x_3547_; double v___x_3548_; double v___x_3549_; double v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3545_ = lean_io_mono_nanos_now();
v___x_3546_ = lean_float_of_nat(v___y_3540_);
v___x_3547_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3548_ = lean_float_div(v___x_3546_, v___x_3547_);
v___x_3549_ = lean_float_of_nat(v___x_3545_);
v___x_3550_ = lean_float_div(v___x_3549_, v___x_3547_);
v___x_3551_ = lean_box_float(v___x_3548_);
v___x_3552_ = lean_box_float(v___x_3550_);
v___x_3553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3551_);
lean_ctor_set(v___x_3553_, 1, v___x_3552_);
v___x_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3554_, 0, v_a_3544_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
lean_inc(v_trace_3009_);
v___x_3555_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3009_, v_hasTrace_3033_, v___x_3115_, v_options_3031_, v___y_3539_, v___y_3541_, v___y_3542_, v___x_3554_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_3532_ = v___y_3538_;
v___y_3533_ = v___y_3543_;
v___y_3534_ = v___x_3555_;
goto v___jp_3531_;
}
v___jp_3556_:
{
lean_object* v___x_3564_; 
v___x_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3564_, 0, v_a_3563_);
v___y_3538_ = v___y_3558_;
v___y_3539_ = v___y_3557_;
v___y_3540_ = v___y_3559_;
v___y_3541_ = v___y_3560_;
v___y_3542_ = v___y_3561_;
v___y_3543_ = v___y_3562_;
v_a_3544_ = v___x_3564_;
goto v___jp_3537_;
}
v___jp_3565_:
{
lean_object* v___x_3573_; 
v___x_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3573_, 0, v_a_3572_);
v___y_3538_ = v___y_3567_;
v___y_3539_ = v___y_3566_;
v___y_3540_ = v___y_3568_;
v___y_3541_ = v___y_3569_;
v___y_3542_ = v___y_3570_;
v___y_3543_ = v___y_3571_;
v_a_3544_ = v___x_3573_;
goto v___jp_3537_;
}
v___jp_3574_:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = l_List_appendTR___redArg(v___y_3579_, v___y_3581_);
v___x_3585_ = l_List_appendTR___redArg(v___x_3584_, v_a_3583_);
v___y_3566_ = v___y_3576_;
v___y_3567_ = v___y_3575_;
v___y_3568_ = v___y_3577_;
v___y_3569_ = v___y_3578_;
v___y_3570_ = v___y_3580_;
v___y_3571_ = v___y_3582_;
v_a_3572_ = v___x_3585_;
goto v___jp_3565_;
}
v___jp_3586_:
{
if (lean_obj_tag(v___y_3595_) == 0)
{
lean_object* v_a_3596_; 
v_a_3596_ = lean_ctor_get(v___y_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref(v___y_3595_);
v___y_3575_ = v___y_3588_;
v___y_3576_ = v___y_3587_;
v___y_3577_ = v___y_3589_;
v___y_3578_ = v___y_3590_;
v___y_3579_ = v___y_3591_;
v___y_3580_ = v___y_3592_;
v___y_3581_ = v___y_3593_;
v___y_3582_ = v___y_3594_;
v_a_3583_ = v_a_3596_;
goto v___jp_3574_;
}
else
{
lean_object* v_a_3597_; 
lean_dec(v___y_3593_);
lean_dec(v___y_3591_);
v_a_3597_ = lean_ctor_get(v___y_3595_, 0);
lean_inc(v_a_3597_);
lean_dec_ref(v___y_3595_);
v___y_3557_ = v___y_3587_;
v___y_3558_ = v___y_3588_;
v___y_3559_ = v___y_3589_;
v___y_3560_ = v___y_3590_;
v___y_3561_ = v___y_3592_;
v___y_3562_ = v___y_3594_;
v_a_3563_ = v_a_3597_;
goto v___jp_3556_;
}
}
v___jp_3598_:
{
if (v___y_3609_ == 0)
{
lean_object* v___x_3610_; 
lean_dec_ref(v___y_3605_);
v___x_3610_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3608_, v_a_3015_, v_a_3017_);
lean_dec_ref(v___y_3608_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_dec_ref(v___x_3610_);
v___y_3575_ = v___y_3600_;
v___y_3576_ = v___y_3599_;
v___y_3577_ = v___y_3601_;
v___y_3578_ = v___y_3602_;
v___y_3579_ = v___y_3603_;
v___y_3580_ = v___y_3604_;
v___y_3581_ = v___y_3606_;
v___y_3582_ = v___y_3607_;
v_a_3583_ = v_snd_3026_;
goto v___jp_3574_;
}
else
{
lean_object* v_a_3611_; 
lean_dec(v___y_3606_);
lean_dec(v___y_3603_);
lean_dec(v_snd_3026_);
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref(v___x_3610_);
v___y_3557_ = v___y_3599_;
v___y_3558_ = v___y_3600_;
v___y_3559_ = v___y_3601_;
v___y_3560_ = v___y_3602_;
v___y_3561_ = v___y_3604_;
v___y_3562_ = v___y_3607_;
v_a_3563_ = v_a_3611_;
goto v___jp_3556_;
}
}
else
{
lean_dec_ref(v___y_3608_);
lean_dec(v_snd_3026_);
v___y_3587_ = v___y_3599_;
v___y_3588_ = v___y_3600_;
v___y_3589_ = v___y_3601_;
v___y_3590_ = v___y_3602_;
v___y_3591_ = v___y_3603_;
v___y_3592_ = v___y_3604_;
v___y_3593_ = v___y_3606_;
v___y_3594_ = v___y_3607_;
v___y_3595_ = v___y_3605_;
goto v___jp_3586_;
}
}
v___jp_3612_:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Lean_Meta_saveState___redArg(v_a_3015_, v_a_3017_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v___x_3624_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref(v___x_3622_);
lean_inc(v_snd_3026_);
lean_inc(v_trace_3009_);
v___x_3624_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3619_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_dec(v_a_3623_);
lean_dec(v_snd_3026_);
v___y_3587_ = v___y_3614_;
v___y_3588_ = v___y_3613_;
v___y_3589_ = v___y_3615_;
v___y_3590_ = v___y_3616_;
v___y_3591_ = v___y_3617_;
v___y_3592_ = v___y_3618_;
v___y_3593_ = v___y_3620_;
v___y_3594_ = v___y_3621_;
v___y_3595_ = v___x_3624_;
goto v___jp_3586_;
}
else
{
lean_object* v_a_3625_; uint8_t v___x_3626_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
v___x_3626_ = l_Lean_Exception_isInterrupt(v_a_3625_);
if (v___x_3626_ == 0)
{
uint8_t v___x_3627_; 
v___x_3627_ = l_Lean_Exception_isRuntime(v_a_3625_);
v___y_3599_ = v___y_3614_;
v___y_3600_ = v___y_3613_;
v___y_3601_ = v___y_3615_;
v___y_3602_ = v___y_3616_;
v___y_3603_ = v___y_3617_;
v___y_3604_ = v___y_3618_;
v___y_3605_ = v___x_3624_;
v___y_3606_ = v___y_3620_;
v___y_3607_ = v___y_3621_;
v___y_3608_ = v_a_3623_;
v___y_3609_ = v___x_3627_;
goto v___jp_3598_;
}
else
{
lean_dec(v_a_3625_);
v___y_3599_ = v___y_3614_;
v___y_3600_ = v___y_3613_;
v___y_3601_ = v___y_3615_;
v___y_3602_ = v___y_3616_;
v___y_3603_ = v___y_3617_;
v___y_3604_ = v___y_3618_;
v___y_3605_ = v___x_3624_;
v___y_3606_ = v___y_3620_;
v___y_3607_ = v___y_3621_;
v___y_3608_ = v_a_3623_;
v___y_3609_ = v___x_3626_;
goto v___jp_3598_;
}
}
}
else
{
lean_object* v_a_3628_; 
lean_dec(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec(v___y_3617_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3628_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3628_);
lean_dec_ref(v___x_3622_);
v___y_3557_ = v___y_3614_;
v___y_3558_ = v___y_3613_;
v___y_3559_ = v___y_3615_;
v___y_3560_ = v___y_3616_;
v___y_3561_ = v___y_3618_;
v___y_3562_ = v___y_3621_;
v_a_3563_ = v_a_3628_;
goto v___jp_3556_;
}
}
v___jp_3629_:
{
if (lean_obj_tag(v___y_3636_) == 0)
{
lean_object* v_a_3637_; 
v_a_3637_ = lean_ctor_get(v___y_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref(v___y_3636_);
v___y_3566_ = v___y_3631_;
v___y_3567_ = v___y_3630_;
v___y_3568_ = v___y_3632_;
v___y_3569_ = v___y_3633_;
v___y_3570_ = v___y_3634_;
v___y_3571_ = v___y_3635_;
v_a_3572_ = v_a_3637_;
goto v___jp_3565_;
}
else
{
lean_object* v_a_3638_; 
v_a_3638_ = lean_ctor_get(v___y_3636_, 0);
lean_inc(v_a_3638_);
lean_dec_ref(v___y_3636_);
v___y_3557_ = v___y_3631_;
v___y_3558_ = v___y_3630_;
v___y_3559_ = v___y_3632_;
v___y_3560_ = v___y_3633_;
v___y_3561_ = v___y_3634_;
v___y_3562_ = v___y_3635_;
v_a_3563_ = v_a_3638_;
goto v___jp_3556_;
}
}
v___jp_3639_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3647_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3646_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_3630_ = v___y_3641_;
v___y_3631_ = v___y_3640_;
v___y_3632_ = v___y_3642_;
v___y_3633_ = v___y_3643_;
v___y_3634_ = v___y_3644_;
v___y_3635_ = v___y_3645_;
v___y_3636_ = v___x_3647_;
goto v___jp_3629_;
}
v___jp_3648_:
{
uint8_t v___x_3659_; 
v___x_3659_ = l_List_isEmpty___redArg(v___y_3656_);
lean_dec(v___y_3656_);
if (v___x_3659_ == 0)
{
lean_dec(v___y_3655_);
lean_dec(v___y_3653_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___y_3640_ = v___y_3650_;
v___y_3641_ = v___y_3649_;
v___y_3642_ = v___y_3651_;
v___y_3643_ = v___y_3652_;
v___y_3644_ = v___y_3654_;
v___y_3645_ = v___y_3658_;
goto v___jp_3639_;
}
else
{
if (v___y_3657_ == 0)
{
lean_object* v___x_3660_; 
lean_inc(v_trace_3009_);
v___x_3660_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3655_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3662_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref(v___x_3660_);
v___x_3662_ = l_List_appendTR___redArg(v___y_3653_, v_a_3661_);
v___y_3566_ = v___y_3650_;
v___y_3567_ = v___y_3649_;
v___y_3568_ = v___y_3651_;
v___y_3569_ = v___y_3652_;
v___y_3570_ = v___y_3654_;
v___y_3571_ = v___y_3658_;
v_a_3572_ = v___x_3662_;
goto v___jp_3565_;
}
else
{
lean_dec(v___y_3653_);
v___y_3630_ = v___y_3649_;
v___y_3631_ = v___y_3650_;
v___y_3632_ = v___y_3651_;
v___y_3633_ = v___y_3652_;
v___y_3634_ = v___y_3654_;
v___y_3635_ = v___y_3658_;
v___y_3636_ = v___x_3660_;
goto v___jp_3629_;
}
}
else
{
lean_dec(v___y_3655_);
lean_dec(v___y_3653_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___y_3640_ = v___y_3650_;
v___y_3641_ = v___y_3649_;
v___y_3642_ = v___y_3651_;
v___y_3643_ = v___y_3652_;
v___y_3644_ = v___y_3654_;
v___y_3645_ = v___y_3658_;
goto v___jp_3639_;
}
}
}
v___jp_3663_:
{
uint8_t v_commitIndependentGoals_3674_; lean_object* v___x_3675_; 
v_commitIndependentGoals_3674_ = lean_ctor_get_uint8(v_cfg_3008_, sizeof(void*)*4);
lean_inc(v___y_3668_);
v___x_3675_ = l_List_appendTR___redArg(v_a_3673_, v___y_3668_);
if (v_commitIndependentGoals_3674_ == 0)
{
v___y_3649_ = v___y_3664_;
v___y_3650_ = v___y_3665_;
v___y_3651_ = v___y_3666_;
v___y_3652_ = v___y_3667_;
v___y_3653_ = v___y_3668_;
v___y_3654_ = v___y_3669_;
v___y_3655_ = v___x_3675_;
v___y_3656_ = v___y_3670_;
v___y_3657_ = v___y_3671_;
v___y_3658_ = v___y_3672_;
goto v___jp_3648_;
}
else
{
uint8_t v___x_3676_; 
v___x_3676_ = l_List_isEmpty___redArg(v___y_3668_);
if (v___x_3676_ == 0)
{
v___y_3613_ = v___y_3664_;
v___y_3614_ = v___y_3665_;
v___y_3615_ = v___y_3666_;
v___y_3616_ = v___y_3667_;
v___y_3617_ = v___y_3668_;
v___y_3618_ = v___y_3669_;
v___y_3619_ = v___x_3675_;
v___y_3620_ = v___y_3670_;
v___y_3621_ = v___y_3672_;
goto v___jp_3612_;
}
else
{
if (v___y_3671_ == 0)
{
v___y_3649_ = v___y_3664_;
v___y_3650_ = v___y_3665_;
v___y_3651_ = v___y_3666_;
v___y_3652_ = v___y_3667_;
v___y_3653_ = v___y_3668_;
v___y_3654_ = v___y_3669_;
v___y_3655_ = v___x_3675_;
v___y_3656_ = v___y_3670_;
v___y_3657_ = v___y_3671_;
v___y_3658_ = v___y_3672_;
goto v___jp_3648_;
}
else
{
v___y_3613_ = v___y_3664_;
v___y_3614_ = v___y_3665_;
v___y_3615_ = v___y_3666_;
v___y_3616_ = v___y_3667_;
v___y_3617_ = v___y_3668_;
v___y_3618_ = v___y_3669_;
v___y_3619_ = v___x_3675_;
v___y_3620_ = v___y_3670_;
v___y_3621_ = v___y_3672_;
goto v___jp_3612_;
}
}
}
}
v___jp_3677_:
{
lean_object* v___x_3685_; double v___x_3686_; double v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3685_ = lean_io_get_num_heartbeats();
v___x_3686_ = lean_float_of_nat(v___y_3682_);
v___x_3687_ = lean_float_of_nat(v___x_3685_);
v___x_3688_ = lean_box_float(v___x_3686_);
v___x_3689_ = lean_box_float(v___x_3687_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3691_, 0, v_a_3684_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
lean_inc(v_trace_3009_);
v___x_3692_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3009_, v_hasTrace_3033_, v___x_3115_, v_options_3031_, v___y_3679_, v___y_3680_, v___y_3681_, v___x_3691_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_3532_ = v___y_3678_;
v___y_3533_ = v___y_3683_;
v___y_3534_ = v___x_3692_;
goto v___jp_3531_;
}
v___jp_3693_:
{
lean_object* v___x_3701_; 
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v_a_3700_);
v___y_3678_ = v___y_3695_;
v___y_3679_ = v___y_3694_;
v___y_3680_ = v___y_3696_;
v___y_3681_ = v___y_3697_;
v___y_3682_ = v___y_3698_;
v___y_3683_ = v___y_3699_;
v_a_3684_ = v___x_3701_;
goto v___jp_3677_;
}
v___jp_3702_:
{
lean_object* v___x_3710_; 
v___x_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3710_, 0, v_a_3709_);
v___y_3678_ = v___y_3704_;
v___y_3679_ = v___y_3703_;
v___y_3680_ = v___y_3705_;
v___y_3681_ = v___y_3706_;
v___y_3682_ = v___y_3707_;
v___y_3683_ = v___y_3708_;
v_a_3684_ = v___x_3710_;
goto v___jp_3677_;
}
v___jp_3711_:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = l_List_appendTR___redArg(v___y_3715_, v___y_3718_);
v___x_3722_ = l_List_appendTR___redArg(v___x_3721_, v_a_3720_);
v___y_3703_ = v___y_3713_;
v___y_3704_ = v___y_3712_;
v___y_3705_ = v___y_3714_;
v___y_3706_ = v___y_3716_;
v___y_3707_ = v___y_3717_;
v___y_3708_ = v___y_3719_;
v_a_3709_ = v___x_3722_;
goto v___jp_3702_;
}
v___jp_3723_:
{
if (lean_obj_tag(v___y_3732_) == 0)
{
lean_object* v_a_3733_; 
v_a_3733_ = lean_ctor_get(v___y_3732_, 0);
lean_inc(v_a_3733_);
lean_dec_ref(v___y_3732_);
v___y_3712_ = v___y_3725_;
v___y_3713_ = v___y_3724_;
v___y_3714_ = v___y_3726_;
v___y_3715_ = v___y_3727_;
v___y_3716_ = v___y_3728_;
v___y_3717_ = v___y_3730_;
v___y_3718_ = v___y_3729_;
v___y_3719_ = v___y_3731_;
v_a_3720_ = v_a_3733_;
goto v___jp_3711_;
}
else
{
lean_object* v_a_3734_; 
lean_dec(v___y_3729_);
lean_dec(v___y_3727_);
v_a_3734_ = lean_ctor_get(v___y_3732_, 0);
lean_inc(v_a_3734_);
lean_dec_ref(v___y_3732_);
v___y_3694_ = v___y_3724_;
v___y_3695_ = v___y_3725_;
v___y_3696_ = v___y_3726_;
v___y_3697_ = v___y_3728_;
v___y_3698_ = v___y_3730_;
v___y_3699_ = v___y_3731_;
v_a_3700_ = v_a_3734_;
goto v___jp_3693_;
}
}
v___jp_3735_:
{
if (v___y_3746_ == 0)
{
lean_object* v___x_3747_; 
lean_dec_ref(v___y_3742_);
v___x_3747_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3738_, v_a_3015_, v_a_3017_);
lean_dec_ref(v___y_3738_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_dec_ref(v___x_3747_);
v___y_3712_ = v___y_3737_;
v___y_3713_ = v___y_3736_;
v___y_3714_ = v___y_3739_;
v___y_3715_ = v___y_3740_;
v___y_3716_ = v___y_3741_;
v___y_3717_ = v___y_3744_;
v___y_3718_ = v___y_3743_;
v___y_3719_ = v___y_3745_;
v_a_3720_ = v_snd_3026_;
goto v___jp_3711_;
}
else
{
lean_object* v_a_3748_; 
lean_dec(v___y_3743_);
lean_dec(v___y_3740_);
lean_dec(v_snd_3026_);
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_a_3748_);
lean_dec_ref(v___x_3747_);
v___y_3694_ = v___y_3736_;
v___y_3695_ = v___y_3737_;
v___y_3696_ = v___y_3739_;
v___y_3697_ = v___y_3741_;
v___y_3698_ = v___y_3744_;
v___y_3699_ = v___y_3745_;
v_a_3700_ = v_a_3748_;
goto v___jp_3693_;
}
}
else
{
lean_dec_ref(v___y_3738_);
lean_dec(v_snd_3026_);
v___y_3724_ = v___y_3736_;
v___y_3725_ = v___y_3737_;
v___y_3726_ = v___y_3739_;
v___y_3727_ = v___y_3740_;
v___y_3728_ = v___y_3741_;
v___y_3729_ = v___y_3743_;
v___y_3730_ = v___y_3744_;
v___y_3731_ = v___y_3745_;
v___y_3732_ = v___y_3742_;
goto v___jp_3723_;
}
}
v___jp_3749_:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Lean_Meta_saveState___redArg(v_a_3015_, v_a_3017_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3761_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref(v___x_3759_);
lean_inc(v_snd_3026_);
lean_inc(v_trace_3009_);
v___x_3761_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3757_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_dec(v_a_3760_);
lean_dec(v_snd_3026_);
v___y_3724_ = v___y_3751_;
v___y_3725_ = v___y_3750_;
v___y_3726_ = v___y_3752_;
v___y_3727_ = v___y_3753_;
v___y_3728_ = v___y_3754_;
v___y_3729_ = v___y_3756_;
v___y_3730_ = v___y_3755_;
v___y_3731_ = v___y_3758_;
v___y_3732_ = v___x_3761_;
goto v___jp_3723_;
}
else
{
lean_object* v_a_3762_; uint8_t v___x_3763_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
v___x_3763_ = l_Lean_Exception_isInterrupt(v_a_3762_);
if (v___x_3763_ == 0)
{
uint8_t v___x_3764_; 
v___x_3764_ = l_Lean_Exception_isRuntime(v_a_3762_);
v___y_3736_ = v___y_3751_;
v___y_3737_ = v___y_3750_;
v___y_3738_ = v_a_3760_;
v___y_3739_ = v___y_3752_;
v___y_3740_ = v___y_3753_;
v___y_3741_ = v___y_3754_;
v___y_3742_ = v___x_3761_;
v___y_3743_ = v___y_3756_;
v___y_3744_ = v___y_3755_;
v___y_3745_ = v___y_3758_;
v___y_3746_ = v___x_3764_;
goto v___jp_3735_;
}
else
{
lean_dec(v_a_3762_);
v___y_3736_ = v___y_3751_;
v___y_3737_ = v___y_3750_;
v___y_3738_ = v_a_3760_;
v___y_3739_ = v___y_3752_;
v___y_3740_ = v___y_3753_;
v___y_3741_ = v___y_3754_;
v___y_3742_ = v___x_3761_;
v___y_3743_ = v___y_3756_;
v___y_3744_ = v___y_3755_;
v___y_3745_ = v___y_3758_;
v___y_3746_ = v___x_3763_;
goto v___jp_3735_;
}
}
}
else
{
lean_object* v_a_3765_; 
lean_dec(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec(v___y_3753_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3765_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3765_);
lean_dec_ref(v___x_3759_);
v___y_3694_ = v___y_3751_;
v___y_3695_ = v___y_3750_;
v___y_3696_ = v___y_3752_;
v___y_3697_ = v___y_3754_;
v___y_3698_ = v___y_3755_;
v___y_3699_ = v___y_3758_;
v_a_3700_ = v_a_3765_;
goto v___jp_3693_;
}
}
v___jp_3766_:
{
if (lean_obj_tag(v___y_3773_) == 0)
{
lean_object* v_a_3774_; 
v_a_3774_ = lean_ctor_get(v___y_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref(v___y_3773_);
v___y_3703_ = v___y_3768_;
v___y_3704_ = v___y_3767_;
v___y_3705_ = v___y_3769_;
v___y_3706_ = v___y_3770_;
v___y_3707_ = v___y_3771_;
v___y_3708_ = v___y_3772_;
v_a_3709_ = v_a_3774_;
goto v___jp_3702_;
}
else
{
lean_object* v_a_3775_; 
v_a_3775_ = lean_ctor_get(v___y_3773_, 0);
lean_inc(v_a_3775_);
lean_dec_ref(v___y_3773_);
v___y_3694_ = v___y_3768_;
v___y_3695_ = v___y_3767_;
v___y_3696_ = v___y_3769_;
v___y_3697_ = v___y_3770_;
v___y_3698_ = v___y_3771_;
v___y_3699_ = v___y_3772_;
v_a_3700_ = v_a_3775_;
goto v___jp_3693_;
}
}
v___jp_3776_:
{
lean_object* v___x_3785_; 
lean_inc(v_trace_3009_);
v___x_3785_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3783_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3787_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref(v___x_3785_);
v___x_3787_ = l_List_appendTR___redArg(v___y_3780_, v_a_3786_);
v___y_3703_ = v___y_3778_;
v___y_3704_ = v___y_3777_;
v___y_3705_ = v___y_3779_;
v___y_3706_ = v___y_3781_;
v___y_3707_ = v___y_3782_;
v___y_3708_ = v___y_3784_;
v_a_3709_ = v___x_3787_;
goto v___jp_3702_;
}
else
{
lean_dec(v___y_3780_);
v___y_3767_ = v___y_3777_;
v___y_3768_ = v___y_3778_;
v___y_3769_ = v___y_3779_;
v___y_3770_ = v___y_3781_;
v___y_3771_ = v___y_3782_;
v___y_3772_ = v___y_3784_;
v___y_3773_ = v___x_3785_;
goto v___jp_3766_;
}
}
v___jp_3788_:
{
uint8_t v___x_3799_; 
v___x_3799_ = l_List_isEmpty___redArg(v___y_3796_);
lean_dec(v___y_3796_);
if (v___x_3799_ == 0)
{
if (v___y_3798_ == 0)
{
v___y_3777_ = v___y_3790_;
v___y_3778_ = v___y_3789_;
v___y_3779_ = v___y_3791_;
v___y_3780_ = v___y_3792_;
v___y_3781_ = v___y_3793_;
v___y_3782_ = v___y_3795_;
v___y_3783_ = v___y_3794_;
v___y_3784_ = v___y_3797_;
goto v___jp_3776_;
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
lean_dec(v___y_3794_);
lean_dec(v___y_3792_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3801_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3800_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_3767_ = v___y_3790_;
v___y_3768_ = v___y_3789_;
v___y_3769_ = v___y_3791_;
v___y_3770_ = v___y_3793_;
v___y_3771_ = v___y_3795_;
v___y_3772_ = v___y_3797_;
v___y_3773_ = v___x_3801_;
goto v___jp_3766_;
}
}
else
{
v___y_3777_ = v___y_3790_;
v___y_3778_ = v___y_3789_;
v___y_3779_ = v___y_3791_;
v___y_3780_ = v___y_3792_;
v___y_3781_ = v___y_3793_;
v___y_3782_ = v___y_3795_;
v___y_3783_ = v___y_3794_;
v___y_3784_ = v___y_3797_;
goto v___jp_3776_;
}
}
v___jp_3802_:
{
uint8_t v_commitIndependentGoals_3813_; lean_object* v___x_3814_; 
v_commitIndependentGoals_3813_ = lean_ctor_get_uint8(v_cfg_3008_, sizeof(void*)*4);
lean_inc(v___y_3806_);
v___x_3814_ = l_List_appendTR___redArg(v_a_3812_, v___y_3806_);
if (v_commitIndependentGoals_3813_ == 0)
{
v___y_3789_ = v___y_3803_;
v___y_3790_ = v___y_3804_;
v___y_3791_ = v___y_3805_;
v___y_3792_ = v___y_3806_;
v___y_3793_ = v___y_3807_;
v___y_3794_ = v___x_3814_;
v___y_3795_ = v___y_3809_;
v___y_3796_ = v___y_3808_;
v___y_3797_ = v___y_3811_;
v___y_3798_ = v___y_3810_;
goto v___jp_3788_;
}
else
{
uint8_t v___x_3815_; 
v___x_3815_ = l_List_isEmpty___redArg(v___y_3806_);
if (v___x_3815_ == 0)
{
v___y_3750_ = v___y_3804_;
v___y_3751_ = v___y_3803_;
v___y_3752_ = v___y_3805_;
v___y_3753_ = v___y_3806_;
v___y_3754_ = v___y_3807_;
v___y_3755_ = v___y_3809_;
v___y_3756_ = v___y_3808_;
v___y_3757_ = v___x_3814_;
v___y_3758_ = v___y_3811_;
goto v___jp_3749_;
}
else
{
if (v___x_3030_ == 0)
{
v___y_3789_ = v___y_3803_;
v___y_3790_ = v___y_3804_;
v___y_3791_ = v___y_3805_;
v___y_3792_ = v___y_3806_;
v___y_3793_ = v___y_3807_;
v___y_3794_ = v___x_3814_;
v___y_3795_ = v___y_3809_;
v___y_3796_ = v___y_3808_;
v___y_3797_ = v___y_3811_;
v___y_3798_ = v___y_3810_;
goto v___jp_3788_;
}
else
{
v___y_3750_ = v___y_3804_;
v___y_3751_ = v___y_3803_;
v___y_3752_ = v___y_3805_;
v___y_3753_ = v___y_3806_;
v___y_3754_ = v___y_3807_;
v___y_3755_ = v___y_3809_;
v___y_3756_ = v___y_3808_;
v___y_3757_ = v___x_3814_;
v___y_3758_ = v___y_3811_;
goto v___jp_3749_;
}
}
}
}
v___jp_3816_:
{
lean_object* v___x_3825_; 
v___x_3825_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3017_);
if (lean_obj_tag(v___x_3825_) == 0)
{
if (v___y_3824_ == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref(v___x_3825_);
v___x_3827_ = lean_io_mono_nanos_now();
v___x_3828_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3824_, v___x_3030_, v_goals_3012_, v___y_3820_, v_a_3015_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref(v___x_3828_);
v___x_3830_ = l_List_reverse___redArg(v_a_3829_);
v___y_3664_ = v___y_3818_;
v___y_3665_ = v___y_3817_;
v___y_3666_ = v___x_3827_;
v___y_3667_ = v_a_3826_;
v___y_3668_ = v___y_3819_;
v___y_3669_ = v___y_3821_;
v___y_3670_ = v___y_3822_;
v___y_3671_ = v___y_3824_;
v___y_3672_ = v___y_3823_;
v_a_3673_ = v___x_3830_;
goto v___jp_3663_;
}
else
{
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3831_; 
v_a_3831_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3831_);
lean_dec_ref(v___x_3828_);
v___y_3664_ = v___y_3818_;
v___y_3665_ = v___y_3817_;
v___y_3666_ = v___x_3827_;
v___y_3667_ = v_a_3826_;
v___y_3668_ = v___y_3819_;
v___y_3669_ = v___y_3821_;
v___y_3670_ = v___y_3822_;
v___y_3671_ = v___y_3824_;
v___y_3672_ = v___y_3823_;
v_a_3673_ = v_a_3831_;
goto v___jp_3663_;
}
else
{
lean_object* v_a_3832_; 
lean_dec(v___y_3822_);
lean_dec(v___y_3819_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3832_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3832_);
lean_dec_ref(v___x_3828_);
v___y_3557_ = v___y_3817_;
v___y_3558_ = v___y_3818_;
v___y_3559_ = v___x_3827_;
v___y_3560_ = v_a_3826_;
v___y_3561_ = v___y_3821_;
v___y_3562_ = v___y_3823_;
v_a_3563_ = v_a_3832_;
goto v___jp_3556_;
}
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v_a_3833_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3833_);
lean_dec_ref(v___x_3825_);
v___x_3834_ = lean_io_get_num_heartbeats();
v___x_3835_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3824_, v___x_3030_, v_goals_3012_, v___y_3820_, v_a_3015_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3837_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref(v___x_3835_);
v___x_3837_ = l_List_reverse___redArg(v_a_3836_);
v___y_3803_ = v___y_3817_;
v___y_3804_ = v___y_3818_;
v___y_3805_ = v_a_3833_;
v___y_3806_ = v___y_3819_;
v___y_3807_ = v___y_3821_;
v___y_3808_ = v___y_3822_;
v___y_3809_ = v___x_3834_;
v___y_3810_ = v___y_3824_;
v___y_3811_ = v___y_3823_;
v_a_3812_ = v___x_3837_;
goto v___jp_3802_;
}
else
{
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3838_; 
v_a_3838_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3838_);
lean_dec_ref(v___x_3835_);
v___y_3803_ = v___y_3817_;
v___y_3804_ = v___y_3818_;
v___y_3805_ = v_a_3833_;
v___y_3806_ = v___y_3819_;
v___y_3807_ = v___y_3821_;
v___y_3808_ = v___y_3822_;
v___y_3809_ = v___x_3834_;
v___y_3810_ = v___y_3824_;
v___y_3811_ = v___y_3823_;
v_a_3812_ = v_a_3838_;
goto v___jp_3802_;
}
else
{
lean_object* v_a_3839_; 
lean_dec(v___y_3822_);
lean_dec(v___y_3819_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3839_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3839_);
lean_dec_ref(v___x_3835_);
v___y_3694_ = v___y_3817_;
v___y_3695_ = v___y_3818_;
v___y_3696_ = v_a_3833_;
v___y_3697_ = v___y_3821_;
v___y_3698_ = v___x_3834_;
v___y_3699_ = v___y_3823_;
v_a_3700_ = v_a_3839_;
goto v___jp_3693_;
}
}
}
}
else
{
lean_object* v_a_3840_; 
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec(v_snd_3026_);
lean_dec(v_goals_3012_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3840_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3840_);
lean_dec_ref(v___x_3825_);
v___y_3522_ = v___y_3818_;
v___y_3523_ = v___y_3823_;
v_a_3524_ = v_a_3840_;
goto v___jp_3521_;
}
}
v___jp_3841_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3845_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3844_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
v___y_3532_ = v___y_3842_;
v___y_3533_ = v___y_3843_;
v___y_3534_ = v___x_3845_;
goto v___jp_3531_;
}
v___jp_3846_:
{
uint8_t v___x_3853_; 
v___x_3853_ = l_List_isEmpty___redArg(v___y_3851_);
lean_dec(v___y_3851_);
if (v___x_3853_ == 0)
{
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___y_3842_ = v___y_3847_;
v___y_3843_ = v___y_3852_;
goto v___jp_3841_;
}
else
{
if (v___y_3850_ == 0)
{
lean_object* v___x_3854_; 
lean_inc(v_trace_3009_);
v___x_3854_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3848_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3856_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref(v___x_3854_);
v___x_3856_ = l_List_appendTR___redArg(v___y_3849_, v_a_3855_);
v___y_3527_ = v___y_3847_;
v___y_3528_ = v___y_3852_;
v_a_3529_ = v___x_3856_;
goto v___jp_3526_;
}
else
{
lean_dec(v___y_3849_);
v___y_3532_ = v___y_3847_;
v___y_3533_ = v___y_3852_;
v___y_3534_ = v___x_3854_;
goto v___jp_3531_;
}
}
else
{
lean_dec(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v___y_3842_ = v___y_3847_;
v___y_3843_ = v___y_3852_;
goto v___jp_3841_;
}
}
}
v___jp_3857_:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = l_List_appendTR___redArg(v___y_3859_, v___y_3860_);
v___x_3864_ = l_List_appendTR___redArg(v___x_3863_, v_a_3862_);
v___y_3527_ = v___y_3858_;
v___y_3528_ = v___y_3861_;
v_a_3529_ = v___x_3864_;
goto v___jp_3526_;
}
v___jp_3865_:
{
if (lean_obj_tag(v___y_3870_) == 0)
{
lean_object* v_a_3871_; 
v_a_3871_ = lean_ctor_get(v___y_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref(v___y_3870_);
v___y_3858_ = v___y_3866_;
v___y_3859_ = v___y_3867_;
v___y_3860_ = v___y_3868_;
v___y_3861_ = v___y_3869_;
v_a_3862_ = v_a_3871_;
goto v___jp_3857_;
}
else
{
lean_object* v_a_3872_; 
lean_dec(v___y_3868_);
lean_dec(v___y_3867_);
v_a_3872_ = lean_ctor_get(v___y_3870_, 0);
lean_inc(v_a_3872_);
lean_dec_ref(v___y_3870_);
v___y_3522_ = v___y_3866_;
v___y_3523_ = v___y_3869_;
v_a_3524_ = v_a_3872_;
goto v___jp_3521_;
}
}
v___jp_3873_:
{
if (v___y_3880_ == 0)
{
lean_object* v___x_3881_; 
lean_dec_ref(v___y_3874_);
v___x_3881_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3879_, v_a_3015_, v_a_3017_);
lean_dec_ref(v___y_3879_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_dec_ref(v___x_3881_);
v___y_3858_ = v___y_3875_;
v___y_3859_ = v___y_3876_;
v___y_3860_ = v___y_3877_;
v___y_3861_ = v___y_3878_;
v_a_3862_ = v_snd_3026_;
goto v___jp_3857_;
}
else
{
lean_object* v_a_3882_; 
lean_dec(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec(v_snd_3026_);
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref(v___x_3881_);
v___y_3522_ = v___y_3875_;
v___y_3523_ = v___y_3878_;
v_a_3524_ = v_a_3882_;
goto v___jp_3521_;
}
}
else
{
lean_dec_ref(v___y_3879_);
lean_dec(v_snd_3026_);
v___y_3866_ = v___y_3875_;
v___y_3867_ = v___y_3876_;
v___y_3868_ = v___y_3877_;
v___y_3869_ = v___y_3878_;
v___y_3870_ = v___y_3874_;
goto v___jp_3865_;
}
}
v___jp_3883_:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_Meta_saveState___redArg(v_a_3015_, v_a_3017_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v___x_3891_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref(v___x_3889_);
lean_inc(v_snd_3026_);
lean_inc(v_trace_3009_);
v___x_3891_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v___y_3885_, v_snd_3026_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_dec(v_a_3890_);
lean_dec(v_snd_3026_);
v___y_3866_ = v___y_3884_;
v___y_3867_ = v___y_3886_;
v___y_3868_ = v___y_3887_;
v___y_3869_ = v___y_3888_;
v___y_3870_ = v___x_3891_;
goto v___jp_3865_;
}
else
{
lean_object* v_a_3892_; uint8_t v___x_3893_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
v___x_3893_ = l_Lean_Exception_isInterrupt(v_a_3892_);
if (v___x_3893_ == 0)
{
uint8_t v___x_3894_; 
v___x_3894_ = l_Lean_Exception_isRuntime(v_a_3892_);
v___y_3874_ = v___x_3891_;
v___y_3875_ = v___y_3884_;
v___y_3876_ = v___y_3886_;
v___y_3877_ = v___y_3887_;
v___y_3878_ = v___y_3888_;
v___y_3879_ = v_a_3890_;
v___y_3880_ = v___x_3894_;
goto v___jp_3873_;
}
else
{
lean_dec(v_a_3892_);
v___y_3874_ = v___x_3891_;
v___y_3875_ = v___y_3884_;
v___y_3876_ = v___y_3886_;
v___y_3877_ = v___y_3887_;
v___y_3878_ = v___y_3888_;
v___y_3879_ = v_a_3890_;
v___y_3880_ = v___x_3893_;
goto v___jp_3873_;
}
}
}
else
{
lean_object* v_a_3895_; 
lean_dec(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3895_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3895_);
lean_dec_ref(v___x_3889_);
v___y_3522_ = v___y_3884_;
v___y_3523_ = v___y_3888_;
v_a_3524_ = v_a_3895_;
goto v___jp_3521_;
}
}
v___jp_3896_:
{
uint8_t v_commitIndependentGoals_3903_; lean_object* v___x_3904_; 
v_commitIndependentGoals_3903_ = lean_ctor_get_uint8(v_cfg_3008_, sizeof(void*)*4);
lean_inc(v___y_3898_);
v___x_3904_ = l_List_appendTR___redArg(v_a_3902_, v___y_3898_);
if (v_commitIndependentGoals_3903_ == 0)
{
v___y_3847_ = v___y_3897_;
v___y_3848_ = v___x_3904_;
v___y_3849_ = v___y_3898_;
v___y_3850_ = v___y_3899_;
v___y_3851_ = v___y_3900_;
v___y_3852_ = v___y_3901_;
goto v___jp_3846_;
}
else
{
uint8_t v___x_3905_; 
v___x_3905_ = l_List_isEmpty___redArg(v___y_3898_);
if (v___x_3905_ == 0)
{
v___y_3884_ = v___y_3897_;
v___y_3885_ = v___x_3904_;
v___y_3886_ = v___y_3898_;
v___y_3887_ = v___y_3900_;
v___y_3888_ = v___y_3901_;
goto v___jp_3883_;
}
else
{
if (v___y_3899_ == 0)
{
v___y_3847_ = v___y_3897_;
v___y_3848_ = v___x_3904_;
v___y_3849_ = v___y_3898_;
v___y_3850_ = v___y_3899_;
v___y_3851_ = v___y_3900_;
v___y_3852_ = v___y_3901_;
goto v___jp_3846_;
}
else
{
v___y_3884_ = v___y_3897_;
v___y_3885_ = v___x_3904_;
v___y_3886_ = v___y_3898_;
v___y_3887_ = v___y_3900_;
v___y_3888_ = v___y_3901_;
goto v___jp_3883_;
}
}
}
}
v___jp_3906_:
{
lean_object* v___x_3907_; 
v___x_3907_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3017_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref(v___x_3907_);
v___x_3909_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3910_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3031_, v___x_3909_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = lean_io_mono_nanos_now();
v___x_3912_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3025_, v___f_3034_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v_fst_3914_; lean_object* v_snd_3915_; lean_object* v___x_3916_; lean_object* v___f_3917_; lean_object* v___x_3918_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref(v___x_3912_);
v_fst_3914_ = lean_ctor_get(v_a_3913_, 0);
lean_inc_n(v_fst_3914_, 2);
v_snd_3915_ = lean_ctor_get(v_a_3913_, 1);
lean_inc(v_snd_3915_);
lean_dec(v_a_3913_);
v___x_3916_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3915_, v___x_3022_);
lean_inc(v___x_3916_);
v___f_3917_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3917_, 0, v_fst_3914_);
lean_closure_set(v___f_3917_, 1, v___x_3916_);
v___x_3918_ = lean_box(0);
if (v___x_3118_ == 0)
{
lean_object* v___x_3919_; uint8_t v___x_3920_; 
v___x_3919_ = l_Lean_trace_profiler;
v___x_3920_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3031_, v___x_3919_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; 
lean_dec_ref(v___f_3917_);
v___x_3921_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3033_, v___x_3910_, v_goals_3012_, v___x_3918_, v_a_3015_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3923_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref(v___x_3921_);
v___x_3923_ = l_List_reverse___redArg(v_a_3922_);
v___y_3500_ = v___x_3920_;
v___y_3501_ = v_a_3908_;
v___y_3502_ = v___x_3911_;
v___y_3503_ = v_fst_3914_;
v___y_3504_ = v___x_3916_;
v_a_3505_ = v___x_3923_;
goto v___jp_3499_;
}
else
{
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3924_; 
v_a_3924_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3924_);
lean_dec_ref(v___x_3921_);
v___y_3500_ = v___x_3920_;
v___y_3501_ = v_a_3908_;
v___y_3502_ = v___x_3911_;
v___y_3503_ = v_fst_3914_;
v___y_3504_ = v___x_3916_;
v_a_3505_ = v_a_3924_;
goto v___jp_3499_;
}
else
{
lean_object* v_a_3925_; 
lean_dec(v___x_3916_);
lean_dec(v_fst_3914_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3925_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3925_);
lean_dec_ref(v___x_3921_);
v___y_3150_ = v_a_3908_;
v___y_3151_ = v___x_3911_;
v_a_3152_ = v_a_3925_;
goto v___jp_3149_;
}
}
}
else
{
v___y_3459_ = v___f_3917_;
v___y_3460_ = v_a_3908_;
v___y_3461_ = v___x_3911_;
v___y_3462_ = v___x_3118_;
v___y_3463_ = v___x_3918_;
v___y_3464_ = v_fst_3914_;
v___y_3465_ = v___x_3916_;
v___y_3466_ = v___x_3910_;
goto v___jp_3458_;
}
}
else
{
v___y_3459_ = v___f_3917_;
v___y_3460_ = v_a_3908_;
v___y_3461_ = v___x_3911_;
v___y_3462_ = v___x_3118_;
v___y_3463_ = v___x_3918_;
v___y_3464_ = v_fst_3914_;
v___y_3465_ = v___x_3916_;
v___y_3466_ = v___x_3910_;
goto v___jp_3458_;
}
}
else
{
lean_object* v_a_3926_; 
lean_dec(v_snd_3026_);
lean_dec(v_goals_3012_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3926_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3926_);
lean_dec_ref(v___x_3912_);
v___y_3150_ = v_a_3908_;
v___y_3151_ = v___x_3911_;
v_a_3152_ = v_a_3926_;
goto v___jp_3149_;
}
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
lean_del_object(v___x_3028_);
v___x_3927_ = lean_io_get_num_heartbeats();
v___x_3928_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3025_, v___f_3034_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v_fst_3930_; lean_object* v_snd_3931_; lean_object* v___x_3932_; lean_object* v___f_3933_; lean_object* v___x_3934_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref(v___x_3928_);
v_fst_3930_ = lean_ctor_get(v_a_3929_, 0);
lean_inc_n(v_fst_3930_, 2);
v_snd_3931_ = lean_ctor_get(v_a_3929_, 1);
lean_inc(v_snd_3931_);
lean_dec(v_a_3929_);
v___x_3932_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3931_, v___x_3022_);
lean_inc(v___x_3932_);
v___f_3933_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3933_, 0, v_fst_3930_);
lean_closure_set(v___f_3933_, 1, v___x_3932_);
v___x_3934_ = lean_box(0);
if (v___x_3118_ == 0)
{
lean_object* v___x_3935_; uint8_t v___x_3936_; 
v___x_3935_ = l_Lean_trace_profiler;
v___x_3936_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3031_, v___x_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; 
lean_dec_ref(v___f_3933_);
v___x_3937_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3910_, v___x_3030_, v_goals_3012_, v___x_3934_, v_a_3015_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3939_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref(v___x_3937_);
v___x_3939_ = l_List_reverse___redArg(v_a_3938_);
v___y_3897_ = v_a_3908_;
v___y_3898_ = v___x_3932_;
v___y_3899_ = v___x_3936_;
v___y_3900_ = v_fst_3930_;
v___y_3901_ = v___x_3927_;
v_a_3902_ = v___x_3939_;
goto v___jp_3896_;
}
else
{
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3940_; 
v_a_3940_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3940_);
lean_dec_ref(v___x_3937_);
v___y_3897_ = v_a_3908_;
v___y_3898_ = v___x_3932_;
v___y_3899_ = v___x_3936_;
v___y_3900_ = v_fst_3930_;
v___y_3901_ = v___x_3927_;
v_a_3902_ = v_a_3940_;
goto v___jp_3896_;
}
else
{
lean_object* v_a_3941_; 
lean_dec(v___x_3932_);
lean_dec(v_fst_3930_);
lean_dec(v_snd_3026_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3941_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3941_);
lean_dec_ref(v___x_3937_);
v___y_3522_ = v_a_3908_;
v___y_3523_ = v___x_3927_;
v_a_3524_ = v_a_3941_;
goto v___jp_3521_;
}
}
}
else
{
v___y_3817_ = v___x_3118_;
v___y_3818_ = v_a_3908_;
v___y_3819_ = v___x_3932_;
v___y_3820_ = v___x_3934_;
v___y_3821_ = v___f_3933_;
v___y_3822_ = v_fst_3930_;
v___y_3823_ = v___x_3927_;
v___y_3824_ = v___x_3910_;
goto v___jp_3816_;
}
}
else
{
v___y_3817_ = v___x_3118_;
v___y_3818_ = v_a_3908_;
v___y_3819_ = v___x_3932_;
v___y_3820_ = v___x_3934_;
v___y_3821_ = v___f_3933_;
v___y_3822_ = v_fst_3930_;
v___y_3823_ = v___x_3927_;
v___y_3824_ = v___x_3910_;
goto v___jp_3816_;
}
}
else
{
lean_object* v_a_3942_; 
lean_dec(v_snd_3026_);
lean_dec(v_goals_3012_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec_ref(v_cfg_3008_);
v_a_3942_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3942_);
lean_dec_ref(v___x_3928_);
v___y_3522_ = v_a_3908_;
v___y_3523_ = v___x_3927_;
v_a_3524_ = v_a_3942_;
goto v___jp_3521_;
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec_ref(v___f_3114_);
lean_dec_ref(v___f_3034_);
lean_del_object(v___x_3028_);
lean_dec(v_snd_3026_);
lean_dec(v_fst_3025_);
lean_dec(v_goals_3012_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
v_a_3943_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3907_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3907_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
}
}
else
{
lean_object* v_maxDepth_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_del_object(v___x_3028_);
lean_dec(v_snd_3026_);
lean_dec(v_fst_3025_);
lean_dec(v_goals_3012_);
v_maxDepth_4231_ = lean_ctor_get(v_cfg_3008_, 0);
lean_inc(v_maxDepth_4231_);
v___x_4232_ = lean_box(0);
v___x_4233_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_3008_, v_trace_3009_, v_next_3010_, v_orig_3011_, v_maxDepth_4231_, v_remaining_3013_, v___x_4232_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
return v___x_4233_;
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec(v_remaining_3013_);
lean_dec(v_goals_3012_);
lean_dec(v_orig_3011_);
lean_dec_ref(v_next_3010_);
lean_dec(v_trace_3009_);
lean_dec_ref(v_cfg_3008_);
v_a_4235_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_3023_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_3023_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
v___jp_3019_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3021_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3020_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
return v___x_3021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_4243_, lean_object* v_trace_4244_, lean_object* v_next_4245_, lean_object* v_orig_4246_, lean_object* v_goals_4247_, lean_object* v_remaining_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4243_, v_trace_4244_, v_next_4245_, v_orig_4246_, v_goals_4247_, v_remaining_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_);
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_4255_, lean_object* v_00_u03b2_4256_, lean_object* v_L_4257_, lean_object* v_f_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_4257_, v_f_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_4265_, lean_object* v_00_u03b2_4266_, lean_object* v_L_4267_, lean_object* v_f_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_4265_, v_00_u03b2_4266_, v_L_4267_, v_f_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_4275_, lean_object* v_x_4276_, lean_object* v_x_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_4275_, v_x_4276_, v_x_4277_, v___y_4279_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_4284_, lean_object* v_x_4285_, lean_object* v_x_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
uint8_t v___x_60526__boxed_4292_; lean_object* v_res_4293_; 
v___x_60526__boxed_4292_ = lean_unbox(v___x_4284_);
v_res_4293_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_60526__boxed_4292_, v_x_4285_, v_x_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_4294_, uint8_t v___x_4295_, lean_object* v_x_4296_, lean_object* v_x_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v___x_4303_; 
v___x_4303_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_4294_, v___x_4295_, v_x_4296_, v_x_4297_, v___y_4299_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_4304_, lean_object* v___x_4305_, lean_object* v_x_4306_, lean_object* v_x_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
uint8_t v___x_60552__boxed_4313_; uint8_t v___x_60553__boxed_4314_; lean_object* v_res_4315_; 
v___x_60552__boxed_4313_ = lean_unbox(v___x_4304_);
v___x_60553__boxed_4314_ = lean_unbox(v___x_4305_);
v_res_4315_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_60552__boxed_4313_, v___x_60553__boxed_4314_, v_x_4306_, v_x_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_4316_, lean_object* v_00_u03b2_4317_, lean_object* v_f_4318_, lean_object* v_x_4319_, lean_object* v_x_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_4318_, v_x_4319_, v_x_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4327_, lean_object* v_00_u03b2_4328_, lean_object* v_f_4329_, lean_object* v_x_4330_, lean_object* v_x_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_4327_, v_00_u03b2_4328_, v_f_4329_, v_x_4330_, v_x_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
return v_res_4337_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_4338_, lean_object* v_00_u03b2_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v___x_4342_; 
v___x_4342_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_4340_, v_a_4341_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_4343_, lean_object* v_00_u03b2_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_){
_start:
{
lean_object* v___x_4347_; 
v___x_4347_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_4345_, v_a_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_4348_, lean_object* v_g_4349_, lean_object* v_f_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_){
_start:
{
lean_object* v___x_4356_; 
lean_inc(v___y_4354_);
lean_inc_ref(v___y_4353_);
lean_inc(v___y_4352_);
lean_inc_ref(v___y_4351_);
v___x_4356_ = lean_apply_6(v_next_4348_, v_g_4349_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, lean_box(0));
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v___x_4358_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref(v___x_4356_);
v___x_4358_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_4357_, v_f_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_);
return v___x_4358_;
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
lean_dec_ref(v_f_4350_);
v_a_4359_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4356_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4356_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_4367_, lean_object* v_g_4368_, lean_object* v_f_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_4367_, v_g_4368_, v_f_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_4376_, lean_object* v_trace_4377_, lean_object* v_next_4378_, lean_object* v_goals_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_){
_start:
{
lean_object* v_resolve_4385_; lean_object* v___x_4386_; 
v_resolve_4385_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_4385_, 0, v_next_4378_);
lean_inc_n(v_goals_4379_, 2);
v___x_4386_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4376_, v_trace_4377_, v_resolve_4385_, v_goals_4379_, v_goals_4379_, v_goals_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_4387_, lean_object* v_trace_4388_, lean_object* v_next_4389_, lean_object* v_goals_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_4387_, v_trace_4388_, v_next_4389_, v_goals_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
lean_dec(v_a_4394_);
lean_dec_ref(v_a_4393_);
lean_dec(v_a_4392_);
lean_dec_ref(v_a_4391_);
return v_res_4396_;
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

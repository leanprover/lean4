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
lean_object* v___x_165_; lean_object* v_traceState_166_; lean_object* v_traces_167_; lean_object* v___x_168_; lean_object* v_traceState_169_; lean_object* v_env_170_; lean_object* v_nextMacroScope_171_; lean_object* v_ngen_172_; lean_object* v_auxDeclNGen_173_; lean_object* v_cache_174_; lean_object* v_messages_175_; lean_object* v_infoState_176_; lean_object* v_snapshotTasks_177_; lean_object* v_newDecls_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_197_; 
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
v_newDecls_178_ = lean_ctor_get(v___x_168_, 9);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_197_ == 0)
{
v___x_180_ = v___x_168_;
v_isShared_181_ = v_isSharedCheck_197_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_newDecls_178_);
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
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_197_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
uint64_t v_tid_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_195_; 
v_tid_182_ = lean_ctor_get_uint64(v_traceState_169_, sizeof(void*)*1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_traceState_169_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v_traceState_169_, 0);
lean_dec(v_unused_196_);
v___x_184_ = v_traceState_169_;
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
else
{
lean_dec(v_traceState_169_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_186_);
lean_ctor_set_uint64(v_reuseFailAlloc_194_, sizeof(void*)*1, v_tid_182_);
v___x_188_ = v_reuseFailAlloc_194_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_190_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 4, v___x_188_);
v___x_190_ = v___x_180_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_env_170_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_nextMacroScope_171_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_ngen_172_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v_auxDeclNGen_173_);
lean_ctor_set(v_reuseFailAlloc_193_, 4, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_193_, 5, v_cache_174_);
lean_ctor_set(v_reuseFailAlloc_193_, 6, v_messages_175_);
lean_ctor_set(v_reuseFailAlloc_193_, 7, v_infoState_176_);
lean_ctor_set(v_reuseFailAlloc_193_, 8, v_snapshotTasks_177_);
lean_ctor_set(v_reuseFailAlloc_193_, 9, v_newDecls_178_);
v___x_190_ = v_reuseFailAlloc_193_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_st_ref_set(v___y_163_, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v_traces_167_);
return v___x_192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___boxed(lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v___y_198_);
lean_dec(v___y_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v___y_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___boxed(lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
return v_res_212_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(lean_object* v_opts_213_, lean_object* v_opt_214_){
_start:
{
lean_object* v_name_215_; lean_object* v_defValue_216_; lean_object* v_map_217_; lean_object* v___x_218_; 
v_name_215_ = lean_ctor_get(v_opt_214_, 0);
v_defValue_216_ = lean_ctor_get(v_opt_214_, 1);
v_map_217_ = lean_ctor_get(v_opts_213_, 0);
v___x_218_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_217_, v_name_215_);
if (lean_obj_tag(v___x_218_) == 0)
{
uint8_t v___x_219_; 
v___x_219_ = lean_unbox(v_defValue_216_);
return v___x_219_;
}
else
{
lean_object* v_val_220_; 
v_val_220_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_val_220_);
lean_dec_ref(v___x_218_);
if (lean_obj_tag(v_val_220_) == 1)
{
uint8_t v_v_221_; 
v_v_221_ = lean_ctor_get_uint8(v_val_220_, 0);
lean_dec_ref(v_val_220_);
return v_v_221_;
}
else
{
uint8_t v___x_222_; 
lean_dec(v_val_220_);
v___x_222_ = lean_unbox(v_defValue_216_);
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___boxed(lean_object* v_opts_223_, lean_object* v_opt_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_223_, v_opt_224_);
lean_dec_ref(v_opt_224_);
lean_dec_ref(v_opts_223_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(lean_object* v_x_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Meta_saveState___redArg(v___y_229_, v___y_231_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref(v___x_233_);
lean_inc(v___y_231_);
lean_inc_ref(v___y_230_);
lean_inc(v___y_229_);
lean_inc_ref(v___y_228_);
v___x_235_ = lean_apply_5(v_x_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, lean_box(0));
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_a_234_);
v_a_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_244_ == 0)
{
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v_a_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_274_; 
v_a_245_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_274_ == 0)
{
v___x_247_ = v___x_235_;
v_isShared_248_ = v_isSharedCheck_274_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_235_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_274_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
uint8_t v___y_250_; uint8_t v___x_272_; 
v___x_272_ = l_Lean_Exception_isInterrupt(v_a_245_);
if (v___x_272_ == 0)
{
uint8_t v___x_273_; 
lean_inc(v_a_245_);
v___x_273_ = l_Lean_Exception_isRuntime(v_a_245_);
v___y_250_ = v___x_273_;
goto v___jp_249_;
}
else
{
v___y_250_ = v___x_272_;
goto v___jp_249_;
}
v___jp_249_:
{
if (v___y_250_ == 0)
{
lean_object* v___x_251_; 
lean_del_object(v___x_247_);
lean_dec(v_a_245_);
v___x_251_ = l_Lean_Meta_SavedState_restore___redArg(v_a_234_, v___y_229_, v___y_231_);
lean_dec(v_a_234_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_259_; 
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_259_ == 0)
{
lean_object* v_unused_260_; 
v_unused_260_ = lean_ctor_get(v___x_251_, 0);
lean_dec(v_unused_260_);
v___x_253_ = v___x_251_;
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
else
{
lean_dec(v___x_251_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_259_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = lean_box(0);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_255_);
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_a_261_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_251_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_251_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
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
else
{
lean_object* v___x_270_; 
lean_dec(v_a_234_);
if (v_isShared_248_ == 0)
{
v___x_270_ = v___x_247_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_245_);
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
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref(v_x_227_);
v_a_275_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_233_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_233_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___boxed(lean_object* v_x_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v_x_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object* v_00_u03b1_290_, lean_object* v_x_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object* v_00_u03b1_298_, lean_object* v_x_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_00_u03b1_298_, v_x_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(lean_object* v_msgData_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v_env_313_; lean_object* v___x_314_; lean_object* v_mctx_315_; lean_object* v_lctx_316_; lean_object* v_options_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_312_ = lean_st_ref_get(v___y_310_);
v_env_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc_ref(v_env_313_);
lean_dec(v___x_312_);
v___x_314_ = lean_st_ref_get(v___y_308_);
v_mctx_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc_ref(v_mctx_315_);
lean_dec(v___x_314_);
v_lctx_316_ = lean_ctor_get(v___y_307_, 2);
v_options_317_ = lean_ctor_get(v___y_309_, 2);
lean_inc_ref(v_options_317_);
lean_inc_ref(v_lctx_316_);
v___x_318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_318_, 0, v_env_313_);
lean_ctor_set(v___x_318_, 1, v_mctx_315_);
lean_ctor_set(v___x_318_, 2, v_lctx_316_);
lean_ctor_set(v___x_318_, 3, v_options_317_);
v___x_319_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_msgData_306_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___boxed(lean_object* v_msgData_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msgData_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_327_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0));
v___x_330_ = l_Lean_stringToMessageData(v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object* v_x_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object* v_x_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(v_x_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec_ref(v_x_339_);
return v_res_345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0));
v___x_348_ = l_Lean_stringToMessageData(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object* v_x_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object* v_x_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(v_x_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec_ref(v_x_357_);
return v_res_363_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0));
v___x_366_ = l_Lean_stringToMessageData(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object* v_x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(v_x_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec_ref(v_x_375_);
return v_res_381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object* v_x_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object* v_x_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(v_x_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v_x_393_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(lean_object* v_opts_400_, lean_object* v_opt_401_){
_start:
{
lean_object* v_name_402_; lean_object* v_defValue_403_; lean_object* v_map_404_; lean_object* v___x_405_; 
v_name_402_ = lean_ctor_get(v_opt_401_, 0);
v_defValue_403_ = lean_ctor_get(v_opt_401_, 1);
v_map_404_ = lean_ctor_get(v_opts_400_, 0);
v___x_405_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_404_, v_name_402_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_inc(v_defValue_403_);
return v_defValue_403_;
}
else
{
lean_object* v_val_406_; 
v_val_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_val_406_);
lean_dec_ref(v___x_405_);
if (lean_obj_tag(v_val_406_) == 3)
{
lean_object* v_v_407_; 
v_v_407_ = lean_ctor_get(v_val_406_, 0);
lean_inc(v_v_407_);
lean_dec_ref(v_val_406_);
return v_v_407_;
}
else
{
lean_dec(v_val_406_);
lean_inc(v_defValue_403_);
return v_defValue_403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6___boxed(lean_object* v_opts_408_, lean_object* v_opt_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_408_, v_opt_409_);
lean_dec_ref(v_opt_409_);
lean_dec_ref(v_opts_408_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4_spec__7(size_t v_sz_411_, size_t v_i_412_, lean_object* v_bs_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = lean_usize_dec_lt(v_i_412_, v_sz_411_);
if (v___x_414_ == 0)
{
return v_bs_413_;
}
else
{
lean_object* v_v_415_; lean_object* v_msg_416_; lean_object* v___x_417_; lean_object* v_bs_x27_418_; size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; 
v_v_415_ = lean_array_uget_borrowed(v_bs_413_, v_i_412_);
v_msg_416_ = lean_ctor_get(v_v_415_, 1);
lean_inc_ref(v_msg_416_);
v___x_417_ = lean_unsigned_to_nat(0u);
v_bs_x27_418_ = lean_array_uset(v_bs_413_, v_i_412_, v___x_417_);
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_add(v_i_412_, v___x_419_);
v___x_421_ = lean_array_uset(v_bs_x27_418_, v_i_412_, v_msg_416_);
v_i_412_ = v___x_420_;
v_bs_413_ = v___x_421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4_spec__7___boxed(lean_object* v_sz_423_, lean_object* v_i_424_, lean_object* v_bs_425_){
_start:
{
size_t v_sz_boxed_426_; size_t v_i_boxed_427_; lean_object* v_res_428_; 
v_sz_boxed_426_ = lean_unbox_usize(v_sz_423_);
lean_dec(v_sz_423_);
v_i_boxed_427_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_res_428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4_spec__7(v_sz_boxed_426_, v_i_boxed_427_, v_bs_425_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object* v_oldTraces_429_, lean_object* v_data_430_, lean_object* v_ref_431_, lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_fileName_438_; lean_object* v_fileMap_439_; lean_object* v_options_440_; lean_object* v_currRecDepth_441_; lean_object* v_maxRecDepth_442_; lean_object* v_ref_443_; lean_object* v_currNamespace_444_; lean_object* v_openDecls_445_; lean_object* v_initHeartbeats_446_; lean_object* v_maxHeartbeats_447_; lean_object* v_quotContext_448_; lean_object* v_currMacroScope_449_; uint8_t v_diag_450_; lean_object* v_cancelTk_x3f_451_; uint8_t v_suppressElabErrors_452_; lean_object* v_inheritedTraceOptions_453_; lean_object* v___x_454_; lean_object* v_traceState_455_; lean_object* v_traces_456_; lean_object* v_ref_457_; lean_object* v___x_458_; lean_object* v___x_459_; size_t v_sz_460_; size_t v___x_461_; lean_object* v___x_462_; lean_object* v_msg_463_; lean_object* v___x_464_; lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_503_; 
v_fileName_438_ = lean_ctor_get(v___y_435_, 0);
v_fileMap_439_ = lean_ctor_get(v___y_435_, 1);
v_options_440_ = lean_ctor_get(v___y_435_, 2);
v_currRecDepth_441_ = lean_ctor_get(v___y_435_, 3);
v_maxRecDepth_442_ = lean_ctor_get(v___y_435_, 4);
v_ref_443_ = lean_ctor_get(v___y_435_, 5);
v_currNamespace_444_ = lean_ctor_get(v___y_435_, 6);
v_openDecls_445_ = lean_ctor_get(v___y_435_, 7);
v_initHeartbeats_446_ = lean_ctor_get(v___y_435_, 8);
v_maxHeartbeats_447_ = lean_ctor_get(v___y_435_, 9);
v_quotContext_448_ = lean_ctor_get(v___y_435_, 10);
v_currMacroScope_449_ = lean_ctor_get(v___y_435_, 11);
v_diag_450_ = lean_ctor_get_uint8(v___y_435_, sizeof(void*)*14);
v_cancelTk_x3f_451_ = lean_ctor_get(v___y_435_, 12);
v_suppressElabErrors_452_ = lean_ctor_get_uint8(v___y_435_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_453_ = lean_ctor_get(v___y_435_, 13);
v___x_454_ = lean_st_ref_get(v___y_436_);
v_traceState_455_ = lean_ctor_get(v___x_454_, 4);
lean_inc_ref(v_traceState_455_);
lean_dec(v___x_454_);
v_traces_456_ = lean_ctor_get(v_traceState_455_, 0);
lean_inc_ref(v_traces_456_);
lean_dec_ref(v_traceState_455_);
v_ref_457_ = l_Lean_replaceRef(v_ref_431_, v_ref_443_);
lean_inc_ref(v_inheritedTraceOptions_453_);
lean_inc(v_cancelTk_x3f_451_);
lean_inc(v_currMacroScope_449_);
lean_inc(v_quotContext_448_);
lean_inc(v_maxHeartbeats_447_);
lean_inc(v_initHeartbeats_446_);
lean_inc(v_openDecls_445_);
lean_inc(v_currNamespace_444_);
lean_inc(v_maxRecDepth_442_);
lean_inc(v_currRecDepth_441_);
lean_inc_ref(v_options_440_);
lean_inc_ref(v_fileMap_439_);
lean_inc_ref(v_fileName_438_);
v___x_458_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_458_, 0, v_fileName_438_);
lean_ctor_set(v___x_458_, 1, v_fileMap_439_);
lean_ctor_set(v___x_458_, 2, v_options_440_);
lean_ctor_set(v___x_458_, 3, v_currRecDepth_441_);
lean_ctor_set(v___x_458_, 4, v_maxRecDepth_442_);
lean_ctor_set(v___x_458_, 5, v_ref_457_);
lean_ctor_set(v___x_458_, 6, v_currNamespace_444_);
lean_ctor_set(v___x_458_, 7, v_openDecls_445_);
lean_ctor_set(v___x_458_, 8, v_initHeartbeats_446_);
lean_ctor_set(v___x_458_, 9, v_maxHeartbeats_447_);
lean_ctor_set(v___x_458_, 10, v_quotContext_448_);
lean_ctor_set(v___x_458_, 11, v_currMacroScope_449_);
lean_ctor_set(v___x_458_, 12, v_cancelTk_x3f_451_);
lean_ctor_set(v___x_458_, 13, v_inheritedTraceOptions_453_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*14, v_diag_450_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*14 + 1, v_suppressElabErrors_452_);
v___x_459_ = l_Lean_PersistentArray_toArray___redArg(v_traces_456_);
lean_dec_ref(v_traces_456_);
v_sz_460_ = lean_array_size(v___x_459_);
v___x_461_ = ((size_t)0ULL);
v___x_462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4_spec__7(v_sz_460_, v___x_461_, v___x_459_);
v_msg_463_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_463_, 0, v_data_430_);
lean_ctor_set(v_msg_463_, 1, v_msg_432_);
lean_ctor_set(v_msg_463_, 2, v___x_462_);
v___x_464_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_463_, v___y_433_, v___y_434_, v___x_458_, v___y_436_);
lean_dec_ref(v___x_458_);
v_a_465_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_503_ == 0)
{
v___x_467_ = v___x_464_;
v_isShared_468_ = v_isSharedCheck_503_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_464_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_503_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v_traceState_470_; lean_object* v_env_471_; lean_object* v_nextMacroScope_472_; lean_object* v_ngen_473_; lean_object* v_auxDeclNGen_474_; lean_object* v_cache_475_; lean_object* v_messages_476_; lean_object* v_infoState_477_; lean_object* v_snapshotTasks_478_; lean_object* v_newDecls_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_502_; 
v___x_469_ = lean_st_ref_take(v___y_436_);
v_traceState_470_ = lean_ctor_get(v___x_469_, 4);
v_env_471_ = lean_ctor_get(v___x_469_, 0);
v_nextMacroScope_472_ = lean_ctor_get(v___x_469_, 1);
v_ngen_473_ = lean_ctor_get(v___x_469_, 2);
v_auxDeclNGen_474_ = lean_ctor_get(v___x_469_, 3);
v_cache_475_ = lean_ctor_get(v___x_469_, 5);
v_messages_476_ = lean_ctor_get(v___x_469_, 6);
v_infoState_477_ = lean_ctor_get(v___x_469_, 7);
v_snapshotTasks_478_ = lean_ctor_get(v___x_469_, 8);
v_newDecls_479_ = lean_ctor_get(v___x_469_, 9);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_502_ == 0)
{
v___x_481_ = v___x_469_;
v_isShared_482_ = v_isSharedCheck_502_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_newDecls_479_);
lean_inc(v_snapshotTasks_478_);
lean_inc(v_infoState_477_);
lean_inc(v_messages_476_);
lean_inc(v_cache_475_);
lean_inc(v_traceState_470_);
lean_inc(v_auxDeclNGen_474_);
lean_inc(v_ngen_473_);
lean_inc(v_nextMacroScope_472_);
lean_inc(v_env_471_);
lean_dec(v___x_469_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_502_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
uint64_t v_tid_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_500_; 
v_tid_483_ = lean_ctor_get_uint64(v_traceState_470_, sizeof(void*)*1);
v_isSharedCheck_500_ = !lean_is_exclusive(v_traceState_470_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v_traceState_470_, 0);
lean_dec(v_unused_501_);
v___x_485_ = v_traceState_470_;
v_isShared_486_ = v_isSharedCheck_500_;
goto v_resetjp_484_;
}
else
{
lean_dec(v_traceState_470_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_500_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_ref_431_);
lean_ctor_set(v___x_487_, 1, v_a_465_);
v___x_488_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_429_, v___x_487_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_488_);
v___x_490_ = v___x_485_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_488_);
lean_ctor_set_uint64(v_reuseFailAlloc_499_, sizeof(void*)*1, v_tid_483_);
v___x_490_ = v_reuseFailAlloc_499_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 4, v___x_490_);
v___x_492_ = v___x_481_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_env_471_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_nextMacroScope_472_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v_ngen_473_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_auxDeclNGen_474_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_498_, 5, v_cache_475_);
lean_ctor_set(v_reuseFailAlloc_498_, 6, v_messages_476_);
lean_ctor_set(v_reuseFailAlloc_498_, 7, v_infoState_477_);
lean_ctor_set(v_reuseFailAlloc_498_, 8, v_snapshotTasks_478_);
lean_ctor_set(v_reuseFailAlloc_498_, 9, v_newDecls_479_);
v___x_492_ = v_reuseFailAlloc_498_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_493_ = lean_st_ref_set(v___y_436_, v___x_492_);
v___x_494_ = lean_box(0);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_494_);
v___x_496_ = v___x_467_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object* v_oldTraces_504_, lean_object* v_data_505_, lean_object* v_ref_506_, lean_object* v_msg_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_oldTraces_504_, v_data_505_, v_ref_506_, v_msg_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_a_516_ = lean_ctor_get(v_x_514_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_514_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v_x_514_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v_x_514_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
lean_ctor_set_tag(v___x_518_, 1);
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
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
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
v_a_524_ = lean_ctor_get(v_x_514_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_514_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v_x_514_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v_x_514_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 0);
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg___boxed(lean_object* v_x_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_x_532_);
return v_res_534_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object* v_e_535_){
_start:
{
if (lean_obj_tag(v_e_535_) == 0)
{
uint8_t v___x_536_; 
v___x_536_ = 2;
return v___x_536_;
}
else
{
lean_object* v_a_537_; 
v_a_537_ = lean_ctor_get(v_e_535_, 0);
if (lean_obj_tag(v_a_537_) == 0)
{
uint8_t v___x_538_; 
v___x_538_ = 1;
return v___x_538_;
}
else
{
uint8_t v___x_539_; 
v___x_539_ = 0;
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object* v_e_540_){
_start:
{
uint8_t v_res_541_; lean_object* v_r_542_; 
v_res_541_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_e_540_);
lean_dec_ref(v_e_540_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2(void){
_start:
{
lean_object* v___x_546_; double v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_float_of_nat(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3));
v___x_550_ = l_Lean_stringToMessageData(v___x_549_);
return v___x_550_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5(void){
_start:
{
lean_object* v___x_551_; double v___x_552_; 
v___x_551_ = lean_unsigned_to_nat(1000u);
v___x_552_ = lean_float_of_nat(v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_cls_553_, uint8_t v_collapsed_554_, lean_object* v_tag_555_, lean_object* v_opts_556_, uint8_t v_clsEnabled_557_, lean_object* v_oldTraces_558_, lean_object* v_msg_559_, lean_object* v_resStartStop_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_666_; 
v_fst_566_ = lean_ctor_get(v_resStartStop_560_, 0);
v_snd_567_ = lean_ctor_get(v_resStartStop_560_, 1);
v_isSharedCheck_666_ = !lean_is_exclusive(v_resStartStop_560_);
if (v_isSharedCheck_666_ == 0)
{
v___x_569_ = v_resStartStop_560_;
v_isShared_570_ = v_isSharedCheck_666_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_snd_567_);
lean_inc(v_fst_566_);
lean_dec(v_resStartStop_560_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_666_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v_data_574_; lean_object* v_fst_585_; lean_object* v_snd_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_665_; 
v_fst_585_ = lean_ctor_get(v_snd_567_, 0);
v_snd_586_ = lean_ctor_get(v_snd_567_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v_snd_567_);
if (v_isSharedCheck_665_ == 0)
{
v___x_588_ = v_snd_567_;
v_isShared_589_ = v_isSharedCheck_665_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_snd_586_);
lean_inc(v_fst_585_);
lean_dec(v_snd_567_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_665_;
goto v_resetjp_587_;
}
v___jp_571_:
{
lean_object* v___x_575_; 
lean_inc(v___y_572_);
v___x_575_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_oldTraces_558_, v_data_574_, v___y_572_, v___y_573_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; 
lean_dec_ref(v___x_575_);
v___x_576_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_fst_566_);
return v___x_576_;
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_fst_566_);
v_a_577_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_575_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
v_resetjp_587_:
{
lean_object* v___x_590_; uint8_t v___x_591_; lean_object* v___y_593_; lean_object* v_a_594_; uint8_t v___y_618_; double v___y_650_; 
v___x_590_ = l_Lean_trace_profiler;
v___x_591_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_556_, v___x_590_);
if (v___x_591_ == 0)
{
v___y_618_ = v___x_591_;
goto v___jp_617_;
}
else
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = l_Lean_trace_profiler_useHeartbeats;
v___x_656_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_556_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; double v___x_659_; double v___x_660_; double v___x_661_; 
v___x_657_ = l_Lean_trace_profiler_threshold;
v___x_658_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_556_, v___x_657_);
v___x_659_ = lean_float_of_nat(v___x_658_);
v___x_660_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5);
v___x_661_ = lean_float_div(v___x_659_, v___x_660_);
v___y_650_ = v___x_661_;
goto v___jp_649_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; double v___x_664_; 
v___x_662_ = l_Lean_trace_profiler_threshold;
v___x_663_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_556_, v___x_662_);
v___x_664_ = lean_float_of_nat(v___x_663_);
v___y_650_ = v___x_664_;
goto v___jp_649_;
}
}
v___jp_592_:
{
uint8_t v_result_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v_result_595_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_fst_566_);
v___x_596_ = l_Lean_TraceResult_toEmoji(v_result_595_);
v___x_597_ = l_Lean_stringToMessageData(v___x_596_);
v___x_598_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 7);
lean_ctor_set(v___x_588_, 1, v___x_598_);
lean_ctor_set(v___x_588_, 0, v___x_597_);
v___x_600_ = v___x_588_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_598_);
v___x_600_ = v_reuseFailAlloc_611_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v_m_602_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 7);
lean_ctor_set(v___x_569_, 1, v_a_594_);
lean_ctor_set(v___x_569_, 0, v___x_600_);
v_m_602_ = v___x_569_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_a_594_);
v_m_602_ = v_reuseFailAlloc_610_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; double v___x_605_; lean_object* v_data_606_; 
v___x_603_ = lean_box(v_result_595_);
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
v___x_605_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
lean_inc_ref(v_tag_555_);
lean_inc_ref(v___x_604_);
lean_inc(v_cls_553_);
v_data_606_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_606_, 0, v_cls_553_);
lean_ctor_set(v_data_606_, 1, v___x_604_);
lean_ctor_set(v_data_606_, 2, v_tag_555_);
lean_ctor_set_float(v_data_606_, sizeof(void*)*3, v___x_605_);
lean_ctor_set_float(v_data_606_, sizeof(void*)*3 + 8, v___x_605_);
lean_ctor_set_uint8(v_data_606_, sizeof(void*)*3 + 16, v_collapsed_554_);
if (v___x_591_ == 0)
{
lean_dec_ref(v___x_604_);
lean_dec(v_snd_586_);
lean_dec(v_fst_585_);
lean_dec_ref(v_tag_555_);
lean_dec(v_cls_553_);
v___y_572_ = v___y_593_;
v___y_573_ = v_m_602_;
v_data_574_ = v_data_606_;
goto v___jp_571_;
}
else
{
lean_object* v_data_607_; double v___x_608_; double v___x_609_; 
lean_dec_ref(v_data_606_);
v_data_607_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_607_, 0, v_cls_553_);
lean_ctor_set(v_data_607_, 1, v___x_604_);
lean_ctor_set(v_data_607_, 2, v_tag_555_);
v___x_608_ = lean_unbox_float(v_fst_585_);
lean_dec(v_fst_585_);
lean_ctor_set_float(v_data_607_, sizeof(void*)*3, v___x_608_);
v___x_609_ = lean_unbox_float(v_snd_586_);
lean_dec(v_snd_586_);
lean_ctor_set_float(v_data_607_, sizeof(void*)*3 + 8, v___x_609_);
lean_ctor_set_uint8(v_data_607_, sizeof(void*)*3 + 16, v_collapsed_554_);
v___y_572_ = v___y_593_;
v___y_573_ = v_m_602_;
v_data_574_ = v_data_607_;
goto v___jp_571_;
}
}
}
}
v___jp_612_:
{
lean_object* v_ref_613_; lean_object* v___x_614_; 
v_ref_613_ = lean_ctor_get(v___y_563_, 5);
lean_inc(v___y_564_);
lean_inc_ref(v___y_563_);
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
lean_inc(v_fst_566_);
v___x_614_ = lean_apply_6(v_msg_559_, v_fst_566_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, lean_box(0));
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref(v___x_614_);
v___y_593_ = v_ref_613_;
v_a_594_ = v_a_615_;
goto v___jp_592_;
}
else
{
lean_object* v___x_616_; 
lean_dec_ref(v___x_614_);
v___x_616_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4);
v___y_593_ = v_ref_613_;
v_a_594_ = v___x_616_;
goto v___jp_592_;
}
}
v___jp_617_:
{
if (v_clsEnabled_557_ == 0)
{
if (v___y_618_ == 0)
{
lean_object* v___x_619_; lean_object* v_traceState_620_; lean_object* v_env_621_; lean_object* v_nextMacroScope_622_; lean_object* v_ngen_623_; lean_object* v_auxDeclNGen_624_; lean_object* v_cache_625_; lean_object* v_messages_626_; lean_object* v_infoState_627_; lean_object* v_snapshotTasks_628_; lean_object* v_newDecls_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_648_; 
lean_del_object(v___x_588_);
lean_dec(v_snd_586_);
lean_dec(v_fst_585_);
lean_del_object(v___x_569_);
lean_dec_ref(v_msg_559_);
lean_dec_ref(v_tag_555_);
lean_dec(v_cls_553_);
v___x_619_ = lean_st_ref_take(v___y_564_);
v_traceState_620_ = lean_ctor_get(v___x_619_, 4);
v_env_621_ = lean_ctor_get(v___x_619_, 0);
v_nextMacroScope_622_ = lean_ctor_get(v___x_619_, 1);
v_ngen_623_ = lean_ctor_get(v___x_619_, 2);
v_auxDeclNGen_624_ = lean_ctor_get(v___x_619_, 3);
v_cache_625_ = lean_ctor_get(v___x_619_, 5);
v_messages_626_ = lean_ctor_get(v___x_619_, 6);
v_infoState_627_ = lean_ctor_get(v___x_619_, 7);
v_snapshotTasks_628_ = lean_ctor_get(v___x_619_, 8);
v_newDecls_629_ = lean_ctor_get(v___x_619_, 9);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_648_ == 0)
{
v___x_631_ = v___x_619_;
v_isShared_632_ = v_isSharedCheck_648_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_newDecls_629_);
lean_inc(v_snapshotTasks_628_);
lean_inc(v_infoState_627_);
lean_inc(v_messages_626_);
lean_inc(v_cache_625_);
lean_inc(v_traceState_620_);
lean_inc(v_auxDeclNGen_624_);
lean_inc(v_ngen_623_);
lean_inc(v_nextMacroScope_622_);
lean_inc(v_env_621_);
lean_dec(v___x_619_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_648_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
uint64_t v_tid_633_; lean_object* v_traces_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_647_; 
v_tid_633_ = lean_ctor_get_uint64(v_traceState_620_, sizeof(void*)*1);
v_traces_634_ = lean_ctor_get(v_traceState_620_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_traceState_620_);
if (v_isSharedCheck_647_ == 0)
{
v___x_636_ = v_traceState_620_;
v_isShared_637_ = v_isSharedCheck_647_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_traces_634_);
lean_dec(v_traceState_620_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_647_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_558_, v_traces_634_);
lean_dec_ref(v_traces_634_);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v___x_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_638_);
lean_ctor_set_uint64(v_reuseFailAlloc_646_, sizeof(void*)*1, v_tid_633_);
v___x_640_ = v_reuseFailAlloc_646_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_642_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 4, v___x_640_);
v___x_642_ = v___x_631_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_env_621_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_nextMacroScope_622_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_ngen_623_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v_auxDeclNGen_624_);
lean_ctor_set(v_reuseFailAlloc_645_, 4, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_645_, 5, v_cache_625_);
lean_ctor_set(v_reuseFailAlloc_645_, 6, v_messages_626_);
lean_ctor_set(v_reuseFailAlloc_645_, 7, v_infoState_627_);
lean_ctor_set(v_reuseFailAlloc_645_, 8, v_snapshotTasks_628_);
lean_ctor_set(v_reuseFailAlloc_645_, 9, v_newDecls_629_);
v___x_642_ = v_reuseFailAlloc_645_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_st_ref_set(v___y_564_, v___x_642_);
v___x_644_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_fst_566_);
return v___x_644_;
}
}
}
}
}
else
{
goto v___jp_612_;
}
}
else
{
goto v___jp_612_;
}
}
v___jp_649_:
{
double v___x_651_; double v___x_652_; double v___x_653_; uint8_t v___x_654_; 
v___x_651_ = lean_unbox_float(v_snd_586_);
v___x_652_ = lean_unbox_float(v_fst_585_);
v___x_653_ = lean_float_sub(v___x_651_, v___x_652_);
v___x_654_ = lean_float_decLt(v___y_650_, v___x_653_);
v___y_618_ = v___x_654_;
goto v___jp_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_cls_667_, lean_object* v_collapsed_668_, lean_object* v_tag_669_, lean_object* v_opts_670_, lean_object* v_clsEnabled_671_, lean_object* v_oldTraces_672_, lean_object* v_msg_673_, lean_object* v_resStartStop_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
uint8_t v_collapsed_boxed_680_; uint8_t v_clsEnabled_boxed_681_; lean_object* v_res_682_; 
v_collapsed_boxed_680_ = lean_unbox(v_collapsed_668_);
v_clsEnabled_boxed_681_ = lean_unbox(v_clsEnabled_671_);
v_res_682_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_cls_667_, v_collapsed_boxed_680_, v_tag_669_, v_opts_670_, v_clsEnabled_boxed_681_, v_oldTraces_672_, v_msg_673_, v_resStartStop_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v_opts_670_);
return v_res_682_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* v_a_686_, lean_object* v_x_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
v___x_694_ = l_Lean_Exception_toMessageData(v_a_686_);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* v_a_697_, lean_object* v_x_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_a_697_, v_x_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v_x_698_);
return v_res_704_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object* v_keys_705_, lean_object* v_i_706_, lean_object* v_k_707_){
_start:
{
lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = lean_array_get_size(v_keys_705_);
v___x_709_ = lean_nat_dec_lt(v_i_706_, v___x_708_);
if (v___x_709_ == 0)
{
lean_dec(v_i_706_);
return v___x_709_;
}
else
{
lean_object* v_k_x27_710_; uint8_t v___x_711_; 
v_k_x27_710_ = lean_array_fget_borrowed(v_keys_705_, v_i_706_);
v___x_711_ = l_Lean_instBEqMVarId_beq(v_k_707_, v_k_x27_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_i_706_, v___x_712_);
lean_dec(v_i_706_);
v_i_706_ = v___x_713_;
goto _start;
}
else
{
lean_dec(v_i_706_);
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object* v_keys_715_, lean_object* v_i_716_, lean_object* v_k_717_){
_start:
{
uint8_t v_res_718_; lean_object* v_r_719_; 
v_res_718_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_715_, v_i_716_, v_k_717_);
lean_dec(v_k_717_);
lean_dec_ref(v_keys_715_);
v_r_719_ = lean_box(v_res_718_);
return v_r_719_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0(void){
_start:
{
size_t v___x_720_; size_t v___x_721_; size_t v___x_722_; 
v___x_720_ = ((size_t)5ULL);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_shift_left(v___x_721_, v___x_720_);
return v___x_722_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1(void){
_start:
{
size_t v___x_723_; size_t v___x_724_; size_t v___x_725_; 
v___x_723_ = ((size_t)1ULL);
v___x_724_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0);
v___x_725_ = lean_usize_sub(v___x_724_, v___x_723_);
return v___x_725_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_726_, size_t v_x_727_, lean_object* v_x_728_){
_start:
{
if (lean_obj_tag(v_x_726_) == 0)
{
lean_object* v_es_729_; lean_object* v___x_730_; size_t v___x_731_; size_t v___x_732_; size_t v___x_733_; lean_object* v_j_734_; lean_object* v___x_735_; 
v_es_729_ = lean_ctor_get(v_x_726_, 0);
v___x_730_ = lean_box(2);
v___x_731_ = ((size_t)5ULL);
v___x_732_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1);
v___x_733_ = lean_usize_land(v_x_727_, v___x_732_);
v_j_734_ = lean_usize_to_nat(v___x_733_);
v___x_735_ = lean_array_get_borrowed(v___x_730_, v_es_729_, v_j_734_);
lean_dec(v_j_734_);
switch(lean_obj_tag(v___x_735_))
{
case 0:
{
lean_object* v_key_736_; uint8_t v___x_737_; 
v_key_736_ = lean_ctor_get(v___x_735_, 0);
v___x_737_ = l_Lean_instBEqMVarId_beq(v_x_728_, v_key_736_);
return v___x_737_;
}
case 1:
{
lean_object* v_node_738_; size_t v___x_739_; 
v_node_738_ = lean_ctor_get(v___x_735_, 0);
v___x_739_ = lean_usize_shift_right(v_x_727_, v___x_731_);
v_x_726_ = v_node_738_;
v_x_727_ = v___x_739_;
goto _start;
}
default: 
{
uint8_t v___x_741_; 
v___x_741_ = 0;
return v___x_741_;
}
}
}
else
{
lean_object* v_ks_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_ks_742_ = lean_ctor_get(v_x_726_, 0);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_ks_742_, v___x_743_, v_x_728_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
size_t v_x_82220__boxed_748_; uint8_t v_res_749_; lean_object* v_r_750_; 
v_x_82220__boxed_748_ = lean_unbox_usize(v_x_746_);
lean_dec(v_x_746_);
v_res_749_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_745_, v_x_82220__boxed_748_, v_x_747_);
lean_dec(v_x_747_);
lean_dec_ref(v_x_745_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
uint64_t v___x_753_; size_t v___x_754_; uint8_t v___x_755_; 
v___x_753_ = l_Lean_instHashableMVarId_hash(v_x_752_);
v___x_754_ = lean_uint64_to_usize(v___x_753_);
v___x_755_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_751_, v___x_754_, v_x_752_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_756_, v_x_757_);
lean_dec(v_x_757_);
lean_dec_ref(v_x_756_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object* v_mvarId_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; lean_object* v_mctx_764_; lean_object* v_eAssignment_765_; uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_763_ = lean_st_ref_get(v___y_761_);
v_mctx_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc_ref(v_mctx_764_);
lean_dec(v___x_763_);
v_eAssignment_765_ = lean_ctor_get(v_mctx_764_, 8);
lean_inc_ref(v_eAssignment_765_);
lean_dec_ref(v_mctx_764_);
v___x_766_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_eAssignment_765_, v_mvarId_760_);
lean_dec_ref(v_eAssignment_765_);
v___x_767_ = lean_box(v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object* v_mvarId_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec(v_mvarId_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_ref_779_; lean_object* v___x_780_; lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_789_; 
v_ref_779_ = lean_ctor_get(v___y_776_, 5);
v___x_780_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_789_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_787_; 
lean_inc(v_ref_779_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_ref_779_);
lean_ctor_set(v___x_785_, 1, v_a_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set_tag(v___x_783_, 1);
lean_ctor_set(v___x_783_, 0, v___x_785_);
v___x_787_ = v___x_783_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
return v_res_796_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object* v_e_797_){
_start:
{
if (lean_obj_tag(v_e_797_) == 0)
{
uint8_t v___x_798_; 
v___x_798_ = 2;
return v___x_798_;
}
else
{
uint8_t v___x_799_; 
v___x_799_ = 0;
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object* v_e_800_){
_start:
{
uint8_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_e_800_);
lean_dec_ref(v_e_800_);
v_r_802_ = lean_box(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_803_, uint8_t v_collapsed_804_, lean_object* v_tag_805_, lean_object* v_opts_806_, uint8_t v_clsEnabled_807_, lean_object* v_oldTraces_808_, lean_object* v_msg_809_, lean_object* v_resStartStop_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_fst_816_; lean_object* v_snd_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_916_; 
v_fst_816_ = lean_ctor_get(v_resStartStop_810_, 0);
v_snd_817_ = lean_ctor_get(v_resStartStop_810_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_resStartStop_810_);
if (v_isSharedCheck_916_ == 0)
{
v___x_819_ = v_resStartStop_810_;
v_isShared_820_ = v_isSharedCheck_916_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_snd_817_);
lean_inc(v_fst_816_);
lean_dec(v_resStartStop_810_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_916_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v_data_824_; lean_object* v_fst_835_; lean_object* v_snd_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_915_; 
v_fst_835_ = lean_ctor_get(v_snd_817_, 0);
v_snd_836_ = lean_ctor_get(v_snd_817_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_snd_817_);
if (v_isSharedCheck_915_ == 0)
{
v___x_838_ = v_snd_817_;
v_isShared_839_ = v_isSharedCheck_915_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_snd_836_);
lean_inc(v_fst_835_);
lean_dec(v_snd_817_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_915_;
goto v_resetjp_837_;
}
v___jp_821_:
{
lean_object* v___x_825_; 
lean_inc(v___y_823_);
v___x_825_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_oldTraces_808_, v_data_824_, v___y_823_, v___y_822_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v___x_826_; 
lean_dec_ref(v___x_825_);
v___x_826_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_fst_816_);
return v___x_826_;
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_fst_816_);
v_a_827_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_825_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_825_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
v_resetjp_837_:
{
lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v___y_843_; lean_object* v_a_844_; uint8_t v___y_868_; double v___y_900_; 
v___x_840_ = l_Lean_trace_profiler;
v___x_841_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_806_, v___x_840_);
if (v___x_841_ == 0)
{
v___y_868_ = v___x_841_;
goto v___jp_867_;
}
else
{
lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_905_ = l_Lean_trace_profiler_useHeartbeats;
v___x_906_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_806_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; double v___x_909_; double v___x_910_; double v___x_911_; 
v___x_907_ = l_Lean_trace_profiler_threshold;
v___x_908_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_806_, v___x_907_);
v___x_909_ = lean_float_of_nat(v___x_908_);
v___x_910_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__5);
v___x_911_ = lean_float_div(v___x_909_, v___x_910_);
v___y_900_ = v___x_911_;
goto v___jp_899_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; double v___x_914_; 
v___x_912_ = l_Lean_trace_profiler_threshold;
v___x_913_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_806_, v___x_912_);
v___x_914_ = lean_float_of_nat(v___x_913_);
v___y_900_ = v___x_914_;
goto v___jp_899_;
}
}
v___jp_842_:
{
uint8_t v_result_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v_result_845_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_fst_816_);
v___x_846_ = l_Lean_TraceResult_toEmoji(v_result_845_);
v___x_847_ = l_Lean_stringToMessageData(v___x_846_);
v___x_848_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 7);
lean_ctor_set(v___x_838_, 1, v___x_848_);
lean_ctor_set(v___x_838_, 0, v___x_847_);
v___x_850_ = v___x_838_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_848_);
v___x_850_ = v_reuseFailAlloc_861_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v_m_852_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 7);
lean_ctor_set(v___x_819_, 1, v_a_844_);
lean_ctor_set(v___x_819_, 0, v___x_850_);
v_m_852_ = v___x_819_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_a_844_);
v_m_852_ = v_reuseFailAlloc_860_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; double v___x_855_; lean_object* v_data_856_; 
v___x_853_ = lean_box(v_result_845_);
v___x_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
v___x_855_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
lean_inc_ref(v_tag_805_);
lean_inc_ref(v___x_854_);
lean_inc(v_cls_803_);
v_data_856_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_856_, 0, v_cls_803_);
lean_ctor_set(v_data_856_, 1, v___x_854_);
lean_ctor_set(v_data_856_, 2, v_tag_805_);
lean_ctor_set_float(v_data_856_, sizeof(void*)*3, v___x_855_);
lean_ctor_set_float(v_data_856_, sizeof(void*)*3 + 8, v___x_855_);
lean_ctor_set_uint8(v_data_856_, sizeof(void*)*3 + 16, v_collapsed_804_);
if (v___x_841_ == 0)
{
lean_dec_ref(v___x_854_);
lean_dec(v_snd_836_);
lean_dec(v_fst_835_);
lean_dec_ref(v_tag_805_);
lean_dec(v_cls_803_);
v___y_822_ = v_m_852_;
v___y_823_ = v___y_843_;
v_data_824_ = v_data_856_;
goto v___jp_821_;
}
else
{
lean_object* v_data_857_; double v___x_858_; double v___x_859_; 
lean_dec_ref(v_data_856_);
v_data_857_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_857_, 0, v_cls_803_);
lean_ctor_set(v_data_857_, 1, v___x_854_);
lean_ctor_set(v_data_857_, 2, v_tag_805_);
v___x_858_ = lean_unbox_float(v_fst_835_);
lean_dec(v_fst_835_);
lean_ctor_set_float(v_data_857_, sizeof(void*)*3, v___x_858_);
v___x_859_ = lean_unbox_float(v_snd_836_);
lean_dec(v_snd_836_);
lean_ctor_set_float(v_data_857_, sizeof(void*)*3 + 8, v___x_859_);
lean_ctor_set_uint8(v_data_857_, sizeof(void*)*3 + 16, v_collapsed_804_);
v___y_822_ = v_m_852_;
v___y_823_ = v___y_843_;
v_data_824_ = v_data_857_;
goto v___jp_821_;
}
}
}
}
v___jp_862_:
{
lean_object* v_ref_863_; lean_object* v___x_864_; 
v_ref_863_ = lean_ctor_get(v___y_813_, 5);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v_fst_816_);
v___x_864_ = lean_apply_6(v_msg_809_, v_fst_816_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, lean_box(0));
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v___x_864_);
v___y_843_ = v_ref_863_;
v_a_844_ = v_a_865_;
goto v___jp_842_;
}
else
{
lean_object* v___x_866_; 
lean_dec_ref(v___x_864_);
v___x_866_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__4);
v___y_843_ = v_ref_863_;
v_a_844_ = v___x_866_;
goto v___jp_842_;
}
}
v___jp_867_:
{
if (v_clsEnabled_807_ == 0)
{
if (v___y_868_ == 0)
{
lean_object* v___x_869_; lean_object* v_traceState_870_; lean_object* v_env_871_; lean_object* v_nextMacroScope_872_; lean_object* v_ngen_873_; lean_object* v_auxDeclNGen_874_; lean_object* v_cache_875_; lean_object* v_messages_876_; lean_object* v_infoState_877_; lean_object* v_snapshotTasks_878_; lean_object* v_newDecls_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_898_; 
lean_del_object(v___x_838_);
lean_dec(v_snd_836_);
lean_dec(v_fst_835_);
lean_del_object(v___x_819_);
lean_dec_ref(v_msg_809_);
lean_dec_ref(v_tag_805_);
lean_dec(v_cls_803_);
v___x_869_ = lean_st_ref_take(v___y_814_);
v_traceState_870_ = lean_ctor_get(v___x_869_, 4);
v_env_871_ = lean_ctor_get(v___x_869_, 0);
v_nextMacroScope_872_ = lean_ctor_get(v___x_869_, 1);
v_ngen_873_ = lean_ctor_get(v___x_869_, 2);
v_auxDeclNGen_874_ = lean_ctor_get(v___x_869_, 3);
v_cache_875_ = lean_ctor_get(v___x_869_, 5);
v_messages_876_ = lean_ctor_get(v___x_869_, 6);
v_infoState_877_ = lean_ctor_get(v___x_869_, 7);
v_snapshotTasks_878_ = lean_ctor_get(v___x_869_, 8);
v_newDecls_879_ = lean_ctor_get(v___x_869_, 9);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_898_ == 0)
{
v___x_881_ = v___x_869_;
v_isShared_882_ = v_isSharedCheck_898_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_newDecls_879_);
lean_inc(v_snapshotTasks_878_);
lean_inc(v_infoState_877_);
lean_inc(v_messages_876_);
lean_inc(v_cache_875_);
lean_inc(v_traceState_870_);
lean_inc(v_auxDeclNGen_874_);
lean_inc(v_ngen_873_);
lean_inc(v_nextMacroScope_872_);
lean_inc(v_env_871_);
lean_dec(v___x_869_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_898_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
uint64_t v_tid_883_; lean_object* v_traces_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_897_; 
v_tid_883_ = lean_ctor_get_uint64(v_traceState_870_, sizeof(void*)*1);
v_traces_884_ = lean_ctor_get(v_traceState_870_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_traceState_870_);
if (v_isSharedCheck_897_ == 0)
{
v___x_886_ = v_traceState_870_;
v_isShared_887_ = v_isSharedCheck_897_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_traces_884_);
lean_dec(v_traceState_870_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_897_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_808_, v_traces_884_);
lean_dec_ref(v_traces_884_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_888_);
lean_ctor_set_uint64(v_reuseFailAlloc_896_, sizeof(void*)*1, v_tid_883_);
v___x_890_ = v_reuseFailAlloc_896_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_892_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 4, v___x_890_);
v___x_892_ = v___x_881_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_env_871_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_nextMacroScope_872_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_ngen_873_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_auxDeclNGen_874_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_895_, 5, v_cache_875_);
lean_ctor_set(v_reuseFailAlloc_895_, 6, v_messages_876_);
lean_ctor_set(v_reuseFailAlloc_895_, 7, v_infoState_877_);
lean_ctor_set(v_reuseFailAlloc_895_, 8, v_snapshotTasks_878_);
lean_ctor_set(v_reuseFailAlloc_895_, 9, v_newDecls_879_);
v___x_892_ = v_reuseFailAlloc_895_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_st_ref_set(v___y_814_, v___x_892_);
v___x_894_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_fst_816_);
return v___x_894_;
}
}
}
}
}
else
{
goto v___jp_862_;
}
}
else
{
goto v___jp_862_;
}
}
v___jp_899_:
{
double v___x_901_; double v___x_902_; double v___x_903_; uint8_t v___x_904_; 
v___x_901_ = lean_unbox_float(v_snd_836_);
v___x_902_ = lean_unbox_float(v_fst_835_);
v___x_903_ = lean_float_sub(v___x_901_, v___x_902_);
v___x_904_ = lean_float_decLt(v___y_900_, v___x_903_);
v___y_868_ = v___x_904_;
goto v___jp_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_917_, lean_object* v_collapsed_918_, lean_object* v_tag_919_, lean_object* v_opts_920_, lean_object* v_clsEnabled_921_, lean_object* v_oldTraces_922_, lean_object* v_msg_923_, lean_object* v_resStartStop_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
uint8_t v_collapsed_boxed_930_; uint8_t v_clsEnabled_boxed_931_; lean_object* v_res_932_; 
v_collapsed_boxed_930_ = lean_unbox(v_collapsed_918_);
v_clsEnabled_boxed_931_ = lean_unbox(v_clsEnabled_921_);
v_res_932_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_917_, v_collapsed_boxed_930_, v_tag_919_, v_opts_920_, v_clsEnabled_boxed_931_, v_oldTraces_922_, v_msg_923_, v_resStartStop_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_opts_920_);
return v_res_932_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_935_ = l_Lean_stringToMessageData(v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_head_936_, lean_object* v_x_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_head_936_);
v___x_945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_head_947_, lean_object* v_x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_head_947_, v_x_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec_ref(v_x_948_);
return v_res_954_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object* v_head_958_, lean_object* v_x_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_976_; 
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v_head_958_);
v___x_966_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v___x_965_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_976_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_971_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v_a_967_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_972_);
v___x_974_ = v___x_969_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object* v_head_977_, lean_object* v_x_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(v_head_977_, v_x_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec_ref(v_x_978_);
return v_res_984_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_985_; double v___x_986_; 
v___x_985_ = lean_unsigned_to_nat(1000000000u);
v___x_986_ = lean_float_of_nat(v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_989_ = l_Lean_stringToMessageData(v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* v_tail_998_, lean_object* v_cfg_999_, lean_object* v_trace_1000_, lean_object* v_next_1001_, lean_object* v_goals_1002_, lean_object* v_n_1003_, lean_object* v_acc_1004_, lean_object* v_r_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_998_, v_cfg_999_, v_trace_1000_, v_next_1001_, v_goals_1002_, v_n_1003_, v_acc_1004_, v_r_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_1012_, lean_object* v_trace_1013_, lean_object* v_next_1014_, lean_object* v_goals_1015_, lean_object* v_n_1016_, lean_object* v_curr_1017_, lean_object* v_acc_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; uint8_t v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; uint8_t v___y_1031_; lean_object* v_a_1032_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; uint8_t v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; uint8_t v___y_1048_; lean_object* v_a_1049_; lean_object* v___y_1062_; lean_object* v___y_1063_; uint8_t v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; uint8_t v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; uint8_t v___y_1114_; uint8_t v___y_1115_; lean_object* v___y_1116_; lean_object* v_a_1117_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; uint8_t v___y_1131_; uint8_t v___y_1132_; lean_object* v___y_1133_; lean_object* v_a_1134_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; uint8_t v___y_1141_; uint8_t v___y_1142_; lean_object* v___y_1143_; lean_object* v_a_1144_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; uint8_t v___y_1151_; uint8_t v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; uint8_t v___y_1162_; uint8_t v___y_1163_; lean_object* v___y_1164_; lean_object* v_a_1165_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; uint8_t v___y_1182_; uint8_t v___y_1183_; lean_object* v___y_1184_; lean_object* v_a_1185_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; uint8_t v___y_1192_; uint8_t v___y_1193_; lean_object* v___y_1194_; lean_object* v_a_1195_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; uint8_t v___y_1202_; uint8_t v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v_zero_1208_; uint8_t v_isZero_1209_; 
v_zero_1208_ = lean_unsigned_to_nat(0u);
v_isZero_1209_ = lean_nat_dec_eq(v_n_1016_, v_zero_1208_);
if (v_isZero_1209_ == 1)
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec(v_acc_1018_);
lean_dec(v_curr_1017_);
lean_dec(v_n_1016_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
v___x_1210_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1211_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1210_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1211_;
}
else
{
lean_object* v_proc_1212_; lean_object* v_suspend_1213_; lean_object* v_discharge_1214_; lean_object* v___f_1215_; uint8_t v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; uint8_t v___y_1220_; lean_object* v___y_1221_; lean_object* v___f_1257_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; uint8_t v___y_1263_; uint8_t v___y_1264_; lean_object* v_a_1265_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; uint8_t v___y_1279_; uint8_t v___y_1280_; lean_object* v_a_1281_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; uint8_t v___y_1298_; uint8_t v___y_1299_; lean_object* v___y_1300_; lean_object* v___f_1341_; lean_object* v___y_1343_; lean_object* v___y_1344_; uint8_t v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; uint8_t v___y_1348_; lean_object* v_a_1349_; lean_object* v___y_1362_; uint8_t v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; uint8_t v___y_1367_; lean_object* v_a_1368_; lean_object* v___f_1377_; lean_object* v___y_1379_; uint8_t v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; uint8_t v___y_1386_; uint8_t v___y_1387_; lean_object* v___y_1388_; lean_object* v_a_1389_; lean_object* v___y_1402_; uint8_t v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; uint8_t v___y_1408_; uint8_t v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v_a_1412_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; uint8_t v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; uint8_t v___y_1430_; uint8_t v___y_1431_; lean_object* v___y_1432_; uint8_t v___y_1433_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; uint8_t v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; uint8_t v___y_1481_; uint8_t v___y_1482_; lean_object* v___y_1483_; lean_object* v_a_1484_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; uint8_t v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; uint8_t v___y_1504_; uint8_t v___y_1505_; lean_object* v___y_1506_; lean_object* v_a_1507_; lean_object* v___y_1517_; uint8_t v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; uint8_t v___y_1522_; uint8_t v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; uint8_t v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; uint8_t v___y_1574_; lean_object* v___y_1575_; uint8_t v___y_1576_; lean_object* v___y_1577_; uint8_t v___y_1578_; lean_object* v_a_1579_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; uint8_t v___y_1594_; lean_object* v___y_1595_; uint8_t v___y_1596_; lean_object* v___y_1597_; uint8_t v___y_1598_; lean_object* v_a_1599_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; uint8_t v___y_1617_; lean_object* v___y_1618_; uint8_t v___y_1619_; uint8_t v___y_1620_; lean_object* v___y_1621_; lean_object* v_a_1622_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; uint8_t v___y_1638_; uint8_t v___y_1639_; uint8_t v___y_1640_; lean_object* v___y_1641_; lean_object* v_a_1642_; lean_object* v___y_1655_; lean_object* v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; uint8_t v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; uint8_t v___y_1664_; uint8_t v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; uint8_t v___y_1712_; lean_object* v___y_1713_; uint8_t v___y_1714_; uint8_t v___y_1715_; lean_object* v___y_1716_; lean_object* v_a_1717_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; uint8_t v___y_1736_; uint8_t v___y_1737_; uint8_t v___y_1738_; lean_object* v___y_1739_; lean_object* v_a_1740_; lean_object* v___y_1750_; uint8_t v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; uint8_t v___y_1756_; lean_object* v___y_1757_; uint8_t v___y_1758_; lean_object* v___y_1759_; lean_object* v_a_1760_; lean_object* v___y_1773_; uint8_t v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; uint8_t v___y_1779_; lean_object* v___y_1780_; uint8_t v___y_1781_; lean_object* v___y_1782_; lean_object* v_a_1783_; uint8_t v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; uint8_t v___y_1802_; lean_object* v___y_1803_; uint8_t v___y_1804_; lean_object* v___y_1845_; uint8_t v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; uint8_t v___y_1850_; lean_object* v_a_1851_; lean_object* v___y_1864_; uint8_t v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; uint8_t v___y_1869_; lean_object* v_a_1870_; lean_object* v___y_1880_; uint8_t v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; uint8_t v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v_one_1927_; lean_object* v_n_1928_; lean_object* v___y_1930_; lean_object* v___y_1931_; uint8_t v___y_1932_; uint8_t v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; uint8_t v___y_1981_; uint8_t v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; uint8_t v___y_1985_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; uint8_t v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; uint8_t v___y_2015_; uint8_t v___y_2016_; uint8_t v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; uint8_t v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; uint8_t v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; uint8_t v___y_2070_; lean_object* v___y_2071_; uint8_t v___y_2072_; lean_object* v___y_2093_; lean_object* v___y_2094_; uint8_t v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; uint8_t v___y_2099_; uint8_t v___y_2100_; uint8_t v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2143_; lean_object* v___y_2144_; uint8_t v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; uint8_t v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; uint8_t v___y_2155_; uint8_t v___y_2156_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; uint8_t v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; uint8_t v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; uint8_t v___y_2234_; lean_object* v_a_2252_; lean_object* v___y_2343_; lean_object* v___x_2353_; 
v_proc_1212_ = lean_ctor_get(v_cfg_1012_, 1);
v_suspend_1213_ = lean_ctor_get(v_cfg_1012_, 2);
v_discharge_1214_ = lean_ctor_get(v_cfg_1012_, 3);
v___f_1215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1927_ = lean_unsigned_to_nat(1u);
v_n_1928_ = lean_nat_sub(v_n_1016_, v_one_1927_);
lean_dec(v_n_1016_);
lean_inc_ref(v_proc_1212_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v_curr_1017_);
lean_inc(v_goals_1015_);
v___x_2353_ = lean_apply_7(v_proc_1212_, v_goals_1015_, v_curr_1017_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref(v___x_2353_);
v_a_2252_ = v_a_2354_;
goto v___jp_2251_;
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2422_; 
v_a_2355_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2357_ = v___x_2353_;
v_isShared_2358_ = v_isSharedCheck_2422_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2353_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2422_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___f_2359_; lean_object* v___y_2361_; uint8_t v___y_2362_; uint8_t v___y_2363_; lean_object* v___y_2364_; uint8_t v___y_2401_; uint8_t v___x_2420_; 
lean_inc(v_a_2355_);
v___f_2359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(v___f_2359_, 0, v_a_2355_);
v___x_2420_ = l_Lean_Exception_isInterrupt(v_a_2355_);
if (v___x_2420_ == 0)
{
uint8_t v___x_2421_; 
lean_inc(v_a_2355_);
v___x_2421_ = l_Lean_Exception_isRuntime(v_a_2355_);
v___y_2401_ = v___x_2421_;
goto v___jp_2400_;
}
else
{
v___y_2401_ = v___x_2420_;
goto v___jp_2400_;
}
v___jp_2360_:
{
lean_object* v___x_2365_; lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2399_; 
v___x_2365_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2399_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2399_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; uint8_t v___x_2371_; 
v___x_2370_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2371_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2364_, v___x_2370_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2372_ = lean_io_mono_nanos_now();
v___x_2373_ = lean_io_mono_nanos_now();
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v_a_2355_);
v___x_2375_ = v___x_2368_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2355_);
v___x_2375_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
double v___x_2376_; double v___x_2377_; double v___x_2378_; double v___x_2379_; double v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2376_ = lean_float_of_nat(v___x_2372_);
v___x_2377_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2378_ = lean_float_div(v___x_2376_, v___x_2377_);
v___x_2379_ = lean_float_of_nat(v___x_2373_);
v___x_2380_ = lean_float_div(v___x_2379_, v___x_2377_);
v___x_2381_ = lean_box_float(v___x_2378_);
v___x_2382_ = lean_box_float(v___x_2380_);
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2375_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
lean_inc_ref(v___y_2361_);
lean_inc(v_trace_1013_);
v___x_2385_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_1013_, v___y_2362_, v___y_2361_, v___y_2364_, v___y_2363_, v_a_2366_, v___f_2359_, v___x_2384_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_2343_ = v___x_2385_;
goto v___jp_2342_;
}
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2390_; 
v___x_2387_ = lean_io_get_num_heartbeats();
v___x_2388_ = lean_io_get_num_heartbeats();
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v_a_2355_);
v___x_2390_ = v___x_2368_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2355_);
v___x_2390_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
double v___x_2391_; double v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2391_ = lean_float_of_nat(v___x_2387_);
v___x_2392_ = lean_float_of_nat(v___x_2388_);
v___x_2393_ = lean_box_float(v___x_2391_);
v___x_2394_ = lean_box_float(v___x_2392_);
v___x_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2390_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
lean_inc_ref(v___y_2361_);
lean_inc(v_trace_1013_);
v___x_2397_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_1013_, v___y_2362_, v___y_2361_, v___y_2364_, v___y_2363_, v_a_2366_, v___f_2359_, v___x_2396_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_2343_ = v___x_2397_;
goto v___jp_2342_;
}
}
}
}
v___jp_2400_:
{
if (v___y_2401_ == 0)
{
lean_object* v_options_2402_; uint8_t v_hasTrace_2403_; 
v_options_2402_ = lean_ctor_get(v_a_1021_, 2);
v_hasTrace_2403_ = lean_ctor_get_uint8(v_options_2402_, sizeof(void*)*1);
if (v_hasTrace_2403_ == 0)
{
lean_object* v___x_2405_; 
lean_dec_ref(v___f_2359_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_curr_1017_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
if (v_isShared_2358_ == 0)
{
v___x_2405_ = v___x_2357_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2355_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; 
v_inheritedTraceOptions_2407_ = lean_ctor_get(v_a_1021_, 13);
v___x_2408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1013_);
v___x_2410_ = l_Lean_Name_append(v___x_2409_, v_trace_1013_);
v___x_2411_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2407_, v_options_2402_, v___x_2410_);
lean_dec(v___x_2410_);
if (v___x_2411_ == 0)
{
lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2412_ = l_Lean_trace_profiler;
v___x_2413_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2402_, v___x_2412_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2415_; 
lean_dec_ref(v___f_2359_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_curr_1017_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
if (v_isShared_2358_ == 0)
{
v___x_2415_ = v___x_2357_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2355_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
else
{
lean_del_object(v___x_2357_);
v___y_2361_ = v___x_2408_;
v___y_2362_ = v_hasTrace_2403_;
v___y_2363_ = v___x_2411_;
v___y_2364_ = v_options_2402_;
goto v___jp_2360_;
}
}
else
{
lean_del_object(v___x_2357_);
v___y_2361_ = v___x_2408_;
v___y_2362_ = v_hasTrace_2403_;
v___y_2363_ = v___x_2411_;
v___y_2364_ = v_options_2402_;
goto v___jp_2360_;
}
}
}
else
{
lean_object* v___x_2418_; 
lean_dec_ref(v___f_2359_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_curr_1017_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
if (v_isShared_2358_ == 0)
{
v___x_2418_ = v___x_2357_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2355_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
v___jp_1216_:
{
lean_object* v___x_1222_; lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1256_; 
v___x_1222_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1256_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1256_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; uint8_t v___x_1228_; 
v___x_1227_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1228_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1219_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1229_ = lean_io_mono_nanos_now();
v___x_1230_ = lean_io_mono_nanos_now();
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 1);
lean_ctor_set(v___x_1225_, 0, v___y_1218_);
v___x_1232_ = v___x_1225_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___y_1218_);
v___x_1232_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
double v___x_1233_; double v___x_1234_; double v___x_1235_; double v___x_1236_; double v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1233_ = lean_float_of_nat(v___x_1229_);
v___x_1234_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1235_ = lean_float_div(v___x_1233_, v___x_1234_);
v___x_1236_ = lean_float_of_nat(v___x_1230_);
v___x_1237_ = lean_float_div(v___x_1236_, v___x_1234_);
v___x_1238_ = lean_box_float(v___x_1235_);
v___x_1239_ = lean_box_float(v___x_1237_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1238_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1232_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
lean_inc_ref(v___y_1221_);
v___x_1242_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1217_, v___y_1221_, v___y_1219_, v___y_1220_, v_a_1223_, v___f_1215_, v___x_1241_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1242_;
}
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1244_ = lean_io_get_num_heartbeats();
v___x_1245_ = lean_io_get_num_heartbeats();
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 1);
lean_ctor_set(v___x_1225_, 0, v___y_1218_);
v___x_1247_ = v___x_1225_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___y_1218_);
v___x_1247_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
double v___x_1248_; double v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1248_ = lean_float_of_nat(v___x_1244_);
v___x_1249_ = lean_float_of_nat(v___x_1245_);
v___x_1250_ = lean_box_float(v___x_1248_);
v___x_1251_ = lean_box_float(v___x_1249_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1247_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
lean_inc_ref(v___y_1221_);
v___x_1254_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1217_, v___y_1221_, v___y_1219_, v___y_1220_, v_a_1223_, v___f_1215_, v___x_1253_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1254_;
}
}
}
}
v___jp_1258_:
{
lean_object* v___x_1266_; double v___x_1267_; double v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1266_ = lean_io_get_num_heartbeats();
v___x_1267_ = lean_float_of_nat(v___y_1262_);
v___x_1268_ = lean_float_of_nat(v___x_1266_);
v___x_1269_ = lean_box_float(v___x_1267_);
v___x_1270_ = lean_box_float(v___x_1268_);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1269_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_a_1265_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
lean_inc_ref(v___y_1261_);
v___x_1273_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1263_, v___y_1261_, v___y_1260_, v___y_1264_, v___y_1259_, v___f_1257_, v___x_1272_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1273_;
}
v___jp_1274_:
{
lean_object* v___x_1282_; double v___x_1283_; double v___x_1284_; double v___x_1285_; double v___x_1286_; double v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1282_ = lean_io_mono_nanos_now();
v___x_1283_ = lean_float_of_nat(v___y_1278_);
v___x_1284_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1285_ = lean_float_div(v___x_1283_, v___x_1284_);
v___x_1286_ = lean_float_of_nat(v___x_1282_);
v___x_1287_ = lean_float_div(v___x_1286_, v___x_1284_);
v___x_1288_ = lean_box_float(v___x_1285_);
v___x_1289_ = lean_box_float(v___x_1287_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_a_1281_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
lean_inc_ref(v___y_1277_);
v___x_1292_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1279_, v___y_1277_, v___y_1276_, v___y_1280_, v___y_1275_, v___f_1257_, v___x_1291_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1292_;
}
v___jp_1293_:
{
lean_object* v___x_1301_; lean_object* v_a_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1301_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref(v___x_1301_);
v___x_1303_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1304_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1295_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1013_);
v___x_1306_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1294_, v___y_1300_, v___y_1297_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set_tag(v___x_1309_, 1);
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
v___y_1275_ = v_a_1302_;
v___y_1276_ = v___y_1295_;
v___y_1277_ = v___y_1296_;
v___y_1278_ = v___x_1305_;
v___y_1279_ = v___y_1298_;
v___y_1280_ = v___y_1299_;
v_a_1281_ = v___x_1312_;
goto v___jp_1274_;
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
v_a_1315_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1306_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1306_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 0);
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
v___y_1275_ = v_a_1302_;
v___y_1276_ = v___y_1295_;
v___y_1277_ = v___y_1296_;
v___y_1278_ = v___x_1305_;
v___y_1279_ = v___y_1298_;
v___y_1280_ = v___y_1299_;
v_a_1281_ = v___x_1320_;
goto v___jp_1274_;
}
}
}
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1013_);
v___x_1324_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1294_, v___y_1300_, v___y_1297_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 1);
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
v___y_1259_ = v_a_1302_;
v___y_1260_ = v___y_1295_;
v___y_1261_ = v___y_1296_;
v___y_1262_ = v___x_1323_;
v___y_1263_ = v___y_1298_;
v___y_1264_ = v___y_1299_;
v_a_1265_ = v___x_1330_;
goto v___jp_1258_;
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
v_a_1333_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1324_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1324_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set_tag(v___x_1335_, 0);
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
v___y_1259_ = v_a_1302_;
v___y_1260_ = v___y_1295_;
v___y_1261_ = v___y_1296_;
v___y_1262_ = v___x_1323_;
v___y_1263_ = v___y_1298_;
v___y_1264_ = v___y_1299_;
v_a_1265_ = v___x_1338_;
goto v___jp_1258_;
}
}
}
}
}
v___jp_1342_:
{
lean_object* v___x_1350_; double v___x_1351_; double v___x_1352_; double v___x_1353_; double v___x_1354_; double v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1350_ = lean_io_mono_nanos_now();
v___x_1351_ = lean_float_of_nat(v___y_1343_);
v___x_1352_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1353_ = lean_float_div(v___x_1351_, v___x_1352_);
v___x_1354_ = lean_float_of_nat(v___x_1350_);
v___x_1355_ = lean_float_div(v___x_1354_, v___x_1352_);
v___x_1356_ = lean_box_float(v___x_1353_);
v___x_1357_ = lean_box_float(v___x_1355_);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_a_1349_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
lean_inc_ref(v___y_1346_);
v___x_1360_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1348_, v___y_1346_, v___y_1344_, v___y_1345_, v___y_1347_, v___f_1341_, v___x_1359_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1360_;
}
v___jp_1361_:
{
lean_object* v___x_1369_; double v___x_1370_; double v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1369_ = lean_io_get_num_heartbeats();
v___x_1370_ = lean_float_of_nat(v___y_1365_);
v___x_1371_ = lean_float_of_nat(v___x_1369_);
v___x_1372_ = lean_box_float(v___x_1370_);
v___x_1373_ = lean_box_float(v___x_1371_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_a_1368_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
lean_inc_ref(v___y_1364_);
v___x_1376_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1367_, v___y_1364_, v___y_1362_, v___y_1363_, v___y_1366_, v___f_1341_, v___x_1375_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1376_;
}
v___jp_1378_:
{
lean_object* v___x_1390_; double v___x_1391_; double v___x_1392_; double v___x_1393_; double v___x_1394_; double v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1390_ = lean_io_mono_nanos_now();
v___x_1391_ = lean_float_of_nat(v___y_1384_);
v___x_1392_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1393_ = lean_float_div(v___x_1391_, v___x_1392_);
v___x_1394_ = lean_float_of_nat(v___x_1390_);
v___x_1395_ = lean_float_div(v___x_1394_, v___x_1392_);
v___x_1396_ = lean_box_float(v___x_1393_);
v___x_1397_ = lean_box_float(v___x_1395_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1396_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_a_1389_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
lean_inc_ref(v___y_1383_);
lean_inc(v_trace_1013_);
v___x_1400_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1387_, v___y_1383_, v___y_1382_, v___y_1380_, v___y_1385_, v___f_1377_, v___x_1399_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1147_ = v___y_1379_;
v___y_1148_ = v___y_1382_;
v___y_1149_ = v___y_1381_;
v___y_1150_ = v___y_1383_;
v___y_1151_ = v___y_1386_;
v___y_1152_ = v___y_1387_;
v___y_1153_ = v___y_1388_;
v___y_1154_ = v___x_1400_;
goto v___jp_1146_;
}
v___jp_1401_:
{
lean_object* v___x_1413_; double v___x_1414_; double v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1413_ = lean_io_get_num_heartbeats();
v___x_1414_ = lean_float_of_nat(v___y_1410_);
v___x_1415_ = lean_float_of_nat(v___x_1413_);
v___x_1416_ = lean_box_float(v___x_1414_);
v___x_1417_ = lean_box_float(v___x_1415_);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v_a_1412_);
lean_ctor_set(v___x_1419_, 1, v___x_1418_);
lean_inc_ref(v___y_1406_);
lean_inc(v_trace_1013_);
v___x_1420_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1409_, v___y_1406_, v___y_1405_, v___y_1403_, v___y_1407_, v___f_1377_, v___x_1419_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1147_ = v___y_1402_;
v___y_1148_ = v___y_1405_;
v___y_1149_ = v___y_1404_;
v___y_1150_ = v___y_1406_;
v___y_1151_ = v___y_1408_;
v___y_1152_ = v___y_1409_;
v___y_1153_ = v___y_1411_;
v___y_1154_ = v___x_1420_;
goto v___jp_1146_;
}
v___jp_1421_:
{
lean_object* v___x_1434_; 
v___x_1434_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
if (v___y_1431_ == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref(v___x_1434_);
v___x_1436_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1013_);
v___x_1437_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1424_, v___y_1428_, v___y_1425_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set_tag(v___x_1440_, 1);
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
v___y_1379_ = v___y_1429_;
v___y_1380_ = v___y_1430_;
v___y_1381_ = v___y_1422_;
v___y_1382_ = v___y_1423_;
v___y_1383_ = v___y_1432_;
v___y_1384_ = v___x_1436_;
v___y_1385_ = v_a_1435_;
v___y_1386_ = v___y_1433_;
v___y_1387_ = v___y_1426_;
v___y_1388_ = v___y_1427_;
v_a_1389_ = v___x_1443_;
goto v___jp_1378_;
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
v_a_1446_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1437_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1437_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set_tag(v___x_1448_, 0);
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
v___y_1379_ = v___y_1429_;
v___y_1380_ = v___y_1430_;
v___y_1381_ = v___y_1422_;
v___y_1382_ = v___y_1423_;
v___y_1383_ = v___y_1432_;
v___y_1384_ = v___x_1436_;
v___y_1385_ = v_a_1435_;
v___y_1386_ = v___y_1433_;
v___y_1387_ = v___y_1426_;
v___y_1388_ = v___y_1427_;
v_a_1389_ = v___x_1451_;
goto v___jp_1378_;
}
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v_a_1454_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1434_);
v___x_1455_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1013_);
v___x_1456_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1424_, v___y_1428_, v___y_1425_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set_tag(v___x_1459_, 1);
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
v___y_1402_ = v___y_1429_;
v___y_1403_ = v___y_1430_;
v___y_1404_ = v___y_1422_;
v___y_1405_ = v___y_1423_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v_a_1454_;
v___y_1408_ = v___y_1433_;
v___y_1409_ = v___y_1426_;
v___y_1410_ = v___x_1455_;
v___y_1411_ = v___y_1427_;
v_a_1412_ = v___x_1462_;
goto v___jp_1401_;
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
v_a_1465_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1456_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1456_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 0);
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
v___y_1402_ = v___y_1429_;
v___y_1403_ = v___y_1430_;
v___y_1404_ = v___y_1422_;
v___y_1405_ = v___y_1423_;
v___y_1406_ = v___y_1432_;
v___y_1407_ = v_a_1454_;
v___y_1408_ = v___y_1433_;
v___y_1409_ = v___y_1426_;
v___y_1410_ = v___x_1455_;
v___y_1411_ = v___y_1427_;
v_a_1412_ = v___x_1470_;
goto v___jp_1401_;
}
}
}
}
}
v___jp_1473_:
{
lean_object* v___x_1485_; double v___x_1486_; double v___x_1487_; double v___x_1488_; double v___x_1489_; double v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1485_ = lean_io_mono_nanos_now();
v___x_1486_ = lean_float_of_nat(v___y_1478_);
v___x_1487_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1488_ = lean_float_div(v___x_1486_, v___x_1487_);
v___x_1489_ = lean_float_of_nat(v___x_1485_);
v___x_1490_ = lean_float_div(v___x_1489_, v___x_1487_);
v___x_1491_ = lean_box_float(v___x_1488_);
v___x_1492_ = lean_box_float(v___x_1490_);
v___x_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1491_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_a_1484_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
lean_inc_ref(v___y_1479_);
lean_inc(v_trace_1013_);
v___x_1495_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1482_, v___y_1479_, v___y_1475_, v___y_1477_, v___y_1476_, v___f_1257_, v___x_1494_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1198_ = v___y_1474_;
v___y_1199_ = v___y_1475_;
v___y_1200_ = v___y_1479_;
v___y_1201_ = v___y_1480_;
v___y_1202_ = v___y_1481_;
v___y_1203_ = v___y_1482_;
v___y_1204_ = v___y_1483_;
v___y_1205_ = v___x_1495_;
goto v___jp_1197_;
}
v___jp_1496_:
{
lean_object* v___x_1508_; double v___x_1509_; double v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1508_ = lean_io_get_num_heartbeats();
v___x_1509_ = lean_float_of_nat(v___y_1497_);
v___x_1510_ = lean_float_of_nat(v___x_1508_);
v___x_1511_ = lean_box_float(v___x_1509_);
v___x_1512_ = lean_box_float(v___x_1510_);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1511_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_a_1507_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
lean_inc_ref(v___y_1502_);
lean_inc(v_trace_1013_);
v___x_1515_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1505_, v___y_1502_, v___y_1499_, v___y_1501_, v___y_1500_, v___f_1257_, v___x_1514_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1198_ = v___y_1498_;
v___y_1199_ = v___y_1499_;
v___y_1200_ = v___y_1502_;
v___y_1201_ = v___y_1503_;
v___y_1202_ = v___y_1504_;
v___y_1203_ = v___y_1505_;
v___y_1204_ = v___y_1506_;
v___y_1205_ = v___x_1515_;
goto v___jp_1197_;
}
v___jp_1516_:
{
lean_object* v___x_1529_; 
v___x_1529_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
if (v___y_1522_ == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v___x_1531_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1013_);
v___x_1532_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1528_, v___y_1520_, v___y_1527_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1532_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
lean_ctor_set_tag(v___x_1535_, 1);
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
v___y_1474_ = v___y_1521_;
v___y_1475_ = v___y_1517_;
v___y_1476_ = v_a_1530_;
v___y_1477_ = v___y_1523_;
v___y_1478_ = v___x_1531_;
v___y_1479_ = v___y_1524_;
v___y_1480_ = v___y_1525_;
v___y_1481_ = v___y_1526_;
v___y_1482_ = v___y_1518_;
v___y_1483_ = v___y_1519_;
v_a_1484_ = v___x_1538_;
goto v___jp_1473_;
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_a_1541_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1532_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1532_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 0);
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
v___y_1474_ = v___y_1521_;
v___y_1475_ = v___y_1517_;
v___y_1476_ = v_a_1530_;
v___y_1477_ = v___y_1523_;
v___y_1478_ = v___x_1531_;
v___y_1479_ = v___y_1524_;
v___y_1480_ = v___y_1525_;
v___y_1481_ = v___y_1526_;
v___y_1482_ = v___y_1518_;
v___y_1483_ = v___y_1519_;
v_a_1484_ = v___x_1546_;
goto v___jp_1473_;
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_a_1549_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1529_);
v___x_1550_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1013_);
v___x_1551_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1528_, v___y_1520_, v___y_1527_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
lean_ctor_set_tag(v___x_1554_, 1);
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
v___y_1497_ = v___x_1550_;
v___y_1498_ = v___y_1521_;
v___y_1499_ = v___y_1517_;
v___y_1500_ = v_a_1549_;
v___y_1501_ = v___y_1523_;
v___y_1502_ = v___y_1524_;
v___y_1503_ = v___y_1525_;
v___y_1504_ = v___y_1526_;
v___y_1505_ = v___y_1518_;
v___y_1506_ = v___y_1519_;
v_a_1507_ = v___x_1557_;
goto v___jp_1496_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
v_a_1560_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1551_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1551_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set_tag(v___x_1562_, 0);
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
v___y_1497_ = v___x_1550_;
v___y_1498_ = v___y_1521_;
v___y_1499_ = v___y_1517_;
v___y_1500_ = v_a_1549_;
v___y_1501_ = v___y_1523_;
v___y_1502_ = v___y_1524_;
v___y_1503_ = v___y_1525_;
v___y_1504_ = v___y_1526_;
v___y_1505_ = v___y_1518_;
v___y_1506_ = v___y_1519_;
v_a_1507_ = v___x_1565_;
goto v___jp_1496_;
}
}
}
}
}
v___jp_1568_:
{
lean_object* v___x_1580_; double v___x_1581_; double v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1580_ = lean_io_get_num_heartbeats();
v___x_1581_ = lean_float_of_nat(v___y_1573_);
v___x_1582_ = lean_float_of_nat(v___x_1580_);
v___x_1583_ = lean_box_float(v___x_1581_);
v___x_1584_ = lean_box_float(v___x_1582_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_a_1579_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
lean_inc_ref(v___y_1571_);
lean_inc(v_trace_1013_);
v___x_1587_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1576_, v___y_1571_, v___y_1570_, v___y_1578_, v___y_1575_, v___f_1341_, v___x_1586_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1198_ = v___y_1569_;
v___y_1199_ = v___y_1570_;
v___y_1200_ = v___y_1571_;
v___y_1201_ = v___y_1572_;
v___y_1202_ = v___y_1574_;
v___y_1203_ = v___y_1576_;
v___y_1204_ = v___y_1577_;
v___y_1205_ = v___x_1587_;
goto v___jp_1197_;
}
v___jp_1588_:
{
lean_object* v___x_1600_; double v___x_1601_; double v___x_1602_; double v___x_1603_; double v___x_1604_; double v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1600_ = lean_io_mono_nanos_now();
v___x_1601_ = lean_float_of_nat(v___y_1591_);
v___x_1602_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1603_ = lean_float_div(v___x_1601_, v___x_1602_);
v___x_1604_ = lean_float_of_nat(v___x_1600_);
v___x_1605_ = lean_float_div(v___x_1604_, v___x_1602_);
v___x_1606_ = lean_box_float(v___x_1603_);
v___x_1607_ = lean_box_float(v___x_1605_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v_a_1599_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
lean_inc_ref(v___y_1592_);
lean_inc(v_trace_1013_);
v___x_1610_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1596_, v___y_1592_, v___y_1590_, v___y_1598_, v___y_1595_, v___f_1341_, v___x_1609_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1198_ = v___y_1589_;
v___y_1199_ = v___y_1590_;
v___y_1200_ = v___y_1592_;
v___y_1201_ = v___y_1593_;
v___y_1202_ = v___y_1594_;
v___y_1203_ = v___y_1596_;
v___y_1204_ = v___y_1597_;
v___y_1205_ = v___x_1610_;
goto v___jp_1197_;
}
v___jp_1611_:
{
lean_object* v___x_1623_; double v___x_1624_; double v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1623_ = lean_io_get_num_heartbeats();
v___x_1624_ = lean_float_of_nat(v___y_1618_);
v___x_1625_ = lean_float_of_nat(v___x_1623_);
v___x_1626_ = lean_box_float(v___x_1624_);
v___x_1627_ = lean_box_float(v___x_1625_);
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v_a_1622_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
lean_inc_ref(v___y_1615_);
lean_inc(v_trace_1013_);
v___x_1630_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1620_, v___y_1615_, v___y_1613_, v___y_1617_, v___y_1614_, v___f_1377_, v___x_1629_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1198_ = v___y_1612_;
v___y_1199_ = v___y_1613_;
v___y_1200_ = v___y_1615_;
v___y_1201_ = v___y_1616_;
v___y_1202_ = v___y_1619_;
v___y_1203_ = v___y_1620_;
v___y_1204_ = v___y_1621_;
v___y_1205_ = v___x_1630_;
goto v___jp_1197_;
}
v___jp_1631_:
{
lean_object* v___x_1643_; double v___x_1644_; double v___x_1645_; double v___x_1646_; double v___x_1647_; double v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1643_ = lean_io_mono_nanos_now();
v___x_1644_ = lean_float_of_nat(v___y_1635_);
v___x_1645_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1646_ = lean_float_div(v___x_1644_, v___x_1645_);
v___x_1647_ = lean_float_of_nat(v___x_1643_);
v___x_1648_ = lean_float_div(v___x_1647_, v___x_1645_);
v___x_1649_ = lean_box_float(v___x_1646_);
v___x_1650_ = lean_box_float(v___x_1648_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v_a_1642_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
lean_inc_ref(v___y_1636_);
lean_inc(v_trace_1013_);
v___x_1653_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1640_, v___y_1636_, v___y_1633_, v___y_1638_, v___y_1634_, v___f_1377_, v___x_1652_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1198_ = v___y_1632_;
v___y_1199_ = v___y_1633_;
v___y_1200_ = v___y_1636_;
v___y_1201_ = v___y_1637_;
v___y_1202_ = v___y_1639_;
v___y_1203_ = v___y_1640_;
v___y_1204_ = v___y_1641_;
v___y_1205_ = v___x_1653_;
goto v___jp_1197_;
}
v___jp_1654_:
{
lean_object* v___x_1667_; 
v___x_1667_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
if (v___y_1661_ == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1013_);
v___x_1670_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1656_, v___y_1659_, v___y_1666_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 1);
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
v___y_1632_ = v___y_1660_;
v___y_1633_ = v___y_1655_;
v___y_1634_ = v_a_1668_;
v___y_1635_ = v___x_1669_;
v___y_1636_ = v___y_1662_;
v___y_1637_ = v___y_1663_;
v___y_1638_ = v___y_1664_;
v___y_1639_ = v___y_1665_;
v___y_1640_ = v___y_1657_;
v___y_1641_ = v___y_1658_;
v_a_1642_ = v___x_1676_;
goto v___jp_1631_;
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
v_a_1679_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1670_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1670_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 0);
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
v___y_1632_ = v___y_1660_;
v___y_1633_ = v___y_1655_;
v___y_1634_ = v_a_1668_;
v___y_1635_ = v___x_1669_;
v___y_1636_ = v___y_1662_;
v___y_1637_ = v___y_1663_;
v___y_1638_ = v___y_1664_;
v___y_1639_ = v___y_1665_;
v___y_1640_ = v___y_1657_;
v___y_1641_ = v___y_1658_;
v_a_1642_ = v___x_1684_;
goto v___jp_1631_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_a_1687_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1667_);
v___x_1688_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1013_);
v___x_1689_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1656_, v___y_1659_, v___y_1666_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 1);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
v___y_1612_ = v___y_1660_;
v___y_1613_ = v___y_1655_;
v___y_1614_ = v_a_1687_;
v___y_1615_ = v___y_1662_;
v___y_1616_ = v___y_1663_;
v___y_1617_ = v___y_1664_;
v___y_1618_ = v___x_1688_;
v___y_1619_ = v___y_1665_;
v___y_1620_ = v___y_1657_;
v___y_1621_ = v___y_1658_;
v_a_1622_ = v___x_1695_;
goto v___jp_1611_;
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
v_a_1698_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1689_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1689_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 0);
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
v___y_1612_ = v___y_1660_;
v___y_1613_ = v___y_1655_;
v___y_1614_ = v_a_1687_;
v___y_1615_ = v___y_1662_;
v___y_1616_ = v___y_1663_;
v___y_1617_ = v___y_1664_;
v___y_1618_ = v___x_1688_;
v___y_1619_ = v___y_1665_;
v___y_1620_ = v___y_1657_;
v___y_1621_ = v___y_1658_;
v_a_1622_ = v___x_1703_;
goto v___jp_1611_;
}
}
}
}
}
v___jp_1706_:
{
lean_object* v___x_1718_; double v___x_1719_; double v___x_1720_; double v___x_1721_; double v___x_1722_; double v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1718_ = lean_io_mono_nanos_now();
v___x_1719_ = lean_float_of_nat(v___y_1713_);
v___x_1720_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1721_ = lean_float_div(v___x_1719_, v___x_1720_);
v___x_1722_ = lean_float_of_nat(v___x_1718_);
v___x_1723_ = lean_float_div(v___x_1722_, v___x_1720_);
v___x_1724_ = lean_box_float(v___x_1721_);
v___x_1725_ = lean_box_float(v___x_1723_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1724_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v_a_1717_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
lean_inc_ref(v___y_1711_);
lean_inc(v_trace_1013_);
v___x_1728_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1714_, v___y_1711_, v___y_1709_, v___y_1715_, v___y_1710_, v___f_1341_, v___x_1727_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1147_ = v___y_1707_;
v___y_1148_ = v___y_1709_;
v___y_1149_ = v___y_1708_;
v___y_1150_ = v___y_1711_;
v___y_1151_ = v___y_1712_;
v___y_1152_ = v___y_1714_;
v___y_1153_ = v___y_1716_;
v___y_1154_ = v___x_1728_;
goto v___jp_1146_;
}
v___jp_1729_:
{
lean_object* v___x_1741_; double v___x_1742_; double v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1741_ = lean_io_get_num_heartbeats();
v___x_1742_ = lean_float_of_nat(v___y_1733_);
v___x_1743_ = lean_float_of_nat(v___x_1741_);
v___x_1744_ = lean_box_float(v___x_1742_);
v___x_1745_ = lean_box_float(v___x_1743_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_a_1740_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
lean_inc_ref(v___y_1735_);
lean_inc(v_trace_1013_);
v___x_1748_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1737_, v___y_1735_, v___y_1732_, v___y_1738_, v___y_1734_, v___f_1341_, v___x_1747_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1147_ = v___y_1730_;
v___y_1148_ = v___y_1732_;
v___y_1149_ = v___y_1731_;
v___y_1150_ = v___y_1735_;
v___y_1151_ = v___y_1736_;
v___y_1152_ = v___y_1737_;
v___y_1153_ = v___y_1739_;
v___y_1154_ = v___x_1748_;
goto v___jp_1146_;
}
v___jp_1749_:
{
lean_object* v___x_1761_; double v___x_1762_; double v___x_1763_; double v___x_1764_; double v___x_1765_; double v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1761_ = lean_io_mono_nanos_now();
v___x_1762_ = lean_float_of_nat(v___y_1752_);
v___x_1763_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1764_ = lean_float_div(v___x_1762_, v___x_1763_);
v___x_1765_ = lean_float_of_nat(v___x_1761_);
v___x_1766_ = lean_float_div(v___x_1765_, v___x_1763_);
v___x_1767_ = lean_box_float(v___x_1764_);
v___x_1768_ = lean_box_float(v___x_1766_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v_a_1760_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
lean_inc_ref(v___y_1755_);
lean_inc(v_trace_1013_);
v___x_1771_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1758_, v___y_1755_, v___y_1754_, v___y_1751_, v___y_1757_, v___f_1257_, v___x_1770_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1147_ = v___y_1750_;
v___y_1148_ = v___y_1754_;
v___y_1149_ = v___y_1753_;
v___y_1150_ = v___y_1755_;
v___y_1151_ = v___y_1756_;
v___y_1152_ = v___y_1758_;
v___y_1153_ = v___y_1759_;
v___y_1154_ = v___x_1771_;
goto v___jp_1146_;
}
v___jp_1772_:
{
lean_object* v___x_1784_; double v___x_1785_; double v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1784_ = lean_io_get_num_heartbeats();
v___x_1785_ = lean_float_of_nat(v___y_1778_);
v___x_1786_ = lean_float_of_nat(v___x_1784_);
v___x_1787_ = lean_box_float(v___x_1785_);
v___x_1788_ = lean_box_float(v___x_1786_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1787_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_a_1783_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
lean_inc_ref(v___y_1777_);
lean_inc(v_trace_1013_);
v___x_1791_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1781_, v___y_1777_, v___y_1776_, v___y_1774_, v___y_1780_, v___f_1257_, v___x_1790_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1147_ = v___y_1773_;
v___y_1148_ = v___y_1776_;
v___y_1149_ = v___y_1775_;
v___y_1150_ = v___y_1777_;
v___y_1151_ = v___y_1779_;
v___y_1152_ = v___y_1781_;
v___y_1153_ = v___y_1782_;
v___y_1154_ = v___x_1791_;
goto v___jp_1146_;
}
v___jp_1792_:
{
lean_object* v___x_1805_; 
v___x_1805_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
if (v___y_1802_ == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref(v___x_1805_);
v___x_1807_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1013_);
v___x_1808_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1796_, v___y_1800_, v___y_1797_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 1);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
v___y_1750_ = v___y_1801_;
v___y_1751_ = v___y_1793_;
v___y_1752_ = v___x_1807_;
v___y_1753_ = v___y_1794_;
v___y_1754_ = v___y_1795_;
v___y_1755_ = v___y_1803_;
v___y_1756_ = v___y_1804_;
v___y_1757_ = v_a_1806_;
v___y_1758_ = v___y_1798_;
v___y_1759_ = v___y_1799_;
v_a_1760_ = v___x_1814_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_a_1817_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1808_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1808_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set_tag(v___x_1819_, 0);
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
v___y_1750_ = v___y_1801_;
v___y_1751_ = v___y_1793_;
v___y_1752_ = v___x_1807_;
v___y_1753_ = v___y_1794_;
v___y_1754_ = v___y_1795_;
v___y_1755_ = v___y_1803_;
v___y_1756_ = v___y_1804_;
v___y_1757_ = v_a_1806_;
v___y_1758_ = v___y_1798_;
v___y_1759_ = v___y_1799_;
v_a_1760_ = v___x_1822_;
goto v___jp_1749_;
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v_a_1825_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1825_);
lean_dec_ref(v___x_1805_);
v___x_1826_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1013_);
v___x_1827_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1796_, v___y_1800_, v___y_1797_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 1);
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
v___y_1773_ = v___y_1801_;
v___y_1774_ = v___y_1793_;
v___y_1775_ = v___y_1794_;
v___y_1776_ = v___y_1795_;
v___y_1777_ = v___y_1803_;
v___y_1778_ = v___x_1826_;
v___y_1779_ = v___y_1804_;
v___y_1780_ = v_a_1825_;
v___y_1781_ = v___y_1798_;
v___y_1782_ = v___y_1799_;
v_a_1783_ = v___x_1833_;
goto v___jp_1772_;
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_a_1836_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1827_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1827_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set_tag(v___x_1838_, 0);
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
v___y_1773_ = v___y_1801_;
v___y_1774_ = v___y_1793_;
v___y_1775_ = v___y_1794_;
v___y_1776_ = v___y_1795_;
v___y_1777_ = v___y_1803_;
v___y_1778_ = v___x_1826_;
v___y_1779_ = v___y_1804_;
v___y_1780_ = v_a_1825_;
v___y_1781_ = v___y_1798_;
v___y_1782_ = v___y_1799_;
v_a_1783_ = v___x_1841_;
goto v___jp_1772_;
}
}
}
}
}
v___jp_1844_:
{
lean_object* v___x_1852_; double v___x_1853_; double v___x_1854_; double v___x_1855_; double v___x_1856_; double v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1852_ = lean_io_mono_nanos_now();
v___x_1853_ = lean_float_of_nat(v___y_1849_);
v___x_1854_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1855_ = lean_float_div(v___x_1853_, v___x_1854_);
v___x_1856_ = lean_float_of_nat(v___x_1852_);
v___x_1857_ = lean_float_div(v___x_1856_, v___x_1854_);
v___x_1858_ = lean_box_float(v___x_1855_);
v___x_1859_ = lean_box_float(v___x_1857_);
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v_a_1851_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
lean_inc_ref(v___y_1847_);
v___x_1862_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1850_, v___y_1847_, v___y_1845_, v___y_1846_, v___y_1848_, v___f_1377_, v___x_1861_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1862_;
}
v___jp_1863_:
{
lean_object* v___x_1871_; double v___x_1872_; double v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1871_ = lean_io_get_num_heartbeats();
v___x_1872_ = lean_float_of_nat(v___y_1866_);
v___x_1873_ = lean_float_of_nat(v___x_1871_);
v___x_1874_ = lean_box_float(v___x_1872_);
v___x_1875_ = lean_box_float(v___x_1873_);
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v_a_1870_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
lean_inc_ref(v___y_1867_);
v___x_1878_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1869_, v___y_1867_, v___y_1864_, v___y_1865_, v___y_1868_, v___f_1377_, v___x_1877_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1878_;
}
v___jp_1879_:
{
lean_object* v___x_1887_; lean_object* v_a_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1887_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1887_);
v___x_1889_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1890_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1880_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1013_);
v___x_1892_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1883_, v___y_1886_, v___y_1885_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 1);
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
v___y_1845_ = v___y_1880_;
v___y_1846_ = v___y_1881_;
v___y_1847_ = v___y_1882_;
v___y_1848_ = v_a_1888_;
v___y_1849_ = v___x_1891_;
v___y_1850_ = v___y_1884_;
v_a_1851_ = v___x_1898_;
goto v___jp_1844_;
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_a_1901_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1892_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1892_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 0);
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
v___y_1845_ = v___y_1880_;
v___y_1846_ = v___y_1881_;
v___y_1847_ = v___y_1882_;
v___y_1848_ = v_a_1888_;
v___y_1849_ = v___x_1891_;
v___y_1850_ = v___y_1884_;
v_a_1851_ = v___x_1906_;
goto v___jp_1844_;
}
}
}
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1013_);
v___x_1910_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1883_, v___y_1886_, v___y_1885_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 1);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
v___y_1864_ = v___y_1880_;
v___y_1865_ = v___y_1881_;
v___y_1866_ = v___x_1909_;
v___y_1867_ = v___y_1882_;
v___y_1868_ = v_a_1888_;
v___y_1869_ = v___y_1884_;
v_a_1870_ = v___x_1916_;
goto v___jp_1863_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1919_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1910_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1910_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 0);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
v___y_1864_ = v___y_1880_;
v___y_1865_ = v___y_1881_;
v___y_1866_ = v___x_1909_;
v___y_1867_ = v___y_1882_;
v___y_1868_ = v_a_1888_;
v___y_1869_ = v___y_1884_;
v_a_1870_ = v___x_1924_;
goto v___jp_1863_;
}
}
}
}
}
v___jp_1929_:
{
lean_object* v___x_1935_; lean_object* v_a_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v___x_1935_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1935_);
v___x_1937_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1938_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1930_, v___x_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1013_);
v___x_1940_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v_n_1928_, v___y_1934_, v_acc_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set_tag(v___x_1943_, 1);
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
v___y_1343_ = v___x_1939_;
v___y_1344_ = v___y_1930_;
v___y_1345_ = v___y_1932_;
v___y_1346_ = v___y_1931_;
v___y_1347_ = v_a_1936_;
v___y_1348_ = v___y_1933_;
v_a_1349_ = v___x_1946_;
goto v___jp_1342_;
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v_a_1949_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1940_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1940_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set_tag(v___x_1951_, 0);
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
v___y_1343_ = v___x_1939_;
v___y_1344_ = v___y_1930_;
v___y_1345_ = v___y_1932_;
v___y_1346_ = v___y_1931_;
v___y_1347_ = v_a_1936_;
v___y_1348_ = v___y_1933_;
v_a_1349_ = v___x_1954_;
goto v___jp_1342_;
}
}
}
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1013_);
v___x_1958_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v_n_1928_, v___y_1934_, v_acc_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 1);
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
v___y_1362_ = v___y_1930_;
v___y_1363_ = v___y_1932_;
v___y_1364_ = v___y_1931_;
v___y_1365_ = v___x_1957_;
v___y_1366_ = v_a_1936_;
v___y_1367_ = v___y_1933_;
v_a_1368_ = v___x_1964_;
goto v___jp_1361_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v_a_1967_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1958_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1958_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set_tag(v___x_1969_, 0);
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
v___y_1362_ = v___y_1930_;
v___y_1363_ = v___y_1932_;
v___y_1364_ = v___y_1931_;
v___y_1365_ = v___x_1957_;
v___y_1366_ = v_a_1936_;
v___y_1367_ = v___y_1933_;
v_a_1368_ = v___x_1972_;
goto v___jp_1361_;
}
}
}
}
}
v___jp_1975_:
{
if (v___y_1985_ == 0)
{
lean_object* v___x_1986_; 
lean_dec_ref(v___y_1976_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v___y_1980_);
v___x_1986_ = lean_apply_6(v___y_1978_, v___y_1980_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1986_);
if (lean_obj_tag(v_a_1987_) == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v___x_1988_ = lean_nat_add(v_n_1928_, v_one_1927_);
lean_dec(v_n_1928_);
v___x_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___y_1980_);
lean_ctor_set(v___x_1989_, 1, v_acc_1018_);
v___x_1990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1013_);
v___x_1991_ = l_Lean_Name_append(v___x_1990_, v_trace_1013_);
v___x_1992_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1984_, v___y_1977_, v___x_1991_);
lean_dec(v___x_1991_);
if (v___x_1992_ == 0)
{
if (v___y_1981_ == 0)
{
v_n_1016_ = v___x_1988_;
v_curr_1017_ = v___y_1983_;
v_acc_1018_ = v___x_1989_;
goto _start;
}
else
{
v___y_1294_ = v___x_1988_;
v___y_1295_ = v___y_1977_;
v___y_1296_ = v___y_1979_;
v___y_1297_ = v___x_1989_;
v___y_1298_ = v___y_1982_;
v___y_1299_ = v___x_1992_;
v___y_1300_ = v___y_1983_;
goto v___jp_1293_;
}
}
else
{
v___y_1294_ = v___x_1988_;
v___y_1295_ = v___y_1977_;
v___y_1296_ = v___y_1979_;
v___y_1297_ = v___x_1989_;
v___y_1298_ = v___y_1982_;
v___y_1299_ = v___x_1992_;
v___y_1300_ = v___y_1983_;
goto v___jp_1293_;
}
}
else
{
lean_object* v_val_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
lean_dec(v___y_1980_);
v_val_1994_ = lean_ctor_get(v_a_1987_, 0);
lean_inc(v_val_1994_);
lean_dec_ref(v_a_1987_);
v___x_1995_ = l_List_appendTR___redArg(v_val_1994_, v___y_1983_);
v___x_1996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1013_);
v___x_1997_ = l_Lean_Name_append(v___x_1996_, v_trace_1013_);
v___x_1998_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1984_, v___y_1977_, v___x_1997_);
lean_dec(v___x_1997_);
if (v___x_1998_ == 0)
{
if (v___y_1981_ == 0)
{
v_n_1016_ = v_n_1928_;
v_curr_1017_ = v___x_1995_;
goto _start;
}
else
{
v___y_1930_ = v___y_1977_;
v___y_1931_ = v___y_1979_;
v___y_1932_ = v___x_1998_;
v___y_1933_ = v___y_1982_;
v___y_1934_ = v___x_1995_;
goto v___jp_1929_;
}
}
else
{
v___y_1930_ = v___y_1977_;
v___y_1931_ = v___y_1979_;
v___y_1932_ = v___x_1998_;
v___y_1933_ = v___y_1982_;
v___y_1934_ = v___x_1995_;
goto v___jp_1929_;
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v___y_1983_);
lean_dec(v___y_1980_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
v_a_2000_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1986_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1986_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_dec(v___y_1983_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1978_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
return v___y_1976_;
}
}
v___jp_2008_:
{
lean_object* v___x_2019_; 
v___x_2019_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
if (v___y_2012_ == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref(v___x_2019_);
v___x_2021_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1013_);
v___x_2022_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v_n_1928_, v___y_2013_, v_acc_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set_tag(v___x_2025_, 1);
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
v___y_1707_ = v___y_2009_;
v___y_1708_ = v___y_2011_;
v___y_1709_ = v___y_2010_;
v___y_1710_ = v_a_2020_;
v___y_1711_ = v___y_2014_;
v___y_1712_ = v___y_2015_;
v___y_1713_ = v___x_2021_;
v___y_1714_ = v___y_2016_;
v___y_1715_ = v___y_2017_;
v___y_1716_ = v___y_2018_;
v_a_1717_ = v___x_2028_;
goto v___jp_1706_;
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
v_a_2031_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2022_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2022_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 0);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
v___y_1707_ = v___y_2009_;
v___y_1708_ = v___y_2011_;
v___y_1709_ = v___y_2010_;
v___y_1710_ = v_a_2020_;
v___y_1711_ = v___y_2014_;
v___y_1712_ = v___y_2015_;
v___y_1713_ = v___x_2021_;
v___y_1714_ = v___y_2016_;
v___y_1715_ = v___y_2017_;
v___y_1716_ = v___y_2018_;
v_a_1717_ = v___x_2036_;
goto v___jp_1706_;
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v_a_2039_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2039_);
lean_dec_ref(v___x_2019_);
v___x_2040_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1013_);
v___x_2041_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v_n_1928_, v___y_2013_, v_acc_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 1);
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
v___y_1730_ = v___y_2009_;
v___y_1731_ = v___y_2011_;
v___y_1732_ = v___y_2010_;
v___y_1733_ = v___x_2040_;
v___y_1734_ = v_a_2039_;
v___y_1735_ = v___y_2014_;
v___y_1736_ = v___y_2015_;
v___y_1737_ = v___y_2016_;
v___y_1738_ = v___y_2017_;
v___y_1739_ = v___y_2018_;
v_a_1740_ = v___x_2047_;
goto v___jp_1729_;
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
v_a_2050_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2041_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2041_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set_tag(v___x_2052_, 0);
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
v___y_1730_ = v___y_2009_;
v___y_1731_ = v___y_2011_;
v___y_1732_ = v___y_2010_;
v___y_1733_ = v___x_2040_;
v___y_1734_ = v_a_2039_;
v___y_1735_ = v___y_2014_;
v___y_1736_ = v___y_2015_;
v___y_1737_ = v___y_2016_;
v___y_1738_ = v___y_2017_;
v___y_1739_ = v___y_2018_;
v_a_1740_ = v___x_2055_;
goto v___jp_1729_;
}
}
}
}
}
v___jp_2058_:
{
if (v___y_2072_ == 0)
{
lean_object* v___x_2073_; 
lean_dec_ref(v___y_2071_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v___y_2069_);
v___x_2073_ = lean_apply_6(v___y_2061_, v___y_2069_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2073_);
if (lean_obj_tag(v_a_2074_) == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2075_ = lean_nat_add(v_n_1928_, v_one_1927_);
lean_dec(v_n_1928_);
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___y_2069_);
lean_ctor_set(v___x_2076_, 1, v_acc_1018_);
v___x_2077_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1013_);
v___x_2078_ = l_Lean_Name_append(v___x_2077_, v_trace_1013_);
v___x_2079_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2063_, v___y_2059_, v___x_2078_);
lean_dec(v___x_2078_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; uint8_t v___x_2081_; 
v___x_2080_ = l_Lean_trace_profiler;
v___x_2081_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2059_, v___x_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; 
lean_inc(v_trace_1013_);
v___x_2082_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___x_2075_, v___y_2065_, v___x_2076_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1147_ = v___y_2066_;
v___y_1148_ = v___y_2059_;
v___y_1149_ = v___y_2060_;
v___y_1150_ = v___y_2068_;
v___y_1151_ = v___y_2070_;
v___y_1152_ = v___y_2062_;
v___y_1153_ = v___y_2064_;
v___y_1154_ = v___x_2082_;
goto v___jp_1146_;
}
else
{
v___y_1793_ = v___x_2079_;
v___y_1794_ = v___y_2060_;
v___y_1795_ = v___y_2059_;
v___y_1796_ = v___x_2075_;
v___y_1797_ = v___x_2076_;
v___y_1798_ = v___y_2062_;
v___y_1799_ = v___y_2064_;
v___y_1800_ = v___y_2065_;
v___y_1801_ = v___y_2066_;
v___y_1802_ = v___y_2067_;
v___y_1803_ = v___y_2068_;
v___y_1804_ = v___y_2070_;
goto v___jp_1792_;
}
}
else
{
v___y_1793_ = v___x_2079_;
v___y_1794_ = v___y_2060_;
v___y_1795_ = v___y_2059_;
v___y_1796_ = v___x_2075_;
v___y_1797_ = v___x_2076_;
v___y_1798_ = v___y_2062_;
v___y_1799_ = v___y_2064_;
v___y_1800_ = v___y_2065_;
v___y_1801_ = v___y_2066_;
v___y_1802_ = v___y_2067_;
v___y_1803_ = v___y_2068_;
v___y_1804_ = v___y_2070_;
goto v___jp_1792_;
}
}
else
{
lean_object* v_val_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
lean_dec(v___y_2069_);
v_val_2083_ = lean_ctor_get(v_a_2074_, 0);
lean_inc(v_val_2083_);
lean_dec_ref(v_a_2074_);
v___x_2084_ = l_List_appendTR___redArg(v_val_2083_, v___y_2065_);
v___x_2085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1013_);
v___x_2086_ = l_Lean_Name_append(v___x_2085_, v_trace_1013_);
v___x_2087_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2063_, v___y_2059_, v___x_2086_);
lean_dec(v___x_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; uint8_t v___x_2089_; 
v___x_2088_ = l_Lean_trace_profiler;
v___x_2089_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2059_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_inc(v_trace_1013_);
v___x_2090_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v_n_1928_, v___x_2084_, v_acc_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1147_ = v___y_2066_;
v___y_1148_ = v___y_2059_;
v___y_1149_ = v___y_2060_;
v___y_1150_ = v___y_2068_;
v___y_1151_ = v___y_2070_;
v___y_1152_ = v___y_2062_;
v___y_1153_ = v___y_2064_;
v___y_1154_ = v___x_2090_;
goto v___jp_1146_;
}
else
{
v___y_2009_ = v___y_2066_;
v___y_2010_ = v___y_2059_;
v___y_2011_ = v___y_2060_;
v___y_2012_ = v___y_2067_;
v___y_2013_ = v___x_2084_;
v___y_2014_ = v___y_2068_;
v___y_2015_ = v___y_2070_;
v___y_2016_ = v___y_2062_;
v___y_2017_ = v___x_2087_;
v___y_2018_ = v___y_2064_;
goto v___jp_2008_;
}
}
else
{
v___y_2009_ = v___y_2066_;
v___y_2010_ = v___y_2059_;
v___y_2011_ = v___y_2060_;
v___y_2012_ = v___y_2067_;
v___y_2013_ = v___x_2084_;
v___y_2014_ = v___y_2068_;
v___y_2015_ = v___y_2070_;
v___y_2016_ = v___y_2062_;
v___y_2017_ = v___x_2087_;
v___y_2018_ = v___y_2064_;
goto v___jp_2008_;
}
}
}
else
{
lean_object* v_a_2091_; 
lean_dec(v___y_2069_);
lean_dec(v___y_2065_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec_ref(v_cfg_1012_);
v_a_2091_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2073_);
v___y_1137_ = v___y_2066_;
v___y_1138_ = v___y_2060_;
v___y_1139_ = v___y_2059_;
v___y_1140_ = v___y_2068_;
v___y_1141_ = v___y_2070_;
v___y_1142_ = v___y_2062_;
v___y_1143_ = v___y_2064_;
v_a_1144_ = v_a_2091_;
goto v___jp_1136_;
}
}
else
{
lean_dec(v___y_2069_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2061_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec_ref(v_cfg_1012_);
v___y_1137_ = v___y_2066_;
v___y_1138_ = v___y_2060_;
v___y_1139_ = v___y_2059_;
v___y_1140_ = v___y_2068_;
v___y_1141_ = v___y_2070_;
v___y_1142_ = v___y_2062_;
v___y_1143_ = v___y_2064_;
v_a_1144_ = v___y_2071_;
goto v___jp_1136_;
}
}
v___jp_2092_:
{
lean_object* v___x_2103_; 
v___x_2103_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
if (v___y_2095_ == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v___x_2103_);
v___x_2105_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1013_);
v___x_2106_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v_n_1928_, v___y_2097_, v_acc_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set_tag(v___x_2109_, 1);
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
v___y_1589_ = v___y_2093_;
v___y_1590_ = v___y_2094_;
v___y_1591_ = v___x_2105_;
v___y_1592_ = v___y_2096_;
v___y_1593_ = v___y_2098_;
v___y_1594_ = v___y_2099_;
v___y_1595_ = v_a_2104_;
v___y_1596_ = v___y_2100_;
v___y_1597_ = v___y_2102_;
v___y_1598_ = v___y_2101_;
v_a_1599_ = v___x_2112_;
goto v___jp_1588_;
}
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
v_a_2115_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2106_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2106_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set_tag(v___x_2117_, 0);
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
v___y_1589_ = v___y_2093_;
v___y_1590_ = v___y_2094_;
v___y_1591_ = v___x_2105_;
v___y_1592_ = v___y_2096_;
v___y_1593_ = v___y_2098_;
v___y_1594_ = v___y_2099_;
v___y_1595_ = v_a_2104_;
v___y_1596_ = v___y_2100_;
v___y_1597_ = v___y_2102_;
v___y_1598_ = v___y_2101_;
v_a_1599_ = v___x_2120_;
goto v___jp_1588_;
}
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_a_2123_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2103_);
v___x_2124_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1013_);
v___x_2125_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v_n_1928_, v___y_2097_, v_acc_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 1);
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
v___y_1569_ = v___y_2093_;
v___y_1570_ = v___y_2094_;
v___y_1571_ = v___y_2096_;
v___y_1572_ = v___y_2098_;
v___y_1573_ = v___x_2124_;
v___y_1574_ = v___y_2099_;
v___y_1575_ = v_a_2123_;
v___y_1576_ = v___y_2100_;
v___y_1577_ = v___y_2102_;
v___y_1578_ = v___y_2101_;
v_a_1579_ = v___x_2131_;
goto v___jp_1568_;
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
v_a_2134_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2125_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2125_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set_tag(v___x_2136_, 0);
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
v___y_1569_ = v___y_2093_;
v___y_1570_ = v___y_2094_;
v___y_1571_ = v___y_2096_;
v___y_1572_ = v___y_2098_;
v___y_1573_ = v___x_2124_;
v___y_1574_ = v___y_2099_;
v___y_1575_ = v_a_2123_;
v___y_1576_ = v___y_2100_;
v___y_1577_ = v___y_2102_;
v___y_1578_ = v___y_2101_;
v_a_1579_ = v___x_2139_;
goto v___jp_1568_;
}
}
}
}
}
v___jp_2142_:
{
if (v___y_2156_ == 0)
{
lean_object* v___x_2157_; 
lean_dec_ref(v___y_2154_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v___y_2152_);
v___x_2157_ = lean_apply_6(v___y_2144_, v___y_2152_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref(v___x_2157_);
if (lean_obj_tag(v_a_2158_) == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2159_ = lean_nat_add(v_n_1928_, v_one_1927_);
lean_dec(v_n_1928_);
v___x_2160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___y_2152_);
lean_ctor_set(v___x_2160_, 1, v_acc_1018_);
v___x_2161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1013_);
v___x_2162_ = l_Lean_Name_append(v___x_2161_, v_trace_1013_);
v___x_2163_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2146_, v___y_2143_, v___x_2162_);
lean_dec(v___x_2162_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = l_Lean_trace_profiler;
v___x_2165_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2143_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; 
lean_inc(v_trace_1013_);
v___x_2166_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___x_2159_, v___y_2148_, v___x_2160_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1198_ = v___y_2149_;
v___y_1199_ = v___y_2143_;
v___y_1200_ = v___y_2151_;
v___y_1201_ = v___y_2153_;
v___y_1202_ = v___y_2155_;
v___y_1203_ = v___y_2145_;
v___y_1204_ = v___y_2147_;
v___y_1205_ = v___x_2166_;
goto v___jp_1197_;
}
else
{
v___y_1517_ = v___y_2143_;
v___y_1518_ = v___y_2145_;
v___y_1519_ = v___y_2147_;
v___y_1520_ = v___y_2148_;
v___y_1521_ = v___y_2149_;
v___y_1522_ = v___y_2150_;
v___y_1523_ = v___x_2163_;
v___y_1524_ = v___y_2151_;
v___y_1525_ = v___y_2153_;
v___y_1526_ = v___y_2155_;
v___y_1527_ = v___x_2160_;
v___y_1528_ = v___x_2159_;
goto v___jp_1516_;
}
}
else
{
v___y_1517_ = v___y_2143_;
v___y_1518_ = v___y_2145_;
v___y_1519_ = v___y_2147_;
v___y_1520_ = v___y_2148_;
v___y_1521_ = v___y_2149_;
v___y_1522_ = v___y_2150_;
v___y_1523_ = v___x_2163_;
v___y_1524_ = v___y_2151_;
v___y_1525_ = v___y_2153_;
v___y_1526_ = v___y_2155_;
v___y_1527_ = v___x_2160_;
v___y_1528_ = v___x_2159_;
goto v___jp_1516_;
}
}
else
{
lean_object* v_val_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
lean_dec(v___y_2152_);
v_val_2167_ = lean_ctor_get(v_a_2158_, 0);
lean_inc(v_val_2167_);
lean_dec_ref(v_a_2158_);
v___x_2168_ = l_List_appendTR___redArg(v_val_2167_, v___y_2148_);
v___x_2169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1013_);
v___x_2170_ = l_Lean_Name_append(v___x_2169_, v_trace_1013_);
v___x_2171_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2146_, v___y_2143_, v___x_2170_);
lean_dec(v___x_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = l_Lean_trace_profiler;
v___x_2173_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2143_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_inc(v_trace_1013_);
v___x_2174_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v_n_1928_, v___x_2168_, v_acc_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1198_ = v___y_2149_;
v___y_1199_ = v___y_2143_;
v___y_1200_ = v___y_2151_;
v___y_1201_ = v___y_2153_;
v___y_1202_ = v___y_2155_;
v___y_1203_ = v___y_2145_;
v___y_1204_ = v___y_2147_;
v___y_1205_ = v___x_2174_;
goto v___jp_1197_;
}
else
{
v___y_2093_ = v___y_2149_;
v___y_2094_ = v___y_2143_;
v___y_2095_ = v___y_2150_;
v___y_2096_ = v___y_2151_;
v___y_2097_ = v___x_2168_;
v___y_2098_ = v___y_2153_;
v___y_2099_ = v___y_2155_;
v___y_2100_ = v___y_2145_;
v___y_2101_ = v___x_2171_;
v___y_2102_ = v___y_2147_;
goto v___jp_2092_;
}
}
else
{
v___y_2093_ = v___y_2149_;
v___y_2094_ = v___y_2143_;
v___y_2095_ = v___y_2150_;
v___y_2096_ = v___y_2151_;
v___y_2097_ = v___x_2168_;
v___y_2098_ = v___y_2153_;
v___y_2099_ = v___y_2155_;
v___y_2100_ = v___y_2145_;
v___y_2101_ = v___x_2171_;
v___y_2102_ = v___y_2147_;
goto v___jp_2092_;
}
}
}
else
{
lean_object* v_a_2175_; 
lean_dec(v___y_2152_);
lean_dec(v___y_2148_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec_ref(v_cfg_1012_);
v_a_2175_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2157_);
v___y_1188_ = v___y_2149_;
v___y_1189_ = v___y_2143_;
v___y_1190_ = v___y_2151_;
v___y_1191_ = v___y_2153_;
v___y_1192_ = v___y_2155_;
v___y_1193_ = v___y_2145_;
v___y_1194_ = v___y_2147_;
v_a_1195_ = v_a_2175_;
goto v___jp_1187_;
}
}
else
{
lean_dec(v___y_2152_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2144_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec_ref(v_cfg_1012_);
v___y_1188_ = v___y_2149_;
v___y_1189_ = v___y_2143_;
v___y_1190_ = v___y_2151_;
v___y_1191_ = v___y_2153_;
v___y_1192_ = v___y_2155_;
v___y_1193_ = v___y_2145_;
v___y_1194_ = v___y_2147_;
v_a_1195_ = v___y_2154_;
goto v___jp_1187_;
}
}
v___jp_2176_:
{
lean_object* v___x_2189_; lean_object* v_a_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2189_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref(v___x_2189_);
v___x_2191_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2192_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2177_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
lean_dec_ref(v___y_2179_);
v___x_2193_ = lean_io_mono_nanos_now();
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v___y_2186_);
v___x_2194_ = lean_apply_6(v___y_2180_, v___y_2186_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; uint8_t v___x_2196_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref(v___x_2194_);
v___x_2196_ = lean_unbox(v_a_2195_);
lean_dec(v_a_2195_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2197_; 
lean_inc_ref(v_next_1014_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v___y_2186_);
v___x_2197_ = lean_apply_7(v_next_1014_, v___y_2186_, v___y_2188_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; 
lean_dec(v___y_2186_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2178_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec_ref(v_cfg_1012_);
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
v___y_1178_ = v___y_2184_;
v___y_1179_ = v___y_2177_;
v___y_1180_ = v___y_2185_;
v___y_1181_ = v___x_2193_;
v___y_1182_ = v___y_2187_;
v___y_1183_ = v___y_2181_;
v___y_1184_ = v_a_2190_;
v_a_1185_ = v_a_2198_;
goto v___jp_1177_;
}
else
{
lean_object* v_a_2199_; uint8_t v___x_2200_; 
v_a_2199_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2197_);
v___x_2200_ = l_Lean_Exception_isInterrupt(v_a_2199_);
if (v___x_2200_ == 0)
{
uint8_t v___x_2201_; 
lean_inc(v_a_2199_);
v___x_2201_ = l_Lean_Exception_isRuntime(v_a_2199_);
v___y_2143_ = v___y_2177_;
v___y_2144_ = v___y_2178_;
v___y_2145_ = v___y_2181_;
v___y_2146_ = v___y_2182_;
v___y_2147_ = v_a_2190_;
v___y_2148_ = v___y_2183_;
v___y_2149_ = v___y_2184_;
v___y_2150_ = v___x_2192_;
v___y_2151_ = v___y_2185_;
v___y_2152_ = v___y_2186_;
v___y_2153_ = v___x_2193_;
v___y_2154_ = v_a_2199_;
v___y_2155_ = v___y_2187_;
v___y_2156_ = v___x_2201_;
goto v___jp_2142_;
}
else
{
v___y_2143_ = v___y_2177_;
v___y_2144_ = v___y_2178_;
v___y_2145_ = v___y_2181_;
v___y_2146_ = v___y_2182_;
v___y_2147_ = v_a_2190_;
v___y_2148_ = v___y_2183_;
v___y_2149_ = v___y_2184_;
v___y_2150_ = v___x_2192_;
v___y_2151_ = v___y_2185_;
v___y_2152_ = v___y_2186_;
v___y_2153_ = v___x_2193_;
v___y_2154_ = v_a_2199_;
v___y_2155_ = v___y_2187_;
v___y_2156_ = v___x_2200_;
goto v___jp_2142_;
}
}
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
lean_dec_ref(v___y_2188_);
lean_dec_ref(v___y_2178_);
v___x_2202_ = lean_nat_add(v_n_1928_, v_one_1927_);
lean_dec(v_n_1928_);
v___x_2203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___y_2186_);
lean_ctor_set(v___x_2203_, 1, v_acc_1018_);
v___x_2204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1013_);
v___x_2205_ = l_Lean_Name_append(v___x_2204_, v_trace_1013_);
v___x_2206_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2182_, v___y_2177_, v___x_2205_);
lean_dec(v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = l_Lean_trace_profiler;
v___x_2208_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2177_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_object* v___x_2209_; 
lean_inc(v_trace_1013_);
v___x_2209_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___x_2202_, v___y_2183_, v___x_2203_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1198_ = v___y_2184_;
v___y_1199_ = v___y_2177_;
v___y_1200_ = v___y_2185_;
v___y_1201_ = v___x_2193_;
v___y_1202_ = v___y_2187_;
v___y_1203_ = v___y_2181_;
v___y_1204_ = v_a_2190_;
v___y_1205_ = v___x_2209_;
goto v___jp_1197_;
}
else
{
v___y_1655_ = v___y_2177_;
v___y_1656_ = v___x_2202_;
v___y_1657_ = v___y_2181_;
v___y_1658_ = v_a_2190_;
v___y_1659_ = v___y_2183_;
v___y_1660_ = v___y_2184_;
v___y_1661_ = v___x_2192_;
v___y_1662_ = v___y_2185_;
v___y_1663_ = v___x_2193_;
v___y_1664_ = v___x_2206_;
v___y_1665_ = v___y_2187_;
v___y_1666_ = v___x_2203_;
goto v___jp_1654_;
}
}
else
{
v___y_1655_ = v___y_2177_;
v___y_1656_ = v___x_2202_;
v___y_1657_ = v___y_2181_;
v___y_1658_ = v_a_2190_;
v___y_1659_ = v___y_2183_;
v___y_1660_ = v___y_2184_;
v___y_1661_ = v___x_2192_;
v___y_1662_ = v___y_2185_;
v___y_1663_ = v___x_2193_;
v___y_1664_ = v___x_2206_;
v___y_1665_ = v___y_2187_;
v___y_1666_ = v___x_2203_;
goto v___jp_1654_;
}
}
}
else
{
lean_object* v_a_2210_; 
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2186_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2178_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec_ref(v_cfg_1012_);
v_a_2210_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2210_);
lean_dec_ref(v___x_2194_);
v___y_1188_ = v___y_2184_;
v___y_1189_ = v___y_2177_;
v___y_1190_ = v___y_2185_;
v___y_1191_ = v___x_2193_;
v___y_1192_ = v___y_2187_;
v___y_1193_ = v___y_2181_;
v___y_1194_ = v_a_2190_;
v_a_1195_ = v_a_2210_;
goto v___jp_1187_;
}
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_dec_ref(v___y_2188_);
v___x_2211_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v___y_2186_);
v___x_2212_ = lean_apply_6(v___y_2180_, v___y_2186_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; uint8_t v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref(v___x_2212_);
v___x_2214_ = lean_unbox(v_a_2213_);
lean_dec(v_a_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; 
lean_inc_ref(v_next_1014_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v___y_2186_);
v___x_2215_ = lean_apply_7(v_next_1014_, v___y_2186_, v___y_2179_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; 
lean_dec(v___y_2186_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2178_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec_ref(v_cfg_1012_);
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref(v___x_2215_);
v___y_1127_ = v___y_2184_;
v___y_1128_ = v___x_2211_;
v___y_1129_ = v___y_2177_;
v___y_1130_ = v___y_2185_;
v___y_1131_ = v___y_2187_;
v___y_1132_ = v___y_2181_;
v___y_1133_ = v_a_2190_;
v_a_1134_ = v_a_2216_;
goto v___jp_1126_;
}
else
{
lean_object* v_a_2217_; uint8_t v___x_2218_; 
v_a_2217_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2217_);
lean_dec_ref(v___x_2215_);
v___x_2218_ = l_Lean_Exception_isInterrupt(v_a_2217_);
if (v___x_2218_ == 0)
{
uint8_t v___x_2219_; 
lean_inc(v_a_2217_);
v___x_2219_ = l_Lean_Exception_isRuntime(v_a_2217_);
v___y_2059_ = v___y_2177_;
v___y_2060_ = v___x_2211_;
v___y_2061_ = v___y_2178_;
v___y_2062_ = v___y_2181_;
v___y_2063_ = v___y_2182_;
v___y_2064_ = v_a_2190_;
v___y_2065_ = v___y_2183_;
v___y_2066_ = v___y_2184_;
v___y_2067_ = v___x_2192_;
v___y_2068_ = v___y_2185_;
v___y_2069_ = v___y_2186_;
v___y_2070_ = v___y_2187_;
v___y_2071_ = v_a_2217_;
v___y_2072_ = v___x_2219_;
goto v___jp_2058_;
}
else
{
v___y_2059_ = v___y_2177_;
v___y_2060_ = v___x_2211_;
v___y_2061_ = v___y_2178_;
v___y_2062_ = v___y_2181_;
v___y_2063_ = v___y_2182_;
v___y_2064_ = v_a_2190_;
v___y_2065_ = v___y_2183_;
v___y_2066_ = v___y_2184_;
v___y_2067_ = v___x_2192_;
v___y_2068_ = v___y_2185_;
v___y_2069_ = v___y_2186_;
v___y_2070_ = v___y_2187_;
v___y_2071_ = v_a_2217_;
v___y_2072_ = v___x_2218_;
goto v___jp_2058_;
}
}
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
lean_dec_ref(v___y_2179_);
lean_dec_ref(v___y_2178_);
v___x_2220_ = lean_nat_add(v_n_1928_, v_one_1927_);
lean_dec(v_n_1928_);
v___x_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___y_2186_);
lean_ctor_set(v___x_2221_, 1, v_acc_1018_);
v___x_2222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1013_);
v___x_2223_ = l_Lean_Name_append(v___x_2222_, v_trace_1013_);
v___x_2224_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2182_, v___y_2177_, v___x_2223_);
lean_dec(v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = l_Lean_trace_profiler;
v___x_2226_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2177_, v___x_2225_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; 
lean_inc(v_trace_1013_);
v___x_2227_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___x_2220_, v___y_2183_, v___x_2221_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
v___y_1147_ = v___y_2184_;
v___y_1148_ = v___y_2177_;
v___y_1149_ = v___x_2211_;
v___y_1150_ = v___y_2185_;
v___y_1151_ = v___y_2187_;
v___y_1152_ = v___y_2181_;
v___y_1153_ = v_a_2190_;
v___y_1154_ = v___x_2227_;
goto v___jp_1146_;
}
else
{
v___y_1422_ = v___x_2211_;
v___y_1423_ = v___y_2177_;
v___y_1424_ = v___x_2220_;
v___y_1425_ = v___x_2221_;
v___y_1426_ = v___y_2181_;
v___y_1427_ = v_a_2190_;
v___y_1428_ = v___y_2183_;
v___y_1429_ = v___y_2184_;
v___y_1430_ = v___x_2224_;
v___y_1431_ = v___x_2192_;
v___y_1432_ = v___y_2185_;
v___y_1433_ = v___y_2187_;
goto v___jp_1421_;
}
}
else
{
v___y_1422_ = v___x_2211_;
v___y_1423_ = v___y_2177_;
v___y_1424_ = v___x_2220_;
v___y_1425_ = v___x_2221_;
v___y_1426_ = v___y_2181_;
v___y_1427_ = v_a_2190_;
v___y_1428_ = v___y_2183_;
v___y_1429_ = v___y_2184_;
v___y_1430_ = v___x_2224_;
v___y_1431_ = v___x_2192_;
v___y_1432_ = v___y_2185_;
v___y_1433_ = v___y_2187_;
goto v___jp_1421_;
}
}
}
else
{
lean_object* v_a_2228_; 
lean_dec(v___y_2186_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec_ref(v_cfg_1012_);
v_a_2228_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2228_);
lean_dec_ref(v___x_2212_);
v___y_1137_ = v___y_2184_;
v___y_1138_ = v___x_2211_;
v___y_1139_ = v___y_2177_;
v___y_1140_ = v___y_2185_;
v___y_1141_ = v___y_2187_;
v___y_1142_ = v___y_2181_;
v___y_1143_ = v_a_2190_;
v_a_1144_ = v_a_2228_;
goto v___jp_1136_;
}
}
}
v___jp_2229_:
{
if (v___y_2234_ == 0)
{
lean_object* v___x_2235_; 
lean_dec_ref(v___y_2232_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v___y_2231_);
v___x_2235_ = lean_apply_6(v___y_2230_, v___y_2231_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
if (lean_obj_tag(v_a_2236_) == 0)
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_nat_add(v_n_1928_, v_one_1927_);
lean_dec(v_n_1928_);
v___x_2238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___y_2231_);
lean_ctor_set(v___x_2238_, 1, v_acc_1018_);
v_n_1016_ = v___x_2237_;
v_curr_1017_ = v___y_2233_;
v_acc_1018_ = v___x_2238_;
goto _start;
}
else
{
lean_object* v_val_2240_; lean_object* v___x_2241_; 
lean_dec(v___y_2231_);
v_val_2240_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_val_2240_);
lean_dec_ref(v_a_2236_);
v___x_2241_ = l_List_appendTR___redArg(v_val_2240_, v___y_2233_);
v_n_1016_ = v_n_1928_;
v_curr_1017_ = v___x_2241_;
goto _start;
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v___y_2233_);
lean_dec(v___y_2231_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
v_a_2243_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2235_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2235_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_dec(v___y_2233_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
return v___y_2232_;
}
}
v___jp_2251_:
{
if (lean_obj_tag(v_a_2252_) == 0)
{
if (lean_obj_tag(v_curr_1017_) == 0)
{
lean_object* v_options_2253_; lean_object* v_inheritedTraceOptions_2254_; uint8_t v_hasTrace_2255_; lean_object* v___x_2256_; 
lean_dec(v_n_1928_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec_ref(v_cfg_1012_);
v_options_2253_ = lean_ctor_get(v_a_1021_, 2);
v_inheritedTraceOptions_2254_ = lean_ctor_get(v_a_1021_, 13);
v_hasTrace_2255_ = lean_ctor_get_uint8(v_options_2253_, sizeof(void*)*1);
v___x_2256_ = l_List_reverse___redArg(v_acc_1018_);
if (v_hasTrace_2255_ == 0)
{
lean_object* v___x_2257_; 
lean_dec(v_trace_1013_);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
return v___x_2257_;
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1013_);
v___x_2260_ = l_Lean_Name_append(v___x_2259_, v_trace_1013_);
v___x_2261_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2254_, v_options_2253_, v___x_2260_);
lean_dec(v___x_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = l_Lean_trace_profiler;
v___x_2263_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2253_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; 
lean_dec(v_trace_1013_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2256_);
return v___x_2264_;
}
else
{
v___y_1217_ = v_hasTrace_2255_;
v___y_1218_ = v___x_2256_;
v___y_1219_ = v_options_2253_;
v___y_1220_ = v___x_2261_;
v___y_1221_ = v___x_2258_;
goto v___jp_1216_;
}
}
else
{
v___y_1217_ = v_hasTrace_2255_;
v___y_1218_ = v___x_2256_;
v___y_1219_ = v_options_2253_;
v___y_1220_ = v___x_2261_;
v___y_1221_ = v___x_2258_;
goto v___jp_1216_;
}
}
}
else
{
lean_object* v_head_2265_; lean_object* v_tail_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2339_; 
v_head_2265_ = lean_ctor_get(v_curr_1017_, 0);
v_tail_2266_ = lean_ctor_get(v_curr_1017_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_curr_1017_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2268_ = v_curr_1017_;
v_isShared_2269_ = v_isSharedCheck_2339_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_tail_2266_);
lean_inc(v_head_2265_);
lean_dec(v_curr_1017_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2339_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v_a_2271_; uint8_t v___x_2272_; uint8_t v___x_2273_; 
v___x_2270_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2265_, v_a_1020_);
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref(v___x_2270_);
v___x_2272_ = 1;
v___x_2273_ = lean_unbox(v_a_2271_);
lean_dec(v_a_2271_);
if (v___x_2273_ == 0)
{
lean_object* v_options_2274_; uint8_t v_hasTrace_2275_; 
v_options_2274_ = lean_ctor_get(v_a_1021_, 2);
v_hasTrace_2275_ = lean_ctor_get_uint8(v_options_2274_, sizeof(void*)*1);
if (v_hasTrace_2275_ == 0)
{
lean_object* v___x_2276_; 
lean_inc_ref(v_suspend_1213_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v_head_2265_);
v___x_2276_ = lean_apply_6(v_suspend_1213_, v_head_2265_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; uint8_t v___x_2278_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref(v___x_2276_);
v___x_2278_ = lean_unbox(v_a_2277_);
lean_dec(v_a_2277_);
if (v___x_2278_ == 0)
{
lean_object* v___f_2279_; lean_object* v___x_2280_; 
lean_del_object(v___x_2268_);
lean_inc(v_acc_1018_);
lean_inc(v_n_1928_);
lean_inc(v_goals_1015_);
lean_inc_ref_n(v_next_1014_, 2);
lean_inc(v_trace_1013_);
lean_inc_ref(v_cfg_1012_);
lean_inc(v_tail_2266_);
v___f_2279_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2279_, 0, v_tail_2266_);
lean_closure_set(v___f_2279_, 1, v_cfg_1012_);
lean_closure_set(v___f_2279_, 2, v_trace_1013_);
lean_closure_set(v___f_2279_, 3, v_next_1014_);
lean_closure_set(v___f_2279_, 4, v_goals_1015_);
lean_closure_set(v___f_2279_, 5, v_n_1928_);
lean_closure_set(v___f_2279_, 6, v_acc_1018_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v_head_2265_);
v___x_2280_ = lean_apply_7(v_next_1014_, v_head_2265_, v___f_2279_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_dec(v_tail_2266_);
lean_dec(v_head_2265_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
return v___x_2280_;
}
else
{
lean_object* v_a_2281_; uint8_t v___x_2282_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
v___x_2282_ = l_Lean_Exception_isInterrupt(v_a_2281_);
if (v___x_2282_ == 0)
{
uint8_t v___x_2283_; 
v___x_2283_ = l_Lean_Exception_isRuntime(v_a_2281_);
lean_inc_ref(v_discharge_1214_);
v___y_2230_ = v_discharge_1214_;
v___y_2231_ = v_head_2265_;
v___y_2232_ = v___x_2280_;
v___y_2233_ = v_tail_2266_;
v___y_2234_ = v___x_2283_;
goto v___jp_2229_;
}
else
{
lean_dec(v_a_2281_);
lean_inc_ref(v_discharge_1214_);
v___y_2230_ = v_discharge_1214_;
v___y_2231_ = v_head_2265_;
v___y_2232_ = v___x_2280_;
v___y_2233_ = v_tail_2266_;
v___y_2234_ = v___x_2282_;
goto v___jp_2229_;
}
}
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2284_ = lean_nat_add(v_n_1928_, v_one_1927_);
lean_dec(v_n_1928_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v_acc_1018_);
v___x_2286_ = v___x_2268_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_head_2265_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_acc_1018_);
v___x_2286_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
v_n_1016_ = v___x_2284_;
v_curr_1017_ = v_tail_2266_;
v_acc_1018_ = v___x_2286_;
goto _start;
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_del_object(v___x_2268_);
lean_dec(v_tail_2266_);
lean_dec(v_head_2265_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
v_a_2289_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2276_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2276_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2297_; lean_object* v___f_2298_; lean_object* v___f_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v_inheritedTraceOptions_2297_ = lean_ctor_get(v_a_1021_, 13);
lean_inc(v_acc_1018_);
lean_inc(v_n_1928_);
lean_inc(v_goals_1015_);
lean_inc_ref(v_next_1014_);
lean_inc_n(v_trace_1013_, 2);
lean_inc_ref(v_cfg_1012_);
lean_inc(v_tail_2266_);
v___f_2298_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2298_, 0, v_tail_2266_);
lean_closure_set(v___f_2298_, 1, v_cfg_1012_);
lean_closure_set(v___f_2298_, 2, v_trace_1013_);
lean_closure_set(v___f_2298_, 3, v_next_1014_);
lean_closure_set(v___f_2298_, 4, v_goals_1015_);
lean_closure_set(v___f_2298_, 5, v_n_1928_);
lean_closure_set(v___f_2298_, 6, v_acc_1018_);
lean_inc(v_head_2265_);
v___f_2299_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(v___f_2299_, 0, v_head_2265_);
v___x_2300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
v___x_2302_ = l_Lean_Name_append(v___x_2301_, v_trace_1013_);
v___x_2303_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2297_, v_options_2274_, v___x_2302_);
lean_dec(v___x_2302_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2304_ = l_Lean_trace_profiler;
v___x_2305_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2274_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; 
lean_dec_ref(v___f_2299_);
lean_inc_ref(v_suspend_1213_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v_head_2265_);
v___x_2306_ = lean_apply_6(v_suspend_1213_, v_head_2265_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; uint8_t v___x_2308_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref(v___x_2306_);
v___x_2308_ = lean_unbox(v_a_2307_);
lean_dec(v_a_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; 
lean_del_object(v___x_2268_);
lean_inc_ref(v_next_1014_);
lean_inc(v_a_1022_);
lean_inc_ref(v_a_1021_);
lean_inc(v_a_1020_);
lean_inc_ref(v_a_1019_);
lean_inc(v_head_2265_);
v___x_2309_ = lean_apply_7(v_next_1014_, v_head_2265_, v___f_2298_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, lean_box(0));
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_dec(v_tail_2266_);
lean_dec(v_head_2265_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
return v___x_2309_;
}
else
{
lean_object* v_a_2310_; uint8_t v___x_2311_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
v___x_2311_ = l_Lean_Exception_isInterrupt(v_a_2310_);
if (v___x_2311_ == 0)
{
uint8_t v___x_2312_; 
v___x_2312_ = l_Lean_Exception_isRuntime(v_a_2310_);
lean_inc_ref(v_discharge_1214_);
v___y_1976_ = v___x_2309_;
v___y_1977_ = v_options_2274_;
v___y_1978_ = v_discharge_1214_;
v___y_1979_ = v___x_2300_;
v___y_1980_ = v_head_2265_;
v___y_1981_ = v___x_2305_;
v___y_1982_ = v___x_2272_;
v___y_1983_ = v_tail_2266_;
v___y_1984_ = v_inheritedTraceOptions_2297_;
v___y_1985_ = v___x_2312_;
goto v___jp_1975_;
}
else
{
lean_dec(v_a_2310_);
lean_inc_ref(v_discharge_1214_);
v___y_1976_ = v___x_2309_;
v___y_1977_ = v_options_2274_;
v___y_1978_ = v_discharge_1214_;
v___y_1979_ = v___x_2300_;
v___y_1980_ = v_head_2265_;
v___y_1981_ = v___x_2305_;
v___y_1982_ = v___x_2272_;
v___y_1983_ = v_tail_2266_;
v___y_1984_ = v_inheritedTraceOptions_2297_;
v___y_1985_ = v___x_2311_;
goto v___jp_1975_;
}
}
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
lean_dec_ref(v___f_2298_);
v___x_2313_ = lean_nat_add(v_n_1928_, v_one_1927_);
lean_dec(v_n_1928_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v_acc_1018_);
v___x_2315_ = v___x_2268_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_head_2265_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_acc_1018_);
v___x_2315_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
if (v___x_2303_ == 0)
{
if (v___x_2305_ == 0)
{
v_n_1016_ = v___x_2313_;
v_curr_1017_ = v_tail_2266_;
v_acc_1018_ = v___x_2315_;
goto _start;
}
else
{
v___y_1880_ = v_options_2274_;
v___y_1881_ = v___x_2303_;
v___y_1882_ = v___x_2300_;
v___y_1883_ = v___x_2313_;
v___y_1884_ = v___x_2272_;
v___y_1885_ = v___x_2315_;
v___y_1886_ = v_tail_2266_;
goto v___jp_1879_;
}
}
else
{
v___y_1880_ = v_options_2274_;
v___y_1881_ = v___x_2303_;
v___y_1882_ = v___x_2300_;
v___y_1883_ = v___x_2313_;
v___y_1884_ = v___x_2272_;
v___y_1885_ = v___x_2315_;
v___y_1886_ = v_tail_2266_;
goto v___jp_1879_;
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v___f_2298_);
lean_del_object(v___x_2268_);
lean_dec(v_tail_2266_);
lean_dec(v_head_2265_);
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
v_a_2318_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2306_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2306_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
else
{
lean_del_object(v___x_2268_);
lean_inc_ref(v_suspend_1213_);
lean_inc_ref(v___f_2298_);
lean_inc_ref(v_discharge_1214_);
v___y_2177_ = v_options_2274_;
v___y_2178_ = v_discharge_1214_;
v___y_2179_ = v___f_2298_;
v___y_2180_ = v_suspend_1213_;
v___y_2181_ = v___x_2272_;
v___y_2182_ = v_inheritedTraceOptions_2297_;
v___y_2183_ = v_tail_2266_;
v___y_2184_ = v___f_2299_;
v___y_2185_ = v___x_2300_;
v___y_2186_ = v_head_2265_;
v___y_2187_ = v___x_2303_;
v___y_2188_ = v___f_2298_;
goto v___jp_2176_;
}
}
else
{
lean_del_object(v___x_2268_);
lean_inc_ref(v_suspend_1213_);
lean_inc_ref(v___f_2298_);
lean_inc_ref(v_discharge_1214_);
v___y_2177_ = v_options_2274_;
v___y_2178_ = v_discharge_1214_;
v___y_2179_ = v___f_2298_;
v___y_2180_ = v_suspend_1213_;
v___y_2181_ = v___x_2272_;
v___y_2182_ = v_inheritedTraceOptions_2297_;
v___y_2183_ = v_tail_2266_;
v___y_2184_ = v___f_2299_;
v___y_2185_ = v___x_2300_;
v___y_2186_ = v_head_2265_;
v___y_2187_ = v___x_2303_;
v___y_2188_ = v___f_2298_;
goto v___jp_2176_;
}
}
}
else
{
lean_object* v_options_2326_; lean_object* v_inheritedTraceOptions_2327_; uint8_t v_hasTrace_2328_; lean_object* v___x_2329_; 
lean_del_object(v___x_2268_);
v_options_2326_ = lean_ctor_get(v_a_1021_, 2);
v_inheritedTraceOptions_2327_ = lean_ctor_get(v_a_1021_, 13);
v_hasTrace_2328_ = lean_ctor_get_uint8(v_options_2326_, sizeof(void*)*1);
v___x_2329_ = lean_nat_add(v_n_1928_, v_one_1927_);
lean_dec(v_n_1928_);
if (v_hasTrace_2328_ == 0)
{
lean_dec(v_head_2265_);
v_n_1016_ = v___x_2329_;
v_curr_1017_ = v_tail_2266_;
goto _start;
}
else
{
lean_object* v___f_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___f_2331_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2331_, 0, v_head_2265_);
v___x_2332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_1013_);
v___x_2334_ = l_Lean_Name_append(v___x_2333_, v_trace_1013_);
v___x_2335_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2327_, v_options_2326_, v___x_2334_);
lean_dec(v___x_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; uint8_t v___x_2337_; 
v___x_2336_ = l_Lean_trace_profiler;
v___x_2337_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2326_, v___x_2336_);
if (v___x_2337_ == 0)
{
lean_dec_ref(v___f_2331_);
v_n_1016_ = v___x_2329_;
v_curr_1017_ = v_tail_2266_;
goto _start;
}
else
{
v___y_1062_ = v___f_2331_;
v___y_1063_ = v___x_2332_;
v___y_1064_ = v___x_2335_;
v___y_1065_ = v___x_2329_;
v___y_1066_ = v_options_2326_;
v___y_1067_ = v___x_2272_;
v___y_1068_ = v_tail_2266_;
goto v___jp_1061_;
}
}
else
{
v___y_1062_ = v___f_2331_;
v___y_1063_ = v___x_2332_;
v___y_1064_ = v___x_2335_;
v___y_1065_ = v___x_2329_;
v___y_1066_ = v_options_2326_;
v___y_1067_ = v___x_2272_;
v___y_1068_ = v_tail_2266_;
goto v___jp_1061_;
}
}
}
}
}
}
else
{
lean_object* v_val_2340_; 
lean_dec(v_curr_1017_);
v_val_2340_ = lean_ctor_get(v_a_2252_, 0);
lean_inc(v_val_2340_);
lean_dec_ref(v_a_2252_);
v_n_1016_ = v_n_1928_;
v_curr_1017_ = v_val_2340_;
goto _start;
}
}
v___jp_2342_:
{
if (lean_obj_tag(v___y_2343_) == 0)
{
lean_object* v_a_2344_; 
v_a_2344_ = lean_ctor_get(v___y_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref(v___y_2343_);
v_a_2252_ = v_a_2344_;
goto v___jp_2251_;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_n_1928_);
lean_dec(v_acc_1018_);
lean_dec(v_curr_1017_);
lean_dec(v_goals_1015_);
lean_dec_ref(v_next_1014_);
lean_dec(v_trace_1013_);
lean_dec_ref(v_cfg_1012_);
v_a_2345_ = lean_ctor_get(v___y_2343_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___y_2343_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___y_2343_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___y_2343_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
v___jp_1024_:
{
lean_object* v___x_1033_; double v___x_1034_; double v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1033_ = lean_io_get_num_heartbeats();
v___x_1034_ = lean_float_of_nat(v___y_1027_);
v___x_1035_ = lean_float_of_nat(v___x_1033_);
v___x_1036_ = lean_box_float(v___x_1034_);
v___x_1037_ = lean_box_float(v___x_1035_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_a_1032_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
lean_inc_ref(v___y_1026_);
v___x_1040_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1031_, v___y_1026_, v___y_1030_, v___y_1028_, v___y_1029_, v___y_1025_, v___x_1039_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1040_;
}
v___jp_1041_:
{
lean_object* v___x_1050_; double v___x_1051_; double v___x_1052_; double v___x_1053_; double v___x_1054_; double v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1050_ = lean_io_mono_nanos_now();
v___x_1051_ = lean_float_of_nat(v___y_1043_);
v___x_1052_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1053_ = lean_float_div(v___x_1051_, v___x_1052_);
v___x_1054_ = lean_float_of_nat(v___x_1050_);
v___x_1055_ = lean_float_div(v___x_1054_, v___x_1052_);
v___x_1056_ = lean_box_float(v___x_1053_);
v___x_1057_ = lean_box_float(v___x_1055_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_a_1049_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
lean_inc_ref(v___y_1044_);
v___x_1060_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1048_, v___y_1044_, v___y_1047_, v___y_1045_, v___y_1046_, v___y_1042_, v___x_1059_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1060_;
}
v___jp_1061_:
{
lean_object* v___x_1069_; lean_object* v_a_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1069_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1022_);
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1072_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1066_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_io_mono_nanos_now();
lean_inc(v_trace_1013_);
v___x_1074_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1065_, v___y_1068_, v_acc_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set_tag(v___x_1077_, 1);
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
v___y_1042_ = v___y_1062_;
v___y_1043_ = v___x_1073_;
v___y_1044_ = v___y_1063_;
v___y_1045_ = v___y_1064_;
v___y_1046_ = v_a_1070_;
v___y_1047_ = v___y_1066_;
v___y_1048_ = v___y_1067_;
v_a_1049_ = v___x_1080_;
goto v___jp_1041_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_a_1083_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1074_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1074_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 0);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
v___y_1042_ = v___y_1062_;
v___y_1043_ = v___x_1073_;
v___y_1044_ = v___y_1063_;
v___y_1045_ = v___y_1064_;
v___y_1046_ = v_a_1070_;
v___y_1047_ = v___y_1066_;
v___y_1048_ = v___y_1067_;
v_a_1049_ = v___x_1088_;
goto v___jp_1041_;
}
}
}
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_1013_);
v___x_1092_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_1012_, v_trace_1013_, v_next_1014_, v_goals_1015_, v___y_1065_, v___y_1068_, v_acc_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 1);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
v___y_1025_ = v___y_1062_;
v___y_1026_ = v___y_1063_;
v___y_1027_ = v___x_1091_;
v___y_1028_ = v___y_1064_;
v___y_1029_ = v_a_1070_;
v___y_1030_ = v___y_1066_;
v___y_1031_ = v___y_1067_;
v_a_1032_ = v___x_1098_;
goto v___jp_1024_;
}
}
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_a_1101_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1092_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1092_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 0);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
v___y_1025_ = v___y_1062_;
v___y_1026_ = v___y_1063_;
v___y_1027_ = v___x_1091_;
v___y_1028_ = v___y_1064_;
v___y_1029_ = v_a_1070_;
v___y_1030_ = v___y_1066_;
v___y_1031_ = v___y_1067_;
v_a_1032_ = v___x_1106_;
goto v___jp_1024_;
}
}
}
}
}
v___jp_1109_:
{
lean_object* v___x_1118_; double v___x_1119_; double v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1118_ = lean_io_get_num_heartbeats();
v___x_1119_ = lean_float_of_nat(v___y_1112_);
v___x_1120_ = lean_float_of_nat(v___x_1118_);
v___x_1121_ = lean_box_float(v___x_1119_);
v___x_1122_ = lean_box_float(v___x_1120_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1117_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
lean_inc_ref(v___y_1113_);
v___x_1125_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1115_, v___y_1113_, v___y_1111_, v___y_1114_, v___y_1116_, v___y_1110_, v___x_1124_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1125_;
}
v___jp_1126_:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_a_1134_);
v___y_1110_ = v___y_1127_;
v___y_1111_ = v___y_1129_;
v___y_1112_ = v___y_1128_;
v___y_1113_ = v___y_1130_;
v___y_1114_ = v___y_1131_;
v___y_1115_ = v___y_1132_;
v___y_1116_ = v___y_1133_;
v_a_1117_ = v___x_1135_;
goto v___jp_1109_;
}
v___jp_1136_:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_a_1144_);
v___y_1110_ = v___y_1137_;
v___y_1111_ = v___y_1139_;
v___y_1112_ = v___y_1138_;
v___y_1113_ = v___y_1140_;
v___y_1114_ = v___y_1141_;
v___y_1115_ = v___y_1142_;
v___y_1116_ = v___y_1143_;
v_a_1117_ = v___x_1145_;
goto v___jp_1109_;
}
v___jp_1146_:
{
if (lean_obj_tag(v___y_1154_) == 0)
{
lean_object* v_a_1155_; 
v_a_1155_ = lean_ctor_get(v___y_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref(v___y_1154_);
v___y_1127_ = v___y_1147_;
v___y_1128_ = v___y_1149_;
v___y_1129_ = v___y_1148_;
v___y_1130_ = v___y_1150_;
v___y_1131_ = v___y_1151_;
v___y_1132_ = v___y_1152_;
v___y_1133_ = v___y_1153_;
v_a_1134_ = v_a_1155_;
goto v___jp_1126_;
}
else
{
lean_object* v_a_1156_; 
v_a_1156_ = lean_ctor_get(v___y_1154_, 0);
lean_inc(v_a_1156_);
lean_dec_ref(v___y_1154_);
v___y_1137_ = v___y_1147_;
v___y_1138_ = v___y_1149_;
v___y_1139_ = v___y_1148_;
v___y_1140_ = v___y_1150_;
v___y_1141_ = v___y_1151_;
v___y_1142_ = v___y_1152_;
v___y_1143_ = v___y_1153_;
v_a_1144_ = v_a_1156_;
goto v___jp_1136_;
}
}
v___jp_1157_:
{
lean_object* v___x_1166_; double v___x_1167_; double v___x_1168_; double v___x_1169_; double v___x_1170_; double v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1166_ = lean_io_mono_nanos_now();
v___x_1167_ = lean_float_of_nat(v___y_1161_);
v___x_1168_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1169_ = lean_float_div(v___x_1167_, v___x_1168_);
v___x_1170_ = lean_float_of_nat(v___x_1166_);
v___x_1171_ = lean_float_div(v___x_1170_, v___x_1168_);
v___x_1172_ = lean_box_float(v___x_1169_);
v___x_1173_ = lean_box_float(v___x_1171_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_a_1165_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
lean_inc_ref(v___y_1160_);
v___x_1176_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_1013_, v___y_1163_, v___y_1160_, v___y_1159_, v___y_1162_, v___y_1164_, v___y_1158_, v___x_1175_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1176_;
}
v___jp_1177_:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_a_1185_);
v___y_1158_ = v___y_1178_;
v___y_1159_ = v___y_1179_;
v___y_1160_ = v___y_1180_;
v___y_1161_ = v___y_1181_;
v___y_1162_ = v___y_1182_;
v___y_1163_ = v___y_1183_;
v___y_1164_ = v___y_1184_;
v_a_1165_ = v___x_1186_;
goto v___jp_1157_;
}
v___jp_1187_:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v_a_1195_);
v___y_1158_ = v___y_1188_;
v___y_1159_ = v___y_1189_;
v___y_1160_ = v___y_1190_;
v___y_1161_ = v___y_1191_;
v___y_1162_ = v___y_1192_;
v___y_1163_ = v___y_1193_;
v___y_1164_ = v___y_1194_;
v_a_1165_ = v___x_1196_;
goto v___jp_1157_;
}
v___jp_1197_:
{
if (lean_obj_tag(v___y_1205_) == 0)
{
lean_object* v_a_1206_; 
v_a_1206_ = lean_ctor_get(v___y_1205_, 0);
lean_inc(v_a_1206_);
lean_dec_ref(v___y_1205_);
v___y_1178_ = v___y_1198_;
v___y_1179_ = v___y_1199_;
v___y_1180_ = v___y_1200_;
v___y_1181_ = v___y_1201_;
v___y_1182_ = v___y_1202_;
v___y_1183_ = v___y_1203_;
v___y_1184_ = v___y_1204_;
v_a_1185_ = v_a_1206_;
goto v___jp_1177_;
}
else
{
lean_object* v_a_1207_; 
v_a_1207_ = lean_ctor_get(v___y_1205_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___y_1205_);
v___y_1188_ = v___y_1198_;
v___y_1189_ = v___y_1199_;
v___y_1190_ = v___y_1200_;
v___y_1191_ = v___y_1201_;
v___y_1192_ = v___y_1202_;
v___y_1193_ = v___y_1203_;
v___y_1194_ = v___y_1204_;
v_a_1195_ = v_a_1207_;
goto v___jp_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2423_, lean_object* v_trace_2424_, lean_object* v_next_2425_, lean_object* v_goals_2426_, lean_object* v_n_2427_, lean_object* v_curr_2428_, lean_object* v_acc_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2423_, v_trace_2424_, v_next_2425_, v_goals_2426_, v_n_2427_, v_curr_2428_, v_acc_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object* v_tail_2436_, lean_object* v_cfg_2437_, lean_object* v_trace_2438_, lean_object* v_next_2439_, lean_object* v_goals_2440_, lean_object* v_n_2441_, lean_object* v_acc_2442_, lean_object* v_r_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = l_List_appendTR___redArg(v_r_2443_, v_tail_2436_);
v___x_2450_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2450_, 0, v_cfg_2437_);
lean_closure_set(v___x_2450_, 1, v_trace_2438_);
lean_closure_set(v___x_2450_, 2, v_next_2439_);
lean_closure_set(v___x_2450_, 3, v_goals_2440_);
lean_closure_set(v___x_2450_, 4, v_n_2441_);
lean_closure_set(v___x_2450_, 5, v___x_2449_);
lean_closure_set(v___x_2450_, 6, v_acc_2442_);
v___x_2451_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v___x_2450_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2452_, lean_object* v_msg_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2460_, lean_object* v_msg_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2460_, v_msg_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_00_u03b1_2468_, lean_object* v_x_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___redArg(v_x_2469_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_00_u03b1_2476_, v_x_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* v_mvarId_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_2484_, v___y_2486_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* v_mvarId_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_mvarId_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v_mvarId_2491_);
return v_res_2497_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_object* v_00_u03b2_2498_, lean_object* v_x_2499_, lean_object* v_x_2500_){
_start:
{
uint8_t v___x_2501_; 
v___x_2501_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_2499_, v_x_2500_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2502_, lean_object* v_x_2503_, lean_object* v_x_2504_){
_start:
{
uint8_t v_res_2505_; lean_object* v_r_2506_; 
v_res_2505_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(v_00_u03b2_2502_, v_x_2503_, v_x_2504_);
lean_dec(v_x_2504_);
lean_dec_ref(v_x_2503_);
v_r_2506_ = lean_box(v_res_2505_);
return v_r_2506_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_2507_, lean_object* v_x_2508_, size_t v_x_2509_, lean_object* v_x_2510_){
_start:
{
uint8_t v___x_2511_; 
v___x_2511_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_2508_, v_x_2509_, v_x_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___boxed(lean_object* v_00_u03b2_2512_, lean_object* v_x_2513_, lean_object* v_x_2514_, lean_object* v_x_2515_){
_start:
{
size_t v_x_85594__boxed_2516_; uint8_t v_res_2517_; lean_object* v_r_2518_; 
v_x_85594__boxed_2516_ = lean_unbox_usize(v_x_2514_);
lean_dec(v_x_2514_);
v_res_2517_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2512_, v_x_2513_, v_x_85594__boxed_2516_, v_x_2515_);
lean_dec(v_x_2515_);
lean_dec_ref(v_x_2513_);
v_r_2518_ = lean_box(v_res_2517_);
return v_r_2518_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_object* v_00_u03b2_2519_, lean_object* v_keys_2520_, lean_object* v_vals_2521_, lean_object* v_heq_2522_, lean_object* v_i_2523_, lean_object* v_k_2524_){
_start:
{
uint8_t v___x_2525_; 
v___x_2525_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_2520_, v_i_2523_, v_k_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2526_, lean_object* v_keys_2527_, lean_object* v_vals_2528_, lean_object* v_heq_2529_, lean_object* v_i_2530_, lean_object* v_k_2531_){
_start:
{
uint8_t v_res_2532_; lean_object* v_r_2533_; 
v_res_2532_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(v_00_u03b2_2526_, v_keys_2527_, v_vals_2528_, v_heq_2529_, v_i_2530_, v_k_2531_);
lean_dec(v_k_2531_);
lean_dec_ref(v_vals_2528_);
lean_dec_ref(v_keys_2527_);
v_r_2533_ = lean_box(v_res_2532_);
return v_r_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2534_, lean_object* v_h__1_2535_, lean_object* v_h__2_2536_){
_start:
{
lean_object* v_zero_2537_; uint8_t v_isZero_2538_; 
v_zero_2537_ = lean_unsigned_to_nat(0u);
v_isZero_2538_ = lean_nat_dec_eq(v_n_2534_, v_zero_2537_);
if (v_isZero_2538_ == 1)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
lean_dec(v_h__2_2536_);
v___x_2539_ = lean_box(0);
v___x_2540_ = lean_apply_1(v_h__1_2535_, v___x_2539_);
return v___x_2540_;
}
else
{
lean_object* v_one_2541_; lean_object* v_n_2542_; lean_object* v___x_2543_; 
lean_dec(v_h__1_2535_);
v_one_2541_ = lean_unsigned_to_nat(1u);
v_n_2542_ = lean_nat_sub(v_n_2534_, v_one_2541_);
v___x_2543_ = lean_apply_1(v_h__2_2536_, v_n_2542_);
return v___x_2543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2544_, lean_object* v_h__1_2545_, lean_object* v_h__2_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2544_, v_h__1_2545_, v_h__2_2546_);
lean_dec(v_n_2544_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2548_, lean_object* v_n_2549_, lean_object* v_h__1_2550_, lean_object* v_h__2_2551_){
_start:
{
lean_object* v_zero_2552_; uint8_t v_isZero_2553_; 
v_zero_2552_ = lean_unsigned_to_nat(0u);
v_isZero_2553_ = lean_nat_dec_eq(v_n_2549_, v_zero_2552_);
if (v_isZero_2553_ == 1)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec(v_h__2_2551_);
v___x_2554_ = lean_box(0);
v___x_2555_ = lean_apply_1(v_h__1_2550_, v___x_2554_);
return v___x_2555_;
}
else
{
lean_object* v_one_2556_; lean_object* v_n_2557_; lean_object* v___x_2558_; 
lean_dec(v_h__1_2550_);
v_one_2556_ = lean_unsigned_to_nat(1u);
v_n_2557_ = lean_nat_sub(v_n_2549_, v_one_2556_);
v___x_2558_ = lean_apply_1(v_h__2_2551_, v_n_2557_);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* v_motive_2559_, lean_object* v_n_2560_, lean_object* v_h__1_2561_, lean_object* v_h__2_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(v_motive_2559_, v_n_2560_, v_h__1_2561_, v_h__2_2562_);
lean_dec(v_n_2560_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* v_procResult_x3f_2564_, lean_object* v_h__1_2565_, lean_object* v_h__2_2566_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2564_) == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
lean_dec(v_h__1_2565_);
v___x_2567_ = lean_box(0);
v___x_2568_ = lean_apply_1(v_h__2_2566_, v___x_2567_);
return v___x_2568_;
}
else
{
lean_object* v_val_2569_; lean_object* v___x_2570_; 
lean_dec(v_h__2_2566_);
v_val_2569_ = lean_ctor_get(v_procResult_x3f_2564_, 0);
lean_inc(v_val_2569_);
lean_dec_ref(v_procResult_x3f_2564_);
v___x_2570_ = lean_apply_1(v_h__1_2565_, v_val_2569_);
return v___x_2570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* v_motive_2571_, lean_object* v_procResult_x3f_2572_, lean_object* v_h__1_2573_, lean_object* v_h__2_2574_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2572_) == 0)
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_dec(v_h__1_2573_);
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_apply_1(v_h__2_2574_, v___x_2575_);
return v___x_2576_;
}
else
{
lean_object* v_val_2577_; lean_object* v___x_2578_; 
lean_dec(v_h__2_2574_);
v_val_2577_ = lean_ctor_get(v_procResult_x3f_2572_, 0);
lean_inc(v_val_2577_);
lean_dec_ref(v_procResult_x3f_2572_);
v___x_2578_ = lean_apply_1(v_h__1_2573_, v_val_2577_);
return v___x_2578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2579_, lean_object* v_h__1_2580_, lean_object* v_h__2_2581_){
_start:
{
if (lean_obj_tag(v_curr_2579_) == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_dec(v_h__2_2581_);
v___x_2582_ = lean_box(0);
v___x_2583_ = lean_apply_1(v_h__1_2580_, v___x_2582_);
return v___x_2583_;
}
else
{
lean_object* v_head_2584_; lean_object* v_tail_2585_; lean_object* v___x_2586_; 
lean_dec(v_h__1_2580_);
v_head_2584_ = lean_ctor_get(v_curr_2579_, 0);
lean_inc(v_head_2584_);
v_tail_2585_ = lean_ctor_get(v_curr_2579_, 1);
lean_inc(v_tail_2585_);
lean_dec_ref(v_curr_2579_);
v___x_2586_ = lean_apply_2(v_h__2_2581_, v_head_2584_, v_tail_2585_);
return v___x_2586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2587_, lean_object* v_curr_2588_, lean_object* v_h__1_2589_, lean_object* v_h__2_2590_){
_start:
{
if (lean_obj_tag(v_curr_2588_) == 0)
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
lean_dec(v_h__2_2590_);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_apply_1(v_h__1_2589_, v___x_2591_);
return v___x_2592_;
}
else
{
lean_object* v_head_2593_; lean_object* v_tail_2594_; lean_object* v___x_2595_; 
lean_dec(v_h__1_2589_);
v_head_2593_ = lean_ctor_get(v_curr_2588_, 0);
lean_inc(v_head_2593_);
v_tail_2594_ = lean_ctor_get(v_curr_2588_, 1);
lean_inc(v_tail_2594_);
lean_dec_ref(v_curr_2588_);
v___x_2595_ = lean_apply_2(v_h__2_2590_, v_head_2593_, v_tail_2594_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2596_, lean_object* v_h__1_2597_, lean_object* v_h__2_2598_){
_start:
{
if (lean_obj_tag(v_____do__lift_2596_) == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec(v_h__2_2598_);
v___x_2599_ = lean_box(0);
v___x_2600_ = lean_apply_1(v_h__1_2597_, v___x_2599_);
return v___x_2600_;
}
else
{
lean_object* v_val_2601_; lean_object* v___x_2602_; 
lean_dec(v_h__1_2597_);
v_val_2601_ = lean_ctor_get(v_____do__lift_2596_, 0);
lean_inc(v_val_2601_);
lean_dec_ref(v_____do__lift_2596_);
v___x_2602_ = lean_apply_1(v_h__2_2598_, v_val_2601_);
return v___x_2602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_2603_, lean_object* v_____do__lift_2604_, lean_object* v_h__1_2605_, lean_object* v_h__2_2606_){
_start:
{
if (lean_obj_tag(v_____do__lift_2604_) == 0)
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_dec(v_h__2_2606_);
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_apply_1(v_h__1_2605_, v___x_2607_);
return v___x_2608_;
}
else
{
lean_object* v_val_2609_; lean_object* v___x_2610_; 
lean_dec(v_h__1_2605_);
v_val_2609_ = lean_ctor_get(v_____do__lift_2604_, 0);
lean_inc(v_val_2609_);
lean_dec_ref(v_____do__lift_2604_);
v___x_2610_ = lean_apply_1(v_h__2_2606_, v_val_2609_);
return v___x_2610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_2611_, lean_object* v_trace_2612_, lean_object* v_next_2613_, lean_object* v_orig_2614_, lean_object* v_g_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_maxDepth_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v_maxDepth_2621_ = lean_ctor_get(v_cfg_2611_, 0);
lean_inc(v_maxDepth_2621_);
v___x_2622_ = lean_box(0);
v___x_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2623_, 0, v_g_2615_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2611_, v_trace_2612_, v_next_2613_, v_orig_2614_, v_maxDepth_2621_, v___x_2623_, v___x_2622_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_2625_, lean_object* v_trace_2626_, lean_object* v_next_2627_, lean_object* v_orig_2628_, lean_object* v_g_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2625_, v_trace_2626_, v_next_2627_, v_orig_2628_, v_g_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
if (lean_obj_tag(v_a_2636_) == 0)
{
lean_object* v___x_2638_; 
v___x_2638_ = l_List_reverse___redArg(v_a_2637_);
return v___x_2638_;
}
else
{
lean_object* v_head_2639_; lean_object* v_tail_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2649_; 
v_head_2639_ = lean_ctor_get(v_a_2636_, 0);
v_tail_2640_ = lean_ctor_get(v_a_2636_, 1);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_a_2636_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2642_ = v_a_2636_;
v_isShared_2643_ = v_isSharedCheck_2649_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_tail_2640_);
lean_inc(v_head_2639_);
lean_dec(v_a_2636_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2649_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2644_ = l_Lean_MessageData_ofFormat(v_head_2639_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 1, v_a_2637_);
lean_ctor_set(v___x_2642_, 0, v___x_2644_);
v___x_2646_ = v___x_2642_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_a_2637_);
v___x_2646_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
v_a_2636_ = v_tail_2640_;
v_a_2637_ = v___x_2646_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_2652_ = l_Lean_stringToMessageData(v___x_2651_);
return v___x_2652_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_2655_ = l_Lean_stringToMessageData(v___x_2654_);
return v___x_2655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_2658_ = l_Lean_stringToMessageData(v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_2659_, lean_object* v_snd_2660_, lean_object* v_x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; 
v___x_2667_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2659_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2669_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref(v___x_2667_);
v___x_2669_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_2660_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2689_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2672_ = v___x_2669_;
v_isShared_2673_ = v_isSharedCheck_2689_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2669_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2689_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2674_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_2675_ = lean_box(0);
v___x_2676_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2668_, v___x_2675_);
v___x_2677_ = l_Lean_MessageData_ofList(v___x_2676_);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2674_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_2682_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2670_, v___x_2675_);
v___x_2683_ = l_Lean_MessageData_ofList(v___x_2682_);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2681_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2680_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 0, v___x_2685_);
v___x_2687_ = v___x_2672_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v_a_2668_);
v_a_2690_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2669_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2669_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v_snd_2660_);
v_a_2698_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2667_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2667_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_2706_, lean_object* v_snd_2707_, lean_object* v_x_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2706_, v_snd_2707_, v_x_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_x_2708_);
return v_res_2714_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_2717_ = l_Lean_stringToMessageData(v___x_2716_);
return v___x_2717_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_2720_ = l_Lean_stringToMessageData(v___x_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_2721_, lean_object* v___x_2722_, lean_object* v_x_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2721_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2731_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref(v___x_2729_);
v___x_2731_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_2722_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2749_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2749_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2749_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2736_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_2737_ = lean_box(0);
v___x_2738_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2730_, v___x_2737_);
v___x_2739_ = l_Lean_MessageData_ofList(v___x_2738_);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2736_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2732_, v___x_2737_);
v___x_2744_ = l_Lean_MessageData_ofList(v___x_2743_);
v___x_2745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2742_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2745_);
v___x_2747_ = v___x_2734_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v_a_2730_);
v_a_2750_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2731_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2731_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec(v___x_2722_);
v_a_2758_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2729_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2729_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_2766_, lean_object* v___x_2767_, lean_object* v_x_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2766_, v___x_2767_, v_x_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec_ref(v_x_2768_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t v___x_2775_, lean_object* v_x_2776_, lean_object* v_x_2777_, lean_object* v___y_2778_){
_start:
{
if (lean_obj_tag(v_x_2776_) == 0)
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v_x_2777_);
return v___x_2780_;
}
else
{
lean_object* v_head_2781_; lean_object* v_tail_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2797_; 
v_head_2781_ = lean_ctor_get(v_x_2776_, 0);
v_tail_2782_ = lean_ctor_get(v_x_2776_, 1);
v_isSharedCheck_2797_ = !lean_is_exclusive(v_x_2776_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2784_ = v_x_2776_;
v_isShared_2785_ = v_isSharedCheck_2797_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_tail_2782_);
lean_inc(v_head_2781_);
lean_dec(v_x_2776_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2797_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
uint8_t v_a_2792_; lean_object* v___x_2794_; lean_object* v_a_2795_; uint8_t v___x_2796_; 
v___x_2794_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2781_, v___y_2778_);
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref(v___x_2794_);
v___x_2796_ = lean_unbox(v_a_2795_);
lean_dec(v_a_2795_);
if (v___x_2796_ == 0)
{
goto v___jp_2786_;
}
else
{
v_a_2792_ = v___x_2775_;
goto v___jp_2791_;
}
v___jp_2786_:
{
lean_object* v___x_2788_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 1, v_x_2777_);
v___x_2788_ = v___x_2784_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_head_2781_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_x_2777_);
v___x_2788_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
v_x_2776_ = v_tail_2782_;
v_x_2777_ = v___x_2788_;
goto _start;
}
}
v___jp_2791_:
{
if (v_a_2792_ == 0)
{
lean_del_object(v___x_2784_);
lean_dec(v_head_2781_);
v_x_2776_ = v_tail_2782_;
goto _start;
}
else
{
goto v___jp_2786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v___x_2798_, lean_object* v_x_2799_, lean_object* v_x_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v___x_57593__boxed_2803_; lean_object* v_res_2804_; 
v___x_57593__boxed_2803_ = lean_unbox(v___x_2798_);
v_res_2804_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_57593__boxed_2803_, v_x_2799_, v_x_2800_, v___y_2801_);
lean_dec(v___y_2801_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
if (lean_obj_tag(v_a_2805_) == 0)
{
lean_object* v___x_2807_; 
v___x_2807_ = lean_array_to_list(v_a_2806_);
return v___x_2807_;
}
else
{
lean_object* v_head_2808_; lean_object* v_tail_2809_; lean_object* v___x_2810_; 
v_head_2808_ = lean_ctor_get(v_a_2805_, 0);
lean_inc(v_head_2808_);
v_tail_2809_ = lean_ctor_get(v_a_2805_, 1);
lean_inc(v_tail_2809_);
lean_dec_ref(v_a_2805_);
v___x_2810_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2806_, v_head_2808_);
v_a_2805_ = v_tail_2809_;
v_a_2806_ = v___x_2810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
if (lean_obj_tag(v_a_2813_) == 0)
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec(v_goals_2812_);
v___x_2821_ = lean_array_to_list(v_a_2814_);
v___x_2822_ = lean_array_to_list(v_a_2815_);
v___x_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2821_);
lean_ctor_set(v___x_2823_, 1, v___x_2822_);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
return v___x_2824_;
}
else
{
lean_object* v_head_2825_; lean_object* v_tail_2826_; lean_object* v___x_2827_; 
v_head_2825_ = lean_ctor_get(v_a_2813_, 0);
lean_inc_n(v_head_2825_, 2);
v_tail_2826_ = lean_ctor_get(v_a_2813_, 1);
lean_inc(v_tail_2826_);
lean_dec_ref(v_a_2813_);
lean_inc(v_goals_2812_);
v___x_2827_ = l_Lean_MVarId_isIndependentOf(v_goals_2812_, v_head_2825_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; uint8_t v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref(v___x_2827_);
v___x_2829_ = lean_unbox(v_a_2828_);
lean_dec(v_a_2828_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; 
v___x_2830_ = lean_array_push(v_a_2815_, v_head_2825_);
v_a_2813_ = v_tail_2826_;
v_a_2815_ = v___x_2830_;
goto _start;
}
else
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_array_push(v_a_2814_, v_head_2825_);
v_a_2813_ = v_tail_2826_;
v_a_2814_ = v___x_2832_;
goto _start;
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_tail_2826_);
lean_dec(v_head_2825_);
lean_dec_ref(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_goals_2812_);
v_a_2834_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2827_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2827_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
if (lean_obj_tag(v_a_2852_) == 0)
{
lean_object* v___x_2854_; 
v___x_2854_ = lean_array_to_list(v_a_2853_);
return v___x_2854_;
}
else
{
lean_object* v_head_2855_; 
v_head_2855_ = lean_ctor_get(v_a_2852_, 0);
if (lean_obj_tag(v_head_2855_) == 0)
{
lean_object* v_tail_2856_; lean_object* v_val_2857_; lean_object* v___x_2858_; 
lean_inc_ref(v_head_2855_);
v_tail_2856_ = lean_ctor_get(v_a_2852_, 1);
lean_inc(v_tail_2856_);
lean_dec_ref(v_a_2852_);
v_val_2857_ = lean_ctor_get(v_head_2855_, 0);
lean_inc(v_val_2857_);
lean_dec_ref(v_head_2855_);
v___x_2858_ = lean_array_push(v_a_2853_, v_val_2857_);
v_a_2852_ = v_tail_2856_;
v_a_2853_ = v___x_2858_;
goto _start;
}
else
{
lean_object* v_tail_2860_; 
v_tail_2860_ = lean_ctor_get(v_a_2852_, 1);
lean_inc(v_tail_2860_);
lean_dec_ref(v_a_2852_);
v_a_2852_ = v_tail_2860_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_2862_, lean_object* v_x_2863_, lean_object* v_x_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
if (lean_obj_tag(v_x_2863_) == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec_ref(v_f_2862_);
v___x_2870_ = l_List_reverse___redArg(v_x_2864_);
v___x_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
return v___x_2871_;
}
else
{
lean_object* v_head_2872_; lean_object* v_tail_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2918_; 
v_head_2872_ = lean_ctor_get(v_x_2863_, 0);
v_tail_2873_ = lean_ctor_get(v_x_2863_, 1);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_x_2863_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2875_ = v_x_2863_;
v_isShared_2876_ = v_isSharedCheck_2918_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_tail_2873_);
lean_inc(v_head_2872_);
lean_dec(v_x_2863_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2918_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v_a_2878_; lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_Meta_saveState___redArg(v___y_2866_, v___y_2868_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref(v___x_2883_);
lean_inc_ref(v_f_2862_);
lean_inc(v___y_2868_);
lean_inc_ref(v___y_2867_);
lean_inc(v___y_2866_);
lean_inc_ref(v___y_2865_);
lean_inc(v_head_2872_);
v___x_2885_ = lean_apply_6(v_f_2862_, v_head_2872_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, lean_box(0));
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2887_; 
lean_dec(v_a_2884_);
lean_dec(v_head_2872_);
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___x_2885_);
v___x_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2887_, 0, v_a_2886_);
v_a_2878_ = v___x_2887_;
goto v___jp_2877_;
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2909_; 
v_a_2888_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2890_ = v___x_2885_;
v_isShared_2891_ = v_isSharedCheck_2909_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2885_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2909_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
uint8_t v___y_2893_; uint8_t v___x_2907_; 
v___x_2907_ = l_Lean_Exception_isInterrupt(v_a_2888_);
if (v___x_2907_ == 0)
{
uint8_t v___x_2908_; 
lean_inc(v_a_2888_);
v___x_2908_ = l_Lean_Exception_isRuntime(v_a_2888_);
v___y_2893_ = v___x_2908_;
goto v___jp_2892_;
}
else
{
v___y_2893_ = v___x_2907_;
goto v___jp_2892_;
}
v___jp_2892_:
{
if (v___y_2893_ == 0)
{
lean_object* v___x_2894_; 
lean_del_object(v___x_2890_);
lean_dec(v_a_2888_);
v___x_2894_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2884_, v___y_2866_, v___y_2868_);
lean_dec(v_a_2884_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v___x_2895_; 
lean_dec_ref(v___x_2894_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_head_2872_);
v_a_2878_ = v___x_2895_;
goto v___jp_2877_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_del_object(v___x_2875_);
lean_dec(v_tail_2873_);
lean_dec(v_head_2872_);
lean_dec(v_x_2864_);
lean_dec_ref(v_f_2862_);
v_a_2896_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2894_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2894_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
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
else
{
lean_object* v___x_2905_; 
lean_dec(v_a_2884_);
lean_del_object(v___x_2875_);
lean_dec(v_tail_2873_);
lean_dec(v_head_2872_);
lean_dec(v_x_2864_);
lean_dec_ref(v_f_2862_);
if (v_isShared_2891_ == 0)
{
v___x_2905_ = v___x_2890_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2888_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_del_object(v___x_2875_);
lean_dec(v_tail_2873_);
lean_dec(v_head_2872_);
lean_dec(v_x_2864_);
lean_dec_ref(v_f_2862_);
v_a_2910_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2883_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2883_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
v___jp_2877_:
{
lean_object* v___x_2880_; 
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v_x_2864_);
lean_ctor_set(v___x_2875_, 0, v_a_2878_);
v___x_2880_ = v___x_2875_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2878_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_x_2864_);
v___x_2880_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
v_x_2863_ = v_tail_2873_;
v_x_2864_ = v___x_2880_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_2919_, lean_object* v_x_2920_, lean_object* v_x_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2919_, v_x_2920_, v_x_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_2928_, lean_object* v_a_2929_){
_start:
{
if (lean_obj_tag(v_a_2928_) == 0)
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_array_to_list(v_a_2929_);
return v___x_2930_;
}
else
{
lean_object* v_head_2931_; 
v_head_2931_ = lean_ctor_get(v_a_2928_, 0);
if (lean_obj_tag(v_head_2931_) == 1)
{
lean_object* v_tail_2932_; lean_object* v_val_2933_; lean_object* v___x_2934_; 
lean_inc_ref(v_head_2931_);
v_tail_2932_ = lean_ctor_get(v_a_2928_, 1);
lean_inc(v_tail_2932_);
lean_dec_ref(v_a_2928_);
v_val_2933_ = lean_ctor_get(v_head_2931_, 0);
lean_inc(v_val_2933_);
lean_dec_ref(v_head_2931_);
v___x_2934_ = lean_array_push(v_a_2929_, v_val_2933_);
v_a_2928_ = v_tail_2932_;
v_a_2929_ = v___x_2934_;
goto _start;
}
else
{
lean_object* v_tail_2936_; 
v_tail_2936_ = lean_ctor_get(v_a_2928_, 1);
lean_inc(v_tail_2936_);
lean_dec_ref(v_a_2928_);
v_a_2928_ = v_tail_2936_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_2938_, lean_object* v_f_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = lean_box(0);
v___x_2946_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2939_, v_L_2938_, v___x_2945_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2958_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2958_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2958_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2951_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_2947_);
v___x_2952_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_2947_, v___x_2951_);
v___x_2953_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_2947_, v___x_2951_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 0, v___x_2954_);
v___x_2956_ = v___x_2949_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
v_a_2959_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2946_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2946_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* v_L_2967_, lean_object* v_f_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_2967_, v_f_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t v___x_2975_, uint8_t v___x_2976_, lean_object* v_x_2977_, lean_object* v_x_2978_, lean_object* v___y_2979_){
_start:
{
if (lean_obj_tag(v_x_2977_) == 0)
{
lean_object* v___x_2981_; 
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_x_2978_);
return v___x_2981_;
}
else
{
lean_object* v_head_2982_; lean_object* v_tail_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2997_; 
v_head_2982_ = lean_ctor_get(v_x_2977_, 0);
v_tail_2983_ = lean_ctor_get(v_x_2977_, 1);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_x_2977_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2985_ = v_x_2977_;
v_isShared_2986_ = v_isSharedCheck_2997_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_tail_2983_);
lean_inc(v_head_2982_);
lean_dec(v_x_2977_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2997_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
uint8_t v_a_2988_; lean_object* v___x_2994_; lean_object* v_a_2995_; uint8_t v___x_2996_; 
v___x_2994_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2982_, v___y_2979_);
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref(v___x_2994_);
v___x_2996_ = lean_unbox(v_a_2995_);
lean_dec(v_a_2995_);
if (v___x_2996_ == 0)
{
v_a_2988_ = v___x_2975_;
goto v___jp_2987_;
}
else
{
v_a_2988_ = v___x_2976_;
goto v___jp_2987_;
}
v___jp_2987_:
{
if (v_a_2988_ == 0)
{
lean_del_object(v___x_2985_);
lean_dec(v_head_2982_);
v_x_2977_ = v_tail_2983_;
goto _start;
}
else
{
lean_object* v___x_2991_; 
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 1, v_x_2978_);
v___x_2991_ = v___x_2985_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_head_2982_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_x_2978_);
v___x_2991_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
v_x_2977_ = v_tail_2983_;
v_x_2978_ = v___x_2991_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* v___x_2998_, lean_object* v___x_2999_, lean_object* v_x_3000_, lean_object* v_x_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
uint8_t v___x_57947__boxed_3004_; uint8_t v___x_57948__boxed_3005_; lean_object* v_res_3006_; 
v___x_57947__boxed_3004_ = lean_unbox(v___x_2998_);
v___x_57948__boxed_3005_ = lean_unbox(v___x_2999_);
v_res_3006_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_57947__boxed_3004_, v___x_57948__boxed_3005_, v_x_3000_, v_x_3001_, v___y_3002_);
lean_dec(v___y_3002_);
return v_res_3006_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
v___x_3009_ = l_Lean_stringToMessageData(v___x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_3012_, lean_object* v_trace_3013_, lean_object* v_next_3014_, lean_object* v_orig_3015_, lean_object* v_goals_3016_, lean_object* v_remaining_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2));
lean_inc(v_remaining_3017_);
lean_inc(v_goals_3016_);
v___x_3027_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_3016_, v_remaining_3017_, v___x_3026_, v___x_3026_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v_fst_3029_; lean_object* v_snd_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_4238_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref(v___x_3027_);
v_fst_3029_ = lean_ctor_get(v_a_3028_, 0);
v_snd_3030_ = lean_ctor_get(v_a_3028_, 1);
v_isSharedCheck_4238_ = !lean_is_exclusive(v_a_3028_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_3032_ = v_a_3028_;
v_isShared_3033_ = v_isSharedCheck_4238_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_snd_3030_);
lean_inc(v_fst_3029_);
lean_dec(v_a_3028_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_4238_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
uint8_t v___x_3034_; 
v___x_3034_ = l_List_isEmpty___redArg(v_fst_3029_);
if (v___x_3034_ == 0)
{
lean_object* v_options_3035_; lean_object* v_inheritedTraceOptions_3036_; uint8_t v_hasTrace_3037_; lean_object* v___f_3038_; 
lean_dec(v_remaining_3017_);
v_options_3035_ = lean_ctor_get(v_a_3020_, 2);
v_inheritedTraceOptions_3036_ = lean_ctor_get(v_a_3020_, 13);
v_hasTrace_3037_ = lean_ctor_get_uint8(v_options_3035_, sizeof(void*)*1);
lean_inc(v_orig_3015_);
lean_inc_ref(v_next_3014_);
lean_inc(v_trace_3013_);
lean_inc_ref(v_cfg_3012_);
v___f_3038_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3038_, 0, v_cfg_3012_);
lean_closure_set(v___f_3038_, 1, v_trace_3013_);
lean_closure_set(v___f_3038_, 2, v_next_3014_);
lean_closure_set(v___f_3038_, 3, v_orig_3015_);
if (v_hasTrace_3037_ == 0)
{
lean_object* v___x_3039_; 
lean_del_object(v___x_3032_);
v___x_3039_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3029_, v___f_3038_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3109_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3042_ = v___x_3039_;
v_isShared_3043_ = v_isSharedCheck_3109_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3039_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3109_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_fst_3044_; lean_object* v_snd_3045_; lean_object* v___x_3046_; lean_object* v_a_3048_; lean_object* v___y_3055_; lean_object* v___y_3058_; lean_object* v___y_3059_; uint8_t v___y_3060_; lean_object* v___y_3071_; lean_object* v_a_3086_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v_fst_3044_ = lean_ctor_get(v_a_3040_, 0);
lean_inc(v_fst_3044_);
v_snd_3045_ = lean_ctor_get(v_a_3040_, 1);
lean_inc(v_snd_3045_);
lean_dec(v_a_3040_);
v___x_3046_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3045_, v___x_3026_);
v___x_3104_ = lean_box(0);
v___x_3105_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_hasTrace_3037_, v_goals_3016_, v___x_3104_, v_a_3019_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3107_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref(v___x_3105_);
v___x_3107_ = l_List_reverse___redArg(v_a_3106_);
v_a_3086_ = v___x_3107_;
goto v___jp_3085_;
}
else
{
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3108_; 
v_a_3108_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3108_);
lean_dec_ref(v___x_3105_);
v_a_3086_ = v_a_3108_;
goto v___jp_3085_;
}
else
{
lean_dec(v___x_3046_);
lean_dec(v_fst_3044_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
return v___x_3105_;
}
}
v___jp_3047_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3049_ = l_List_appendTR___redArg(v___x_3046_, v_fst_3044_);
v___x_3050_ = l_List_appendTR___redArg(v___x_3049_, v_a_3048_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3050_);
v___x_3052_ = v___x_3042_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
v___jp_3054_:
{
if (lean_obj_tag(v___y_3055_) == 0)
{
lean_object* v_a_3056_; 
v_a_3056_ = lean_ctor_get(v___y_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref(v___y_3055_);
v_a_3048_ = v_a_3056_;
goto v___jp_3047_;
}
else
{
lean_dec(v___x_3046_);
lean_dec(v_fst_3044_);
lean_del_object(v___x_3042_);
return v___y_3055_;
}
}
v___jp_3057_:
{
if (v___y_3060_ == 0)
{
lean_object* v___x_3061_; 
lean_dec_ref(v___y_3058_);
v___x_3061_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3059_, v_a_3019_, v_a_3021_);
lean_dec_ref(v___y_3059_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_dec_ref(v___x_3061_);
v_a_3048_ = v_snd_3030_;
goto v___jp_3047_;
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v___x_3046_);
lean_dec(v_fst_3044_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3030_);
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
else
{
lean_dec_ref(v___y_3059_);
lean_dec(v_snd_3030_);
v___y_3055_ = v___y_3058_;
goto v___jp_3054_;
}
}
v___jp_3070_:
{
uint8_t v___x_3072_; 
v___x_3072_ = l_List_isEmpty___redArg(v_fst_3044_);
lean_dec(v_fst_3044_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_dec(v___y_3071_);
lean_dec(v___x_3046_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
v___x_3073_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3074_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3073_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
return v___x_3074_;
}
else
{
lean_object* v___x_3075_; 
v___x_3075_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3071_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3084_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = l_List_appendTR___redArg(v___x_3046_, v_a_3076_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3080_);
v___x_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
else
{
lean_dec(v___x_3046_);
return v___x_3075_;
}
}
}
v___jp_3085_:
{
uint8_t v_commitIndependentGoals_3087_; lean_object* v___x_3088_; 
v_commitIndependentGoals_3087_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*4);
lean_inc(v___x_3046_);
v___x_3088_ = l_List_appendTR___redArg(v_a_3086_, v___x_3046_);
if (v_commitIndependentGoals_3087_ == 0)
{
lean_del_object(v___x_3042_);
v___y_3071_ = v___x_3088_;
goto v___jp_3070_;
}
else
{
uint8_t v___x_3089_; 
v___x_3089_ = l_List_isEmpty___redArg(v___x_3046_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_Meta_saveState___redArg(v_a_3019_, v_a_3021_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3092_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref(v___x_3090_);
lean_inc(v_snd_3030_);
v___x_3092_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___x_3088_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_dec(v_a_3091_);
lean_dec(v_snd_3030_);
v___y_3055_ = v___x_3092_;
goto v___jp_3054_;
}
else
{
lean_object* v_a_3093_; uint8_t v___x_3094_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
v___x_3094_ = l_Lean_Exception_isInterrupt(v_a_3093_);
if (v___x_3094_ == 0)
{
uint8_t v___x_3095_; 
v___x_3095_ = l_Lean_Exception_isRuntime(v_a_3093_);
v___y_3058_ = v___x_3092_;
v___y_3059_ = v_a_3091_;
v___y_3060_ = v___x_3095_;
goto v___jp_3057_;
}
else
{
lean_dec(v_a_3093_);
v___y_3058_ = v___x_3092_;
v___y_3059_ = v_a_3091_;
v___y_3060_ = v___x_3094_;
goto v___jp_3057_;
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v___x_3088_);
lean_dec(v___x_3046_);
lean_dec(v_fst_3044_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
v_a_3096_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3090_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3090_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_del_object(v___x_3042_);
v___y_3071_ = v___x_3088_;
goto v___jp_3070_;
}
}
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec(v_snd_3030_);
lean_dec(v_goals_3016_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
v_a_3110_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3039_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3039_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
else
{
lean_object* v___f_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v_a_3126_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v_a_3143_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v_a_3150_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v_a_3156_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; uint8_t v___y_3173_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3196_; lean_object* v___y_3197_; uint8_t v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v_a_3202_; uint8_t v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v_a_3221_; uint8_t v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v_a_3230_; lean_object* v___y_3233_; lean_object* v___y_3234_; uint8_t v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v_a_3241_; uint8_t v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3257_; uint8_t v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; uint8_t v___y_3267_; lean_object* v___y_3271_; lean_object* v___y_3272_; uint8_t v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3288_; lean_object* v___y_3289_; uint8_t v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; uint8_t v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; uint8_t v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; uint8_t v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; uint8_t v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; uint8_t v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v_a_3331_; lean_object* v___y_3336_; lean_object* v___y_3337_; uint8_t v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v_a_3342_; uint8_t v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v_a_3358_; lean_object* v___y_3361_; lean_object* v___y_3362_; uint8_t v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v_a_3369_; uint8_t v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v_a_3379_; lean_object* v___y_3382_; lean_object* v___y_3383_; uint8_t v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3392_; lean_object* v___y_3393_; uint8_t v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; uint8_t v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; uint8_t v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; uint8_t v___y_3426_; lean_object* v___y_3430_; lean_object* v___y_3431_; uint8_t v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; uint8_t v___y_3447_; uint8_t v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v_a_3456_; uint8_t v___y_3463_; uint8_t v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3493_; uint8_t v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3504_; uint8_t v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v_a_3509_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v_a_3516_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v_a_3528_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v_a_3533_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3542_; lean_object* v___y_3543_; uint8_t v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v_a_3548_; lean_object* v___y_3561_; lean_object* v___y_3562_; uint8_t v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v_a_3567_; lean_object* v___y_3570_; lean_object* v___y_3571_; uint8_t v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v_a_3576_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; uint8_t v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v_a_3587_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; uint8_t v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; uint8_t v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; uint8_t v___y_3613_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; uint8_t v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3634_; lean_object* v___y_3635_; uint8_t v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3644_; lean_object* v___y_3645_; uint8_t v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; uint8_t v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; uint8_t v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; uint8_t v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; uint8_t v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v_a_3677_; lean_object* v___y_3682_; uint8_t v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v_a_3688_; lean_object* v___y_3698_; uint8_t v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v_a_3704_; lean_object* v___y_3707_; uint8_t v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v_a_3713_; lean_object* v___y_3716_; lean_object* v___y_3717_; uint8_t v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v_a_3724_; lean_object* v___y_3728_; lean_object* v___y_3729_; uint8_t v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; uint8_t v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; uint8_t v___y_3750_; lean_object* v___y_3754_; lean_object* v___y_3755_; uint8_t v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3771_; uint8_t v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3781_; lean_object* v___y_3782_; uint8_t v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; uint8_t v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; uint8_t v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; uint8_t v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v_a_3816_; uint8_t v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; uint8_t v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3846_; lean_object* v___y_3847_; uint8_t v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v_a_3866_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; uint8_t v___y_3884_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; uint8_t v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v_a_3906_; 
lean_inc(v_snd_3030_);
lean_inc(v_fst_3029_);
v___f_3118_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3118_, 0, v_fst_3029_);
lean_closure_set(v___f_3118_, 1, v_snd_3030_);
v___x_3119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_3120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_3013_);
v___x_3121_ = l_Lean_Name_append(v___x_3120_, v_trace_3013_);
v___x_3122_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3036_, v_options_3035_, v___x_3121_);
lean_dec(v___x_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3955_; uint8_t v___x_3956_; 
v___x_3955_ = l_Lean_trace_profiler;
v___x_3956_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3035_, v___x_3955_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; 
lean_dec_ref(v___f_3118_);
lean_del_object(v___x_3032_);
v___x_3957_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3029_, v___f_3038_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_4226_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_3960_ = v___x_3957_;
v_isShared_3961_ = v_isSharedCheck_4226_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_4226_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v_fst_3962_; lean_object* v_snd_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_4225_; 
v_fst_3962_ = lean_ctor_get(v_a_3958_, 0);
v_snd_3963_ = lean_ctor_get(v_a_3958_, 1);
v_isSharedCheck_4225_ = !lean_is_exclusive(v_a_3958_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_3965_ = v_a_3958_;
v_isShared_3966_ = v_isSharedCheck_4225_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_snd_3963_);
lean_inc(v_fst_3962_);
lean_dec(v_a_3958_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_4225_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3967_; lean_object* v___y_3969_; lean_object* v_a_3982_; lean_object* v___y_3989_; lean_object* v___y_3992_; lean_object* v___y_3993_; uint8_t v___y_3994_; lean_object* v___y_4005_; lean_object* v_a_4021_; lean_object* v___f_4025_; lean_object* v___x_4026_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v_a_4030_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v_a_4047_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v_a_4052_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v_a_4057_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; uint8_t v___y_4071_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; uint8_t v___y_4100_; lean_object* v___y_4106_; lean_object* v___y_4107_; uint8_t v___y_4108_; lean_object* v_a_4109_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v_a_4116_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v_a_4128_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v_a_4133_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v_a_4139_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; uint8_t v___y_4151_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; uint8_t v___y_4161_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; uint8_t v___y_4174_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4189_; lean_object* v___y_4190_; uint8_t v___y_4191_; lean_object* v_a_4192_; 
v___x_3967_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3963_, v___x_3026_);
lean_inc(v___x_3967_);
lean_inc(v_fst_3962_);
v___f_4025_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_4025_, 0, v_fst_3962_);
lean_closure_set(v___f_4025_, 1, v___x_3967_);
v___x_4026_ = lean_box(0);
if (v___x_3122_ == 0)
{
if (v___x_3956_ == 0)
{
lean_object* v___x_4221_; 
lean_dec_ref(v___f_4025_);
lean_del_object(v___x_3965_);
v___x_4221_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3037_, v___x_3956_, v_goals_3016_, v___x_4026_, v_a_3019_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4223_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4222_);
lean_dec_ref(v___x_4221_);
v___x_4223_ = l_List_reverse___redArg(v_a_4222_);
v_a_4021_ = v___x_4223_;
goto v___jp_4020_;
}
else
{
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4224_; 
v_a_4224_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4224_);
lean_dec_ref(v___x_4221_);
v_a_4021_ = v_a_4224_;
goto v___jp_4020_;
}
else
{
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
lean_del_object(v___x_3960_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
return v___x_4221_;
}
}
}
else
{
lean_del_object(v___x_3960_);
goto v___jp_4196_;
}
}
else
{
lean_del_object(v___x_3960_);
goto v___jp_4196_;
}
v___jp_3968_:
{
uint8_t v___x_3970_; 
v___x_3970_ = l_List_isEmpty___redArg(v_fst_3962_);
lean_dec(v_fst_3962_);
if (v___x_3970_ == 0)
{
lean_dec(v___y_3969_);
lean_dec(v___x_3967_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
goto v___jp_3023_;
}
else
{
if (v___x_3956_ == 0)
{
lean_object* v___x_3971_; 
v___x_3971_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3969_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3980_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3974_ = v___x_3971_;
v_isShared_3975_ = v_isSharedCheck_3980_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3971_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3980_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3976_ = l_List_appendTR___redArg(v___x_3967_, v_a_3972_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v___x_3976_);
v___x_3978_ = v___x_3974_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
else
{
lean_dec(v___x_3967_);
return v___x_3971_;
}
}
else
{
lean_dec(v___y_3969_);
lean_dec(v___x_3967_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
goto v___jp_3023_;
}
}
}
v___jp_3981_:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3986_; 
v___x_3983_ = l_List_appendTR___redArg(v___x_3967_, v_fst_3962_);
v___x_3984_ = l_List_appendTR___redArg(v___x_3983_, v_a_3982_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3984_);
v___x_3986_ = v___x_3960_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3984_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
v___jp_3988_:
{
if (lean_obj_tag(v___y_3989_) == 0)
{
lean_object* v_a_3990_; 
v_a_3990_ = lean_ctor_get(v___y_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref(v___y_3989_);
v_a_3982_ = v_a_3990_;
goto v___jp_3981_;
}
else
{
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
lean_del_object(v___x_3960_);
return v___y_3989_;
}
}
v___jp_3991_:
{
if (v___y_3994_ == 0)
{
lean_object* v___x_3995_; 
lean_dec_ref(v___y_3993_);
v___x_3995_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3992_, v_a_3019_, v_a_3021_);
lean_dec_ref(v___y_3992_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_dec_ref(v___x_3995_);
v_a_3982_ = v_snd_3030_;
goto v___jp_3981_;
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
lean_del_object(v___x_3960_);
lean_dec(v_snd_3030_);
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3995_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3995_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
}
else
{
lean_dec_ref(v___y_3992_);
lean_dec(v_snd_3030_);
v___y_3989_ = v___y_3993_;
goto v___jp_3988_;
}
}
v___jp_4004_:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_Meta_saveState___redArg(v_a_3019_, v_a_3021_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v___x_4008_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref(v___x_4006_);
lean_inc(v_snd_3030_);
v___x_4008_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_4005_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_dec(v_a_4007_);
lean_dec(v_snd_3030_);
v___y_3989_ = v___x_4008_;
goto v___jp_3988_;
}
else
{
lean_object* v_a_4009_; uint8_t v___x_4010_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
v___x_4010_ = l_Lean_Exception_isInterrupt(v_a_4009_);
if (v___x_4010_ == 0)
{
uint8_t v___x_4011_; 
v___x_4011_ = l_Lean_Exception_isRuntime(v_a_4009_);
v___y_3992_ = v_a_4007_;
v___y_3993_ = v___x_4008_;
v___y_3994_ = v___x_4011_;
goto v___jp_3991_;
}
else
{
lean_dec(v_a_4009_);
v___y_3992_ = v_a_4007_;
v___y_3993_ = v___x_4008_;
v___y_3994_ = v___x_4010_;
goto v___jp_3991_;
}
}
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
lean_dec(v___y_4005_);
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
lean_del_object(v___x_3960_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
v_a_4012_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4006_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4006_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
v___jp_4020_:
{
uint8_t v_commitIndependentGoals_4022_; lean_object* v___x_4023_; 
v_commitIndependentGoals_4022_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*4);
lean_inc(v___x_3967_);
v___x_4023_ = l_List_appendTR___redArg(v_a_4021_, v___x_3967_);
if (v_commitIndependentGoals_4022_ == 0)
{
lean_del_object(v___x_3960_);
v___y_3969_ = v___x_4023_;
goto v___jp_3968_;
}
else
{
uint8_t v___x_4024_; 
v___x_4024_ = l_List_isEmpty___redArg(v___x_3967_);
if (v___x_4024_ == 0)
{
v___y_4005_ = v___x_4023_;
goto v___jp_4004_;
}
else
{
if (v___x_3956_ == 0)
{
lean_del_object(v___x_3960_);
v___y_3969_ = v___x_4023_;
goto v___jp_3968_;
}
else
{
v___y_4005_ = v___x_4023_;
goto v___jp_4004_;
}
}
}
}
v___jp_4027_:
{
lean_object* v___x_4031_; double v___x_4032_; double v___x_4033_; double v___x_4034_; double v___x_4035_; double v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
v___x_4031_ = lean_io_mono_nanos_now();
v___x_4032_ = lean_float_of_nat(v___y_4029_);
v___x_4033_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_4034_ = lean_float_div(v___x_4032_, v___x_4033_);
v___x_4035_ = lean_float_of_nat(v___x_4031_);
v___x_4036_ = lean_float_div(v___x_4035_, v___x_4033_);
v___x_4037_ = lean_box_float(v___x_4034_);
v___x_4038_ = lean_box_float(v___x_4036_);
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 1, v___x_4038_);
lean_ctor_set(v___x_3965_, 0, v___x_4037_);
v___x_4040_ = v___x_3965_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4037_);
lean_ctor_set(v_reuseFailAlloc_4043_, 1, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4041_, 0, v_a_4030_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
v___x_4042_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3013_, v_hasTrace_3037_, v___x_3119_, v_options_3035_, v___x_3122_, v___y_4028_, v___f_4025_, v___x_4041_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
return v___x_4042_;
}
}
v___jp_4044_:
{
lean_object* v___x_4048_; 
v___x_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4048_, 0, v_a_4047_);
v___y_4028_ = v___y_4045_;
v___y_4029_ = v___y_4046_;
v_a_4030_ = v___x_4048_;
goto v___jp_4027_;
}
v___jp_4049_:
{
lean_object* v___x_4053_; 
v___x_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4053_, 0, v_a_4052_);
v___y_4028_ = v___y_4050_;
v___y_4029_ = v___y_4051_;
v_a_4030_ = v___x_4053_;
goto v___jp_4027_;
}
v___jp_4054_:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4058_ = l_List_appendTR___redArg(v___x_3967_, v_fst_3962_);
v___x_4059_ = l_List_appendTR___redArg(v___x_4058_, v_a_4057_);
v___y_4050_ = v___y_4055_;
v___y_4051_ = v___y_4056_;
v_a_4052_ = v___x_4059_;
goto v___jp_4049_;
}
v___jp_4060_:
{
if (lean_obj_tag(v___y_4063_) == 0)
{
lean_object* v_a_4064_; 
v_a_4064_ = lean_ctor_get(v___y_4063_, 0);
lean_inc(v_a_4064_);
lean_dec_ref(v___y_4063_);
v___y_4055_ = v___y_4061_;
v___y_4056_ = v___y_4062_;
v_a_4057_ = v_a_4064_;
goto v___jp_4054_;
}
else
{
lean_object* v_a_4065_; 
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
v_a_4065_ = lean_ctor_get(v___y_4063_, 0);
lean_inc(v_a_4065_);
lean_dec_ref(v___y_4063_);
v___y_4045_ = v___y_4061_;
v___y_4046_ = v___y_4062_;
v_a_4047_ = v_a_4065_;
goto v___jp_4044_;
}
}
v___jp_4066_:
{
if (v___y_4071_ == 0)
{
lean_object* v___x_4072_; 
lean_dec_ref(v___y_4068_);
v___x_4072_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4070_, v_a_3019_, v_a_3021_);
lean_dec_ref(v___y_4070_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_dec_ref(v___x_4072_);
v___y_4055_ = v___y_4067_;
v___y_4056_ = v___y_4069_;
v_a_4057_ = v_snd_3030_;
goto v___jp_4054_;
}
else
{
lean_object* v_a_4073_; 
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
lean_dec(v_snd_3030_);
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_a_4073_);
lean_dec_ref(v___x_4072_);
v___y_4045_ = v___y_4067_;
v___y_4046_ = v___y_4069_;
v_a_4047_ = v_a_4073_;
goto v___jp_4044_;
}
}
else
{
lean_dec_ref(v___y_4070_);
lean_dec(v_snd_3030_);
v___y_4061_ = v___y_4067_;
v___y_4062_ = v___y_4069_;
v___y_4063_ = v___y_4068_;
goto v___jp_4060_;
}
}
v___jp_4074_:
{
lean_object* v___x_4078_; 
v___x_4078_ = l_Lean_Meta_saveState___redArg(v_a_3019_, v_a_3021_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v___x_4080_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
lean_inc(v_a_4079_);
lean_dec_ref(v___x_4078_);
lean_inc(v_snd_3030_);
lean_inc(v_trace_3013_);
v___x_4080_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_4076_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_dec(v_a_4079_);
lean_dec(v_snd_3030_);
v___y_4061_ = v___y_4075_;
v___y_4062_ = v___y_4077_;
v___y_4063_ = v___x_4080_;
goto v___jp_4060_;
}
else
{
lean_object* v_a_4081_; uint8_t v___x_4082_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
v___x_4082_ = l_Lean_Exception_isInterrupt(v_a_4081_);
if (v___x_4082_ == 0)
{
uint8_t v___x_4083_; 
v___x_4083_ = l_Lean_Exception_isRuntime(v_a_4081_);
v___y_4067_ = v___y_4075_;
v___y_4068_ = v___x_4080_;
v___y_4069_ = v___y_4077_;
v___y_4070_ = v_a_4079_;
v___y_4071_ = v___x_4083_;
goto v___jp_4066_;
}
else
{
lean_dec(v_a_4081_);
v___y_4067_ = v___y_4075_;
v___y_4068_ = v___x_4080_;
v___y_4069_ = v___y_4077_;
v___y_4070_ = v_a_4079_;
v___y_4071_ = v___x_4082_;
goto v___jp_4066_;
}
}
}
else
{
lean_object* v_a_4084_; 
lean_dec(v___y_4076_);
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_4084_ = lean_ctor_get(v___x_4078_, 0);
lean_inc(v_a_4084_);
lean_dec_ref(v___x_4078_);
v___y_4045_ = v___y_4075_;
v___y_4046_ = v___y_4077_;
v_a_4047_ = v_a_4084_;
goto v___jp_4044_;
}
}
v___jp_4085_:
{
if (lean_obj_tag(v___y_4088_) == 0)
{
lean_object* v_a_4089_; 
v_a_4089_ = lean_ctor_get(v___y_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref(v___y_4088_);
v___y_4050_ = v___y_4086_;
v___y_4051_ = v___y_4087_;
v_a_4052_ = v_a_4089_;
goto v___jp_4049_;
}
else
{
lean_object* v_a_4090_; 
v_a_4090_ = lean_ctor_get(v___y_4088_, 0);
lean_inc(v_a_4090_);
lean_dec_ref(v___y_4088_);
v___y_4045_ = v___y_4086_;
v___y_4046_ = v___y_4087_;
v_a_4047_ = v_a_4090_;
goto v___jp_4044_;
}
}
v___jp_4091_:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4095_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4094_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_4086_ = v___y_4092_;
v___y_4087_ = v___y_4093_;
v___y_4088_ = v___x_4095_;
goto v___jp_4085_;
}
v___jp_4096_:
{
uint8_t v___x_4101_; 
v___x_4101_ = l_List_isEmpty___redArg(v_fst_3962_);
lean_dec(v_fst_3962_);
if (v___x_4101_ == 0)
{
lean_dec(v___y_4098_);
lean_dec(v___x_3967_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___y_4092_ = v___y_4097_;
v___y_4093_ = v___y_4099_;
goto v___jp_4091_;
}
else
{
if (v___y_4100_ == 0)
{
lean_object* v___x_4102_; 
lean_inc(v_trace_3013_);
v___x_4102_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_4098_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4104_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref(v___x_4102_);
v___x_4104_ = l_List_appendTR___redArg(v___x_3967_, v_a_4103_);
v___y_4050_ = v___y_4097_;
v___y_4051_ = v___y_4099_;
v_a_4052_ = v___x_4104_;
goto v___jp_4049_;
}
else
{
lean_dec(v___x_3967_);
v___y_4086_ = v___y_4097_;
v___y_4087_ = v___y_4099_;
v___y_4088_ = v___x_4102_;
goto v___jp_4085_;
}
}
else
{
lean_dec(v___y_4098_);
lean_dec(v___x_3967_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___y_4092_ = v___y_4097_;
v___y_4093_ = v___y_4099_;
goto v___jp_4091_;
}
}
}
v___jp_4105_:
{
uint8_t v_commitIndependentGoals_4110_; lean_object* v___x_4111_; 
v_commitIndependentGoals_4110_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*4);
lean_inc(v___x_3967_);
v___x_4111_ = l_List_appendTR___redArg(v_a_4109_, v___x_3967_);
if (v_commitIndependentGoals_4110_ == 0)
{
v___y_4097_ = v___y_4106_;
v___y_4098_ = v___x_4111_;
v___y_4099_ = v___y_4107_;
v___y_4100_ = v___y_4108_;
goto v___jp_4096_;
}
else
{
uint8_t v___x_4112_; 
v___x_4112_ = l_List_isEmpty___redArg(v___x_3967_);
if (v___x_4112_ == 0)
{
v___y_4075_ = v___y_4106_;
v___y_4076_ = v___x_4111_;
v___y_4077_ = v___y_4107_;
goto v___jp_4074_;
}
else
{
if (v___y_4108_ == 0)
{
v___y_4097_ = v___y_4106_;
v___y_4098_ = v___x_4111_;
v___y_4099_ = v___y_4107_;
v___y_4100_ = v___y_4108_;
goto v___jp_4096_;
}
else
{
v___y_4075_ = v___y_4106_;
v___y_4076_ = v___x_4111_;
v___y_4077_ = v___y_4107_;
goto v___jp_4074_;
}
}
}
}
v___jp_4113_:
{
lean_object* v___x_4117_; double v___x_4118_; double v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4117_ = lean_io_get_num_heartbeats();
v___x_4118_ = lean_float_of_nat(v___y_4115_);
v___x_4119_ = lean_float_of_nat(v___x_4117_);
v___x_4120_ = lean_box_float(v___x_4118_);
v___x_4121_ = lean_box_float(v___x_4119_);
v___x_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4120_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4123_, 0, v_a_4116_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3013_, v_hasTrace_3037_, v___x_3119_, v_options_3035_, v___x_3122_, v___y_4114_, v___f_4025_, v___x_4123_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
return v___x_4124_;
}
v___jp_4125_:
{
lean_object* v___x_4129_; 
v___x_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4129_, 0, v_a_4128_);
v___y_4114_ = v___y_4126_;
v___y_4115_ = v___y_4127_;
v_a_4116_ = v___x_4129_;
goto v___jp_4113_;
}
v___jp_4130_:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = l_List_appendTR___redArg(v___x_3967_, v_fst_3962_);
v___x_4135_ = l_List_appendTR___redArg(v___x_4134_, v_a_4133_);
v___y_4126_ = v___y_4131_;
v___y_4127_ = v___y_4132_;
v_a_4128_ = v___x_4135_;
goto v___jp_4125_;
}
v___jp_4136_:
{
lean_object* v___x_4140_; 
v___x_4140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4140_, 0, v_a_4139_);
v___y_4114_ = v___y_4137_;
v___y_4115_ = v___y_4138_;
v_a_4116_ = v___x_4140_;
goto v___jp_4113_;
}
v___jp_4141_:
{
if (lean_obj_tag(v___y_4144_) == 0)
{
lean_object* v_a_4145_; 
v_a_4145_ = lean_ctor_get(v___y_4144_, 0);
lean_inc(v_a_4145_);
lean_dec_ref(v___y_4144_);
v___y_4126_ = v___y_4142_;
v___y_4127_ = v___y_4143_;
v_a_4128_ = v_a_4145_;
goto v___jp_4125_;
}
else
{
lean_object* v_a_4146_; 
v_a_4146_ = lean_ctor_get(v___y_4144_, 0);
lean_inc(v_a_4146_);
lean_dec_ref(v___y_4144_);
v___y_4137_ = v___y_4142_;
v___y_4138_ = v___y_4143_;
v_a_4139_ = v_a_4146_;
goto v___jp_4136_;
}
}
v___jp_4147_:
{
if (v___y_4151_ == 0)
{
lean_object* v___x_4152_; 
lean_inc(v_trace_3013_);
v___x_4152_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_4150_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4154_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref(v___x_4152_);
v___x_4154_ = l_List_appendTR___redArg(v___x_3967_, v_a_4153_);
v___y_4126_ = v___y_4148_;
v___y_4127_ = v___y_4149_;
v_a_4128_ = v___x_4154_;
goto v___jp_4125_;
}
else
{
lean_dec(v___x_3967_);
v___y_4142_ = v___y_4148_;
v___y_4143_ = v___y_4149_;
v___y_4144_ = v___x_4152_;
goto v___jp_4141_;
}
}
else
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_dec(v___y_4150_);
lean_dec(v___x_3967_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___x_4155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4156_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4155_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_4142_ = v___y_4148_;
v___y_4143_ = v___y_4149_;
v___y_4144_ = v___x_4156_;
goto v___jp_4141_;
}
}
v___jp_4157_:
{
uint8_t v___x_4162_; 
v___x_4162_ = l_List_isEmpty___redArg(v_fst_3962_);
lean_dec(v_fst_3962_);
if (v___x_4162_ == 0)
{
v___y_4148_ = v___y_4158_;
v___y_4149_ = v___y_4159_;
v___y_4150_ = v___y_4160_;
v___y_4151_ = v___y_4161_;
goto v___jp_4147_;
}
else
{
v___y_4148_ = v___y_4158_;
v___y_4149_ = v___y_4159_;
v___y_4150_ = v___y_4160_;
v___y_4151_ = v___x_3956_;
goto v___jp_4147_;
}
}
v___jp_4163_:
{
if (lean_obj_tag(v___y_4166_) == 0)
{
lean_object* v_a_4167_; 
v_a_4167_ = lean_ctor_get(v___y_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref(v___y_4166_);
v___y_4131_ = v___y_4164_;
v___y_4132_ = v___y_4165_;
v_a_4133_ = v_a_4167_;
goto v___jp_4130_;
}
else
{
lean_object* v_a_4168_; 
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
v_a_4168_ = lean_ctor_get(v___y_4166_, 0);
lean_inc(v_a_4168_);
lean_dec_ref(v___y_4166_);
v___y_4137_ = v___y_4164_;
v___y_4138_ = v___y_4165_;
v_a_4139_ = v_a_4168_;
goto v___jp_4136_;
}
}
v___jp_4169_:
{
if (v___y_4174_ == 0)
{
lean_object* v___x_4175_; 
lean_dec_ref(v___y_4172_);
v___x_4175_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4173_, v_a_3019_, v_a_3021_);
lean_dec_ref(v___y_4173_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_dec_ref(v___x_4175_);
v___y_4131_ = v___y_4170_;
v___y_4132_ = v___y_4171_;
v_a_4133_ = v_snd_3030_;
goto v___jp_4130_;
}
else
{
lean_object* v_a_4176_; 
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
lean_dec(v_snd_3030_);
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
lean_dec_ref(v___x_4175_);
v___y_4137_ = v___y_4170_;
v___y_4138_ = v___y_4171_;
v_a_4139_ = v_a_4176_;
goto v___jp_4136_;
}
}
else
{
lean_dec_ref(v___y_4173_);
lean_dec(v_snd_3030_);
v___y_4164_ = v___y_4170_;
v___y_4165_ = v___y_4171_;
v___y_4166_ = v___y_4172_;
goto v___jp_4163_;
}
}
v___jp_4177_:
{
lean_object* v___x_4181_; 
v___x_4181_ = l_Lean_Meta_saveState___redArg(v_a_3019_, v_a_3021_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4183_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref(v___x_4181_);
lean_inc(v_snd_3030_);
lean_inc(v_trace_3013_);
v___x_4183_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_4180_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_dec(v_a_4182_);
lean_dec(v_snd_3030_);
v___y_4164_ = v___y_4178_;
v___y_4165_ = v___y_4179_;
v___y_4166_ = v___x_4183_;
goto v___jp_4163_;
}
else
{
lean_object* v_a_4184_; uint8_t v___x_4185_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
v___x_4185_ = l_Lean_Exception_isInterrupt(v_a_4184_);
if (v___x_4185_ == 0)
{
uint8_t v___x_4186_; 
v___x_4186_ = l_Lean_Exception_isRuntime(v_a_4184_);
v___y_4170_ = v___y_4178_;
v___y_4171_ = v___y_4179_;
v___y_4172_ = v___x_4183_;
v___y_4173_ = v_a_4182_;
v___y_4174_ = v___x_4186_;
goto v___jp_4169_;
}
else
{
lean_dec(v_a_4184_);
v___y_4170_ = v___y_4178_;
v___y_4171_ = v___y_4179_;
v___y_4172_ = v___x_4183_;
v___y_4173_ = v_a_4182_;
v___y_4174_ = v___x_4185_;
goto v___jp_4169_;
}
}
}
else
{
lean_object* v_a_4187_; 
lean_dec(v___y_4180_);
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_4187_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4187_);
lean_dec_ref(v___x_4181_);
v___y_4137_ = v___y_4178_;
v___y_4138_ = v___y_4179_;
v_a_4139_ = v_a_4187_;
goto v___jp_4136_;
}
}
v___jp_4188_:
{
uint8_t v_commitIndependentGoals_4193_; lean_object* v___x_4194_; 
v_commitIndependentGoals_4193_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*4);
lean_inc(v___x_3967_);
v___x_4194_ = l_List_appendTR___redArg(v_a_4192_, v___x_3967_);
if (v_commitIndependentGoals_4193_ == 0)
{
v___y_4158_ = v___y_4189_;
v___y_4159_ = v___y_4190_;
v___y_4160_ = v___x_4194_;
v___y_4161_ = v___y_4191_;
goto v___jp_4157_;
}
else
{
uint8_t v___x_4195_; 
v___x_4195_ = l_List_isEmpty___redArg(v___x_3967_);
if (v___x_4195_ == 0)
{
v___y_4178_ = v___y_4189_;
v___y_4179_ = v___y_4190_;
v___y_4180_ = v___x_4194_;
goto v___jp_4177_;
}
else
{
if (v___x_3956_ == 0)
{
v___y_4158_ = v___y_4189_;
v___y_4159_ = v___y_4190_;
v___y_4160_ = v___x_4194_;
v___y_4161_ = v___y_4191_;
goto v___jp_4157_;
}
else
{
v___y_4178_ = v___y_4189_;
v___y_4179_ = v___y_4190_;
v___y_4180_ = v___x_4194_;
goto v___jp_4177_;
}
}
}
}
v___jp_4196_:
{
lean_object* v___x_4197_; 
v___x_4197_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3021_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref(v___x_4197_);
v___x_4199_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4200_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3035_, v___x_4199_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4201_ = lean_io_mono_nanos_now();
v___x_4202_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3037_, v___x_3956_, v_goals_3016_, v___x_4026_, v_a_3019_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4204_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref(v___x_4202_);
v___x_4204_ = l_List_reverse___redArg(v_a_4203_);
v___y_4106_ = v_a_4198_;
v___y_4107_ = v___x_4201_;
v___y_4108_ = v___x_4200_;
v_a_4109_ = v___x_4204_;
goto v___jp_4105_;
}
else
{
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4205_; 
v_a_4205_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4205_);
lean_dec_ref(v___x_4202_);
v___y_4106_ = v_a_4198_;
v___y_4107_ = v___x_4201_;
v___y_4108_ = v___x_4200_;
v_a_4109_ = v_a_4205_;
goto v___jp_4105_;
}
else
{
lean_object* v_a_4206_; 
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_4206_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4206_);
lean_dec_ref(v___x_4202_);
v___y_4045_ = v_a_4198_;
v___y_4046_ = v___x_4201_;
v_a_4047_ = v_a_4206_;
goto v___jp_4044_;
}
}
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_del_object(v___x_3965_);
v___x_4207_ = lean_io_get_num_heartbeats();
v___x_4208_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3037_, v___x_3956_, v_goals_3016_, v___x_4026_, v_a_3019_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4210_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref(v___x_4208_);
v___x_4210_ = l_List_reverse___redArg(v_a_4209_);
v___y_4189_ = v_a_4198_;
v___y_4190_ = v___x_4207_;
v___y_4191_ = v___x_4200_;
v_a_4192_ = v___x_4210_;
goto v___jp_4188_;
}
else
{
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4211_; 
v_a_4211_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4211_);
lean_dec_ref(v___x_4208_);
v___y_4189_ = v_a_4198_;
v___y_4190_ = v___x_4207_;
v___y_4191_ = v___x_4200_;
v_a_4192_ = v_a_4211_;
goto v___jp_4188_;
}
else
{
lean_object* v_a_4212_; 
lean_dec(v___x_3967_);
lean_dec(v_fst_3962_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_4212_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4212_);
lean_dec_ref(v___x_4208_);
v___y_4137_ = v_a_4198_;
v___y_4138_ = v___x_4207_;
v_a_4139_ = v_a_4212_;
goto v___jp_4136_;
}
}
}
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec_ref(v___f_4025_);
lean_dec(v___x_3967_);
lean_del_object(v___x_3965_);
lean_dec(v_fst_3962_);
lean_dec(v_snd_3030_);
lean_dec(v_goals_3016_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
v_a_4213_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4197_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4197_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec(v_snd_3030_);
lean_dec(v_goals_3016_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
v_a_4227_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_3957_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_3957_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
else
{
goto v___jp_3910_;
}
}
else
{
goto v___jp_3910_;
}
v___jp_3123_:
{
lean_object* v___x_3127_; double v___x_3128_; double v___x_3129_; double v___x_3130_; double v___x_3131_; double v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3127_ = lean_io_mono_nanos_now();
v___x_3128_ = lean_float_of_nat(v___y_3125_);
v___x_3129_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3130_ = lean_float_div(v___x_3128_, v___x_3129_);
v___x_3131_ = lean_float_of_nat(v___x_3127_);
v___x_3132_ = lean_float_div(v___x_3131_, v___x_3129_);
v___x_3133_ = lean_box_float(v___x_3130_);
v___x_3134_ = lean_box_float(v___x_3132_);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 1, v___x_3134_);
lean_ctor_set(v___x_3032_, 0, v___x_3133_);
v___x_3136_ = v___x_3032_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3137_, 0, v_a_3126_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
v___x_3138_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3013_, v_hasTrace_3037_, v___x_3119_, v_options_3035_, v___x_3122_, v___y_3124_, v___f_3118_, v___x_3137_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
return v___x_3138_;
}
}
v___jp_3140_:
{
lean_object* v___x_3144_; 
v___x_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3144_, 0, v_a_3143_);
v___y_3124_ = v___y_3141_;
v___y_3125_ = v___y_3142_;
v_a_3126_ = v___x_3144_;
goto v___jp_3123_;
}
v___jp_3145_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = l_List_appendTR___redArg(v___y_3148_, v___y_3149_);
v___x_3152_ = l_List_appendTR___redArg(v___x_3151_, v_a_3150_);
v___y_3141_ = v___y_3146_;
v___y_3142_ = v___y_3147_;
v_a_3143_ = v___x_3152_;
goto v___jp_3140_;
}
v___jp_3153_:
{
lean_object* v___x_3157_; 
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v_a_3156_);
v___y_3124_ = v___y_3154_;
v___y_3125_ = v___y_3155_;
v_a_3126_ = v___x_3157_;
goto v___jp_3123_;
}
v___jp_3158_:
{
if (lean_obj_tag(v___y_3163_) == 0)
{
lean_object* v_a_3164_; 
v_a_3164_ = lean_ctor_get(v___y_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref(v___y_3163_);
v___y_3146_ = v___y_3159_;
v___y_3147_ = v___y_3160_;
v___y_3148_ = v___y_3161_;
v___y_3149_ = v___y_3162_;
v_a_3150_ = v_a_3164_;
goto v___jp_3145_;
}
else
{
lean_object* v_a_3165_; 
lean_dec(v___y_3162_);
lean_dec(v___y_3161_);
v_a_3165_ = lean_ctor_get(v___y_3163_, 0);
lean_inc(v_a_3165_);
lean_dec_ref(v___y_3163_);
v___y_3154_ = v___y_3159_;
v___y_3155_ = v___y_3160_;
v_a_3156_ = v_a_3165_;
goto v___jp_3153_;
}
}
v___jp_3166_:
{
if (v___y_3173_ == 0)
{
lean_object* v___x_3174_; 
lean_dec_ref(v___y_3171_);
v___x_3174_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3169_, v_a_3019_, v_a_3021_);
lean_dec_ref(v___y_3169_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_dec_ref(v___x_3174_);
v___y_3146_ = v___y_3167_;
v___y_3147_ = v___y_3168_;
v___y_3148_ = v___y_3170_;
v___y_3149_ = v___y_3172_;
v_a_3150_ = v_snd_3030_;
goto v___jp_3145_;
}
else
{
lean_object* v_a_3175_; 
lean_dec(v___y_3172_);
lean_dec(v___y_3170_);
lean_dec(v_snd_3030_);
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref(v___x_3174_);
v___y_3154_ = v___y_3167_;
v___y_3155_ = v___y_3168_;
v_a_3156_ = v_a_3175_;
goto v___jp_3153_;
}
}
else
{
lean_dec_ref(v___y_3169_);
lean_dec(v_snd_3030_);
v___y_3159_ = v___y_3167_;
v___y_3160_ = v___y_3168_;
v___y_3161_ = v___y_3170_;
v___y_3162_ = v___y_3172_;
v___y_3163_ = v___y_3171_;
goto v___jp_3158_;
}
}
v___jp_3176_:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Lean_Meta_saveState___redArg(v_a_3019_, v_a_3021_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3184_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref(v___x_3182_);
lean_inc(v_snd_3030_);
lean_inc(v_trace_3013_);
v___x_3184_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3179_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_dec(v_a_3183_);
lean_dec(v_snd_3030_);
v___y_3159_ = v___y_3177_;
v___y_3160_ = v___y_3178_;
v___y_3161_ = v___y_3180_;
v___y_3162_ = v___y_3181_;
v___y_3163_ = v___x_3184_;
goto v___jp_3158_;
}
else
{
lean_object* v_a_3185_; uint8_t v___x_3186_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
v___x_3186_ = l_Lean_Exception_isInterrupt(v_a_3185_);
if (v___x_3186_ == 0)
{
uint8_t v___x_3187_; 
v___x_3187_ = l_Lean_Exception_isRuntime(v_a_3185_);
v___y_3167_ = v___y_3177_;
v___y_3168_ = v___y_3178_;
v___y_3169_ = v_a_3183_;
v___y_3170_ = v___y_3180_;
v___y_3171_ = v___x_3184_;
v___y_3172_ = v___y_3181_;
v___y_3173_ = v___x_3187_;
goto v___jp_3166_;
}
else
{
lean_dec(v_a_3185_);
v___y_3167_ = v___y_3177_;
v___y_3168_ = v___y_3178_;
v___y_3169_ = v_a_3183_;
v___y_3170_ = v___y_3180_;
v___y_3171_ = v___x_3184_;
v___y_3172_ = v___y_3181_;
v___y_3173_ = v___x_3186_;
goto v___jp_3166_;
}
}
}
else
{
lean_object* v_a_3188_; 
lean_dec(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3188_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3188_);
lean_dec_ref(v___x_3182_);
v___y_3154_ = v___y_3177_;
v___y_3155_ = v___y_3178_;
v_a_3156_ = v_a_3188_;
goto v___jp_3153_;
}
}
v___jp_3189_:
{
if (lean_obj_tag(v___y_3192_) == 0)
{
lean_object* v_a_3193_; 
v_a_3193_ = lean_ctor_get(v___y_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref(v___y_3192_);
v___y_3141_ = v___y_3190_;
v___y_3142_ = v___y_3191_;
v_a_3143_ = v_a_3193_;
goto v___jp_3140_;
}
else
{
lean_object* v_a_3194_; 
v_a_3194_ = lean_ctor_get(v___y_3192_, 0);
lean_inc(v_a_3194_);
lean_dec_ref(v___y_3192_);
v___y_3154_ = v___y_3190_;
v___y_3155_ = v___y_3191_;
v_a_3156_ = v_a_3194_;
goto v___jp_3153_;
}
}
v___jp_3195_:
{
lean_object* v___x_3203_; double v___x_3204_; double v___x_3205_; double v___x_3206_; double v___x_3207_; double v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3203_ = lean_io_mono_nanos_now();
v___x_3204_ = lean_float_of_nat(v___y_3200_);
v___x_3205_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3206_ = lean_float_div(v___x_3204_, v___x_3205_);
v___x_3207_ = lean_float_of_nat(v___x_3203_);
v___x_3208_ = lean_float_div(v___x_3207_, v___x_3205_);
v___x_3209_ = lean_box_float(v___x_3206_);
v___x_3210_ = lean_box_float(v___x_3208_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3209_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v_a_3202_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
lean_inc(v_trace_3013_);
v___x_3213_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3013_, v_hasTrace_3037_, v___x_3119_, v_options_3035_, v___y_3198_, v___y_3197_, v___y_3201_, v___x_3212_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3190_ = v___y_3196_;
v___y_3191_ = v___y_3199_;
v___y_3192_ = v___x_3213_;
goto v___jp_3189_;
}
v___jp_3214_:
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v_a_3221_);
v___y_3196_ = v___y_3217_;
v___y_3197_ = v___y_3216_;
v___y_3198_ = v___y_3215_;
v___y_3199_ = v___y_3218_;
v___y_3200_ = v___y_3219_;
v___y_3201_ = v___y_3220_;
v_a_3202_ = v___x_3222_;
goto v___jp_3195_;
}
v___jp_3223_:
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_a_3230_);
v___y_3196_ = v___y_3226_;
v___y_3197_ = v___y_3225_;
v___y_3198_ = v___y_3224_;
v___y_3199_ = v___y_3227_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3229_;
v_a_3202_ = v___x_3231_;
goto v___jp_3195_;
}
v___jp_3232_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = l_List_appendTR___redArg(v___y_3238_, v___y_3239_);
v___x_3243_ = l_List_appendTR___redArg(v___x_3242_, v_a_3241_);
v___y_3224_ = v___y_3235_;
v___y_3225_ = v___y_3234_;
v___y_3226_ = v___y_3233_;
v___y_3227_ = v___y_3236_;
v___y_3228_ = v___y_3237_;
v___y_3229_ = v___y_3240_;
v_a_3230_ = v___x_3243_;
goto v___jp_3223_;
}
v___jp_3244_:
{
if (lean_obj_tag(v___y_3253_) == 0)
{
lean_object* v_a_3254_; 
v_a_3254_ = lean_ctor_get(v___y_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref(v___y_3253_);
v___y_3233_ = v___y_3247_;
v___y_3234_ = v___y_3246_;
v___y_3235_ = v___y_3245_;
v___y_3236_ = v___y_3248_;
v___y_3237_ = v___y_3249_;
v___y_3238_ = v___y_3250_;
v___y_3239_ = v___y_3251_;
v___y_3240_ = v___y_3252_;
v_a_3241_ = v_a_3254_;
goto v___jp_3232_;
}
else
{
lean_object* v_a_3255_; 
lean_dec(v___y_3251_);
lean_dec(v___y_3250_);
v_a_3255_ = lean_ctor_get(v___y_3253_, 0);
lean_inc(v_a_3255_);
lean_dec_ref(v___y_3253_);
v___y_3215_ = v___y_3245_;
v___y_3216_ = v___y_3246_;
v___y_3217_ = v___y_3247_;
v___y_3218_ = v___y_3248_;
v___y_3219_ = v___y_3249_;
v___y_3220_ = v___y_3252_;
v_a_3221_ = v_a_3255_;
goto v___jp_3214_;
}
}
v___jp_3256_:
{
if (v___y_3267_ == 0)
{
lean_object* v___x_3268_; 
lean_dec_ref(v___y_3257_);
v___x_3268_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3262_, v_a_3019_, v_a_3021_);
lean_dec_ref(v___y_3262_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_dec_ref(v___x_3268_);
v___y_3233_ = v___y_3260_;
v___y_3234_ = v___y_3259_;
v___y_3235_ = v___y_3258_;
v___y_3236_ = v___y_3261_;
v___y_3237_ = v___y_3263_;
v___y_3238_ = v___y_3264_;
v___y_3239_ = v___y_3265_;
v___y_3240_ = v___y_3266_;
v_a_3241_ = v_snd_3030_;
goto v___jp_3232_;
}
else
{
lean_object* v_a_3269_; 
lean_dec(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec(v_snd_3030_);
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref(v___x_3268_);
v___y_3215_ = v___y_3258_;
v___y_3216_ = v___y_3259_;
v___y_3217_ = v___y_3260_;
v___y_3218_ = v___y_3261_;
v___y_3219_ = v___y_3263_;
v___y_3220_ = v___y_3266_;
v_a_3221_ = v_a_3269_;
goto v___jp_3214_;
}
}
else
{
lean_dec_ref(v___y_3262_);
lean_dec(v_snd_3030_);
v___y_3245_ = v___y_3258_;
v___y_3246_ = v___y_3259_;
v___y_3247_ = v___y_3260_;
v___y_3248_ = v___y_3261_;
v___y_3249_ = v___y_3263_;
v___y_3250_ = v___y_3264_;
v___y_3251_ = v___y_3265_;
v___y_3252_ = v___y_3266_;
v___y_3253_ = v___y_3257_;
goto v___jp_3244_;
}
}
v___jp_3270_:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Lean_Meta_saveState___redArg(v_a_3019_, v_a_3021_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3282_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref(v___x_3280_);
lean_inc(v_snd_3030_);
lean_inc(v_trace_3013_);
v___x_3282_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3274_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_dec(v_a_3281_);
lean_dec(v_snd_3030_);
v___y_3245_ = v___y_3273_;
v___y_3246_ = v___y_3272_;
v___y_3247_ = v___y_3271_;
v___y_3248_ = v___y_3275_;
v___y_3249_ = v___y_3276_;
v___y_3250_ = v___y_3277_;
v___y_3251_ = v___y_3278_;
v___y_3252_ = v___y_3279_;
v___y_3253_ = v___x_3282_;
goto v___jp_3244_;
}
else
{
lean_object* v_a_3283_; uint8_t v___x_3284_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
v___x_3284_ = l_Lean_Exception_isInterrupt(v_a_3283_);
if (v___x_3284_ == 0)
{
uint8_t v___x_3285_; 
v___x_3285_ = l_Lean_Exception_isRuntime(v_a_3283_);
v___y_3257_ = v___x_3282_;
v___y_3258_ = v___y_3273_;
v___y_3259_ = v___y_3272_;
v___y_3260_ = v___y_3271_;
v___y_3261_ = v___y_3275_;
v___y_3262_ = v_a_3281_;
v___y_3263_ = v___y_3276_;
v___y_3264_ = v___y_3277_;
v___y_3265_ = v___y_3278_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___x_3285_;
goto v___jp_3256_;
}
else
{
lean_dec(v_a_3283_);
v___y_3257_ = v___x_3282_;
v___y_3258_ = v___y_3273_;
v___y_3259_ = v___y_3272_;
v___y_3260_ = v___y_3271_;
v___y_3261_ = v___y_3275_;
v___y_3262_ = v_a_3281_;
v___y_3263_ = v___y_3276_;
v___y_3264_ = v___y_3277_;
v___y_3265_ = v___y_3278_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___x_3284_;
goto v___jp_3256_;
}
}
}
else
{
lean_object* v_a_3286_; 
lean_dec(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec(v___y_3274_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3286_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3286_);
lean_dec_ref(v___x_3280_);
v___y_3215_ = v___y_3273_;
v___y_3216_ = v___y_3272_;
v___y_3217_ = v___y_3271_;
v___y_3218_ = v___y_3275_;
v___y_3219_ = v___y_3276_;
v___y_3220_ = v___y_3279_;
v_a_3221_ = v_a_3286_;
goto v___jp_3214_;
}
}
v___jp_3287_:
{
if (lean_obj_tag(v___y_3294_) == 0)
{
lean_object* v_a_3295_; 
v_a_3295_ = lean_ctor_get(v___y_3294_, 0);
lean_inc(v_a_3295_);
lean_dec_ref(v___y_3294_);
v___y_3224_ = v___y_3290_;
v___y_3225_ = v___y_3289_;
v___y_3226_ = v___y_3288_;
v___y_3227_ = v___y_3291_;
v___y_3228_ = v___y_3292_;
v___y_3229_ = v___y_3293_;
v_a_3230_ = v_a_3295_;
goto v___jp_3223_;
}
else
{
lean_object* v_a_3296_; 
v_a_3296_ = lean_ctor_get(v___y_3294_, 0);
lean_inc(v_a_3296_);
lean_dec_ref(v___y_3294_);
v___y_3215_ = v___y_3290_;
v___y_3216_ = v___y_3289_;
v___y_3217_ = v___y_3288_;
v___y_3218_ = v___y_3291_;
v___y_3219_ = v___y_3292_;
v___y_3220_ = v___y_3293_;
v_a_3221_ = v_a_3296_;
goto v___jp_3214_;
}
}
v___jp_3297_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3305_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3304_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3288_ = v___y_3300_;
v___y_3289_ = v___y_3299_;
v___y_3290_ = v___y_3298_;
v___y_3291_ = v___y_3301_;
v___y_3292_ = v___y_3302_;
v___y_3293_ = v___y_3303_;
v___y_3294_ = v___x_3305_;
goto v___jp_3287_;
}
v___jp_3306_:
{
uint8_t v___x_3317_; 
v___x_3317_ = l_List_isEmpty___redArg(v___y_3315_);
lean_dec(v___y_3315_);
if (v___x_3317_ == 0)
{
lean_dec(v___y_3314_);
lean_dec(v___y_3311_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___y_3298_ = v___y_3310_;
v___y_3299_ = v___y_3309_;
v___y_3300_ = v___y_3308_;
v___y_3301_ = v___y_3312_;
v___y_3302_ = v___y_3313_;
v___y_3303_ = v___y_3316_;
goto v___jp_3297_;
}
else
{
if (v___y_3307_ == 0)
{
lean_object* v___x_3318_; 
lean_inc(v_trace_3013_);
v___x_3318_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3311_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3320_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref(v___x_3318_);
v___x_3320_ = l_List_appendTR___redArg(v___y_3314_, v_a_3319_);
v___y_3224_ = v___y_3310_;
v___y_3225_ = v___y_3309_;
v___y_3226_ = v___y_3308_;
v___y_3227_ = v___y_3312_;
v___y_3228_ = v___y_3313_;
v___y_3229_ = v___y_3316_;
v_a_3230_ = v___x_3320_;
goto v___jp_3223_;
}
else
{
lean_dec(v___y_3314_);
v___y_3288_ = v___y_3308_;
v___y_3289_ = v___y_3309_;
v___y_3290_ = v___y_3310_;
v___y_3291_ = v___y_3312_;
v___y_3292_ = v___y_3313_;
v___y_3293_ = v___y_3316_;
v___y_3294_ = v___x_3318_;
goto v___jp_3287_;
}
}
else
{
lean_dec(v___y_3314_);
lean_dec(v___y_3311_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___y_3298_ = v___y_3310_;
v___y_3299_ = v___y_3309_;
v___y_3300_ = v___y_3308_;
v___y_3301_ = v___y_3312_;
v___y_3302_ = v___y_3313_;
v___y_3303_ = v___y_3316_;
goto v___jp_3297_;
}
}
}
v___jp_3321_:
{
uint8_t v_commitIndependentGoals_3332_; lean_object* v___x_3333_; 
v_commitIndependentGoals_3332_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*4);
lean_inc(v___y_3328_);
v___x_3333_ = l_List_appendTR___redArg(v_a_3331_, v___y_3328_);
if (v_commitIndependentGoals_3332_ == 0)
{
v___y_3307_ = v___y_3322_;
v___y_3308_ = v___y_3323_;
v___y_3309_ = v___y_3324_;
v___y_3310_ = v___y_3325_;
v___y_3311_ = v___x_3333_;
v___y_3312_ = v___y_3326_;
v___y_3313_ = v___y_3327_;
v___y_3314_ = v___y_3328_;
v___y_3315_ = v___y_3329_;
v___y_3316_ = v___y_3330_;
goto v___jp_3306_;
}
else
{
uint8_t v___x_3334_; 
v___x_3334_ = l_List_isEmpty___redArg(v___y_3328_);
if (v___x_3334_ == 0)
{
v___y_3271_ = v___y_3323_;
v___y_3272_ = v___y_3324_;
v___y_3273_ = v___y_3325_;
v___y_3274_ = v___x_3333_;
v___y_3275_ = v___y_3326_;
v___y_3276_ = v___y_3327_;
v___y_3277_ = v___y_3328_;
v___y_3278_ = v___y_3329_;
v___y_3279_ = v___y_3330_;
goto v___jp_3270_;
}
else
{
if (v___y_3322_ == 0)
{
v___y_3307_ = v___y_3322_;
v___y_3308_ = v___y_3323_;
v___y_3309_ = v___y_3324_;
v___y_3310_ = v___y_3325_;
v___y_3311_ = v___x_3333_;
v___y_3312_ = v___y_3326_;
v___y_3313_ = v___y_3327_;
v___y_3314_ = v___y_3328_;
v___y_3315_ = v___y_3329_;
v___y_3316_ = v___y_3330_;
goto v___jp_3306_;
}
else
{
v___y_3271_ = v___y_3323_;
v___y_3272_ = v___y_3324_;
v___y_3273_ = v___y_3325_;
v___y_3274_ = v___x_3333_;
v___y_3275_ = v___y_3326_;
v___y_3276_ = v___y_3327_;
v___y_3277_ = v___y_3328_;
v___y_3278_ = v___y_3329_;
v___y_3279_ = v___y_3330_;
goto v___jp_3270_;
}
}
}
}
v___jp_3335_:
{
lean_object* v___x_3343_; double v___x_3344_; double v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3343_ = lean_io_get_num_heartbeats();
v___x_3344_ = lean_float_of_nat(v___y_3341_);
v___x_3345_ = lean_float_of_nat(v___x_3343_);
v___x_3346_ = lean_box_float(v___x_3344_);
v___x_3347_ = lean_box_float(v___x_3345_);
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3349_, 0, v_a_3342_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
lean_inc(v_trace_3013_);
v___x_3350_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3013_, v_hasTrace_3037_, v___x_3119_, v_options_3035_, v___y_3338_, v___y_3337_, v___y_3340_, v___x_3349_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3190_ = v___y_3336_;
v___y_3191_ = v___y_3339_;
v___y_3192_ = v___x_3350_;
goto v___jp_3189_;
}
v___jp_3351_:
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3359_, 0, v_a_3358_);
v___y_3336_ = v___y_3354_;
v___y_3337_ = v___y_3353_;
v___y_3338_ = v___y_3352_;
v___y_3339_ = v___y_3355_;
v___y_3340_ = v___y_3356_;
v___y_3341_ = v___y_3357_;
v_a_3342_ = v___x_3359_;
goto v___jp_3335_;
}
v___jp_3360_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = l_List_appendTR___redArg(v___y_3365_, v___y_3366_);
v___x_3371_ = l_List_appendTR___redArg(v___x_3370_, v_a_3369_);
v___y_3352_ = v___y_3363_;
v___y_3353_ = v___y_3362_;
v___y_3354_ = v___y_3361_;
v___y_3355_ = v___y_3364_;
v___y_3356_ = v___y_3367_;
v___y_3357_ = v___y_3368_;
v_a_3358_ = v___x_3371_;
goto v___jp_3351_;
}
v___jp_3372_:
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3380_, 0, v_a_3379_);
v___y_3336_ = v___y_3375_;
v___y_3337_ = v___y_3374_;
v___y_3338_ = v___y_3373_;
v___y_3339_ = v___y_3376_;
v___y_3340_ = v___y_3377_;
v___y_3341_ = v___y_3378_;
v_a_3342_ = v___x_3380_;
goto v___jp_3335_;
}
v___jp_3381_:
{
if (lean_obj_tag(v___y_3388_) == 0)
{
lean_object* v_a_3389_; 
v_a_3389_ = lean_ctor_get(v___y_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref(v___y_3388_);
v___y_3352_ = v___y_3384_;
v___y_3353_ = v___y_3383_;
v___y_3354_ = v___y_3382_;
v___y_3355_ = v___y_3385_;
v___y_3356_ = v___y_3386_;
v___y_3357_ = v___y_3387_;
v_a_3358_ = v_a_3389_;
goto v___jp_3351_;
}
else
{
lean_object* v_a_3390_; 
v_a_3390_ = lean_ctor_get(v___y_3388_, 0);
lean_inc(v_a_3390_);
lean_dec_ref(v___y_3388_);
v___y_3373_ = v___y_3384_;
v___y_3374_ = v___y_3383_;
v___y_3375_ = v___y_3382_;
v___y_3376_ = v___y_3385_;
v___y_3377_ = v___y_3386_;
v___y_3378_ = v___y_3387_;
v_a_3379_ = v_a_3390_;
goto v___jp_3372_;
}
}
v___jp_3391_:
{
lean_object* v___x_3400_; 
lean_inc(v_trace_3013_);
v___x_3400_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3398_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3402_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref(v___x_3400_);
v___x_3402_ = l_List_appendTR___redArg(v___y_3396_, v_a_3401_);
v___y_3352_ = v___y_3394_;
v___y_3353_ = v___y_3393_;
v___y_3354_ = v___y_3392_;
v___y_3355_ = v___y_3395_;
v___y_3356_ = v___y_3397_;
v___y_3357_ = v___y_3399_;
v_a_3358_ = v___x_3402_;
goto v___jp_3351_;
}
else
{
lean_dec(v___y_3396_);
v___y_3382_ = v___y_3392_;
v___y_3383_ = v___y_3393_;
v___y_3384_ = v___y_3394_;
v___y_3385_ = v___y_3395_;
v___y_3386_ = v___y_3397_;
v___y_3387_ = v___y_3399_;
v___y_3388_ = v___x_3400_;
goto v___jp_3381_;
}
}
v___jp_3403_:
{
if (lean_obj_tag(v___y_3412_) == 0)
{
lean_object* v_a_3413_; 
v_a_3413_ = lean_ctor_get(v___y_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref(v___y_3412_);
v___y_3361_ = v___y_3406_;
v___y_3362_ = v___y_3405_;
v___y_3363_ = v___y_3404_;
v___y_3364_ = v___y_3407_;
v___y_3365_ = v___y_3408_;
v___y_3366_ = v___y_3409_;
v___y_3367_ = v___y_3410_;
v___y_3368_ = v___y_3411_;
v_a_3369_ = v_a_3413_;
goto v___jp_3360_;
}
else
{
lean_object* v_a_3414_; 
lean_dec(v___y_3409_);
lean_dec(v___y_3408_);
v_a_3414_ = lean_ctor_get(v___y_3412_, 0);
lean_inc(v_a_3414_);
lean_dec_ref(v___y_3412_);
v___y_3373_ = v___y_3404_;
v___y_3374_ = v___y_3405_;
v___y_3375_ = v___y_3406_;
v___y_3376_ = v___y_3407_;
v___y_3377_ = v___y_3410_;
v___y_3378_ = v___y_3411_;
v_a_3379_ = v_a_3414_;
goto v___jp_3372_;
}
}
v___jp_3415_:
{
if (v___y_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_dec_ref(v___y_3420_);
v___x_3427_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3424_, v_a_3019_, v_a_3021_);
lean_dec_ref(v___y_3424_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_dec_ref(v___x_3427_);
v___y_3361_ = v___y_3418_;
v___y_3362_ = v___y_3417_;
v___y_3363_ = v___y_3416_;
v___y_3364_ = v___y_3419_;
v___y_3365_ = v___y_3421_;
v___y_3366_ = v___y_3422_;
v___y_3367_ = v___y_3423_;
v___y_3368_ = v___y_3425_;
v_a_3369_ = v_snd_3030_;
goto v___jp_3360_;
}
else
{
lean_object* v_a_3428_; 
lean_dec(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec(v_snd_3030_);
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref(v___x_3427_);
v___y_3373_ = v___y_3416_;
v___y_3374_ = v___y_3417_;
v___y_3375_ = v___y_3418_;
v___y_3376_ = v___y_3419_;
v___y_3377_ = v___y_3423_;
v___y_3378_ = v___y_3425_;
v_a_3379_ = v_a_3428_;
goto v___jp_3372_;
}
}
else
{
lean_dec_ref(v___y_3424_);
lean_dec(v_snd_3030_);
v___y_3404_ = v___y_3416_;
v___y_3405_ = v___y_3417_;
v___y_3406_ = v___y_3418_;
v___y_3407_ = v___y_3419_;
v___y_3408_ = v___y_3421_;
v___y_3409_ = v___y_3422_;
v___y_3410_ = v___y_3423_;
v___y_3411_ = v___y_3425_;
v___y_3412_ = v___y_3420_;
goto v___jp_3403_;
}
}
v___jp_3429_:
{
lean_object* v___x_3439_; 
v___x_3439_ = l_Lean_Meta_saveState___redArg(v_a_3019_, v_a_3021_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3441_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref(v___x_3439_);
lean_inc(v_snd_3030_);
lean_inc(v_trace_3013_);
v___x_3441_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3437_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_dec(v_a_3440_);
lean_dec(v_snd_3030_);
v___y_3404_ = v___y_3432_;
v___y_3405_ = v___y_3431_;
v___y_3406_ = v___y_3430_;
v___y_3407_ = v___y_3433_;
v___y_3408_ = v___y_3434_;
v___y_3409_ = v___y_3435_;
v___y_3410_ = v___y_3436_;
v___y_3411_ = v___y_3438_;
v___y_3412_ = v___x_3441_;
goto v___jp_3403_;
}
else
{
lean_object* v_a_3442_; uint8_t v___x_3443_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
v___x_3443_ = l_Lean_Exception_isInterrupt(v_a_3442_);
if (v___x_3443_ == 0)
{
uint8_t v___x_3444_; 
v___x_3444_ = l_Lean_Exception_isRuntime(v_a_3442_);
v___y_3416_ = v___y_3432_;
v___y_3417_ = v___y_3431_;
v___y_3418_ = v___y_3430_;
v___y_3419_ = v___y_3433_;
v___y_3420_ = v___x_3441_;
v___y_3421_ = v___y_3434_;
v___y_3422_ = v___y_3435_;
v___y_3423_ = v___y_3436_;
v___y_3424_ = v_a_3440_;
v___y_3425_ = v___y_3438_;
v___y_3426_ = v___x_3444_;
goto v___jp_3415_;
}
else
{
lean_dec(v_a_3442_);
v___y_3416_ = v___y_3432_;
v___y_3417_ = v___y_3431_;
v___y_3418_ = v___y_3430_;
v___y_3419_ = v___y_3433_;
v___y_3420_ = v___x_3441_;
v___y_3421_ = v___y_3434_;
v___y_3422_ = v___y_3435_;
v___y_3423_ = v___y_3436_;
v___y_3424_ = v_a_3440_;
v___y_3425_ = v___y_3438_;
v___y_3426_ = v___x_3443_;
goto v___jp_3415_;
}
}
}
else
{
lean_object* v_a_3445_; 
lean_dec(v___y_3437_);
lean_dec(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3445_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3445_);
lean_dec_ref(v___x_3439_);
v___y_3373_ = v___y_3432_;
v___y_3374_ = v___y_3431_;
v___y_3375_ = v___y_3430_;
v___y_3376_ = v___y_3433_;
v___y_3377_ = v___y_3436_;
v___y_3378_ = v___y_3438_;
v_a_3379_ = v_a_3445_;
goto v___jp_3372_;
}
}
v___jp_3446_:
{
uint8_t v_commitIndependentGoals_3457_; lean_object* v___x_3458_; 
v_commitIndependentGoals_3457_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*4);
lean_inc(v___y_3452_);
v___x_3458_ = l_List_appendTR___redArg(v_a_3456_, v___y_3452_);
if (v_commitIndependentGoals_3457_ == 0)
{
lean_dec(v___y_3453_);
if (v___y_3447_ == 0)
{
v___y_3392_ = v___y_3450_;
v___y_3393_ = v___y_3449_;
v___y_3394_ = v___y_3448_;
v___y_3395_ = v___y_3451_;
v___y_3396_ = v___y_3452_;
v___y_3397_ = v___y_3454_;
v___y_3398_ = v___x_3458_;
v___y_3399_ = v___y_3455_;
goto v___jp_3391_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
lean_dec(v___x_3458_);
lean_dec(v___y_3452_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___x_3459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3460_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3459_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3382_ = v___y_3450_;
v___y_3383_ = v___y_3449_;
v___y_3384_ = v___y_3448_;
v___y_3385_ = v___y_3451_;
v___y_3386_ = v___y_3454_;
v___y_3387_ = v___y_3455_;
v___y_3388_ = v___x_3460_;
goto v___jp_3381_;
}
}
else
{
uint8_t v___x_3461_; 
v___x_3461_ = l_List_isEmpty___redArg(v___y_3452_);
if (v___x_3461_ == 0)
{
v___y_3430_ = v___y_3450_;
v___y_3431_ = v___y_3449_;
v___y_3432_ = v___y_3448_;
v___y_3433_ = v___y_3451_;
v___y_3434_ = v___y_3452_;
v___y_3435_ = v___y_3453_;
v___y_3436_ = v___y_3454_;
v___y_3437_ = v___x_3458_;
v___y_3438_ = v___y_3455_;
goto v___jp_3429_;
}
else
{
if (v___y_3447_ == 0)
{
lean_dec(v___y_3453_);
v___y_3392_ = v___y_3450_;
v___y_3393_ = v___y_3449_;
v___y_3394_ = v___y_3448_;
v___y_3395_ = v___y_3451_;
v___y_3396_ = v___y_3452_;
v___y_3397_ = v___y_3454_;
v___y_3398_ = v___x_3458_;
v___y_3399_ = v___y_3455_;
goto v___jp_3391_;
}
else
{
v___y_3430_ = v___y_3450_;
v___y_3431_ = v___y_3449_;
v___y_3432_ = v___y_3448_;
v___y_3433_ = v___y_3451_;
v___y_3434_ = v___y_3452_;
v___y_3435_ = v___y_3453_;
v___y_3436_ = v___y_3454_;
v___y_3437_ = v___x_3458_;
v___y_3438_ = v___y_3455_;
goto v___jp_3429_;
}
}
}
}
v___jp_3462_:
{
lean_object* v___x_3471_; 
v___x_3471_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3021_);
if (lean_obj_tag(v___x_3471_) == 0)
{
if (v___y_3463_ == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref(v___x_3471_);
v___x_3473_ = lean_io_mono_nanos_now();
v___x_3474_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3037_, v___y_3463_, v_goals_3016_, v___y_3470_, v_a_3019_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3476_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref(v___x_3474_);
v___x_3476_ = l_List_reverse___redArg(v_a_3475_);
v___y_3322_ = v___y_3463_;
v___y_3323_ = v___y_3465_;
v___y_3324_ = v_a_3472_;
v___y_3325_ = v___y_3464_;
v___y_3326_ = v___y_3466_;
v___y_3327_ = v___x_3473_;
v___y_3328_ = v___y_3467_;
v___y_3329_ = v___y_3468_;
v___y_3330_ = v___y_3469_;
v_a_3331_ = v___x_3476_;
goto v___jp_3321_;
}
else
{
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3477_; 
v_a_3477_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3477_);
lean_dec_ref(v___x_3474_);
v___y_3322_ = v___y_3463_;
v___y_3323_ = v___y_3465_;
v___y_3324_ = v_a_3472_;
v___y_3325_ = v___y_3464_;
v___y_3326_ = v___y_3466_;
v___y_3327_ = v___x_3473_;
v___y_3328_ = v___y_3467_;
v___y_3329_ = v___y_3468_;
v___y_3330_ = v___y_3469_;
v_a_3331_ = v_a_3477_;
goto v___jp_3321_;
}
else
{
lean_object* v_a_3478_; 
lean_dec(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3478_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3474_);
v___y_3215_ = v___y_3464_;
v___y_3216_ = v_a_3472_;
v___y_3217_ = v___y_3465_;
v___y_3218_ = v___y_3466_;
v___y_3219_ = v___x_3473_;
v___y_3220_ = v___y_3469_;
v_a_3221_ = v_a_3478_;
goto v___jp_3214_;
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v_a_3479_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3479_);
lean_dec_ref(v___x_3471_);
v___x_3480_ = lean_io_get_num_heartbeats();
v___x_3481_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3037_, v___y_3463_, v_goals_3016_, v___y_3470_, v_a_3019_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3483_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref(v___x_3481_);
v___x_3483_ = l_List_reverse___redArg(v_a_3482_);
v___y_3447_ = v___y_3463_;
v___y_3448_ = v___y_3464_;
v___y_3449_ = v_a_3479_;
v___y_3450_ = v___y_3465_;
v___y_3451_ = v___y_3466_;
v___y_3452_ = v___y_3467_;
v___y_3453_ = v___y_3468_;
v___y_3454_ = v___y_3469_;
v___y_3455_ = v___x_3480_;
v_a_3456_ = v___x_3483_;
goto v___jp_3446_;
}
else
{
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3484_; 
v_a_3484_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3484_);
lean_dec_ref(v___x_3481_);
v___y_3447_ = v___y_3463_;
v___y_3448_ = v___y_3464_;
v___y_3449_ = v_a_3479_;
v___y_3450_ = v___y_3465_;
v___y_3451_ = v___y_3466_;
v___y_3452_ = v___y_3467_;
v___y_3453_ = v___y_3468_;
v___y_3454_ = v___y_3469_;
v___y_3455_ = v___x_3480_;
v_a_3456_ = v_a_3484_;
goto v___jp_3446_;
}
else
{
lean_object* v_a_3485_; 
lean_dec(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3485_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3485_);
lean_dec_ref(v___x_3481_);
v___y_3373_ = v___y_3464_;
v___y_3374_ = v_a_3479_;
v___y_3375_ = v___y_3465_;
v___y_3376_ = v___y_3466_;
v___y_3377_ = v___y_3469_;
v___y_3378_ = v___x_3480_;
v_a_3379_ = v_a_3485_;
goto v___jp_3372_;
}
}
}
}
else
{
lean_object* v_a_3486_; 
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec(v_snd_3030_);
lean_dec(v_goals_3016_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3486_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3486_);
lean_dec_ref(v___x_3471_);
v___y_3154_ = v___y_3465_;
v___y_3155_ = v___y_3466_;
v_a_3156_ = v_a_3486_;
goto v___jp_3153_;
}
}
v___jp_3487_:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3491_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3490_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3190_ = v___y_3488_;
v___y_3191_ = v___y_3489_;
v___y_3192_ = v___x_3491_;
goto v___jp_3189_;
}
v___jp_3492_:
{
uint8_t v___x_3499_; 
v___x_3499_ = l_List_isEmpty___redArg(v___y_3498_);
lean_dec(v___y_3498_);
if (v___x_3499_ == 0)
{
lean_dec(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___y_3488_ = v___y_3493_;
v___y_3489_ = v___y_3495_;
goto v___jp_3487_;
}
else
{
if (v___y_3494_ == 0)
{
lean_object* v___x_3500_; 
lean_inc(v_trace_3013_);
v___x_3500_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3496_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3502_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref(v___x_3500_);
v___x_3502_ = l_List_appendTR___redArg(v___y_3497_, v_a_3501_);
v___y_3141_ = v___y_3493_;
v___y_3142_ = v___y_3495_;
v_a_3143_ = v___x_3502_;
goto v___jp_3140_;
}
else
{
lean_dec(v___y_3497_);
v___y_3190_ = v___y_3493_;
v___y_3191_ = v___y_3495_;
v___y_3192_ = v___x_3500_;
goto v___jp_3189_;
}
}
else
{
lean_dec(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___y_3488_ = v___y_3493_;
v___y_3489_ = v___y_3495_;
goto v___jp_3487_;
}
}
}
v___jp_3503_:
{
uint8_t v_commitIndependentGoals_3510_; lean_object* v___x_3511_; 
v_commitIndependentGoals_3510_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*4);
lean_inc(v___y_3507_);
v___x_3511_ = l_List_appendTR___redArg(v_a_3509_, v___y_3507_);
if (v_commitIndependentGoals_3510_ == 0)
{
v___y_3493_ = v___y_3504_;
v___y_3494_ = v___y_3505_;
v___y_3495_ = v___y_3506_;
v___y_3496_ = v___x_3511_;
v___y_3497_ = v___y_3507_;
v___y_3498_ = v___y_3508_;
goto v___jp_3492_;
}
else
{
uint8_t v___x_3512_; 
v___x_3512_ = l_List_isEmpty___redArg(v___y_3507_);
if (v___x_3512_ == 0)
{
v___y_3177_ = v___y_3504_;
v___y_3178_ = v___y_3506_;
v___y_3179_ = v___x_3511_;
v___y_3180_ = v___y_3507_;
v___y_3181_ = v___y_3508_;
goto v___jp_3176_;
}
else
{
if (v___y_3505_ == 0)
{
v___y_3493_ = v___y_3504_;
v___y_3494_ = v___y_3505_;
v___y_3495_ = v___y_3506_;
v___y_3496_ = v___x_3511_;
v___y_3497_ = v___y_3507_;
v___y_3498_ = v___y_3508_;
goto v___jp_3492_;
}
else
{
v___y_3177_ = v___y_3504_;
v___y_3178_ = v___y_3506_;
v___y_3179_ = v___x_3511_;
v___y_3180_ = v___y_3507_;
v___y_3181_ = v___y_3508_;
goto v___jp_3176_;
}
}
}
}
v___jp_3513_:
{
lean_object* v___x_3517_; double v___x_3518_; double v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3517_ = lean_io_get_num_heartbeats();
v___x_3518_ = lean_float_of_nat(v___y_3515_);
v___x_3519_ = lean_float_of_nat(v___x_3517_);
v___x_3520_ = lean_box_float(v___x_3518_);
v___x_3521_ = lean_box_float(v___x_3519_);
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3523_, 0, v_a_3516_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v___x_3524_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3013_, v_hasTrace_3037_, v___x_3119_, v_options_3035_, v___x_3122_, v___y_3514_, v___f_3118_, v___x_3523_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
return v___x_3524_;
}
v___jp_3525_:
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3529_, 0, v_a_3528_);
v___y_3514_ = v___y_3526_;
v___y_3515_ = v___y_3527_;
v_a_3516_ = v___x_3529_;
goto v___jp_3513_;
}
v___jp_3530_:
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v_a_3533_);
v___y_3514_ = v___y_3531_;
v___y_3515_ = v___y_3532_;
v_a_3516_ = v___x_3534_;
goto v___jp_3513_;
}
v___jp_3535_:
{
if (lean_obj_tag(v___y_3538_) == 0)
{
lean_object* v_a_3539_; 
v_a_3539_ = lean_ctor_get(v___y_3538_, 0);
lean_inc(v_a_3539_);
lean_dec_ref(v___y_3538_);
v___y_3531_ = v___y_3536_;
v___y_3532_ = v___y_3537_;
v_a_3533_ = v_a_3539_;
goto v___jp_3530_;
}
else
{
lean_object* v_a_3540_; 
v_a_3540_ = lean_ctor_get(v___y_3538_, 0);
lean_inc(v_a_3540_);
lean_dec_ref(v___y_3538_);
v___y_3526_ = v___y_3536_;
v___y_3527_ = v___y_3537_;
v_a_3528_ = v_a_3540_;
goto v___jp_3525_;
}
}
v___jp_3541_:
{
lean_object* v___x_3549_; double v___x_3550_; double v___x_3551_; double v___x_3552_; double v___x_3553_; double v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3549_ = lean_io_mono_nanos_now();
v___x_3550_ = lean_float_of_nat(v___y_3543_);
v___x_3551_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3552_ = lean_float_div(v___x_3550_, v___x_3551_);
v___x_3553_ = lean_float_of_nat(v___x_3549_);
v___x_3554_ = lean_float_div(v___x_3553_, v___x_3551_);
v___x_3555_ = lean_box_float(v___x_3552_);
v___x_3556_ = lean_box_float(v___x_3554_);
v___x_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3555_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3558_, 0, v_a_3548_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
lean_inc(v_trace_3013_);
v___x_3559_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3013_, v_hasTrace_3037_, v___x_3119_, v_options_3035_, v___y_3544_, v___y_3545_, v___y_3546_, v___x_3558_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3536_ = v___y_3542_;
v___y_3537_ = v___y_3547_;
v___y_3538_ = v___x_3559_;
goto v___jp_3535_;
}
v___jp_3560_:
{
lean_object* v___x_3568_; 
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v_a_3567_);
v___y_3542_ = v___y_3562_;
v___y_3543_ = v___y_3561_;
v___y_3544_ = v___y_3563_;
v___y_3545_ = v___y_3564_;
v___y_3546_ = v___y_3565_;
v___y_3547_ = v___y_3566_;
v_a_3548_ = v___x_3568_;
goto v___jp_3541_;
}
v___jp_3569_:
{
lean_object* v___x_3577_; 
v___x_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3577_, 0, v_a_3576_);
v___y_3542_ = v___y_3571_;
v___y_3543_ = v___y_3570_;
v___y_3544_ = v___y_3572_;
v___y_3545_ = v___y_3573_;
v___y_3546_ = v___y_3574_;
v___y_3547_ = v___y_3575_;
v_a_3548_ = v___x_3577_;
goto v___jp_3541_;
}
v___jp_3578_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = l_List_appendTR___redArg(v___y_3581_, v___y_3584_);
v___x_3589_ = l_List_appendTR___redArg(v___x_3588_, v_a_3587_);
v___y_3570_ = v___y_3580_;
v___y_3571_ = v___y_3579_;
v___y_3572_ = v___y_3582_;
v___y_3573_ = v___y_3583_;
v___y_3574_ = v___y_3585_;
v___y_3575_ = v___y_3586_;
v_a_3576_ = v___x_3589_;
goto v___jp_3569_;
}
v___jp_3590_:
{
if (lean_obj_tag(v___y_3599_) == 0)
{
lean_object* v_a_3600_; 
v_a_3600_ = lean_ctor_get(v___y_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref(v___y_3599_);
v___y_3579_ = v___y_3592_;
v___y_3580_ = v___y_3591_;
v___y_3581_ = v___y_3593_;
v___y_3582_ = v___y_3594_;
v___y_3583_ = v___y_3595_;
v___y_3584_ = v___y_3596_;
v___y_3585_ = v___y_3597_;
v___y_3586_ = v___y_3598_;
v_a_3587_ = v_a_3600_;
goto v___jp_3578_;
}
else
{
lean_object* v_a_3601_; 
lean_dec(v___y_3596_);
lean_dec(v___y_3593_);
v_a_3601_ = lean_ctor_get(v___y_3599_, 0);
lean_inc(v_a_3601_);
lean_dec_ref(v___y_3599_);
v___y_3561_ = v___y_3591_;
v___y_3562_ = v___y_3592_;
v___y_3563_ = v___y_3594_;
v___y_3564_ = v___y_3595_;
v___y_3565_ = v___y_3597_;
v___y_3566_ = v___y_3598_;
v_a_3567_ = v_a_3601_;
goto v___jp_3560_;
}
}
v___jp_3602_:
{
if (v___y_3613_ == 0)
{
lean_object* v___x_3614_; 
lean_dec_ref(v___y_3605_);
v___x_3614_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3612_, v_a_3019_, v_a_3021_);
lean_dec_ref(v___y_3612_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_dec_ref(v___x_3614_);
v___y_3579_ = v___y_3604_;
v___y_3580_ = v___y_3603_;
v___y_3581_ = v___y_3606_;
v___y_3582_ = v___y_3607_;
v___y_3583_ = v___y_3608_;
v___y_3584_ = v___y_3609_;
v___y_3585_ = v___y_3610_;
v___y_3586_ = v___y_3611_;
v_a_3587_ = v_snd_3030_;
goto v___jp_3578_;
}
else
{
lean_object* v_a_3615_; 
lean_dec(v___y_3609_);
lean_dec(v___y_3606_);
lean_dec(v_snd_3030_);
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref(v___x_3614_);
v___y_3561_ = v___y_3603_;
v___y_3562_ = v___y_3604_;
v___y_3563_ = v___y_3607_;
v___y_3564_ = v___y_3608_;
v___y_3565_ = v___y_3610_;
v___y_3566_ = v___y_3611_;
v_a_3567_ = v_a_3615_;
goto v___jp_3560_;
}
}
else
{
lean_dec_ref(v___y_3612_);
lean_dec(v_snd_3030_);
v___y_3591_ = v___y_3603_;
v___y_3592_ = v___y_3604_;
v___y_3593_ = v___y_3606_;
v___y_3594_ = v___y_3607_;
v___y_3595_ = v___y_3608_;
v___y_3596_ = v___y_3609_;
v___y_3597_ = v___y_3610_;
v___y_3598_ = v___y_3611_;
v___y_3599_ = v___y_3605_;
goto v___jp_3590_;
}
}
v___jp_3616_:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_Lean_Meta_saveState___redArg(v_a_3019_, v_a_3021_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3628_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
lean_dec_ref(v___x_3626_);
lean_inc(v_snd_3030_);
lean_inc(v_trace_3013_);
v___x_3628_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3619_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_dec(v_a_3627_);
lean_dec(v_snd_3030_);
v___y_3591_ = v___y_3618_;
v___y_3592_ = v___y_3617_;
v___y_3593_ = v___y_3620_;
v___y_3594_ = v___y_3621_;
v___y_3595_ = v___y_3622_;
v___y_3596_ = v___y_3623_;
v___y_3597_ = v___y_3624_;
v___y_3598_ = v___y_3625_;
v___y_3599_ = v___x_3628_;
goto v___jp_3590_;
}
else
{
lean_object* v_a_3629_; uint8_t v___x_3630_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
v___x_3630_ = l_Lean_Exception_isInterrupt(v_a_3629_);
if (v___x_3630_ == 0)
{
uint8_t v___x_3631_; 
v___x_3631_ = l_Lean_Exception_isRuntime(v_a_3629_);
v___y_3603_ = v___y_3618_;
v___y_3604_ = v___y_3617_;
v___y_3605_ = v___x_3628_;
v___y_3606_ = v___y_3620_;
v___y_3607_ = v___y_3621_;
v___y_3608_ = v___y_3622_;
v___y_3609_ = v___y_3623_;
v___y_3610_ = v___y_3624_;
v___y_3611_ = v___y_3625_;
v___y_3612_ = v_a_3627_;
v___y_3613_ = v___x_3631_;
goto v___jp_3602_;
}
else
{
lean_dec(v_a_3629_);
v___y_3603_ = v___y_3618_;
v___y_3604_ = v___y_3617_;
v___y_3605_ = v___x_3628_;
v___y_3606_ = v___y_3620_;
v___y_3607_ = v___y_3621_;
v___y_3608_ = v___y_3622_;
v___y_3609_ = v___y_3623_;
v___y_3610_ = v___y_3624_;
v___y_3611_ = v___y_3625_;
v___y_3612_ = v_a_3627_;
v___y_3613_ = v___x_3630_;
goto v___jp_3602_;
}
}
}
else
{
lean_object* v_a_3632_; 
lean_dec(v___y_3623_);
lean_dec(v___y_3620_);
lean_dec(v___y_3619_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3632_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3632_);
lean_dec_ref(v___x_3626_);
v___y_3561_ = v___y_3618_;
v___y_3562_ = v___y_3617_;
v___y_3563_ = v___y_3621_;
v___y_3564_ = v___y_3622_;
v___y_3565_ = v___y_3624_;
v___y_3566_ = v___y_3625_;
v_a_3567_ = v_a_3632_;
goto v___jp_3560_;
}
}
v___jp_3633_:
{
if (lean_obj_tag(v___y_3640_) == 0)
{
lean_object* v_a_3641_; 
v_a_3641_ = lean_ctor_get(v___y_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref(v___y_3640_);
v___y_3570_ = v___y_3635_;
v___y_3571_ = v___y_3634_;
v___y_3572_ = v___y_3636_;
v___y_3573_ = v___y_3637_;
v___y_3574_ = v___y_3638_;
v___y_3575_ = v___y_3639_;
v_a_3576_ = v_a_3641_;
goto v___jp_3569_;
}
else
{
lean_object* v_a_3642_; 
v_a_3642_ = lean_ctor_get(v___y_3640_, 0);
lean_inc(v_a_3642_);
lean_dec_ref(v___y_3640_);
v___y_3561_ = v___y_3635_;
v___y_3562_ = v___y_3634_;
v___y_3563_ = v___y_3636_;
v___y_3564_ = v___y_3637_;
v___y_3565_ = v___y_3638_;
v___y_3566_ = v___y_3639_;
v_a_3567_ = v_a_3642_;
goto v___jp_3560_;
}
}
v___jp_3643_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3651_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3650_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3634_ = v___y_3645_;
v___y_3635_ = v___y_3644_;
v___y_3636_ = v___y_3646_;
v___y_3637_ = v___y_3647_;
v___y_3638_ = v___y_3648_;
v___y_3639_ = v___y_3649_;
v___y_3640_ = v___x_3651_;
goto v___jp_3633_;
}
v___jp_3652_:
{
uint8_t v___x_3663_; 
v___x_3663_ = l_List_isEmpty___redArg(v___y_3660_);
lean_dec(v___y_3660_);
if (v___x_3663_ == 0)
{
lean_dec(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___y_3644_ = v___y_3655_;
v___y_3645_ = v___y_3654_;
v___y_3646_ = v___y_3658_;
v___y_3647_ = v___y_3659_;
v___y_3648_ = v___y_3661_;
v___y_3649_ = v___y_3662_;
goto v___jp_3643_;
}
else
{
if (v___y_3653_ == 0)
{
lean_object* v___x_3664_; 
lean_inc(v_trace_3013_);
v___x_3664_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3656_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3666_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref(v___x_3664_);
v___x_3666_ = l_List_appendTR___redArg(v___y_3657_, v_a_3665_);
v___y_3570_ = v___y_3655_;
v___y_3571_ = v___y_3654_;
v___y_3572_ = v___y_3658_;
v___y_3573_ = v___y_3659_;
v___y_3574_ = v___y_3661_;
v___y_3575_ = v___y_3662_;
v_a_3576_ = v___x_3666_;
goto v___jp_3569_;
}
else
{
lean_dec(v___y_3657_);
v___y_3634_ = v___y_3654_;
v___y_3635_ = v___y_3655_;
v___y_3636_ = v___y_3658_;
v___y_3637_ = v___y_3659_;
v___y_3638_ = v___y_3661_;
v___y_3639_ = v___y_3662_;
v___y_3640_ = v___x_3664_;
goto v___jp_3633_;
}
}
else
{
lean_dec(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___y_3644_ = v___y_3655_;
v___y_3645_ = v___y_3654_;
v___y_3646_ = v___y_3658_;
v___y_3647_ = v___y_3659_;
v___y_3648_ = v___y_3661_;
v___y_3649_ = v___y_3662_;
goto v___jp_3643_;
}
}
}
v___jp_3667_:
{
uint8_t v_commitIndependentGoals_3678_; lean_object* v___x_3679_; 
v_commitIndependentGoals_3678_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*4);
lean_inc(v___y_3671_);
v___x_3679_ = l_List_appendTR___redArg(v_a_3677_, v___y_3671_);
if (v_commitIndependentGoals_3678_ == 0)
{
v___y_3653_ = v___y_3668_;
v___y_3654_ = v___y_3669_;
v___y_3655_ = v___y_3670_;
v___y_3656_ = v___x_3679_;
v___y_3657_ = v___y_3671_;
v___y_3658_ = v___y_3672_;
v___y_3659_ = v___y_3673_;
v___y_3660_ = v___y_3674_;
v___y_3661_ = v___y_3675_;
v___y_3662_ = v___y_3676_;
goto v___jp_3652_;
}
else
{
uint8_t v___x_3680_; 
v___x_3680_ = l_List_isEmpty___redArg(v___y_3671_);
if (v___x_3680_ == 0)
{
v___y_3617_ = v___y_3669_;
v___y_3618_ = v___y_3670_;
v___y_3619_ = v___x_3679_;
v___y_3620_ = v___y_3671_;
v___y_3621_ = v___y_3672_;
v___y_3622_ = v___y_3673_;
v___y_3623_ = v___y_3674_;
v___y_3624_ = v___y_3675_;
v___y_3625_ = v___y_3676_;
goto v___jp_3616_;
}
else
{
if (v___y_3668_ == 0)
{
v___y_3653_ = v___y_3668_;
v___y_3654_ = v___y_3669_;
v___y_3655_ = v___y_3670_;
v___y_3656_ = v___x_3679_;
v___y_3657_ = v___y_3671_;
v___y_3658_ = v___y_3672_;
v___y_3659_ = v___y_3673_;
v___y_3660_ = v___y_3674_;
v___y_3661_ = v___y_3675_;
v___y_3662_ = v___y_3676_;
goto v___jp_3652_;
}
else
{
v___y_3617_ = v___y_3669_;
v___y_3618_ = v___y_3670_;
v___y_3619_ = v___x_3679_;
v___y_3620_ = v___y_3671_;
v___y_3621_ = v___y_3672_;
v___y_3622_ = v___y_3673_;
v___y_3623_ = v___y_3674_;
v___y_3624_ = v___y_3675_;
v___y_3625_ = v___y_3676_;
goto v___jp_3616_;
}
}
}
}
v___jp_3681_:
{
lean_object* v___x_3689_; double v___x_3690_; double v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3689_ = lean_io_get_num_heartbeats();
v___x_3690_ = lean_float_of_nat(v___y_3687_);
v___x_3691_ = lean_float_of_nat(v___x_3689_);
v___x_3692_ = lean_box_float(v___x_3690_);
v___x_3693_ = lean_box_float(v___x_3691_);
v___x_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3695_, 0, v_a_3688_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
lean_inc(v_trace_3013_);
v___x_3696_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3013_, v_hasTrace_3037_, v___x_3119_, v_options_3035_, v___y_3683_, v___y_3684_, v___y_3685_, v___x_3695_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3536_ = v___y_3682_;
v___y_3537_ = v___y_3686_;
v___y_3538_ = v___x_3696_;
goto v___jp_3535_;
}
v___jp_3697_:
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v_a_3704_);
v___y_3682_ = v___y_3698_;
v___y_3683_ = v___y_3699_;
v___y_3684_ = v___y_3700_;
v___y_3685_ = v___y_3701_;
v___y_3686_ = v___y_3702_;
v___y_3687_ = v___y_3703_;
v_a_3688_ = v___x_3705_;
goto v___jp_3681_;
}
v___jp_3706_:
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3714_, 0, v_a_3713_);
v___y_3682_ = v___y_3707_;
v___y_3683_ = v___y_3708_;
v___y_3684_ = v___y_3709_;
v___y_3685_ = v___y_3710_;
v___y_3686_ = v___y_3711_;
v___y_3687_ = v___y_3712_;
v_a_3688_ = v___x_3714_;
goto v___jp_3681_;
}
v___jp_3715_:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = l_List_appendTR___redArg(v___y_3717_, v___y_3720_);
v___x_3726_ = l_List_appendTR___redArg(v___x_3725_, v_a_3724_);
v___y_3707_ = v___y_3716_;
v___y_3708_ = v___y_3718_;
v___y_3709_ = v___y_3719_;
v___y_3710_ = v___y_3721_;
v___y_3711_ = v___y_3722_;
v___y_3712_ = v___y_3723_;
v_a_3713_ = v___x_3726_;
goto v___jp_3706_;
}
v___jp_3727_:
{
if (lean_obj_tag(v___y_3736_) == 0)
{
lean_object* v_a_3737_; 
v_a_3737_ = lean_ctor_get(v___y_3736_, 0);
lean_inc(v_a_3737_);
lean_dec_ref(v___y_3736_);
v___y_3716_ = v___y_3728_;
v___y_3717_ = v___y_3729_;
v___y_3718_ = v___y_3730_;
v___y_3719_ = v___y_3731_;
v___y_3720_ = v___y_3732_;
v___y_3721_ = v___y_3733_;
v___y_3722_ = v___y_3734_;
v___y_3723_ = v___y_3735_;
v_a_3724_ = v_a_3737_;
goto v___jp_3715_;
}
else
{
lean_object* v_a_3738_; 
lean_dec(v___y_3732_);
lean_dec(v___y_3729_);
v_a_3738_ = lean_ctor_get(v___y_3736_, 0);
lean_inc(v_a_3738_);
lean_dec_ref(v___y_3736_);
v___y_3698_ = v___y_3728_;
v___y_3699_ = v___y_3730_;
v___y_3700_ = v___y_3731_;
v___y_3701_ = v___y_3733_;
v___y_3702_ = v___y_3734_;
v___y_3703_ = v___y_3735_;
v_a_3704_ = v_a_3738_;
goto v___jp_3697_;
}
}
v___jp_3739_:
{
if (v___y_3750_ == 0)
{
lean_object* v___x_3751_; 
lean_dec_ref(v___y_3740_);
v___x_3751_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3747_, v_a_3019_, v_a_3021_);
lean_dec_ref(v___y_3747_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_dec_ref(v___x_3751_);
v___y_3716_ = v___y_3741_;
v___y_3717_ = v___y_3742_;
v___y_3718_ = v___y_3743_;
v___y_3719_ = v___y_3744_;
v___y_3720_ = v___y_3745_;
v___y_3721_ = v___y_3746_;
v___y_3722_ = v___y_3748_;
v___y_3723_ = v___y_3749_;
v_a_3724_ = v_snd_3030_;
goto v___jp_3715_;
}
else
{
lean_object* v_a_3752_; 
lean_dec(v___y_3745_);
lean_dec(v___y_3742_);
lean_dec(v_snd_3030_);
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref(v___x_3751_);
v___y_3698_ = v___y_3741_;
v___y_3699_ = v___y_3743_;
v___y_3700_ = v___y_3744_;
v___y_3701_ = v___y_3746_;
v___y_3702_ = v___y_3748_;
v___y_3703_ = v___y_3749_;
v_a_3704_ = v_a_3752_;
goto v___jp_3697_;
}
}
else
{
lean_dec_ref(v___y_3747_);
lean_dec(v_snd_3030_);
v___y_3728_ = v___y_3741_;
v___y_3729_ = v___y_3742_;
v___y_3730_ = v___y_3743_;
v___y_3731_ = v___y_3744_;
v___y_3732_ = v___y_3745_;
v___y_3733_ = v___y_3746_;
v___y_3734_ = v___y_3748_;
v___y_3735_ = v___y_3749_;
v___y_3736_ = v___y_3740_;
goto v___jp_3727_;
}
}
v___jp_3753_:
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Lean_Meta_saveState___redArg(v_a_3019_, v_a_3021_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3765_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref(v___x_3763_);
lean_inc(v_snd_3030_);
lean_inc(v_trace_3013_);
v___x_3765_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3759_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_dec(v_a_3764_);
lean_dec(v_snd_3030_);
v___y_3728_ = v___y_3754_;
v___y_3729_ = v___y_3755_;
v___y_3730_ = v___y_3756_;
v___y_3731_ = v___y_3757_;
v___y_3732_ = v___y_3758_;
v___y_3733_ = v___y_3760_;
v___y_3734_ = v___y_3761_;
v___y_3735_ = v___y_3762_;
v___y_3736_ = v___x_3765_;
goto v___jp_3727_;
}
else
{
lean_object* v_a_3766_; uint8_t v___x_3767_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
v___x_3767_ = l_Lean_Exception_isInterrupt(v_a_3766_);
if (v___x_3767_ == 0)
{
uint8_t v___x_3768_; 
v___x_3768_ = l_Lean_Exception_isRuntime(v_a_3766_);
v___y_3740_ = v___x_3765_;
v___y_3741_ = v___y_3754_;
v___y_3742_ = v___y_3755_;
v___y_3743_ = v___y_3756_;
v___y_3744_ = v___y_3757_;
v___y_3745_ = v___y_3758_;
v___y_3746_ = v___y_3760_;
v___y_3747_ = v_a_3764_;
v___y_3748_ = v___y_3761_;
v___y_3749_ = v___y_3762_;
v___y_3750_ = v___x_3768_;
goto v___jp_3739_;
}
else
{
lean_dec(v_a_3766_);
v___y_3740_ = v___x_3765_;
v___y_3741_ = v___y_3754_;
v___y_3742_ = v___y_3755_;
v___y_3743_ = v___y_3756_;
v___y_3744_ = v___y_3757_;
v___y_3745_ = v___y_3758_;
v___y_3746_ = v___y_3760_;
v___y_3747_ = v_a_3764_;
v___y_3748_ = v___y_3761_;
v___y_3749_ = v___y_3762_;
v___y_3750_ = v___x_3767_;
goto v___jp_3739_;
}
}
}
else
{
lean_object* v_a_3769_; 
lean_dec(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec(v___y_3755_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3769_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3769_);
lean_dec_ref(v___x_3763_);
v___y_3698_ = v___y_3754_;
v___y_3699_ = v___y_3756_;
v___y_3700_ = v___y_3757_;
v___y_3701_ = v___y_3760_;
v___y_3702_ = v___y_3761_;
v___y_3703_ = v___y_3762_;
v_a_3704_ = v_a_3769_;
goto v___jp_3697_;
}
}
v___jp_3770_:
{
if (lean_obj_tag(v___y_3777_) == 0)
{
lean_object* v_a_3778_; 
v_a_3778_ = lean_ctor_get(v___y_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref(v___y_3777_);
v___y_3707_ = v___y_3771_;
v___y_3708_ = v___y_3772_;
v___y_3709_ = v___y_3773_;
v___y_3710_ = v___y_3774_;
v___y_3711_ = v___y_3775_;
v___y_3712_ = v___y_3776_;
v_a_3713_ = v_a_3778_;
goto v___jp_3706_;
}
else
{
lean_object* v_a_3779_; 
v_a_3779_ = lean_ctor_get(v___y_3777_, 0);
lean_inc(v_a_3779_);
lean_dec_ref(v___y_3777_);
v___y_3698_ = v___y_3771_;
v___y_3699_ = v___y_3772_;
v___y_3700_ = v___y_3773_;
v___y_3701_ = v___y_3774_;
v___y_3702_ = v___y_3775_;
v___y_3703_ = v___y_3776_;
v_a_3704_ = v_a_3779_;
goto v___jp_3697_;
}
}
v___jp_3780_:
{
lean_object* v___x_3789_; 
lean_inc(v_trace_3013_);
v___x_3789_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3785_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3791_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v___x_3789_);
v___x_3791_ = l_List_appendTR___redArg(v___y_3782_, v_a_3790_);
v___y_3707_ = v___y_3781_;
v___y_3708_ = v___y_3783_;
v___y_3709_ = v___y_3784_;
v___y_3710_ = v___y_3786_;
v___y_3711_ = v___y_3787_;
v___y_3712_ = v___y_3788_;
v_a_3713_ = v___x_3791_;
goto v___jp_3706_;
}
else
{
lean_dec(v___y_3782_);
v___y_3771_ = v___y_3781_;
v___y_3772_ = v___y_3783_;
v___y_3773_ = v___y_3784_;
v___y_3774_ = v___y_3786_;
v___y_3775_ = v___y_3787_;
v___y_3776_ = v___y_3788_;
v___y_3777_ = v___x_3789_;
goto v___jp_3770_;
}
}
v___jp_3792_:
{
uint8_t v___x_3803_; 
v___x_3803_ = l_List_isEmpty___redArg(v___y_3799_);
lean_dec(v___y_3799_);
if (v___x_3803_ == 0)
{
if (v___y_3793_ == 0)
{
v___y_3781_ = v___y_3794_;
v___y_3782_ = v___y_3795_;
v___y_3783_ = v___y_3796_;
v___y_3784_ = v___y_3797_;
v___y_3785_ = v___y_3798_;
v___y_3786_ = v___y_3800_;
v___y_3787_ = v___y_3801_;
v___y_3788_ = v___y_3802_;
goto v___jp_3780_;
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
lean_dec(v___y_3798_);
lean_dec(v___y_3795_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___x_3804_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3805_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3804_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3771_ = v___y_3794_;
v___y_3772_ = v___y_3796_;
v___y_3773_ = v___y_3797_;
v___y_3774_ = v___y_3800_;
v___y_3775_ = v___y_3801_;
v___y_3776_ = v___y_3802_;
v___y_3777_ = v___x_3805_;
goto v___jp_3770_;
}
}
else
{
v___y_3781_ = v___y_3794_;
v___y_3782_ = v___y_3795_;
v___y_3783_ = v___y_3796_;
v___y_3784_ = v___y_3797_;
v___y_3785_ = v___y_3798_;
v___y_3786_ = v___y_3800_;
v___y_3787_ = v___y_3801_;
v___y_3788_ = v___y_3802_;
goto v___jp_3780_;
}
}
v___jp_3806_:
{
uint8_t v_commitIndependentGoals_3817_; lean_object* v___x_3818_; 
v_commitIndependentGoals_3817_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*4);
lean_inc(v___y_3809_);
v___x_3818_ = l_List_appendTR___redArg(v_a_3816_, v___y_3809_);
if (v_commitIndependentGoals_3817_ == 0)
{
v___y_3793_ = v___y_3807_;
v___y_3794_ = v___y_3808_;
v___y_3795_ = v___y_3809_;
v___y_3796_ = v___y_3810_;
v___y_3797_ = v___y_3811_;
v___y_3798_ = v___x_3818_;
v___y_3799_ = v___y_3812_;
v___y_3800_ = v___y_3813_;
v___y_3801_ = v___y_3814_;
v___y_3802_ = v___y_3815_;
goto v___jp_3792_;
}
else
{
uint8_t v___x_3819_; 
v___x_3819_ = l_List_isEmpty___redArg(v___y_3809_);
if (v___x_3819_ == 0)
{
v___y_3754_ = v___y_3808_;
v___y_3755_ = v___y_3809_;
v___y_3756_ = v___y_3810_;
v___y_3757_ = v___y_3811_;
v___y_3758_ = v___y_3812_;
v___y_3759_ = v___x_3818_;
v___y_3760_ = v___y_3813_;
v___y_3761_ = v___y_3814_;
v___y_3762_ = v___y_3815_;
goto v___jp_3753_;
}
else
{
if (v___x_3034_ == 0)
{
v___y_3793_ = v___y_3807_;
v___y_3794_ = v___y_3808_;
v___y_3795_ = v___y_3809_;
v___y_3796_ = v___y_3810_;
v___y_3797_ = v___y_3811_;
v___y_3798_ = v___x_3818_;
v___y_3799_ = v___y_3812_;
v___y_3800_ = v___y_3813_;
v___y_3801_ = v___y_3814_;
v___y_3802_ = v___y_3815_;
goto v___jp_3792_;
}
else
{
v___y_3754_ = v___y_3808_;
v___y_3755_ = v___y_3809_;
v___y_3756_ = v___y_3810_;
v___y_3757_ = v___y_3811_;
v___y_3758_ = v___y_3812_;
v___y_3759_ = v___x_3818_;
v___y_3760_ = v___y_3813_;
v___y_3761_ = v___y_3814_;
v___y_3762_ = v___y_3815_;
goto v___jp_3753_;
}
}
}
}
v___jp_3820_:
{
lean_object* v___x_3829_; 
v___x_3829_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3021_);
if (lean_obj_tag(v___x_3829_) == 0)
{
if (v___y_3821_ == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref(v___x_3829_);
v___x_3831_ = lean_io_mono_nanos_now();
v___x_3832_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3821_, v___x_3034_, v_goals_3016_, v___y_3827_, v_a_3019_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3834_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref(v___x_3832_);
v___x_3834_ = l_List_reverse___redArg(v_a_3833_);
v___y_3668_ = v___y_3821_;
v___y_3669_ = v___y_3822_;
v___y_3670_ = v___x_3831_;
v___y_3671_ = v___y_3823_;
v___y_3672_ = v___y_3824_;
v___y_3673_ = v_a_3830_;
v___y_3674_ = v___y_3825_;
v___y_3675_ = v___y_3826_;
v___y_3676_ = v___y_3828_;
v_a_3677_ = v___x_3834_;
goto v___jp_3667_;
}
else
{
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3835_; 
v_a_3835_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3835_);
lean_dec_ref(v___x_3832_);
v___y_3668_ = v___y_3821_;
v___y_3669_ = v___y_3822_;
v___y_3670_ = v___x_3831_;
v___y_3671_ = v___y_3823_;
v___y_3672_ = v___y_3824_;
v___y_3673_ = v_a_3830_;
v___y_3674_ = v___y_3825_;
v___y_3675_ = v___y_3826_;
v___y_3676_ = v___y_3828_;
v_a_3677_ = v_a_3835_;
goto v___jp_3667_;
}
else
{
lean_object* v_a_3836_; 
lean_dec(v___y_3825_);
lean_dec(v___y_3823_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3836_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3836_);
lean_dec_ref(v___x_3832_);
v___y_3561_ = v___x_3831_;
v___y_3562_ = v___y_3822_;
v___y_3563_ = v___y_3824_;
v___y_3564_ = v_a_3830_;
v___y_3565_ = v___y_3826_;
v___y_3566_ = v___y_3828_;
v_a_3567_ = v_a_3836_;
goto v___jp_3560_;
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v_a_3837_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3837_);
lean_dec_ref(v___x_3829_);
v___x_3838_ = lean_io_get_num_heartbeats();
v___x_3839_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3821_, v___x_3034_, v_goals_3016_, v___y_3827_, v_a_3019_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3841_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
lean_dec_ref(v___x_3839_);
v___x_3841_ = l_List_reverse___redArg(v_a_3840_);
v___y_3807_ = v___y_3821_;
v___y_3808_ = v___y_3822_;
v___y_3809_ = v___y_3823_;
v___y_3810_ = v___y_3824_;
v___y_3811_ = v_a_3837_;
v___y_3812_ = v___y_3825_;
v___y_3813_ = v___y_3826_;
v___y_3814_ = v___y_3828_;
v___y_3815_ = v___x_3838_;
v_a_3816_ = v___x_3841_;
goto v___jp_3806_;
}
else
{
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3842_; 
v_a_3842_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3842_);
lean_dec_ref(v___x_3839_);
v___y_3807_ = v___y_3821_;
v___y_3808_ = v___y_3822_;
v___y_3809_ = v___y_3823_;
v___y_3810_ = v___y_3824_;
v___y_3811_ = v_a_3837_;
v___y_3812_ = v___y_3825_;
v___y_3813_ = v___y_3826_;
v___y_3814_ = v___y_3828_;
v___y_3815_ = v___x_3838_;
v_a_3816_ = v_a_3842_;
goto v___jp_3806_;
}
else
{
lean_object* v_a_3843_; 
lean_dec(v___y_3825_);
lean_dec(v___y_3823_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3843_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3843_);
lean_dec_ref(v___x_3839_);
v___y_3698_ = v___y_3822_;
v___y_3699_ = v___y_3824_;
v___y_3700_ = v_a_3837_;
v___y_3701_ = v___y_3826_;
v___y_3702_ = v___y_3828_;
v___y_3703_ = v___x_3838_;
v_a_3704_ = v_a_3843_;
goto v___jp_3697_;
}
}
}
}
else
{
lean_object* v_a_3844_; 
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec(v___y_3823_);
lean_dec(v_snd_3030_);
lean_dec(v_goals_3016_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3844_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3844_);
lean_dec_ref(v___x_3829_);
v___y_3526_ = v___y_3822_;
v___y_3527_ = v___y_3828_;
v_a_3528_ = v_a_3844_;
goto v___jp_3525_;
}
}
v___jp_3845_:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3849_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3848_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
v___y_3536_ = v___y_3846_;
v___y_3537_ = v___y_3847_;
v___y_3538_ = v___x_3849_;
goto v___jp_3535_;
}
v___jp_3850_:
{
uint8_t v___x_3857_; 
v___x_3857_ = l_List_isEmpty___redArg(v___y_3855_);
lean_dec(v___y_3855_);
if (v___x_3857_ == 0)
{
lean_dec(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___y_3846_ = v___y_3852_;
v___y_3847_ = v___y_3856_;
goto v___jp_3845_;
}
else
{
if (v___y_3851_ == 0)
{
lean_object* v___x_3858_; 
lean_inc(v_trace_3013_);
v___x_3858_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3854_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; lean_object* v___x_3860_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref(v___x_3858_);
v___x_3860_ = l_List_appendTR___redArg(v___y_3853_, v_a_3859_);
v___y_3531_ = v___y_3852_;
v___y_3532_ = v___y_3856_;
v_a_3533_ = v___x_3860_;
goto v___jp_3530_;
}
else
{
lean_dec(v___y_3853_);
v___y_3536_ = v___y_3852_;
v___y_3537_ = v___y_3856_;
v___y_3538_ = v___x_3858_;
goto v___jp_3535_;
}
}
else
{
lean_dec(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v___y_3846_ = v___y_3852_;
v___y_3847_ = v___y_3856_;
goto v___jp_3845_;
}
}
}
v___jp_3861_:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = l_List_appendTR___redArg(v___y_3863_, v___y_3864_);
v___x_3868_ = l_List_appendTR___redArg(v___x_3867_, v_a_3866_);
v___y_3531_ = v___y_3862_;
v___y_3532_ = v___y_3865_;
v_a_3533_ = v___x_3868_;
goto v___jp_3530_;
}
v___jp_3869_:
{
if (lean_obj_tag(v___y_3874_) == 0)
{
lean_object* v_a_3875_; 
v_a_3875_ = lean_ctor_get(v___y_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref(v___y_3874_);
v___y_3862_ = v___y_3870_;
v___y_3863_ = v___y_3871_;
v___y_3864_ = v___y_3872_;
v___y_3865_ = v___y_3873_;
v_a_3866_ = v_a_3875_;
goto v___jp_3861_;
}
else
{
lean_object* v_a_3876_; 
lean_dec(v___y_3872_);
lean_dec(v___y_3871_);
v_a_3876_ = lean_ctor_get(v___y_3874_, 0);
lean_inc(v_a_3876_);
lean_dec_ref(v___y_3874_);
v___y_3526_ = v___y_3870_;
v___y_3527_ = v___y_3873_;
v_a_3528_ = v_a_3876_;
goto v___jp_3525_;
}
}
v___jp_3877_:
{
if (v___y_3884_ == 0)
{
lean_object* v___x_3885_; 
lean_dec_ref(v___y_3880_);
v___x_3885_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3882_, v_a_3019_, v_a_3021_);
lean_dec_ref(v___y_3882_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_dec_ref(v___x_3885_);
v___y_3862_ = v___y_3878_;
v___y_3863_ = v___y_3879_;
v___y_3864_ = v___y_3881_;
v___y_3865_ = v___y_3883_;
v_a_3866_ = v_snd_3030_;
goto v___jp_3861_;
}
else
{
lean_object* v_a_3886_; 
lean_dec(v___y_3881_);
lean_dec(v___y_3879_);
lean_dec(v_snd_3030_);
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref(v___x_3885_);
v___y_3526_ = v___y_3878_;
v___y_3527_ = v___y_3883_;
v_a_3528_ = v_a_3886_;
goto v___jp_3525_;
}
}
else
{
lean_dec_ref(v___y_3882_);
lean_dec(v_snd_3030_);
v___y_3870_ = v___y_3878_;
v___y_3871_ = v___y_3879_;
v___y_3872_ = v___y_3881_;
v___y_3873_ = v___y_3883_;
v___y_3874_ = v___y_3880_;
goto v___jp_3869_;
}
}
v___jp_3887_:
{
lean_object* v___x_3893_; 
v___x_3893_ = l_Lean_Meta_saveState___redArg(v_a_3019_, v_a_3021_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3895_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref(v___x_3893_);
lean_inc(v_snd_3030_);
lean_inc(v_trace_3013_);
v___x_3895_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v___y_3890_, v_snd_3030_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_dec(v_a_3894_);
lean_dec(v_snd_3030_);
v___y_3870_ = v___y_3888_;
v___y_3871_ = v___y_3889_;
v___y_3872_ = v___y_3891_;
v___y_3873_ = v___y_3892_;
v___y_3874_ = v___x_3895_;
goto v___jp_3869_;
}
else
{
lean_object* v_a_3896_; uint8_t v___x_3897_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
v___x_3897_ = l_Lean_Exception_isInterrupt(v_a_3896_);
if (v___x_3897_ == 0)
{
uint8_t v___x_3898_; 
v___x_3898_ = l_Lean_Exception_isRuntime(v_a_3896_);
v___y_3878_ = v___y_3888_;
v___y_3879_ = v___y_3889_;
v___y_3880_ = v___x_3895_;
v___y_3881_ = v___y_3891_;
v___y_3882_ = v_a_3894_;
v___y_3883_ = v___y_3892_;
v___y_3884_ = v___x_3898_;
goto v___jp_3877_;
}
else
{
lean_dec(v_a_3896_);
v___y_3878_ = v___y_3888_;
v___y_3879_ = v___y_3889_;
v___y_3880_ = v___x_3895_;
v___y_3881_ = v___y_3891_;
v___y_3882_ = v_a_3894_;
v___y_3883_ = v___y_3892_;
v___y_3884_ = v___x_3897_;
goto v___jp_3877_;
}
}
}
else
{
lean_object* v_a_3899_; 
lean_dec(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3899_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3899_);
lean_dec_ref(v___x_3893_);
v___y_3526_ = v___y_3888_;
v___y_3527_ = v___y_3892_;
v_a_3528_ = v_a_3899_;
goto v___jp_3525_;
}
}
v___jp_3900_:
{
uint8_t v_commitIndependentGoals_3907_; lean_object* v___x_3908_; 
v_commitIndependentGoals_3907_ = lean_ctor_get_uint8(v_cfg_3012_, sizeof(void*)*4);
lean_inc(v___y_3903_);
v___x_3908_ = l_List_appendTR___redArg(v_a_3906_, v___y_3903_);
if (v_commitIndependentGoals_3907_ == 0)
{
v___y_3851_ = v___y_3901_;
v___y_3852_ = v___y_3902_;
v___y_3853_ = v___y_3903_;
v___y_3854_ = v___x_3908_;
v___y_3855_ = v___y_3904_;
v___y_3856_ = v___y_3905_;
goto v___jp_3850_;
}
else
{
uint8_t v___x_3909_; 
v___x_3909_ = l_List_isEmpty___redArg(v___y_3903_);
if (v___x_3909_ == 0)
{
v___y_3888_ = v___y_3902_;
v___y_3889_ = v___y_3903_;
v___y_3890_ = v___x_3908_;
v___y_3891_ = v___y_3904_;
v___y_3892_ = v___y_3905_;
goto v___jp_3887_;
}
else
{
if (v___y_3901_ == 0)
{
v___y_3851_ = v___y_3901_;
v___y_3852_ = v___y_3902_;
v___y_3853_ = v___y_3903_;
v___y_3854_ = v___x_3908_;
v___y_3855_ = v___y_3904_;
v___y_3856_ = v___y_3905_;
goto v___jp_3850_;
}
else
{
v___y_3888_ = v___y_3902_;
v___y_3889_ = v___y_3903_;
v___y_3890_ = v___x_3908_;
v___y_3891_ = v___y_3904_;
v___y_3892_ = v___y_3905_;
goto v___jp_3887_;
}
}
}
}
v___jp_3910_:
{
lean_object* v___x_3911_; 
v___x_3911_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3021_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref(v___x_3911_);
v___x_3913_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3914_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3035_, v___x_3913_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = lean_io_mono_nanos_now();
v___x_3916_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3029_, v___f_3038_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v_fst_3918_; lean_object* v_snd_3919_; lean_object* v___x_3920_; lean_object* v___f_3921_; lean_object* v___x_3922_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref(v___x_3916_);
v_fst_3918_ = lean_ctor_get(v_a_3917_, 0);
lean_inc_n(v_fst_3918_, 2);
v_snd_3919_ = lean_ctor_get(v_a_3917_, 1);
lean_inc(v_snd_3919_);
lean_dec(v_a_3917_);
v___x_3920_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3919_, v___x_3026_);
lean_inc(v___x_3920_);
v___f_3921_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3921_, 0, v_fst_3918_);
lean_closure_set(v___f_3921_, 1, v___x_3920_);
v___x_3922_ = lean_box(0);
if (v___x_3122_ == 0)
{
lean_object* v___x_3923_; uint8_t v___x_3924_; 
v___x_3923_ = l_Lean_trace_profiler;
v___x_3924_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3035_, v___x_3923_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; 
lean_dec_ref(v___f_3921_);
v___x_3925_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3037_, v___x_3914_, v_goals_3016_, v___x_3922_, v_a_3019_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___x_3927_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref(v___x_3925_);
v___x_3927_ = l_List_reverse___redArg(v_a_3926_);
v___y_3504_ = v_a_3912_;
v___y_3505_ = v___x_3924_;
v___y_3506_ = v___x_3915_;
v___y_3507_ = v___x_3920_;
v___y_3508_ = v_fst_3918_;
v_a_3509_ = v___x_3927_;
goto v___jp_3503_;
}
else
{
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3928_; 
v_a_3928_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3928_);
lean_dec_ref(v___x_3925_);
v___y_3504_ = v_a_3912_;
v___y_3505_ = v___x_3924_;
v___y_3506_ = v___x_3915_;
v___y_3507_ = v___x_3920_;
v___y_3508_ = v_fst_3918_;
v_a_3509_ = v_a_3928_;
goto v___jp_3503_;
}
else
{
lean_object* v_a_3929_; 
lean_dec(v___x_3920_);
lean_dec(v_fst_3918_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3929_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3929_);
lean_dec_ref(v___x_3925_);
v___y_3154_ = v_a_3912_;
v___y_3155_ = v___x_3915_;
v_a_3156_ = v_a_3929_;
goto v___jp_3153_;
}
}
}
else
{
v___y_3463_ = v___x_3914_;
v___y_3464_ = v___x_3122_;
v___y_3465_ = v_a_3912_;
v___y_3466_ = v___x_3915_;
v___y_3467_ = v___x_3920_;
v___y_3468_ = v_fst_3918_;
v___y_3469_ = v___f_3921_;
v___y_3470_ = v___x_3922_;
goto v___jp_3462_;
}
}
else
{
v___y_3463_ = v___x_3914_;
v___y_3464_ = v___x_3122_;
v___y_3465_ = v_a_3912_;
v___y_3466_ = v___x_3915_;
v___y_3467_ = v___x_3920_;
v___y_3468_ = v_fst_3918_;
v___y_3469_ = v___f_3921_;
v___y_3470_ = v___x_3922_;
goto v___jp_3462_;
}
}
else
{
lean_object* v_a_3930_; 
lean_dec(v_snd_3030_);
lean_dec(v_goals_3016_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3930_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3930_);
lean_dec_ref(v___x_3916_);
v___y_3154_ = v_a_3912_;
v___y_3155_ = v___x_3915_;
v_a_3156_ = v_a_3930_;
goto v___jp_3153_;
}
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_del_object(v___x_3032_);
v___x_3931_ = lean_io_get_num_heartbeats();
v___x_3932_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3029_, v___f_3038_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; lean_object* v_fst_3934_; lean_object* v_snd_3935_; lean_object* v___x_3936_; lean_object* v___f_3937_; lean_object* v___x_3938_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_a_3933_);
lean_dec_ref(v___x_3932_);
v_fst_3934_ = lean_ctor_get(v_a_3933_, 0);
lean_inc_n(v_fst_3934_, 2);
v_snd_3935_ = lean_ctor_get(v_a_3933_, 1);
lean_inc(v_snd_3935_);
lean_dec(v_a_3933_);
v___x_3936_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3935_, v___x_3026_);
lean_inc(v___x_3936_);
v___f_3937_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3937_, 0, v_fst_3934_);
lean_closure_set(v___f_3937_, 1, v___x_3936_);
v___x_3938_ = lean_box(0);
if (v___x_3122_ == 0)
{
lean_object* v___x_3939_; uint8_t v___x_3940_; 
v___x_3939_ = l_Lean_trace_profiler;
v___x_3940_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3035_, v___x_3939_);
if (v___x_3940_ == 0)
{
lean_object* v___x_3941_; 
lean_dec_ref(v___f_3937_);
v___x_3941_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3914_, v___x_3034_, v_goals_3016_, v___x_3938_, v_a_3019_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3943_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref(v___x_3941_);
v___x_3943_ = l_List_reverse___redArg(v_a_3942_);
v___y_3901_ = v___x_3940_;
v___y_3902_ = v_a_3912_;
v___y_3903_ = v___x_3936_;
v___y_3904_ = v_fst_3934_;
v___y_3905_ = v___x_3931_;
v_a_3906_ = v___x_3943_;
goto v___jp_3900_;
}
else
{
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3944_; 
v_a_3944_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3944_);
lean_dec_ref(v___x_3941_);
v___y_3901_ = v___x_3940_;
v___y_3902_ = v_a_3912_;
v___y_3903_ = v___x_3936_;
v___y_3904_ = v_fst_3934_;
v___y_3905_ = v___x_3931_;
v_a_3906_ = v_a_3944_;
goto v___jp_3900_;
}
else
{
lean_object* v_a_3945_; 
lean_dec(v___x_3936_);
lean_dec(v_fst_3934_);
lean_dec(v_snd_3030_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3945_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3945_);
lean_dec_ref(v___x_3941_);
v___y_3526_ = v_a_3912_;
v___y_3527_ = v___x_3931_;
v_a_3528_ = v_a_3945_;
goto v___jp_3525_;
}
}
}
else
{
v___y_3821_ = v___x_3914_;
v___y_3822_ = v_a_3912_;
v___y_3823_ = v___x_3936_;
v___y_3824_ = v___x_3122_;
v___y_3825_ = v_fst_3934_;
v___y_3826_ = v___f_3937_;
v___y_3827_ = v___x_3938_;
v___y_3828_ = v___x_3931_;
goto v___jp_3820_;
}
}
else
{
v___y_3821_ = v___x_3914_;
v___y_3822_ = v_a_3912_;
v___y_3823_ = v___x_3936_;
v___y_3824_ = v___x_3122_;
v___y_3825_ = v_fst_3934_;
v___y_3826_ = v___f_3937_;
v___y_3827_ = v___x_3938_;
v___y_3828_ = v___x_3931_;
goto v___jp_3820_;
}
}
else
{
lean_object* v_a_3946_; 
lean_dec(v_snd_3030_);
lean_dec(v_goals_3016_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec_ref(v_cfg_3012_);
v_a_3946_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_a_3946_);
lean_dec_ref(v___x_3932_);
v___y_3526_ = v_a_3912_;
v___y_3527_ = v___x_3931_;
v_a_3528_ = v_a_3946_;
goto v___jp_3525_;
}
}
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec_ref(v___f_3118_);
lean_dec_ref(v___f_3038_);
lean_del_object(v___x_3032_);
lean_dec(v_snd_3030_);
lean_dec(v_fst_3029_);
lean_dec(v_goals_3016_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
v_a_3947_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3911_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3911_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
}
else
{
lean_object* v_maxDepth_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
lean_del_object(v___x_3032_);
lean_dec(v_snd_3030_);
lean_dec(v_fst_3029_);
lean_dec(v_goals_3016_);
v_maxDepth_4235_ = lean_ctor_get(v_cfg_3012_, 0);
lean_inc(v_maxDepth_4235_);
v___x_4236_ = lean_box(0);
v___x_4237_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_3012_, v_trace_3013_, v_next_3014_, v_orig_3015_, v_maxDepth_4235_, v_remaining_3017_, v___x_4236_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
return v___x_4237_;
}
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
lean_dec(v_remaining_3017_);
lean_dec(v_goals_3016_);
lean_dec(v_orig_3015_);
lean_dec_ref(v_next_3014_);
lean_dec(v_trace_3013_);
lean_dec_ref(v_cfg_3012_);
v_a_4239_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_3027_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_3027_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
v___jp_3023_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3025_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3024_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
return v___x_3025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_4247_, lean_object* v_trace_4248_, lean_object* v_next_4249_, lean_object* v_orig_4250_, lean_object* v_goals_4251_, lean_object* v_remaining_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4247_, v_trace_4248_, v_next_4249_, v_orig_4250_, v_goals_4251_, v_remaining_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
lean_dec(v_a_4254_);
lean_dec_ref(v_a_4253_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_4259_, lean_object* v_00_u03b2_4260_, lean_object* v_L_4261_, lean_object* v_f_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_4261_, v_f_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_4269_, lean_object* v_00_u03b2_4270_, lean_object* v_L_4271_, lean_object* v_f_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_4269_, v_00_u03b2_4270_, v_L_4271_, v_f_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_4279_, lean_object* v_x_4280_, lean_object* v_x_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_4279_, v_x_4280_, v_x_4281_, v___y_4283_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_4288_, lean_object* v_x_4289_, lean_object* v_x_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
uint8_t v___x_60528__boxed_4296_; lean_object* v_res_4297_; 
v___x_60528__boxed_4296_ = lean_unbox(v___x_4288_);
v_res_4297_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_60528__boxed_4296_, v_x_4289_, v_x_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_4298_, uint8_t v___x_4299_, lean_object* v_x_4300_, lean_object* v_x_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v___x_4307_; 
v___x_4307_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_4298_, v___x_4299_, v_x_4300_, v_x_4301_, v___y_4303_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_4308_, lean_object* v___x_4309_, lean_object* v_x_4310_, lean_object* v_x_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
uint8_t v___x_60554__boxed_4317_; uint8_t v___x_60555__boxed_4318_; lean_object* v_res_4319_; 
v___x_60554__boxed_4317_ = lean_unbox(v___x_4308_);
v___x_60555__boxed_4318_ = lean_unbox(v___x_4309_);
v_res_4319_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_60554__boxed_4317_, v___x_60555__boxed_4318_, v_x_4310_, v_x_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
return v_res_4319_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_4320_, lean_object* v_00_u03b2_4321_, lean_object* v_f_4322_, lean_object* v_x_4323_, lean_object* v_x_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_4322_, v_x_4323_, v_x_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4331_, lean_object* v_00_u03b2_4332_, lean_object* v_f_4333_, lean_object* v_x_4334_, lean_object* v_x_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_4331_, v_00_u03b2_4332_, v_f_4333_, v_x_4334_, v_x_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_4342_, lean_object* v_00_u03b2_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v___x_4346_; 
v___x_4346_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_4344_, v_a_4345_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_4347_, lean_object* v_00_u03b2_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_4349_, v_a_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_4352_, lean_object* v_g_4353_, lean_object* v_f_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; 
lean_inc(v___y_4358_);
lean_inc_ref(v___y_4357_);
lean_inc(v___y_4356_);
lean_inc_ref(v___y_4355_);
v___x_4360_ = lean_apply_6(v_next_4352_, v_g_4353_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, lean_box(0));
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v___x_4362_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref(v___x_4360_);
v___x_4362_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_4361_, v_f_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
return v___x_4362_;
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec_ref(v_f_4354_);
v_a_4363_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4360_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4360_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_4371_, lean_object* v_g_4372_, lean_object* v_f_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_4371_, v_g_4372_, v_f_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_4380_, lean_object* v_trace_4381_, lean_object* v_next_4382_, lean_object* v_goals_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_resolve_4389_; lean_object* v___x_4390_; 
v_resolve_4389_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_4389_, 0, v_next_4382_);
lean_inc_n(v_goals_4383_, 2);
v___x_4390_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4380_, v_trace_4381_, v_resolve_4389_, v_goals_4383_, v_goals_4383_, v_goals_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_4391_, lean_object* v_trace_4392_, lean_object* v_next_4393_, lean_object* v_goals_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_4391_, v_trace_4392_, v_next_4393_, v_goals_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_);
lean_dec(v_a_4398_);
lean_dec_ref(v_a_4397_);
lean_dec(v_a_4396_);
lean_dec_ref(v_a_4395_);
return v_res_4400_;
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

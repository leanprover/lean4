// Lean compiler output
// Module: Lean.Meta.Tactic.Backtrack
// Imports: public import Lean.Meta.Iterator public import Lean.Meta.Tactic.IndependentOf import Init.Data.Nat.Internal.Linear import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
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
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "working on: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "BacktrackConfig.proc failed: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "discarding already assigned goal "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2;
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
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(lean_object* v_g_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_MVarId_getType(v_g_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_9_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_a_8_);
lean_dec_ref_known(v___x_7_, 1);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_res_18_;
v_res_18_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(v_g_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId___boxed(lean_object* v_g_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(v_g_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
return v_res_25_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(lean_object* v_x_26_, lean_object* v_x_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = l_List_reverse___redArg(v_x_27_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
else
{
lean_object* v_head_35_; lean_object* v_tail_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_54_; 
v_head_35_ = lean_ctor_get(v_x_26_, 0);
v_tail_36_ = lean_ctor_get(v_x_26_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_x_26_);
if (v_isSharedCheck_54_ == 0)
{
v___x_38_ = v_x_26_;
v_isShared_39_ = v_isSharedCheck_54_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_tail_36_);
lean_inc(v_head_35_);
lean_dec(v_x_26_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_54_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; 
v___x_40_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(v_head_35_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v___x_43_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_a_41_);
lean_dec_ref_known(v___x_40_, 1);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 1, v_x_27_);
lean_ctor_set(v___x_38_, 0, v_a_41_);
v___x_43_ = v___x_38_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_41_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_x_27_);
v___x_43_ = v_reuseFailAlloc_45_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
v_x_26_ = v_tail_36_;
v_x_27_ = v___x_43_;
goto _start;
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
lean_del_object(v___x_38_);
lean_dec(v_tail_36_);
lean_dec(v_x_27_);
v_a_46_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_40_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_40_);
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
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_26_ = stack[0].m_obj;
lean_object* v_x_27_ = stack[1].m_obj;
lean_object* v___y_28_ = stack[2].m_obj;
lean_object* v___y_29_ = stack[3].m_obj;
lean_object* v___y_30_ = stack[4].m_obj;
lean_object* v___y_31_ = stack[5].m_obj;
lean_object* v_res_55_;
v_res_55_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(v_x_26_, v_x_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0___boxed(lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(v_x_56_, v_x_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_63_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(lean_object* v_gs_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_box(0);
v___x_71_ = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(v_gs_64_, v___x_70_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
return v___x_71_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_0interp(lean_interpreter_value* stack)
{
lean_object* v_gs_64_ = stack[0].m_obj;
lean_object* v_a_65_ = stack[1].m_obj;
lean_object* v_a_66_ = stack[2].m_obj;
lean_object* v_a_67_ = stack[3].m_obj;
lean_object* v_a_68_ = stack[4].m_obj;
lean_object* v_res_72_;
v_res_72_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_gs_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds___boxed(lean_object* v_gs_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_gs_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__0(lean_object* v_s_80_){
_start:
{
if (lean_obj_tag(v_s_80_) == 1)
{
lean_object* v_val_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
v_val_81_ = lean_ctor_get(v_s_80_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v_s_80_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v_s_80_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_val_81_);
lean_dec(v_s_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_val_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
else
{
lean_object* v___x_89_; 
lean_dec_ref(v_s_80_);
v___x_89_ = lean_box(0);
return v___x_89_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__1(lean_object* v_s_90_){
_start:
{
if (lean_obj_tag(v_s_90_) == 0)
{
lean_object* v_val_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
v_val_91_ = lean_ctor_get(v_s_90_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v_s_90_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v_s_90_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_val_91_);
lean_dec(v_s_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 1);
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_val_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
else
{
lean_object* v___x_99_; 
lean_dec_ref(v_s_90_);
v___x_99_ = lean_box(0);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__2(lean_object* v_val_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v_val_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3(lean_object* v___f_104_, lean_object* v___f_105_, lean_object* v_toPure_106_, lean_object* v_R_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_108_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_R_107_);
v___x_109_ = l_List_filterMapTR_go___redArg(v___f_104_, v_R_107_, v___x_108_);
v___x_110_ = l_List_filterMapTR_go___redArg(v___f_105_, v_R_107_, v___x_108_);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = lean_apply_2(v_toPure_106_, lean_box(0), v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__4(lean_object* v_a_113_, lean_object* v_toPure_114_, lean_object* v_x_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v_a_113_);
v___x_117_ = lean_apply_2(v_toPure_114_, lean_box(0), v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__5(lean_object* v_toFunctor_118_, lean_object* v_toPure_119_, lean_object* v_f_120_, lean_object* v___f_121_, lean_object* v_orElse_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_map_124_; lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_map_124_ = lean_ctor_get(v_toFunctor_118_, 0);
lean_inc(v_map_124_);
lean_dec_ref(v_toFunctor_118_);
lean_inc(v_a_123_);
v___f_125_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__4), 3, 2);
lean_closure_set(v___f_125_, 0, v_a_123_);
lean_closure_set(v___f_125_, 1, v_toPure_119_);
v___x_126_ = lean_apply_1(v_f_120_, v_a_123_);
v___x_127_ = lean_apply_4(v_map_124_, lean_box(0), lean_box(0), v___f_121_, v___x_126_);
v___x_128_ = lean_apply_3(v_orElse_122_, lean_box(0), v___x_127_, v___f_125_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg(lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_L_134_, lean_object* v_f_135_){
_start:
{
lean_object* v_toApplicative_136_; lean_object* v_toBind_137_; lean_object* v_orElse_138_; lean_object* v_toFunctor_139_; lean_object* v_toPure_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_toApplicative_136_ = lean_ctor_get(v_inst_133_, 0);
lean_inc_ref(v_toApplicative_136_);
v_toBind_137_ = lean_ctor_get(v_inst_132_, 1);
lean_inc(v_toBind_137_);
v_orElse_138_ = lean_ctor_get(v_inst_133_, 2);
lean_inc(v_orElse_138_);
lean_dec_ref(v_inst_133_);
v_toFunctor_139_ = lean_ctor_get(v_toApplicative_136_, 0);
lean_inc_ref(v_toFunctor_139_);
v_toPure_140_ = lean_ctor_get(v_toApplicative_136_, 1);
lean_inc_n(v_toPure_140_, 2);
lean_dec_ref(v_toApplicative_136_);
v___f_141_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__0));
v___f_142_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__1));
v___f_143_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__2));
v___f_144_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3), 4, 3);
lean_closure_set(v___f_144_, 0, v___f_142_);
lean_closure_set(v___f_144_, 1, v___f_141_);
lean_closure_set(v___f_144_, 2, v_toPure_140_);
v___f_145_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__5), 6, 5);
lean_closure_set(v___f_145_, 0, v_toFunctor_139_);
lean_closure_set(v___f_145_, 1, v_toPure_140_);
lean_closure_set(v___f_145_, 2, v_f_135_);
lean_closure_set(v___f_145_, 3, v___f_143_);
lean_closure_set(v___f_145_, 4, v_orElse_138_);
v___x_146_ = lean_box(0);
v___x_147_ = l_List_mapM_loop___redArg(v_inst_132_, v___f_145_, v_L_134_, v___x_146_);
v___x_148_ = lean_apply_4(v_toBind_137_, lean_box(0), lean_box(0), v___x_147_, v___f_144_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM(lean_object* v_m_149_, lean_object* v_00_u03b1_150_, lean_object* v_00_u03b2_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_L_154_, lean_object* v_f_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg(v_inst_152_, v_inst_153_, v_L_154_, v_f_155_);
return v___x_156_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(32u);
v___x_158_ = lean_mk_empty_array_with_capacity(v___x_157_);
v___x_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_160_ = ((size_t)5ULL);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_unsigned_to_nat(32u);
v___x_163_ = lean_mk_empty_array_with_capacity(v___x_162_);
v___x_164_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0);
v___x_165_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
lean_ctor_set(v___x_165_, 2, v___x_161_);
lean_ctor_set(v___x_165_, 3, v___x_161_);
lean_ctor_set_usize(v___x_165_, 4, v___x_160_);
return v___x_165_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(lean_object* v___y_166_){
_start:
{
lean_object* v___x_168_; lean_object* v_traceState_169_; lean_object* v_traces_170_; lean_object* v___x_171_; lean_object* v_traceState_172_; lean_object* v_env_173_; lean_object* v_nextMacroScope_174_; lean_object* v_ngen_175_; lean_object* v_auxDeclNGen_176_; lean_object* v_cache_177_; lean_object* v_recordedDeps_178_; lean_object* v_messages_179_; lean_object* v_infoState_180_; lean_object* v_snapshotTasks_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_200_; 
v___x_168_ = lean_st_ref_get(v___y_166_);
v_traceState_169_ = lean_ctor_get(v___x_168_, 4);
lean_inc_ref(v_traceState_169_);
lean_dec(v___x_168_);
v_traces_170_ = lean_ctor_get(v_traceState_169_, 0);
lean_inc_ref(v_traces_170_);
lean_dec_ref(v_traceState_169_);
v___x_171_ = lean_st_ref_take(v___y_166_);
v_traceState_172_ = lean_ctor_get(v___x_171_, 4);
v_env_173_ = lean_ctor_get(v___x_171_, 0);
v_nextMacroScope_174_ = lean_ctor_get(v___x_171_, 1);
v_ngen_175_ = lean_ctor_get(v___x_171_, 2);
v_auxDeclNGen_176_ = lean_ctor_get(v___x_171_, 3);
v_cache_177_ = lean_ctor_get(v___x_171_, 5);
v_recordedDeps_178_ = lean_ctor_get(v___x_171_, 6);
v_messages_179_ = lean_ctor_get(v___x_171_, 7);
v_infoState_180_ = lean_ctor_get(v___x_171_, 8);
v_snapshotTasks_181_ = lean_ctor_get(v___x_171_, 9);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_200_ == 0)
{
v___x_183_ = v___x_171_;
v_isShared_184_ = v_isSharedCheck_200_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_snapshotTasks_181_);
lean_inc(v_infoState_180_);
lean_inc(v_messages_179_);
lean_inc(v_recordedDeps_178_);
lean_inc(v_cache_177_);
lean_inc(v_traceState_172_);
lean_inc(v_auxDeclNGen_176_);
lean_inc(v_ngen_175_);
lean_inc(v_nextMacroScope_174_);
lean_inc(v_env_173_);
lean_dec(v___x_171_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_200_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
uint64_t v_tid_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_198_; 
v_tid_185_ = lean_ctor_get_uint64(v_traceState_172_, sizeof(void*)*1);
v_isSharedCheck_198_ = !lean_is_exclusive(v_traceState_172_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v_traceState_172_, 0);
lean_dec(v_unused_199_);
v___x_187_ = v_traceState_172_;
v_isShared_188_ = v_isSharedCheck_198_;
goto v_resetjp_186_;
}
else
{
lean_dec(v_traceState_172_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_198_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_189_);
lean_ctor_set_uint64(v_reuseFailAlloc_197_, sizeof(void*)*1, v_tid_185_);
v___x_191_ = v_reuseFailAlloc_197_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 4, v___x_191_);
v___x_193_ = v___x_183_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_env_173_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_nextMacroScope_174_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_ngen_175_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_auxDeclNGen_176_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_196_, 5, v_cache_177_);
lean_ctor_set(v_reuseFailAlloc_196_, 6, v_recordedDeps_178_);
lean_ctor_set(v_reuseFailAlloc_196_, 7, v_messages_179_);
lean_ctor_set(v_reuseFailAlloc_196_, 8, v_infoState_180_);
lean_ctor_set(v_reuseFailAlloc_196_, 9, v_snapshotTasks_181_);
v___x_193_ = v_reuseFailAlloc_196_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_st_ref_put(v___y_166_, v___x_193_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v_traces_170_);
return v___x_195_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_166_ = stack[0].m_obj;
lean_object* v_res_201_;
v_res_201_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v___y_166_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___boxed(lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v___y_202_);
lean_dec(v___y_202_);
return v_res_204_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v___y_208_);
return v___x_210_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_205_ = stack[0].m_obj;
lean_object* v___y_206_ = stack[1].m_obj;
lean_object* v___y_207_ = stack[2].m_obj;
lean_object* v___y_208_ = stack[3].m_obj;
lean_object* v_res_211_;
v_res_211_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(v___y_205_, v___y_206_, v___y_207_, v___y_208_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___boxed(lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_217_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(lean_object* v_opts_218_, lean_object* v_opt_219_){
_start:
{
lean_object* v_name_220_; lean_object* v_defValue_221_; lean_object* v_map_222_; lean_object* v___x_223_; 
v_name_220_ = lean_ctor_get(v_opt_219_, 0);
v_defValue_221_ = lean_ctor_get(v_opt_219_, 1);
v_map_222_ = lean_ctor_get(v_opts_218_, 0);
v___x_223_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_222_, v_name_220_);
if (lean_obj_tag(v___x_223_) == 0)
{
uint8_t v___x_224_; 
v___x_224_ = lean_unbox(v_defValue_221_);
return v___x_224_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_223_, 1);
if (lean_obj_tag(v_val_225_) == 1)
{
uint8_t v_v_226_; 
v_v_226_ = lean_ctor_get_uint8(v_val_225_, 0);
lean_dec_ref_known(v_val_225_, 0);
return v_v_226_;
}
else
{
uint8_t v___x_227_; 
lean_dec(v_val_225_);
v___x_227_ = lean_unbox(v_defValue_221_);
return v___x_227_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_218_ = stack[0].m_obj;
lean_object* v_opt_219_ = stack[1].m_obj;
uint8_t v_res_228_;
v_res_228_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_218_, v_opt_219_);
stack->m_num = v_res_228_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___boxed(lean_object* v_opts_229_, lean_object* v_opt_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_229_, v_opt_230_);
lean_dec_ref(v_opt_230_);
lean_dec_ref(v_opts_229_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(lean_object* v_x_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Meta_saveState___redArg(v___y_235_, v___y_237_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_241_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v___x_239_, 1);
lean_inc(v___y_237_);
lean_inc_ref(v___y_236_);
lean_inc(v___y_235_);
lean_inc_ref(v___y_234_);
v___x_241_ = lean_apply_5(v_x_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, lean_box(0));
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_250_; 
lean_dec(v_a_240_);
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_250_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v_a_242_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_246_);
v___x_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_280_; 
v_a_251_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_280_ == 0)
{
v___x_253_ = v___x_241_;
v_isShared_254_ = v_isSharedCheck_280_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_241_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_280_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
uint8_t v___y_256_; uint8_t v___x_278_; 
v___x_278_ = l_Lean_Exception_isInterrupt(v_a_251_);
if (v___x_278_ == 0)
{
uint8_t v___x_279_; 
lean_inc(v_a_251_);
v___x_279_ = l_Lean_Exception_isRuntime(v_a_251_);
v___y_256_ = v___x_279_;
goto v___jp_255_;
}
else
{
v___y_256_ = v___x_278_;
goto v___jp_255_;
}
v___jp_255_:
{
if (v___y_256_ == 0)
{
lean_object* v___x_257_; 
lean_del_object(v___x_253_);
lean_dec(v_a_251_);
v___x_257_ = l_Lean_Meta_SavedState_restore___redArg(v_a_240_, v___y_235_, v___y_237_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v___x_257_, 0);
lean_dec(v_unused_266_);
v___x_259_ = v___x_257_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_dec(v___x_257_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = lean_box(0);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
v_a_267_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_257_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_257_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_object* v___x_276_; 
lean_dec(v_a_240_);
if (v_isShared_254_ == 0)
{
v___x_276_ = v___x_253_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_251_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v_x_233_);
v_a_281_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_239_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_239_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_233_ = stack[0].m_obj;
lean_object* v___y_234_ = stack[1].m_obj;
lean_object* v___y_235_ = stack[2].m_obj;
lean_object* v___y_236_ = stack[3].m_obj;
lean_object* v___y_237_ = stack[4].m_obj;
lean_object* v_res_289_;
v_res_289_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v_x_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___boxed(lean_object* v_x_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v_x_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_296_;
}
}
lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object* v_00_u03b1_297_, lean_object* v_x_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v_x_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
return v___x_304_;
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_298_ = stack[1].m_obj;
lean_object* v___y_299_ = stack[2].m_obj;
lean_object* v___y_300_ = stack[3].m_obj;
lean_object* v___y_301_ = stack[4].m_obj;
lean_object* v___y_302_ = stack[5].m_obj;
lean_object* v_res_305_;
v_res_305_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_box(0), v_x_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object* v_00_u03b1_306_, lean_object* v_x_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_00_u03b1_306_, v_x_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
return v_res_313_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(lean_object* v_msgData_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; lean_object* v_env_321_; uint8_t v___x_322_; lean_object* v_env_323_; lean_object* v___x_324_; lean_object* v_toCold_325_; lean_object* v_mctx_326_; lean_object* v_lctx_327_; lean_object* v_options_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_320_ = lean_st_ref_get(v___y_318_);
v_env_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc_ref(v_env_321_);
lean_dec(v___x_320_);
v___x_322_ = 0;
v_env_323_ = l_Lean_Environment_setRecordingDeps(v_env_321_, v___x_322_);
v___x_324_ = lean_st_ref_get(v___y_316_);
v_toCold_325_ = lean_ctor_get(v___y_317_, 0);
v_mctx_326_ = lean_ctor_get(v___x_324_, 0);
lean_inc_ref(v_mctx_326_);
lean_dec(v___x_324_);
v_lctx_327_ = lean_ctor_get(v___y_315_, 2);
v_options_328_ = lean_ctor_get(v_toCold_325_, 2);
lean_inc_ref(v_options_328_);
lean_inc_ref(v_lctx_327_);
v___x_329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_329_, 0, v_env_323_);
lean_ctor_set(v___x_329_, 1, v_mctx_326_);
lean_ctor_set(v___x_329_, 2, v_lctx_327_);
lean_ctor_set(v___x_329_, 3, v_options_328_);
v___x_330_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v_msgData_314_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_314_ = stack[0].m_obj;
lean_object* v___y_315_ = stack[1].m_obj;
lean_object* v___y_316_ = stack[2].m_obj;
lean_object* v___y_317_ = stack[3].m_obj;
lean_object* v___y_318_ = stack[4].m_obj;
lean_object* v_res_332_;
v_res_332_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msgData_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
stack->m_obj
 = v_res_332_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___boxed(lean_object* v_msgData_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msgData_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0));
v___x_342_ = l_Lean_stringToMessageData(v___x_341_);
return v___x_342_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object* v_x_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_343_ = stack[0].m_obj;
lean_object* v___y_344_ = stack[1].m_obj;
lean_object* v___y_345_ = stack[2].m_obj;
lean_object* v___y_346_ = stack[3].m_obj;
lean_object* v___y_347_ = stack[4].m_obj;
lean_object* v_res_351_;
v_res_351_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(v_x_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
stack->m_obj
 = v_res_351_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object* v_x_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(v_x_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec_ref(v_x_352_);
return v_res_358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0));
v___x_361_ = l_Lean_stringToMessageData(v___x_360_);
return v___x_361_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object* v_x_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_362_ = stack[0].m_obj;
lean_object* v___y_363_ = stack[1].m_obj;
lean_object* v___y_364_ = stack[2].m_obj;
lean_object* v___y_365_ = stack[3].m_obj;
lean_object* v___y_366_ = stack[4].m_obj;
lean_object* v_res_370_;
v_res_370_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(v_x_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object* v_x_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(v_x_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec_ref(v_x_371_);
return v_res_377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object* v_x_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1);
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_381_ = stack[0].m_obj;
lean_object* v___y_382_ = stack[1].m_obj;
lean_object* v___y_383_ = stack[2].m_obj;
lean_object* v___y_384_ = stack[3].m_obj;
lean_object* v___y_385_ = stack[4].m_obj;
lean_object* v_res_389_;
v_res_389_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(v_x_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object* v_x_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(v_x_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec_ref(v_x_390_);
return v_res_396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0));
v___x_399_ = l_Lean_stringToMessageData(v___x_398_);
return v___x_399_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object* v_x_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_400_ = stack[0].m_obj;
lean_object* v___y_401_ = stack[1].m_obj;
lean_object* v___y_402_ = stack[2].m_obj;
lean_object* v___y_403_ = stack[3].m_obj;
lean_object* v___y_404_ = stack[4].m_obj;
lean_object* v_res_408_;
v_res_408_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(v_x_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object* v_x_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(v_x_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec_ref(v_x_409_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(lean_object* v_opts_416_, lean_object* v_opt_417_){
_start:
{
lean_object* v_name_418_; lean_object* v_defValue_419_; lean_object* v_map_420_; lean_object* v___x_421_; 
v_name_418_ = lean_ctor_get(v_opt_417_, 0);
v_defValue_419_ = lean_ctor_get(v_opt_417_, 1);
v_map_420_ = lean_ctor_get(v_opts_416_, 0);
v___x_421_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_420_, v_name_418_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_inc(v_defValue_419_);
return v_defValue_419_;
}
else
{
lean_object* v_val_422_; 
v_val_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v___x_421_, 1);
if (lean_obj_tag(v_val_422_) == 3)
{
lean_object* v_v_423_; 
v_v_423_ = lean_ctor_get(v_val_422_, 0);
lean_inc(v_v_423_);
lean_dec_ref_known(v_val_422_, 1);
return v_v_423_;
}
else
{
lean_dec(v_val_422_);
lean_inc(v_defValue_419_);
return v_defValue_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6___boxed(lean_object* v_opts_424_, lean_object* v_opt_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_424_, v_opt_425_);
lean_dec_ref(v_opt_425_);
lean_dec_ref(v_opts_424_);
return v_res_426_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object* v_e_427_){
_start:
{
if (lean_obj_tag(v_e_427_) == 0)
{
uint8_t v___x_428_; 
v___x_428_ = 2;
return v___x_428_;
}
else
{
lean_object* v_a_429_; 
v_a_429_ = lean_ctor_get(v_e_427_, 0);
if (lean_obj_tag(v_a_429_) == 0)
{
uint8_t v___x_430_; 
v___x_430_ = 1;
return v___x_430_;
}
else
{
uint8_t v___x_431_; 
v___x_431_ = 0;
return v___x_431_;
}
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_427_ = stack[0].m_obj;
uint8_t v_res_432_;
v_res_432_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_e_427_);
stack->m_num = v_res_432_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object* v_e_433_){
_start:
{
uint8_t v_res_434_; lean_object* v_r_435_; 
v_res_434_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_e_433_);
lean_dec_ref(v_e_433_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(lean_object* v_x_436_){
_start:
{
if (lean_obj_tag(v_x_436_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
v_a_438_ = lean_ctor_get(v_x_436_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_436_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v_x_436_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v_x_436_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 1);
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
v_a_446_ = lean_ctor_get(v_x_436_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_436_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v_x_436_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v_x_436_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 0);
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_436_ = stack[0].m_obj;
lean_object* v_res_454_;
v_res_454_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_436_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg___boxed(lean_object* v_x_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_455_);
return v_res_457_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(size_t v_sz_458_, size_t v_i_459_, lean_object* v_bs_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = lean_usize_dec_lt(v_i_459_, v_sz_458_);
if (v___x_461_ == 0)
{
return v_bs_460_;
}
else
{
lean_object* v_v_462_; lean_object* v_msg_463_; lean_object* v___x_464_; lean_object* v_bs_x27_465_; size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; 
v_v_462_ = lean_array_uget_borrowed(v_bs_460_, v_i_459_);
v_msg_463_ = lean_ctor_get(v_v_462_, 1);
lean_inc_ref(v_msg_463_);
v___x_464_ = lean_unsigned_to_nat(0u);
v_bs_x27_465_ = lean_array_uset(v_bs_460_, v_i_459_, v___x_464_);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_add(v_i_459_, v___x_466_);
v___x_468_ = lean_array_uset(v_bs_x27_465_, v_i_459_, v_msg_463_);
v_i_459_ = v___x_467_;
v_bs_460_ = v___x_468_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_458_ = stack[0].m_num;
size_t v_i_459_ = stack[1].m_num;
lean_object* v_bs_460_ = stack[2].m_obj;
lean_object* v_res_470_;
v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_458_, v_i_459_, v_bs_460_);
stack->m_obj
 = v_res_470_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6___boxed(lean_object* v_sz_471_, lean_object* v_i_472_, lean_object* v_bs_473_){
_start:
{
size_t v_sz_boxed_474_; size_t v_i_boxed_475_; lean_object* v_res_476_; 
v_sz_boxed_474_ = lean_unbox_usize(v_sz_471_);
lean_dec(v_sz_471_);
v_i_boxed_475_ = lean_unbox_usize(v_i_472_);
lean_dec(v_i_472_);
v_res_476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_boxed_474_, v_i_boxed_475_, v_bs_473_);
return v_res_476_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object* v_oldTraces_477_, lean_object* v_data_478_, lean_object* v_ref_479_, lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_toCold_486_; lean_object* v_currRecDepth_487_; lean_object* v_ref_488_; uint16_t v_optionFlags_489_; uint8_t v_suppressElabErrors_490_; uint8_t v_isRecordingDeps_491_; lean_object* v_ref_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v_traceState_495_; lean_object* v_traces_496_; lean_object* v___x_497_; size_t v_sz_498_; size_t v___x_499_; lean_object* v___x_500_; lean_object* v_msg_501_; lean_object* v___x_502_; lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_541_; 
v_toCold_486_ = lean_ctor_get(v___y_483_, 0);
v_currRecDepth_487_ = lean_ctor_get(v___y_483_, 1);
v_ref_488_ = lean_ctor_get(v___y_483_, 2);
v_optionFlags_489_ = lean_ctor_get_uint16(v___y_483_, sizeof(void*)*3);
v_suppressElabErrors_490_ = lean_ctor_get_uint8(v___y_483_, sizeof(void*)*3 + 2);
v_isRecordingDeps_491_ = lean_ctor_get_uint8(v___y_483_, sizeof(void*)*3 + 3);
v_ref_492_ = l_Lean_replaceRef(v_ref_479_, v_ref_488_);
lean_inc(v_currRecDepth_487_);
lean_inc_ref(v_toCold_486_);
v___x_493_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_493_, 0, v_toCold_486_);
lean_ctor_set(v___x_493_, 1, v_currRecDepth_487_);
lean_ctor_set(v___x_493_, 2, v_ref_492_);
lean_ctor_set_uint16(v___x_493_, sizeof(void*)*3, v_optionFlags_489_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*3 + 2, v_suppressElabErrors_490_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*3 + 3, v_isRecordingDeps_491_);
v___x_494_ = lean_st_ref_get(v___y_484_);
v_traceState_495_ = lean_ctor_get(v___x_494_, 4);
lean_inc_ref(v_traceState_495_);
lean_dec(v___x_494_);
v_traces_496_ = lean_ctor_get(v_traceState_495_, 0);
lean_inc_ref(v_traces_496_);
lean_dec_ref(v_traceState_495_);
v___x_497_ = l_Lean_PersistentArray_toArray___redArg(v_traces_496_);
lean_dec_ref(v_traces_496_);
v_sz_498_ = lean_array_size(v___x_497_);
v___x_499_ = ((size_t)0ULL);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_498_, v___x_499_, v___x_497_);
v_msg_501_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_501_, 0, v_data_478_);
lean_ctor_set(v_msg_501_, 1, v_msg_480_);
lean_ctor_set(v_msg_501_, 2, v___x_500_);
v___x_502_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_501_, v___y_481_, v___y_482_, v___x_493_, v___y_484_);
lean_dec_ref_known(v___x_493_, 3);
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_541_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_541_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_541_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v_traceState_508_; lean_object* v_env_509_; lean_object* v_nextMacroScope_510_; lean_object* v_ngen_511_; lean_object* v_auxDeclNGen_512_; lean_object* v_cache_513_; lean_object* v_recordedDeps_514_; lean_object* v_messages_515_; lean_object* v_infoState_516_; lean_object* v_snapshotTasks_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_540_; 
v___x_507_ = lean_st_ref_take(v___y_484_);
v_traceState_508_ = lean_ctor_get(v___x_507_, 4);
v_env_509_ = lean_ctor_get(v___x_507_, 0);
v_nextMacroScope_510_ = lean_ctor_get(v___x_507_, 1);
v_ngen_511_ = lean_ctor_get(v___x_507_, 2);
v_auxDeclNGen_512_ = lean_ctor_get(v___x_507_, 3);
v_cache_513_ = lean_ctor_get(v___x_507_, 5);
v_recordedDeps_514_ = lean_ctor_get(v___x_507_, 6);
v_messages_515_ = lean_ctor_get(v___x_507_, 7);
v_infoState_516_ = lean_ctor_get(v___x_507_, 8);
v_snapshotTasks_517_ = lean_ctor_get(v___x_507_, 9);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_540_ == 0)
{
v___x_519_ = v___x_507_;
v_isShared_520_ = v_isSharedCheck_540_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_snapshotTasks_517_);
lean_inc(v_infoState_516_);
lean_inc(v_messages_515_);
lean_inc(v_recordedDeps_514_);
lean_inc(v_cache_513_);
lean_inc(v_traceState_508_);
lean_inc(v_auxDeclNGen_512_);
lean_inc(v_ngen_511_);
lean_inc(v_nextMacroScope_510_);
lean_inc(v_env_509_);
lean_dec(v___x_507_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_540_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
uint64_t v_tid_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_538_; 
v_tid_521_ = lean_ctor_get_uint64(v_traceState_508_, sizeof(void*)*1);
v_isSharedCheck_538_ = !lean_is_exclusive(v_traceState_508_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v_traceState_508_, 0);
lean_dec(v_unused_539_);
v___x_523_ = v_traceState_508_;
v_isShared_524_ = v_isSharedCheck_538_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_traceState_508_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_538_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_525_ = lean_box(0);
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v_ref_479_);
lean_ctor_set(v___x_526_, 1, v_a_503_);
v___x_527_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_477_, v___x_526_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_527_);
v___x_529_ = v___x_523_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_527_);
lean_ctor_set_uint64(v_reuseFailAlloc_537_, sizeof(void*)*1, v_tid_521_);
v___x_529_ = v_reuseFailAlloc_537_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_531_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 4, v___x_529_);
v___x_531_ = v___x_519_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_env_509_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_nextMacroScope_510_);
lean_ctor_set(v_reuseFailAlloc_536_, 2, v_ngen_511_);
lean_ctor_set(v_reuseFailAlloc_536_, 3, v_auxDeclNGen_512_);
lean_ctor_set(v_reuseFailAlloc_536_, 4, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_536_, 5, v_cache_513_);
lean_ctor_set(v_reuseFailAlloc_536_, 6, v_recordedDeps_514_);
lean_ctor_set(v_reuseFailAlloc_536_, 7, v_messages_515_);
lean_ctor_set(v_reuseFailAlloc_536_, 8, v_infoState_516_);
lean_ctor_set(v_reuseFailAlloc_536_, 9, v_snapshotTasks_517_);
v___x_531_ = v_reuseFailAlloc_536_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_st_ref_put(v___y_484_, v___x_531_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_525_);
v___x_534_ = v___x_505_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_525_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_477_ = stack[0].m_obj;
lean_object* v_data_478_ = stack[1].m_obj;
lean_object* v_ref_479_ = stack[2].m_obj;
lean_object* v_msg_480_ = stack[3].m_obj;
lean_object* v___y_481_ = stack[4].m_obj;
lean_object* v___y_482_ = stack[5].m_obj;
lean_object* v___y_483_ = stack[6].m_obj;
lean_object* v___y_484_ = stack[7].m_obj;
lean_object* v_res_542_;
v_res_542_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_477_, v_data_478_, v_ref_479_, v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
stack->m_obj
 = v_res_542_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object* v_oldTraces_543_, lean_object* v_data_544_, lean_object* v_ref_545_, lean_object* v_msg_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_543_, v_data_544_, v_ref_545_, v_msg_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_552_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0(void){
_start:
{
lean_object* v___x_553_; double v___x_554_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_float_of_nat(v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1));
v___x_557_ = l_Lean_stringToMessageData(v___x_556_);
return v___x_557_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3(void){
_start:
{
lean_object* v___x_558_; double v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(1000u);
v___x_559_ = lean_float_of_nat(v___x_558_);
return v___x_559_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_cls_560_, uint8_t v_collapsed_561_, lean_object* v_tag_562_, lean_object* v_opts_563_, uint8_t v_clsEnabled_564_, lean_object* v_oldTraces_565_, lean_object* v_msg_566_, lean_object* v_resStartStop_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v_data_578_; lean_object* v_fst_589_; lean_object* v_snd_590_; lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___y_594_; lean_object* v_a_595_; uint8_t v___y_610_; double v___y_642_; 
v_fst_573_ = lean_ctor_get(v_resStartStop_567_, 0);
lean_inc(v_fst_573_);
v_snd_574_ = lean_ctor_get(v_resStartStop_567_, 1);
lean_inc(v_snd_574_);
lean_dec_ref(v_resStartStop_567_);
v_fst_589_ = lean_ctor_get(v_snd_574_, 0);
lean_inc(v_fst_589_);
v_snd_590_ = lean_ctor_get(v_snd_574_, 1);
lean_inc(v_snd_590_);
lean_dec(v_snd_574_);
v___x_591_ = l_Lean_trace_profiler;
v___x_592_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_563_, v___x_591_);
if (v___x_592_ == 0)
{
v___y_610_ = v___x_592_;
goto v___jp_609_;
}
else
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = l_Lean_trace_profiler_useHeartbeats;
v___x_648_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_563_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; double v___x_651_; double v___x_652_; double v___x_653_; 
v___x_649_ = l_Lean_trace_profiler_threshold;
v___x_650_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_563_, v___x_649_);
v___x_651_ = lean_float_of_nat(v___x_650_);
v___x_652_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_653_ = lean_float_div(v___x_651_, v___x_652_);
v___y_642_ = v___x_653_;
goto v___jp_641_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; double v___x_656_; 
v___x_654_ = l_Lean_trace_profiler_threshold;
v___x_655_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_563_, v___x_654_);
v___x_656_ = lean_float_of_nat(v___x_655_);
v___y_642_ = v___x_656_;
goto v___jp_641_;
}
}
v___jp_575_:
{
lean_object* v___x_579_; 
lean_inc(v___y_577_);
v___x_579_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_565_, v_data_578_, v___y_577_, v___y_576_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_580_; 
lean_dec_ref_known(v___x_579_, 1);
v___x_580_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_573_);
return v___x_580_;
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec(v_fst_573_);
v_a_581_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_579_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_579_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
v___jp_593_:
{
uint8_t v_result_596_; lean_object* v___x_597_; lean_object* v___x_598_; double v___x_599_; lean_object* v_data_600_; 
v_result_596_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_fst_573_);
v___x_597_ = lean_box(v_result_596_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
v___x_599_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_562_);
lean_inc_ref(v___x_598_);
lean_inc(v_cls_560_);
v_data_600_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_600_, 0, v_cls_560_);
lean_ctor_set(v_data_600_, 1, v___x_598_);
lean_ctor_set(v_data_600_, 2, v_tag_562_);
lean_ctor_set_float(v_data_600_, sizeof(void*)*3, v___x_599_);
lean_ctor_set_float(v_data_600_, sizeof(void*)*3 + 8, v___x_599_);
lean_ctor_set_uint8(v_data_600_, sizeof(void*)*3 + 16, v_collapsed_561_);
if (v___x_592_ == 0)
{
lean_dec_ref_known(v___x_598_, 1);
lean_dec(v_snd_590_);
lean_dec(v_fst_589_);
lean_dec_ref(v_tag_562_);
lean_dec(v_cls_560_);
v___y_576_ = v_a_595_;
v___y_577_ = v___y_594_;
v_data_578_ = v_data_600_;
goto v___jp_575_;
}
else
{
lean_object* v_data_601_; double v___x_602_; double v___x_603_; 
lean_dec_ref_known(v_data_600_, 3);
v_data_601_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_601_, 0, v_cls_560_);
lean_ctor_set(v_data_601_, 1, v___x_598_);
lean_ctor_set(v_data_601_, 2, v_tag_562_);
v___x_602_ = lean_unbox_float(v_fst_589_);
lean_dec(v_fst_589_);
lean_ctor_set_float(v_data_601_, sizeof(void*)*3, v___x_602_);
v___x_603_ = lean_unbox_float(v_snd_590_);
lean_dec(v_snd_590_);
lean_ctor_set_float(v_data_601_, sizeof(void*)*3 + 8, v___x_603_);
lean_ctor_set_uint8(v_data_601_, sizeof(void*)*3 + 16, v_collapsed_561_);
v___y_576_ = v_a_595_;
v___y_577_ = v___y_594_;
v_data_578_ = v_data_601_;
goto v___jp_575_;
}
}
v___jp_604_:
{
lean_object* v_ref_605_; lean_object* v___x_606_; 
v_ref_605_ = lean_ctor_get(v___y_570_, 2);
lean_inc(v___y_571_);
lean_inc_ref(v___y_570_);
lean_inc(v___y_569_);
lean_inc_ref(v___y_568_);
lean_inc(v_fst_573_);
v___x_606_ = lean_apply_6(v_msg_566_, v_fst_573_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, lean_box(0));
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref_known(v___x_606_, 1);
v___y_594_ = v_ref_605_;
v_a_595_ = v_a_607_;
goto v___jp_593_;
}
else
{
lean_object* v___x_608_; 
lean_dec_ref_known(v___x_606_, 1);
v___x_608_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_594_ = v_ref_605_;
v_a_595_ = v___x_608_;
goto v___jp_593_;
}
}
v___jp_609_:
{
if (v_clsEnabled_564_ == 0)
{
if (v___y_610_ == 0)
{
lean_object* v___x_611_; lean_object* v_traceState_612_; lean_object* v_env_613_; lean_object* v_nextMacroScope_614_; lean_object* v_ngen_615_; lean_object* v_auxDeclNGen_616_; lean_object* v_cache_617_; lean_object* v_recordedDeps_618_; lean_object* v_messages_619_; lean_object* v_infoState_620_; lean_object* v_snapshotTasks_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_snd_590_);
lean_dec(v_fst_589_);
lean_dec_ref(v_msg_566_);
lean_dec_ref(v_tag_562_);
lean_dec(v_cls_560_);
v___x_611_ = lean_st_ref_take(v___y_571_);
v_traceState_612_ = lean_ctor_get(v___x_611_, 4);
v_env_613_ = lean_ctor_get(v___x_611_, 0);
v_nextMacroScope_614_ = lean_ctor_get(v___x_611_, 1);
v_ngen_615_ = lean_ctor_get(v___x_611_, 2);
v_auxDeclNGen_616_ = lean_ctor_get(v___x_611_, 3);
v_cache_617_ = lean_ctor_get(v___x_611_, 5);
v_recordedDeps_618_ = lean_ctor_get(v___x_611_, 6);
v_messages_619_ = lean_ctor_get(v___x_611_, 7);
v_infoState_620_ = lean_ctor_get(v___x_611_, 8);
v_snapshotTasks_621_ = lean_ctor_get(v___x_611_, 9);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_640_ == 0)
{
v___x_623_ = v___x_611_;
v_isShared_624_ = v_isSharedCheck_640_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_snapshotTasks_621_);
lean_inc(v_infoState_620_);
lean_inc(v_messages_619_);
lean_inc(v_recordedDeps_618_);
lean_inc(v_cache_617_);
lean_inc(v_traceState_612_);
lean_inc(v_auxDeclNGen_616_);
lean_inc(v_ngen_615_);
lean_inc(v_nextMacroScope_614_);
lean_inc(v_env_613_);
lean_dec(v___x_611_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_640_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint64_t v_tid_625_; lean_object* v_traces_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_639_; 
v_tid_625_ = lean_ctor_get_uint64(v_traceState_612_, sizeof(void*)*1);
v_traces_626_ = lean_ctor_get(v_traceState_612_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_traceState_612_);
if (v_isSharedCheck_639_ == 0)
{
v___x_628_ = v_traceState_612_;
v_isShared_629_ = v_isSharedCheck_639_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_traces_626_);
lean_dec(v_traceState_612_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_639_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_565_, v_traces_626_);
lean_dec_ref(v_traces_626_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_630_);
lean_ctor_set_uint64(v_reuseFailAlloc_638_, sizeof(void*)*1, v_tid_625_);
v___x_632_ = v_reuseFailAlloc_638_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 4, v___x_632_);
v___x_634_ = v___x_623_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_env_613_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_nextMacroScope_614_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_ngen_615_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_auxDeclNGen_616_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_637_, 5, v_cache_617_);
lean_ctor_set(v_reuseFailAlloc_637_, 6, v_recordedDeps_618_);
lean_ctor_set(v_reuseFailAlloc_637_, 7, v_messages_619_);
lean_ctor_set(v_reuseFailAlloc_637_, 8, v_infoState_620_);
lean_ctor_set(v_reuseFailAlloc_637_, 9, v_snapshotTasks_621_);
v___x_634_ = v_reuseFailAlloc_637_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_st_ref_put(v___y_571_, v___x_634_);
v___x_636_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_573_);
return v___x_636_;
}
}
}
}
}
else
{
goto v___jp_604_;
}
}
else
{
goto v___jp_604_;
}
}
v___jp_641_:
{
double v___x_643_; double v___x_644_; double v___x_645_; uint8_t v___x_646_; 
v___x_643_ = lean_unbox_float(v_snd_590_);
v___x_644_ = lean_unbox_float(v_fst_589_);
v___x_645_ = lean_float_sub(v___x_643_, v___x_644_);
v___x_646_ = lean_float_decLt(v___y_642_, v___x_645_);
v___y_610_ = v___x_646_;
goto v___jp_609_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_560_ = stack[0].m_obj;
uint8_t v_collapsed_561_ = stack[1].m_num;
lean_object* v_tag_562_ = stack[2].m_obj;
lean_object* v_opts_563_ = stack[3].m_obj;
uint8_t v_clsEnabled_564_ = stack[4].m_num;
lean_object* v_oldTraces_565_ = stack[5].m_obj;
lean_object* v_msg_566_ = stack[6].m_obj;
lean_object* v_resStartStop_567_ = stack[7].m_obj;
lean_object* v___y_568_ = stack[8].m_obj;
lean_object* v___y_569_ = stack[9].m_obj;
lean_object* v___y_570_ = stack[10].m_obj;
lean_object* v___y_571_ = stack[11].m_obj;
lean_object* v_res_657_;
v_res_657_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_cls_560_, v_collapsed_561_, v_tag_562_, v_opts_563_, v_clsEnabled_564_, v_oldTraces_565_, v_msg_566_, v_resStartStop_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
stack->m_obj
 = v_res_657_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_cls_658_, lean_object* v_collapsed_659_, lean_object* v_tag_660_, lean_object* v_opts_661_, lean_object* v_clsEnabled_662_, lean_object* v_oldTraces_663_, lean_object* v_msg_664_, lean_object* v_resStartStop_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
uint8_t v_collapsed_boxed_671_; uint8_t v_clsEnabled_boxed_672_; lean_object* v_res_673_; 
v_collapsed_boxed_671_ = lean_unbox(v_collapsed_659_);
v_clsEnabled_boxed_672_ = lean_unbox(v_clsEnabled_662_);
v_res_673_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_cls_658_, v_collapsed_boxed_671_, v_tag_660_, v_opts_661_, v_clsEnabled_boxed_672_, v_oldTraces_663_, v_msg_664_, v_resStartStop_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec_ref(v_opts_661_);
return v_res_673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0));
v___x_676_ = l_Lean_stringToMessageData(v___x_675_);
return v___x_676_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* v_head_677_, lean_object* v_x_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_695_; 
v___x_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_684_, 0, v_head_677_);
v___x_685_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v___x_684_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_695_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_695_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_690_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v_a_686_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_head_677_ = stack[0].m_obj;
lean_object* v_x_678_ = stack[1].m_obj;
lean_object* v___y_679_ = stack[2].m_obj;
lean_object* v___y_680_ = stack[3].m_obj;
lean_object* v___y_681_ = stack[4].m_obj;
lean_object* v___y_682_ = stack[5].m_obj;
lean_object* v_res_696_;
v_res_696_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_head_677_, v_x_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
stack->m_obj
 = v_res_696_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* v_head_697_, lean_object* v_x_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_head_697_, v_x_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v_x_698_);
return v_res_704_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object* v_keys_705_, lean_object* v_i_706_, lean_object* v_k_707_){
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
return v___x_709_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_705_ = stack[0].m_obj;
lean_object* v_i_706_ = stack[1].m_obj;
lean_object* v_k_707_ = stack[2].m_obj;
uint8_t v_res_715_;
v_res_715_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_705_, v_i_706_, v_k_707_);
stack->m_num = v_res_715_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object* v_keys_716_, lean_object* v_i_717_, lean_object* v_k_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_716_, v_i_717_, v_k_718_);
lean_dec(v_k_718_);
lean_dec_ref(v_keys_716_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_721_, size_t v_x_722_, lean_object* v_x_723_){
_start:
{
if (lean_obj_tag(v_x_721_) == 0)
{
lean_object* v_es_724_; lean_object* v___x_725_; size_t v___x_726_; size_t v___x_727_; lean_object* v_j_728_; lean_object* v___x_729_; 
v_es_724_ = lean_ctor_get(v_x_721_, 0);
v___x_725_ = lean_box(2);
v___x_726_ = ((size_t)31ULL);
v___x_727_ = lean_usize_land(v_x_722_, v___x_726_);
v_j_728_ = lean_usize_to_nat(v___x_727_);
v___x_729_ = lean_array_get_borrowed(v___x_725_, v_es_724_, v_j_728_);
lean_dec(v_j_728_);
switch(lean_obj_tag(v___x_729_))
{
case 0:
{
lean_object* v_key_730_; uint8_t v___x_731_; 
v_key_730_ = lean_ctor_get(v___x_729_, 0);
v___x_731_ = l_Lean_instBEqMVarId_beq(v_x_723_, v_key_730_);
return v___x_731_;
}
case 1:
{
lean_object* v_node_732_; size_t v___x_733_; size_t v___x_734_; 
v_node_732_ = lean_ctor_get(v___x_729_, 0);
v___x_733_ = ((size_t)5ULL);
v___x_734_ = lean_usize_shift_right(v_x_722_, v___x_733_);
v_x_721_ = v_node_732_;
v_x_722_ = v___x_734_;
goto _start;
}
default: 
{
uint8_t v___x_736_; 
v___x_736_ = 0;
return v___x_736_;
}
}
}
else
{
lean_object* v_ks_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_ks_737_ = lean_ctor_get(v_x_721_, 0);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_ks_737_, v___x_738_, v_x_723_);
return v___x_739_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_721_ = stack[0].m_obj;
size_t v_x_722_ = stack[1].m_num;
lean_object* v_x_723_ = stack[2].m_obj;
uint8_t v_res_740_;
v_res_740_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_721_, v_x_722_, v_x_723_);
stack->m_num = v_res_740_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
size_t v_x_74814__boxed_744_; uint8_t v_res_745_; lean_object* v_r_746_; 
v_x_74814__boxed_744_ = lean_unbox_usize(v_x_742_);
lean_dec(v_x_742_);
v_res_745_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_741_, v_x_74814__boxed_744_, v_x_743_);
lean_dec(v_x_743_);
lean_dec_ref(v_x_741_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
uint64_t v___x_749_; size_t v___x_750_; uint8_t v___x_751_; 
v___x_749_ = l_Lean_instHashableMVarId_hash(v_x_748_);
v___x_750_ = lean_uint64_to_usize(v___x_749_);
v___x_751_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_747_, v___x_750_, v_x_748_);
return v___x_751_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_747_ = stack[0].m_obj;
lean_object* v_x_748_ = stack[1].m_obj;
uint8_t v_res_752_;
v_res_752_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_747_, v_x_748_);
stack->m_num = v_res_752_;
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
lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object* v_mvarId_757_, lean_object* v___y_758_){
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
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_757_ = stack[0].m_obj;
lean_object* v___y_758_ = stack[1].m_obj;
lean_object* v_res_766_;
v_res_766_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_757_, v___y_758_);
stack->m_obj
 = v_res_766_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object* v_mvarId_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec(v_mvarId_767_);
return v_res_770_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_ref_777_; lean_object* v___x_778_; lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_787_; 
v_ref_777_ = lean_ctor_get(v___y_774_, 2);
v___x_778_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_787_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
lean_inc(v_ref_777_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v_ref_777_);
lean_ctor_set(v___x_783_, 1, v_a_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 1);
lean_ctor_set(v___x_781_, 0, v___x_783_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_771_ = stack[0].m_obj;
lean_object* v___y_772_ = stack[1].m_obj;
lean_object* v___y_773_ = stack[2].m_obj;
lean_object* v___y_774_ = stack[3].m_obj;
lean_object* v___y_775_ = stack[4].m_obj;
lean_object* v_res_788_;
v_res_788_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
stack->m_obj
 = v_res_788_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
return v_res_795_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_798_ = l_Lean_stringToMessageData(v___x_797_);
return v___x_798_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_a_799_, lean_object* v_x_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_807_ = l_Lean_Exception_toMessageData(v_a_799_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_799_ = stack[0].m_obj;
lean_object* v_x_800_ = stack[1].m_obj;
lean_object* v___y_801_ = stack[2].m_obj;
lean_object* v___y_802_ = stack[3].m_obj;
lean_object* v___y_803_ = stack[4].m_obj;
lean_object* v___y_804_ = stack[5].m_obj;
lean_object* v_res_810_;
v_res_810_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_a_799_, v_x_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
stack->m_obj
 = v_res_810_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_a_811_, lean_object* v_x_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_a_811_, v_x_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec_ref(v_x_812_);
return v_res_818_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_e_819_){
_start:
{
if (lean_obj_tag(v_e_819_) == 0)
{
uint8_t v___x_820_; 
v___x_820_ = 2;
return v___x_820_;
}
else
{
uint8_t v___x_821_; 
v___x_821_ = 0;
return v___x_821_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_819_ = stack[0].m_obj;
uint8_t v_res_822_;
v_res_822_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_e_819_);
stack->m_num = v_res_822_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_e_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_e_823_);
lean_dec_ref(v_e_823_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_826_, uint8_t v_collapsed_827_, lean_object* v_tag_828_, lean_object* v_opts_829_, uint8_t v_clsEnabled_830_, lean_object* v_oldTraces_831_, lean_object* v_msg_832_, lean_object* v_resStartStop_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_fst_839_; lean_object* v_snd_840_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v_data_844_; lean_object* v_fst_855_; lean_object* v_snd_856_; lean_object* v___x_857_; uint8_t v___x_858_; lean_object* v___y_860_; lean_object* v_a_861_; uint8_t v___y_876_; double v___y_908_; 
v_fst_839_ = lean_ctor_get(v_resStartStop_833_, 0);
lean_inc(v_fst_839_);
v_snd_840_ = lean_ctor_get(v_resStartStop_833_, 1);
lean_inc(v_snd_840_);
lean_dec_ref(v_resStartStop_833_);
v_fst_855_ = lean_ctor_get(v_snd_840_, 0);
lean_inc(v_fst_855_);
v_snd_856_ = lean_ctor_get(v_snd_840_, 1);
lean_inc(v_snd_856_);
lean_dec(v_snd_840_);
v___x_857_ = l_Lean_trace_profiler;
v___x_858_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_829_, v___x_857_);
if (v___x_858_ == 0)
{
v___y_876_ = v___x_858_;
goto v___jp_875_;
}
else
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = l_Lean_trace_profiler_useHeartbeats;
v___x_914_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_829_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; double v___x_917_; double v___x_918_; double v___x_919_; 
v___x_915_ = l_Lean_trace_profiler_threshold;
v___x_916_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_829_, v___x_915_);
v___x_917_ = lean_float_of_nat(v___x_916_);
v___x_918_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_919_ = lean_float_div(v___x_917_, v___x_918_);
v___y_908_ = v___x_919_;
goto v___jp_907_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; double v___x_922_; 
v___x_920_ = l_Lean_trace_profiler_threshold;
v___x_921_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_829_, v___x_920_);
v___x_922_ = lean_float_of_nat(v___x_921_);
v___y_908_ = v___x_922_;
goto v___jp_907_;
}
}
v___jp_841_:
{
lean_object* v___x_845_; 
lean_inc(v___y_842_);
v___x_845_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_831_, v_data_844_, v___y_842_, v___y_843_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_846_; 
lean_dec_ref_known(v___x_845_, 1);
v___x_846_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_839_);
return v___x_846_;
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_fst_839_);
v_a_847_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_845_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_845_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
v___jp_859_:
{
uint8_t v_result_862_; lean_object* v___x_863_; lean_object* v___x_864_; double v___x_865_; lean_object* v_data_866_; 
v_result_862_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_fst_839_);
v___x_863_ = lean_box(v_result_862_);
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
v___x_865_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_828_);
lean_inc_ref(v___x_864_);
lean_inc(v_cls_826_);
v_data_866_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_866_, 0, v_cls_826_);
lean_ctor_set(v_data_866_, 1, v___x_864_);
lean_ctor_set(v_data_866_, 2, v_tag_828_);
lean_ctor_set_float(v_data_866_, sizeof(void*)*3, v___x_865_);
lean_ctor_set_float(v_data_866_, sizeof(void*)*3 + 8, v___x_865_);
lean_ctor_set_uint8(v_data_866_, sizeof(void*)*3 + 16, v_collapsed_827_);
if (v___x_858_ == 0)
{
lean_dec_ref_known(v___x_864_, 1);
lean_dec(v_snd_856_);
lean_dec(v_fst_855_);
lean_dec_ref(v_tag_828_);
lean_dec(v_cls_826_);
v___y_842_ = v___y_860_;
v___y_843_ = v_a_861_;
v_data_844_ = v_data_866_;
goto v___jp_841_;
}
else
{
lean_object* v_data_867_; double v___x_868_; double v___x_869_; 
lean_dec_ref_known(v_data_866_, 3);
v_data_867_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_867_, 0, v_cls_826_);
lean_ctor_set(v_data_867_, 1, v___x_864_);
lean_ctor_set(v_data_867_, 2, v_tag_828_);
v___x_868_ = lean_unbox_float(v_fst_855_);
lean_dec(v_fst_855_);
lean_ctor_set_float(v_data_867_, sizeof(void*)*3, v___x_868_);
v___x_869_ = lean_unbox_float(v_snd_856_);
lean_dec(v_snd_856_);
lean_ctor_set_float(v_data_867_, sizeof(void*)*3 + 8, v___x_869_);
lean_ctor_set_uint8(v_data_867_, sizeof(void*)*3 + 16, v_collapsed_827_);
v___y_842_ = v___y_860_;
v___y_843_ = v_a_861_;
v_data_844_ = v_data_867_;
goto v___jp_841_;
}
}
v___jp_870_:
{
lean_object* v_ref_871_; lean_object* v___x_872_; 
v_ref_871_ = lean_ctor_get(v___y_836_, 2);
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v_fst_839_);
v___x_872_ = lean_apply_6(v_msg_832_, v_fst_839_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, lean_box(0));
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref_known(v___x_872_, 1);
v___y_860_ = v_ref_871_;
v_a_861_ = v_a_873_;
goto v___jp_859_;
}
else
{
lean_object* v___x_874_; 
lean_dec_ref_known(v___x_872_, 1);
v___x_874_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_860_ = v_ref_871_;
v_a_861_ = v___x_874_;
goto v___jp_859_;
}
}
v___jp_875_:
{
if (v_clsEnabled_830_ == 0)
{
if (v___y_876_ == 0)
{
lean_object* v___x_877_; lean_object* v_traceState_878_; lean_object* v_env_879_; lean_object* v_nextMacroScope_880_; lean_object* v_ngen_881_; lean_object* v_auxDeclNGen_882_; lean_object* v_cache_883_; lean_object* v_recordedDeps_884_; lean_object* v_messages_885_; lean_object* v_infoState_886_; lean_object* v_snapshotTasks_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_906_; 
lean_dec(v_snd_856_);
lean_dec(v_fst_855_);
lean_dec_ref(v_msg_832_);
lean_dec_ref(v_tag_828_);
lean_dec(v_cls_826_);
v___x_877_ = lean_st_ref_take(v___y_837_);
v_traceState_878_ = lean_ctor_get(v___x_877_, 4);
v_env_879_ = lean_ctor_get(v___x_877_, 0);
v_nextMacroScope_880_ = lean_ctor_get(v___x_877_, 1);
v_ngen_881_ = lean_ctor_get(v___x_877_, 2);
v_auxDeclNGen_882_ = lean_ctor_get(v___x_877_, 3);
v_cache_883_ = lean_ctor_get(v___x_877_, 5);
v_recordedDeps_884_ = lean_ctor_get(v___x_877_, 6);
v_messages_885_ = lean_ctor_get(v___x_877_, 7);
v_infoState_886_ = lean_ctor_get(v___x_877_, 8);
v_snapshotTasks_887_ = lean_ctor_get(v___x_877_, 9);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_906_ == 0)
{
v___x_889_ = v___x_877_;
v_isShared_890_ = v_isSharedCheck_906_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_snapshotTasks_887_);
lean_inc(v_infoState_886_);
lean_inc(v_messages_885_);
lean_inc(v_recordedDeps_884_);
lean_inc(v_cache_883_);
lean_inc(v_traceState_878_);
lean_inc(v_auxDeclNGen_882_);
lean_inc(v_ngen_881_);
lean_inc(v_nextMacroScope_880_);
lean_inc(v_env_879_);
lean_dec(v___x_877_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_906_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint64_t v_tid_891_; lean_object* v_traces_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_905_; 
v_tid_891_ = lean_ctor_get_uint64(v_traceState_878_, sizeof(void*)*1);
v_traces_892_ = lean_ctor_get(v_traceState_878_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v_traceState_878_);
if (v_isSharedCheck_905_ == 0)
{
v___x_894_ = v_traceState_878_;
v_isShared_895_ = v_isSharedCheck_905_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_traces_892_);
lean_dec(v_traceState_878_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_905_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_831_, v_traces_892_);
lean_dec_ref(v_traces_892_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_896_);
lean_ctor_set_uint64(v_reuseFailAlloc_904_, sizeof(void*)*1, v_tid_891_);
v___x_898_ = v_reuseFailAlloc_904_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 4, v___x_898_);
v___x_900_ = v___x_889_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_env_879_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_nextMacroScope_880_);
lean_ctor_set(v_reuseFailAlloc_903_, 2, v_ngen_881_);
lean_ctor_set(v_reuseFailAlloc_903_, 3, v_auxDeclNGen_882_);
lean_ctor_set(v_reuseFailAlloc_903_, 4, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_903_, 5, v_cache_883_);
lean_ctor_set(v_reuseFailAlloc_903_, 6, v_recordedDeps_884_);
lean_ctor_set(v_reuseFailAlloc_903_, 7, v_messages_885_);
lean_ctor_set(v_reuseFailAlloc_903_, 8, v_infoState_886_);
lean_ctor_set(v_reuseFailAlloc_903_, 9, v_snapshotTasks_887_);
v___x_900_ = v_reuseFailAlloc_903_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_st_ref_put(v___y_837_, v___x_900_);
v___x_902_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_839_);
return v___x_902_;
}
}
}
}
}
else
{
goto v___jp_870_;
}
}
else
{
goto v___jp_870_;
}
}
v___jp_907_:
{
double v___x_909_; double v___x_910_; double v___x_911_; uint8_t v___x_912_; 
v___x_909_ = lean_unbox_float(v_snd_856_);
v___x_910_ = lean_unbox_float(v_fst_855_);
v___x_911_ = lean_float_sub(v___x_909_, v___x_910_);
v___x_912_ = lean_float_decLt(v___y_908_, v___x_911_);
v___y_876_ = v___x_912_;
goto v___jp_875_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_826_ = stack[0].m_obj;
uint8_t v_collapsed_827_ = stack[1].m_num;
lean_object* v_tag_828_ = stack[2].m_obj;
lean_object* v_opts_829_ = stack[3].m_obj;
uint8_t v_clsEnabled_830_ = stack[4].m_num;
lean_object* v_oldTraces_831_ = stack[5].m_obj;
lean_object* v_msg_832_ = stack[6].m_obj;
lean_object* v_resStartStop_833_ = stack[7].m_obj;
lean_object* v___y_834_ = stack[8].m_obj;
lean_object* v___y_835_ = stack[9].m_obj;
lean_object* v___y_836_ = stack[10].m_obj;
lean_object* v___y_837_ = stack[11].m_obj;
lean_object* v_res_923_;
v_res_923_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_826_, v_collapsed_827_, v_tag_828_, v_opts_829_, v_clsEnabled_830_, v_oldTraces_831_, v_msg_832_, v_resStartStop_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
stack->m_obj
 = v_res_923_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_924_, lean_object* v_collapsed_925_, lean_object* v_tag_926_, lean_object* v_opts_927_, lean_object* v_clsEnabled_928_, lean_object* v_oldTraces_929_, lean_object* v_msg_930_, lean_object* v_resStartStop_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
uint8_t v_collapsed_boxed_937_; uint8_t v_clsEnabled_boxed_938_; lean_object* v_res_939_; 
v_collapsed_boxed_937_ = lean_unbox(v_collapsed_925_);
v_clsEnabled_boxed_938_ = lean_unbox(v_clsEnabled_928_);
v_res_939_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_924_, v_collapsed_boxed_937_, v_tag_926_, v_opts_927_, v_clsEnabled_boxed_938_, v_oldTraces_929_, v_msg_930_, v_resStartStop_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_opts_927_);
return v_res_939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__0));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(lean_object* v_head_943_, lean_object* v_x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_950_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1);
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v_head_943_);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_head_943_ = stack[0].m_obj;
lean_object* v_x_944_ = stack[1].m_obj;
lean_object* v___y_945_ = stack[2].m_obj;
lean_object* v___y_946_ = stack[3].m_obj;
lean_object* v___y_947_ = stack[4].m_obj;
lean_object* v___y_948_ = stack[5].m_obj;
lean_object* v_res_954_;
v_res_954_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(v_head_943_, v_x_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
stack->m_obj
 = v_res_954_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___boxed(lean_object* v_head_955_, lean_object* v_x_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(v_head_955_, v_x_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec_ref(v_x_956_);
return v_res_962_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_963_; double v___x_964_; 
v___x_963_ = lean_unsigned_to_nat(1000000000u);
v___x_964_ = lean_float_of_nat(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* v_tail_976_, lean_object* v_cfg_977_, lean_object* v_trace_978_, lean_object* v_next_979_, lean_object* v_goals_980_, lean_object* v_n_981_, lean_object* v_acc_982_, lean_object* v_r_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_976_, v_cfg_977_, v_trace_978_, v_next_979_, v_goals_980_, v_n_981_, v_acc_982_, v_r_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_989_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_990_, lean_object* v_trace_991_, lean_object* v_next_992_, lean_object* v_goals_993_, lean_object* v_n_994_, lean_object* v_curr_995_, lean_object* v_acc_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___y_1003_; uint8_t v___y_1004_; lean_object* v___y_1005_; uint8_t v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v_a_1010_; lean_object* v___y_1020_; lean_object* v___y_1021_; uint8_t v___y_1022_; lean_object* v___y_1023_; uint8_t v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v_a_1027_; lean_object* v___y_1040_; uint8_t v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; uint8_t v___y_1091_; uint8_t v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v_a_1095_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; uint8_t v___y_1108_; uint8_t v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v_a_1112_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; uint8_t v___y_1118_; uint8_t v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v_a_1122_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; uint8_t v___y_1128_; uint8_t v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1136_; lean_object* v___y_1137_; uint8_t v___y_1138_; uint8_t v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v_a_1143_; lean_object* v___y_1156_; lean_object* v___y_1157_; uint8_t v___y_1158_; uint8_t v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v_a_1163_; lean_object* v___y_1166_; lean_object* v___y_1167_; uint8_t v___y_1168_; uint8_t v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v_a_1173_; lean_object* v___y_1176_; lean_object* v___y_1177_; uint8_t v___y_1178_; uint8_t v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v_zero_1186_; uint8_t v_isZero_1187_; 
v_zero_1186_ = lean_unsigned_to_nat(0u);
v_isZero_1187_ = lean_nat_dec_eq(v_n_994_, v_zero_1186_);
if (v_isZero_1187_ == 1)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec(v_acc_996_);
lean_dec(v_curr_995_);
lean_dec(v_n_994_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
v___x_1188_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1189_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1188_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1189_;
}
else
{
lean_object* v_proc_1190_; lean_object* v_suspend_1191_; lean_object* v_discharge_1192_; lean_object* v___f_1193_; lean_object* v___y_1195_; lean_object* v___y_1196_; uint8_t v___y_1197_; uint8_t v___y_1198_; lean_object* v___y_1199_; lean_object* v___f_1235_; lean_object* v___y_1237_; lean_object* v___y_1238_; uint8_t v___y_1239_; uint8_t v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v_a_1243_; lean_object* v___y_1253_; lean_object* v___y_1254_; uint8_t v___y_1255_; uint8_t v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v_a_1259_; lean_object* v___y_1272_; lean_object* v___y_1273_; uint8_t v___y_1274_; uint8_t v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___f_1319_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; uint8_t v___y_1325_; uint8_t v___y_1326_; lean_object* v_a_1327_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; uint8_t v___y_1343_; uint8_t v___y_1344_; lean_object* v___y_1345_; lean_object* v_a_1346_; lean_object* v___f_1355_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; uint8_t v___y_1361_; uint8_t v___y_1362_; uint8_t v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v_a_1367_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; uint8_t v___y_1383_; uint8_t v___y_1384_; uint8_t v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v_a_1390_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; uint8_t v___y_1404_; uint8_t v___y_1405_; uint8_t v___y_1406_; uint8_t v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1452_; lean_object* v___y_1453_; uint8_t v___y_1454_; uint8_t v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; uint8_t v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v_a_1462_; lean_object* v___y_1475_; lean_object* v___y_1476_; uint8_t v___y_1477_; uint8_t v___y_1478_; lean_object* v___y_1479_; uint8_t v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v_a_1485_; lean_object* v___y_1495_; lean_object* v___y_1496_; uint8_t v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; uint8_t v___y_1501_; uint8_t v___y_1502_; uint8_t v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1547_; uint8_t v___y_1548_; lean_object* v___y_1549_; uint8_t v___y_1550_; uint8_t v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v_a_1557_; lean_object* v___y_1567_; uint8_t v___y_1568_; lean_object* v___y_1569_; uint8_t v___y_1570_; uint8_t v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v_a_1577_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; uint8_t v___y_1594_; uint8_t v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; uint8_t v___y_1599_; lean_object* v_a_1600_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; uint8_t v___y_1614_; uint8_t v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; uint8_t v___y_1619_; lean_object* v_a_1620_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; uint8_t v___y_1638_; lean_object* v___y_1639_; uint8_t v___y_1640_; uint8_t v___y_1641_; uint8_t v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; uint8_t v___y_1688_; lean_object* v___y_1689_; uint8_t v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; uint8_t v___y_1694_; lean_object* v_a_1695_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; uint8_t v___y_1712_; lean_object* v___y_1713_; uint8_t v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; uint8_t v___y_1717_; lean_object* v_a_1718_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; uint8_t v___y_1731_; uint8_t v___y_1732_; uint8_t v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v_a_1738_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; uint8_t v___y_1754_; lean_object* v___y_1755_; uint8_t v___y_1756_; uint8_t v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v_a_1761_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; uint8_t v___y_1777_; uint8_t v___y_1778_; uint8_t v___y_1779_; uint8_t v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; uint8_t v___y_1826_; lean_object* v___y_1827_; uint8_t v___y_1828_; lean_object* v_a_1829_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; uint8_t v___y_1846_; uint8_t v___y_1847_; lean_object* v_a_1848_; lean_object* v___y_1858_; lean_object* v___y_1859_; uint8_t v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; uint8_t v___y_1863_; lean_object* v___y_1864_; lean_object* v_one_1905_; lean_object* v_n_1906_; lean_object* v___y_1908_; lean_object* v___y_1909_; uint8_t v___y_1910_; uint8_t v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1954_; lean_object* v___y_1955_; uint8_t v___y_1956_; lean_object* v___y_1957_; uint8_t v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; uint8_t v___y_1963_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; uint8_t v___y_1991_; uint8_t v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; uint8_t v___y_1996_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; uint8_t v___y_2042_; uint8_t v___y_2043_; uint8_t v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; uint8_t v___y_2050_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; uint8_t v___y_2074_; uint8_t v___y_2075_; uint8_t v___y_2076_; uint8_t v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; uint8_t v___y_2127_; uint8_t v___y_2128_; uint8_t v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; uint8_t v___y_2134_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; uint8_t v___y_2160_; uint8_t v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; uint8_t v___y_2212_; lean_object* v_a_2230_; lean_object* v___y_2323_; lean_object* v___x_2333_; 
v_proc_1190_ = lean_ctor_get(v_cfg_990_, 1);
v_suspend_1191_ = lean_ctor_get(v_cfg_990_, 2);
v_discharge_1192_ = lean_ctor_get(v_cfg_990_, 3);
v___f_1193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1905_ = lean_unsigned_to_nat(1u);
v_n_1906_ = lean_nat_sub(v_n_994_, v_one_1905_);
lean_dec(v_n_994_);
lean_inc_ref(v_proc_1190_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v_curr_995_);
lean_inc(v_goals_993_);
v___x_2333_ = lean_apply_7(v_proc_1190_, v_goals_993_, v_curr_995_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v_a_2230_ = v_a_2334_;
goto v___jp_2229_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2403_; 
v_a_2335_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2337_ = v___x_2333_;
v_isShared_2338_ = v_isSharedCheck_2403_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2333_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2403_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___f_2339_; uint8_t v___y_2341_; lean_object* v___y_2342_; lean_object* v___y_2343_; uint8_t v___y_2344_; uint8_t v___y_2381_; uint8_t v___x_2401_; 
lean_inc(v_a_2335_);
v___f_2339_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2339_, 0, v_a_2335_);
v___x_2401_ = l_Lean_Exception_isInterrupt(v_a_2335_);
if (v___x_2401_ == 0)
{
uint8_t v___x_2402_; 
lean_inc(v_a_2335_);
v___x_2402_ = l_Lean_Exception_isRuntime(v_a_2335_);
v___y_2381_ = v___x_2402_;
goto v___jp_2380_;
}
else
{
v___y_2381_ = v___x_2401_;
goto v___jp_2380_;
}
v___jp_2340_:
{
lean_object* v___x_2345_; lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2379_; 
v___x_2345_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2379_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2379_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; uint8_t v___x_2351_; 
v___x_2350_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2351_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2342_, v___x_2350_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2352_ = lean_io_mono_nanos_now();
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v_a_2335_);
v___x_2354_ = v___x_2348_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2335_);
v___x_2354_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2355_; double v___x_2356_; double v___x_2357_; double v___x_2358_; double v___x_2359_; double v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2355_ = lean_io_mono_nanos_now();
v___x_2356_ = lean_float_of_nat(v___x_2352_);
v___x_2357_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2358_ = lean_float_div(v___x_2356_, v___x_2357_);
v___x_2359_ = lean_float_of_nat(v___x_2355_);
v___x_2360_ = lean_float_div(v___x_2359_, v___x_2357_);
v___x_2361_ = lean_box_float(v___x_2358_);
v___x_2362_ = lean_box_float(v___x_2360_);
v___x_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2354_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
lean_inc_ref(v___y_2343_);
lean_inc(v_trace_991_);
v___x_2365_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_991_, v___y_2344_, v___y_2343_, v___y_2342_, v___y_2341_, v_a_2346_, v___f_2339_, v___x_2364_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_2323_ = v___x_2365_;
goto v___jp_2322_;
}
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2367_ = lean_io_get_num_heartbeats();
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v_a_2335_);
v___x_2369_ = v___x_2348_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2335_);
v___x_2369_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; double v___x_2371_; double v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2370_ = lean_io_get_num_heartbeats();
v___x_2371_ = lean_float_of_nat(v___x_2367_);
v___x_2372_ = lean_float_of_nat(v___x_2370_);
v___x_2373_ = lean_box_float(v___x_2371_);
v___x_2374_ = lean_box_float(v___x_2372_);
v___x_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2373_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2369_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
lean_inc_ref(v___y_2343_);
lean_inc(v_trace_991_);
v___x_2377_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_991_, v___y_2344_, v___y_2343_, v___y_2342_, v___y_2341_, v_a_2346_, v___f_2339_, v___x_2376_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_2323_ = v___x_2377_;
goto v___jp_2322_;
}
}
}
}
v___jp_2380_:
{
if (v___y_2381_ == 0)
{
lean_object* v_toCold_2382_; lean_object* v_options_2383_; uint8_t v_hasTrace_2384_; 
v_toCold_2382_ = lean_ctor_get(v_a_999_, 0);
v_options_2383_ = lean_ctor_get(v_toCold_2382_, 2);
v_hasTrace_2384_ = lean_ctor_get_uint8(v_options_2383_, sizeof(void*)*1);
if (v_hasTrace_2384_ == 0)
{
lean_object* v___x_2386_; 
lean_dec_ref(v___f_2339_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_curr_995_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
if (v_isShared_2338_ == 0)
{
v___x_2386_ = v___x_2337_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2335_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_inheritedTraceOptions_2388_ = lean_ctor_get(v_toCold_2382_, 11);
v___x_2389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_2391_ = l_Lean_Name_append(v___x_2390_, v_trace_991_);
v___x_2392_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2388_, v_options_2383_, v___x_2391_);
lean_dec(v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; uint8_t v___x_2394_; 
v___x_2393_ = l_Lean_trace_profiler;
v___x_2394_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2383_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2396_; 
lean_dec_ref(v___f_2339_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_curr_995_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
if (v_isShared_2338_ == 0)
{
v___x_2396_ = v___x_2337_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2335_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
else
{
lean_del_object(v___x_2337_);
v___y_2341_ = v___x_2392_;
v___y_2342_ = v_options_2383_;
v___y_2343_ = v___x_2389_;
v___y_2344_ = v_hasTrace_2384_;
goto v___jp_2340_;
}
}
else
{
lean_del_object(v___x_2337_);
v___y_2341_ = v___x_2392_;
v___y_2342_ = v_options_2383_;
v___y_2343_ = v___x_2389_;
v___y_2344_ = v_hasTrace_2384_;
goto v___jp_2340_;
}
}
}
else
{
lean_object* v___x_2399_; 
lean_dec_ref(v___f_2339_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_curr_995_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
if (v_isShared_2338_ == 0)
{
v___x_2399_ = v___x_2337_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2335_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
v___jp_1194_:
{
lean_object* v___x_1200_; lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1234_; 
v___x_1200_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1234_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1234_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1206_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1199_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1207_ = lean_io_mono_nanos_now();
if (v_isShared_1204_ == 0)
{
lean_ctor_set_tag(v___x_1203_, 1);
lean_ctor_set(v___x_1203_, 0, v___y_1196_);
v___x_1209_ = v___x_1203_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___y_1196_);
v___x_1209_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; double v___x_1211_; double v___x_1212_; double v___x_1213_; double v___x_1214_; double v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1210_ = lean_io_mono_nanos_now();
v___x_1211_ = lean_float_of_nat(v___x_1207_);
v___x_1212_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1213_ = lean_float_div(v___x_1211_, v___x_1212_);
v___x_1214_ = lean_float_of_nat(v___x_1210_);
v___x_1215_ = lean_float_div(v___x_1214_, v___x_1212_);
v___x_1216_ = lean_box_float(v___x_1213_);
v___x_1217_ = lean_box_float(v___x_1215_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1216_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1209_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
lean_inc_ref(v___y_1195_);
v___x_1220_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1197_, v___y_1195_, v___y_1199_, v___y_1198_, v_a_1201_, v___f_1193_, v___x_1219_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1220_;
}
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_io_get_num_heartbeats();
if (v_isShared_1204_ == 0)
{
lean_ctor_set_tag(v___x_1203_, 1);
lean_ctor_set(v___x_1203_, 0, v___y_1196_);
v___x_1224_ = v___x_1203_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___y_1196_);
v___x_1224_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; double v___x_1226_; double v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1225_ = lean_io_get_num_heartbeats();
v___x_1226_ = lean_float_of_nat(v___x_1222_);
v___x_1227_ = lean_float_of_nat(v___x_1225_);
v___x_1228_ = lean_box_float(v___x_1226_);
v___x_1229_ = lean_box_float(v___x_1227_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1224_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
lean_inc_ref(v___y_1195_);
v___x_1232_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1197_, v___y_1195_, v___y_1199_, v___y_1198_, v_a_1201_, v___f_1193_, v___x_1231_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1232_;
}
}
}
}
v___jp_1236_:
{
lean_object* v___x_1244_; double v___x_1245_; double v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1244_ = lean_io_get_num_heartbeats();
v___x_1245_ = lean_float_of_nat(v___y_1242_);
v___x_1246_ = lean_float_of_nat(v___x_1244_);
v___x_1247_ = lean_box_float(v___x_1245_);
v___x_1248_ = lean_box_float(v___x_1246_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_a_1243_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
lean_inc_ref(v___y_1238_);
v___x_1251_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1239_, v___y_1238_, v___y_1237_, v___y_1240_, v___y_1241_, v___f_1235_, v___x_1250_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1251_;
}
v___jp_1252_:
{
lean_object* v___x_1260_; double v___x_1261_; double v___x_1262_; double v___x_1263_; double v___x_1264_; double v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1260_ = lean_io_mono_nanos_now();
v___x_1261_ = lean_float_of_nat(v___y_1258_);
v___x_1262_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1263_ = lean_float_div(v___x_1261_, v___x_1262_);
v___x_1264_ = lean_float_of_nat(v___x_1260_);
v___x_1265_ = lean_float_div(v___x_1264_, v___x_1262_);
v___x_1266_ = lean_box_float(v___x_1263_);
v___x_1267_ = lean_box_float(v___x_1265_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_a_1259_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
lean_inc_ref(v___y_1254_);
v___x_1270_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1255_, v___y_1254_, v___y_1253_, v___y_1256_, v___y_1257_, v___f_1235_, v___x_1269_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1270_;
}
v___jp_1271_:
{
lean_object* v___x_1279_; lean_object* v_a_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1279_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1282_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1272_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_io_mono_nanos_now();
lean_inc(v_trace_991_);
v___x_1284_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1277_, v___y_1278_, v___y_1276_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set_tag(v___x_1287_, 1);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
v___y_1253_ = v___y_1272_;
v___y_1254_ = v___y_1273_;
v___y_1255_ = v___y_1274_;
v___y_1256_ = v___y_1275_;
v___y_1257_ = v_a_1280_;
v___y_1258_ = v___x_1283_;
v_a_1259_ = v___x_1290_;
goto v___jp_1252_;
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
v_a_1293_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1284_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1284_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set_tag(v___x_1295_, 0);
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
v___y_1253_ = v___y_1272_;
v___y_1254_ = v___y_1273_;
v___y_1255_ = v___y_1274_;
v___y_1256_ = v___y_1275_;
v___y_1257_ = v_a_1280_;
v___y_1258_ = v___x_1283_;
v_a_1259_ = v___x_1298_;
goto v___jp_1252_;
}
}
}
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_991_);
v___x_1302_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1277_, v___y_1278_, v___y_1276_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
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
v___y_1237_ = v___y_1272_;
v___y_1238_ = v___y_1273_;
v___y_1239_ = v___y_1274_;
v___y_1240_ = v___y_1275_;
v___y_1241_ = v_a_1280_;
v___y_1242_ = v___x_1301_;
v_a_1243_ = v___x_1308_;
goto v___jp_1236_;
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
v___y_1237_ = v___y_1272_;
v___y_1238_ = v___y_1273_;
v___y_1239_ = v___y_1274_;
v___y_1240_ = v___y_1275_;
v___y_1241_ = v_a_1280_;
v___y_1242_ = v___x_1301_;
v_a_1243_ = v___x_1316_;
goto v___jp_1236_;
}
}
}
}
}
v___jp_1320_:
{
lean_object* v___x_1328_; double v___x_1329_; double v___x_1330_; double v___x_1331_; double v___x_1332_; double v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1328_ = lean_io_mono_nanos_now();
v___x_1329_ = lean_float_of_nat(v___y_1323_);
v___x_1330_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1331_ = lean_float_div(v___x_1329_, v___x_1330_);
v___x_1332_ = lean_float_of_nat(v___x_1328_);
v___x_1333_ = lean_float_div(v___x_1332_, v___x_1330_);
v___x_1334_ = lean_box_float(v___x_1331_);
v___x_1335_ = lean_box_float(v___x_1333_);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_a_1327_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
lean_inc_ref(v___y_1322_);
v___x_1338_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1326_, v___y_1322_, v___y_1321_, v___y_1325_, v___y_1324_, v___f_1319_, v___x_1337_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1338_;
}
v___jp_1339_:
{
lean_object* v___x_1347_; double v___x_1348_; double v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1347_ = lean_io_get_num_heartbeats();
v___x_1348_ = lean_float_of_nat(v___y_1345_);
v___x_1349_ = lean_float_of_nat(v___x_1347_);
v___x_1350_ = lean_box_float(v___x_1348_);
v___x_1351_ = lean_box_float(v___x_1349_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_a_1346_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
lean_inc_ref(v___y_1341_);
v___x_1354_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1344_, v___y_1341_, v___y_1340_, v___y_1343_, v___y_1342_, v___f_1319_, v___x_1353_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1354_;
}
v___jp_1356_:
{
lean_object* v___x_1368_; double v___x_1369_; double v___x_1370_; double v___x_1371_; double v___x_1372_; double v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1368_ = lean_io_mono_nanos_now();
v___x_1369_ = lean_float_of_nat(v___y_1359_);
v___x_1370_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1371_ = lean_float_div(v___x_1369_, v___x_1370_);
v___x_1372_ = lean_float_of_nat(v___x_1368_);
v___x_1373_ = lean_float_div(v___x_1372_, v___x_1370_);
v___x_1374_ = lean_box_float(v___x_1371_);
v___x_1375_ = lean_box_float(v___x_1373_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1374_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_a_1367_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
lean_inc_ref(v___y_1360_);
lean_inc(v_trace_991_);
v___x_1378_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1362_, v___y_1360_, v___y_1358_, v___y_1363_, v___y_1364_, v___f_1355_, v___x_1377_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1125_ = v___y_1358_;
v___y_1126_ = v___y_1357_;
v___y_1127_ = v___y_1360_;
v___y_1128_ = v___y_1361_;
v___y_1129_ = v___y_1362_;
v___y_1130_ = v___y_1365_;
v___y_1131_ = v___y_1366_;
v___y_1132_ = v___x_1378_;
goto v___jp_1124_;
}
v___jp_1379_:
{
lean_object* v___x_1391_; double v___x_1392_; double v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1391_ = lean_io_get_num_heartbeats();
v___x_1392_ = lean_float_of_nat(v___y_1389_);
v___x_1393_ = lean_float_of_nat(v___x_1391_);
v___x_1394_ = lean_box_float(v___x_1392_);
v___x_1395_ = lean_box_float(v___x_1393_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v_a_1390_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
lean_inc_ref(v___y_1382_);
lean_inc(v_trace_991_);
v___x_1398_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1384_, v___y_1382_, v___y_1381_, v___y_1385_, v___y_1386_, v___f_1355_, v___x_1397_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1125_ = v___y_1381_;
v___y_1126_ = v___y_1380_;
v___y_1127_ = v___y_1382_;
v___y_1128_ = v___y_1383_;
v___y_1129_ = v___y_1384_;
v___y_1130_ = v___y_1387_;
v___y_1131_ = v___y_1388_;
v___y_1132_ = v___x_1398_;
goto v___jp_1124_;
}
v___jp_1399_:
{
lean_object* v___x_1412_; 
v___x_1412_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
if (v___y_1404_ == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref(v___x_1412_);
v___x_1414_ = lean_io_mono_nanos_now();
lean_inc(v_trace_991_);
v___x_1415_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1408_, v___y_1411_, v___y_1409_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set_tag(v___x_1418_, 1);
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
v___y_1357_ = v___y_1400_;
v___y_1358_ = v___y_1403_;
v___y_1359_ = v___x_1414_;
v___y_1360_ = v___y_1401_;
v___y_1361_ = v___y_1405_;
v___y_1362_ = v___y_1406_;
v___y_1363_ = v___y_1407_;
v___y_1364_ = v_a_1413_;
v___y_1365_ = v___y_1402_;
v___y_1366_ = v___y_1410_;
v_a_1367_ = v___x_1421_;
goto v___jp_1356_;
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
v_a_1424_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1415_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1415_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set_tag(v___x_1426_, 0);
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
v___y_1357_ = v___y_1400_;
v___y_1358_ = v___y_1403_;
v___y_1359_ = v___x_1414_;
v___y_1360_ = v___y_1401_;
v___y_1361_ = v___y_1405_;
v___y_1362_ = v___y_1406_;
v___y_1363_ = v___y_1407_;
v___y_1364_ = v_a_1413_;
v___y_1365_ = v___y_1402_;
v___y_1366_ = v___y_1410_;
v_a_1367_ = v___x_1429_;
goto v___jp_1356_;
}
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_a_1432_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1412_);
v___x_1433_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_991_);
v___x_1434_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1408_, v___y_1411_, v___y_1409_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
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
v___y_1380_ = v___y_1400_;
v___y_1381_ = v___y_1403_;
v___y_1382_ = v___y_1401_;
v___y_1383_ = v___y_1405_;
v___y_1384_ = v___y_1406_;
v___y_1385_ = v___y_1407_;
v___y_1386_ = v_a_1432_;
v___y_1387_ = v___y_1402_;
v___y_1388_ = v___y_1410_;
v___y_1389_ = v___x_1433_;
v_a_1390_ = v___x_1440_;
goto v___jp_1379_;
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
v___y_1380_ = v___y_1400_;
v___y_1381_ = v___y_1403_;
v___y_1382_ = v___y_1401_;
v___y_1383_ = v___y_1405_;
v___y_1384_ = v___y_1406_;
v___y_1385_ = v___y_1407_;
v___y_1386_ = v_a_1432_;
v___y_1387_ = v___y_1402_;
v___y_1388_ = v___y_1410_;
v___y_1389_ = v___x_1433_;
v_a_1390_ = v___x_1448_;
goto v___jp_1379_;
}
}
}
}
}
v___jp_1451_:
{
lean_object* v___x_1463_; double v___x_1464_; double v___x_1465_; double v___x_1466_; double v___x_1467_; double v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1463_ = lean_io_mono_nanos_now();
v___x_1464_ = lean_float_of_nat(v___y_1456_);
v___x_1465_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1466_ = lean_float_div(v___x_1464_, v___x_1465_);
v___x_1467_ = lean_float_of_nat(v___x_1463_);
v___x_1468_ = lean_float_div(v___x_1467_, v___x_1465_);
v___x_1469_ = lean_box_float(v___x_1466_);
v___x_1470_ = lean_box_float(v___x_1468_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v_a_1462_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
lean_inc_ref(v___y_1453_);
lean_inc(v_trace_991_);
v___x_1473_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1455_, v___y_1453_, v___y_1452_, v___y_1458_, v___y_1459_, v___f_1235_, v___x_1472_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1176_ = v___y_1452_;
v___y_1177_ = v___y_1453_;
v___y_1178_ = v___y_1454_;
v___y_1179_ = v___y_1455_;
v___y_1180_ = v___y_1457_;
v___y_1181_ = v___y_1460_;
v___y_1182_ = v___y_1461_;
v___y_1183_ = v___x_1473_;
goto v___jp_1175_;
}
v___jp_1474_:
{
lean_object* v___x_1486_; double v___x_1487_; double v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1486_ = lean_io_get_num_heartbeats();
v___x_1487_ = lean_float_of_nat(v___y_1482_);
v___x_1488_ = lean_float_of_nat(v___x_1486_);
v___x_1489_ = lean_box_float(v___x_1487_);
v___x_1490_ = lean_box_float(v___x_1488_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v_a_1485_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
lean_inc_ref(v___y_1476_);
lean_inc(v_trace_991_);
v___x_1493_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1478_, v___y_1476_, v___y_1475_, v___y_1480_, v___y_1481_, v___f_1235_, v___x_1492_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1176_ = v___y_1475_;
v___y_1177_ = v___y_1476_;
v___y_1178_ = v___y_1477_;
v___y_1179_ = v___y_1478_;
v___y_1180_ = v___y_1479_;
v___y_1181_ = v___y_1483_;
v___y_1182_ = v___y_1484_;
v___y_1183_ = v___x_1493_;
goto v___jp_1175_;
}
v___jp_1494_:
{
lean_object* v___x_1507_; 
v___x_1507_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
if (v___y_1501_ == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref(v___x_1507_);
v___x_1509_ = lean_io_mono_nanos_now();
lean_inc(v_trace_991_);
v___x_1510_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1499_, v___y_1506_, v___y_1504_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set_tag(v___x_1513_, 1);
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
v___y_1452_ = v___y_1500_;
v___y_1453_ = v___y_1495_;
v___y_1454_ = v___y_1502_;
v___y_1455_ = v___y_1503_;
v___y_1456_ = v___x_1509_;
v___y_1457_ = v___y_1496_;
v___y_1458_ = v___y_1497_;
v___y_1459_ = v_a_1508_;
v___y_1460_ = v___y_1498_;
v___y_1461_ = v___y_1505_;
v_a_1462_ = v___x_1516_;
goto v___jp_1451_;
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
v_a_1519_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1510_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1510_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set_tag(v___x_1521_, 0);
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
v___y_1452_ = v___y_1500_;
v___y_1453_ = v___y_1495_;
v___y_1454_ = v___y_1502_;
v___y_1455_ = v___y_1503_;
v___y_1456_ = v___x_1509_;
v___y_1457_ = v___y_1496_;
v___y_1458_ = v___y_1497_;
v___y_1459_ = v_a_1508_;
v___y_1460_ = v___y_1498_;
v___y_1461_ = v___y_1505_;
v_a_1462_ = v___x_1524_;
goto v___jp_1451_;
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_a_1527_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1527_);
lean_dec_ref(v___x_1507_);
v___x_1528_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_991_);
v___x_1529_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1499_, v___y_1506_, v___y_1504_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 1);
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
v___y_1475_ = v___y_1500_;
v___y_1476_ = v___y_1495_;
v___y_1477_ = v___y_1502_;
v___y_1478_ = v___y_1503_;
v___y_1479_ = v___y_1496_;
v___y_1480_ = v___y_1497_;
v___y_1481_ = v_a_1527_;
v___y_1482_ = v___x_1528_;
v___y_1483_ = v___y_1498_;
v___y_1484_ = v___y_1505_;
v_a_1485_ = v___x_1535_;
goto v___jp_1474_;
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_a_1538_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1529_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1529_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 0);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
v___y_1475_ = v___y_1500_;
v___y_1476_ = v___y_1495_;
v___y_1477_ = v___y_1502_;
v___y_1478_ = v___y_1503_;
v___y_1479_ = v___y_1496_;
v___y_1480_ = v___y_1497_;
v___y_1481_ = v_a_1527_;
v___y_1482_ = v___x_1528_;
v___y_1483_ = v___y_1498_;
v___y_1484_ = v___y_1505_;
v_a_1485_ = v___x_1543_;
goto v___jp_1474_;
}
}
}
}
}
v___jp_1546_:
{
lean_object* v___x_1558_; double v___x_1559_; double v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1558_ = lean_io_get_num_heartbeats();
v___x_1559_ = lean_float_of_nat(v___y_1553_);
v___x_1560_ = lean_float_of_nat(v___x_1558_);
v___x_1561_ = lean_box_float(v___x_1559_);
v___x_1562_ = lean_box_float(v___x_1560_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1564_, 0, v_a_1557_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
lean_inc_ref(v___y_1549_);
lean_inc(v_trace_991_);
v___x_1565_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1551_, v___y_1549_, v___y_1547_, v___y_1548_, v___y_1556_, v___f_1319_, v___x_1564_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1176_ = v___y_1547_;
v___y_1177_ = v___y_1549_;
v___y_1178_ = v___y_1550_;
v___y_1179_ = v___y_1551_;
v___y_1180_ = v___y_1552_;
v___y_1181_ = v___y_1554_;
v___y_1182_ = v___y_1555_;
v___y_1183_ = v___x_1565_;
goto v___jp_1175_;
}
v___jp_1566_:
{
lean_object* v___x_1578_; double v___x_1579_; double v___x_1580_; double v___x_1581_; double v___x_1582_; double v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1578_ = lean_io_mono_nanos_now();
v___x_1579_ = lean_float_of_nat(v___y_1573_);
v___x_1580_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1581_ = lean_float_div(v___x_1579_, v___x_1580_);
v___x_1582_ = lean_float_of_nat(v___x_1578_);
v___x_1583_ = lean_float_div(v___x_1582_, v___x_1580_);
v___x_1584_ = lean_box_float(v___x_1581_);
v___x_1585_ = lean_box_float(v___x_1583_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v_a_1577_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
lean_inc_ref(v___y_1569_);
lean_inc(v_trace_991_);
v___x_1588_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1571_, v___y_1569_, v___y_1567_, v___y_1568_, v___y_1576_, v___f_1319_, v___x_1587_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1176_ = v___y_1567_;
v___y_1177_ = v___y_1569_;
v___y_1178_ = v___y_1570_;
v___y_1179_ = v___y_1571_;
v___y_1180_ = v___y_1572_;
v___y_1181_ = v___y_1574_;
v___y_1182_ = v___y_1575_;
v___y_1183_ = v___x_1588_;
goto v___jp_1175_;
}
v___jp_1589_:
{
lean_object* v___x_1601_; double v___x_1602_; double v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1601_ = lean_io_get_num_heartbeats();
v___x_1602_ = lean_float_of_nat(v___y_1592_);
v___x_1603_ = lean_float_of_nat(v___x_1601_);
v___x_1604_ = lean_box_float(v___x_1602_);
v___x_1605_ = lean_box_float(v___x_1603_);
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1607_, 0, v_a_1600_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
lean_inc_ref(v___y_1593_);
lean_inc(v_trace_991_);
v___x_1608_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1595_, v___y_1593_, v___y_1590_, v___y_1599_, v___y_1591_, v___f_1355_, v___x_1607_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1176_ = v___y_1590_;
v___y_1177_ = v___y_1593_;
v___y_1178_ = v___y_1594_;
v___y_1179_ = v___y_1595_;
v___y_1180_ = v___y_1596_;
v___y_1181_ = v___y_1597_;
v___y_1182_ = v___y_1598_;
v___y_1183_ = v___x_1608_;
goto v___jp_1175_;
}
v___jp_1609_:
{
lean_object* v___x_1621_; double v___x_1622_; double v___x_1623_; double v___x_1624_; double v___x_1625_; double v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1621_ = lean_io_mono_nanos_now();
v___x_1622_ = lean_float_of_nat(v___y_1613_);
v___x_1623_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1624_ = lean_float_div(v___x_1622_, v___x_1623_);
v___x_1625_ = lean_float_of_nat(v___x_1621_);
v___x_1626_ = lean_float_div(v___x_1625_, v___x_1623_);
v___x_1627_ = lean_box_float(v___x_1624_);
v___x_1628_ = lean_box_float(v___x_1626_);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v_a_1620_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
lean_inc_ref(v___y_1612_);
lean_inc(v_trace_991_);
v___x_1631_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1615_, v___y_1612_, v___y_1610_, v___y_1619_, v___y_1611_, v___f_1355_, v___x_1630_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1176_ = v___y_1610_;
v___y_1177_ = v___y_1612_;
v___y_1178_ = v___y_1614_;
v___y_1179_ = v___y_1615_;
v___y_1180_ = v___y_1616_;
v___y_1181_ = v___y_1617_;
v___y_1182_ = v___y_1618_;
v___y_1183_ = v___x_1631_;
goto v___jp_1175_;
}
v___jp_1632_:
{
lean_object* v___x_1645_; 
v___x_1645_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
if (v___y_1640_ == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = lean_io_mono_nanos_now();
lean_inc(v_trace_991_);
v___x_1648_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1636_, v___y_1644_, v___y_1634_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set_tag(v___x_1651_, 1);
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
v___y_1610_ = v___y_1639_;
v___y_1611_ = v_a_1646_;
v___y_1612_ = v___y_1633_;
v___y_1613_ = v___x_1647_;
v___y_1614_ = v___y_1641_;
v___y_1615_ = v___y_1642_;
v___y_1616_ = v___y_1635_;
v___y_1617_ = v___y_1637_;
v___y_1618_ = v___y_1643_;
v___y_1619_ = v___y_1638_;
v_a_1620_ = v___x_1654_;
goto v___jp_1609_;
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_a_1657_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1648_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1648_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set_tag(v___x_1659_, 0);
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
v___y_1610_ = v___y_1639_;
v___y_1611_ = v_a_1646_;
v___y_1612_ = v___y_1633_;
v___y_1613_ = v___x_1647_;
v___y_1614_ = v___y_1641_;
v___y_1615_ = v___y_1642_;
v___y_1616_ = v___y_1635_;
v___y_1617_ = v___y_1637_;
v___y_1618_ = v___y_1643_;
v___y_1619_ = v___y_1638_;
v_a_1620_ = v___x_1662_;
goto v___jp_1609_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_a_1665_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1665_);
lean_dec_ref(v___x_1645_);
v___x_1666_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_991_);
v___x_1667_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1636_, v___y_1644_, v___y_1634_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 1);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
v___y_1590_ = v___y_1639_;
v___y_1591_ = v_a_1665_;
v___y_1592_ = v___x_1666_;
v___y_1593_ = v___y_1633_;
v___y_1594_ = v___y_1641_;
v___y_1595_ = v___y_1642_;
v___y_1596_ = v___y_1635_;
v___y_1597_ = v___y_1637_;
v___y_1598_ = v___y_1643_;
v___y_1599_ = v___y_1638_;
v_a_1600_ = v___x_1673_;
goto v___jp_1589_;
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
v_a_1676_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1667_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1667_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 0);
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
v___y_1590_ = v___y_1639_;
v___y_1591_ = v_a_1665_;
v___y_1592_ = v___x_1666_;
v___y_1593_ = v___y_1633_;
v___y_1594_ = v___y_1641_;
v___y_1595_ = v___y_1642_;
v___y_1596_ = v___y_1635_;
v___y_1597_ = v___y_1637_;
v___y_1598_ = v___y_1643_;
v___y_1599_ = v___y_1638_;
v_a_1600_ = v___x_1681_;
goto v___jp_1589_;
}
}
}
}
}
v___jp_1684_:
{
lean_object* v___x_1696_; double v___x_1697_; double v___x_1698_; double v___x_1699_; double v___x_1700_; double v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1696_ = lean_io_mono_nanos_now();
v___x_1697_ = lean_float_of_nat(v___y_1691_);
v___x_1698_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1699_ = lean_float_div(v___x_1697_, v___x_1698_);
v___x_1700_ = lean_float_of_nat(v___x_1696_);
v___x_1701_ = lean_float_div(v___x_1700_, v___x_1698_);
v___x_1702_ = lean_box_float(v___x_1699_);
v___x_1703_ = lean_box_float(v___x_1701_);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v_a_1695_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
lean_inc_ref(v___y_1687_);
lean_inc(v_trace_991_);
v___x_1706_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1690_, v___y_1687_, v___y_1686_, v___y_1694_, v___y_1689_, v___f_1319_, v___x_1705_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1125_ = v___y_1686_;
v___y_1126_ = v___y_1685_;
v___y_1127_ = v___y_1687_;
v___y_1128_ = v___y_1688_;
v___y_1129_ = v___y_1690_;
v___y_1130_ = v___y_1692_;
v___y_1131_ = v___y_1693_;
v___y_1132_ = v___x_1706_;
goto v___jp_1124_;
}
v___jp_1707_:
{
lean_object* v___x_1719_; double v___x_1720_; double v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1719_ = lean_io_get_num_heartbeats();
v___x_1720_ = lean_float_of_nat(v___y_1711_);
v___x_1721_ = lean_float_of_nat(v___x_1719_);
v___x_1722_ = lean_box_float(v___x_1720_);
v___x_1723_ = lean_box_float(v___x_1721_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1722_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v_a_1718_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
lean_inc_ref(v___y_1710_);
lean_inc(v_trace_991_);
v___x_1726_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1714_, v___y_1710_, v___y_1709_, v___y_1717_, v___y_1713_, v___f_1319_, v___x_1725_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1125_ = v___y_1709_;
v___y_1126_ = v___y_1708_;
v___y_1127_ = v___y_1710_;
v___y_1128_ = v___y_1712_;
v___y_1129_ = v___y_1714_;
v___y_1130_ = v___y_1715_;
v___y_1131_ = v___y_1716_;
v___y_1132_ = v___x_1726_;
goto v___jp_1124_;
}
v___jp_1727_:
{
lean_object* v___x_1739_; double v___x_1740_; double v___x_1741_; double v___x_1742_; double v___x_1743_; double v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1739_ = lean_io_mono_nanos_now();
v___x_1740_ = lean_float_of_nat(v___y_1734_);
v___x_1741_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1742_ = lean_float_div(v___x_1740_, v___x_1741_);
v___x_1743_ = lean_float_of_nat(v___x_1739_);
v___x_1744_ = lean_float_div(v___x_1743_, v___x_1741_);
v___x_1745_ = lean_box_float(v___x_1742_);
v___x_1746_ = lean_box_float(v___x_1744_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_a_1738_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
lean_inc_ref(v___y_1730_);
lean_inc(v_trace_991_);
v___x_1749_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1732_, v___y_1730_, v___y_1729_, v___y_1733_, v___y_1737_, v___f_1235_, v___x_1748_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1125_ = v___y_1729_;
v___y_1126_ = v___y_1728_;
v___y_1127_ = v___y_1730_;
v___y_1128_ = v___y_1731_;
v___y_1129_ = v___y_1732_;
v___y_1130_ = v___y_1735_;
v___y_1131_ = v___y_1736_;
v___y_1132_ = v___x_1749_;
goto v___jp_1124_;
}
v___jp_1750_:
{
lean_object* v___x_1762_; double v___x_1763_; double v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1762_ = lean_io_get_num_heartbeats();
v___x_1763_ = lean_float_of_nat(v___y_1755_);
v___x_1764_ = lean_float_of_nat(v___x_1762_);
v___x_1765_ = lean_box_float(v___x_1763_);
v___x_1766_ = lean_box_float(v___x_1764_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v_a_1761_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
lean_inc_ref(v___y_1753_);
lean_inc(v_trace_991_);
v___x_1769_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1756_, v___y_1753_, v___y_1752_, v___y_1757_, v___y_1760_, v___f_1235_, v___x_1768_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1125_ = v___y_1752_;
v___y_1126_ = v___y_1751_;
v___y_1127_ = v___y_1753_;
v___y_1128_ = v___y_1754_;
v___y_1129_ = v___y_1756_;
v___y_1130_ = v___y_1758_;
v___y_1131_ = v___y_1759_;
v___y_1132_ = v___x_1769_;
goto v___jp_1124_;
}
v___jp_1770_:
{
lean_object* v___x_1783_; 
v___x_1783_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
if (v___y_1777_ == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1783_);
v___x_1785_ = lean_io_mono_nanos_now();
lean_inc(v_trace_991_);
v___x_1786_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1773_, v___y_1782_, v___y_1775_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set_tag(v___x_1789_, 1);
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
v___y_1728_ = v___y_1771_;
v___y_1729_ = v___y_1776_;
v___y_1730_ = v___y_1772_;
v___y_1731_ = v___y_1778_;
v___y_1732_ = v___y_1779_;
v___y_1733_ = v___y_1780_;
v___y_1734_ = v___x_1785_;
v___y_1735_ = v___y_1774_;
v___y_1736_ = v___y_1781_;
v___y_1737_ = v_a_1784_;
v_a_1738_ = v___x_1792_;
goto v___jp_1727_;
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_a_1795_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1786_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1786_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 0);
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
v___y_1728_ = v___y_1771_;
v___y_1729_ = v___y_1776_;
v___y_1730_ = v___y_1772_;
v___y_1731_ = v___y_1778_;
v___y_1732_ = v___y_1779_;
v___y_1733_ = v___y_1780_;
v___y_1734_ = v___x_1785_;
v___y_1735_ = v___y_1774_;
v___y_1736_ = v___y_1781_;
v___y_1737_ = v_a_1784_;
v_a_1738_ = v___x_1800_;
goto v___jp_1727_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_a_1803_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1803_);
lean_dec_ref(v___x_1783_);
v___x_1804_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_991_);
v___x_1805_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1773_, v___y_1782_, v___y_1775_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 1);
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
v___y_1751_ = v___y_1771_;
v___y_1752_ = v___y_1776_;
v___y_1753_ = v___y_1772_;
v___y_1754_ = v___y_1778_;
v___y_1755_ = v___x_1804_;
v___y_1756_ = v___y_1779_;
v___y_1757_ = v___y_1780_;
v___y_1758_ = v___y_1774_;
v___y_1759_ = v___y_1781_;
v___y_1760_ = v_a_1803_;
v_a_1761_ = v___x_1811_;
goto v___jp_1750_;
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_a_1814_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1805_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1805_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set_tag(v___x_1816_, 0);
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
v___y_1751_ = v___y_1771_;
v___y_1752_ = v___y_1776_;
v___y_1753_ = v___y_1772_;
v___y_1754_ = v___y_1778_;
v___y_1755_ = v___x_1804_;
v___y_1756_ = v___y_1779_;
v___y_1757_ = v___y_1780_;
v___y_1758_ = v___y_1774_;
v___y_1759_ = v___y_1781_;
v___y_1760_ = v_a_1803_;
v_a_1761_ = v___x_1819_;
goto v___jp_1750_;
}
}
}
}
}
v___jp_1822_:
{
lean_object* v___x_1830_; double v___x_1831_; double v___x_1832_; double v___x_1833_; double v___x_1834_; double v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1830_ = lean_io_mono_nanos_now();
v___x_1831_ = lean_float_of_nat(v___y_1827_);
v___x_1832_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1833_ = lean_float_div(v___x_1831_, v___x_1832_);
v___x_1834_ = lean_float_of_nat(v___x_1830_);
v___x_1835_ = lean_float_div(v___x_1834_, v___x_1832_);
v___x_1836_ = lean_box_float(v___x_1833_);
v___x_1837_ = lean_box_float(v___x_1835_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_a_1829_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
lean_inc_ref(v___y_1825_);
v___x_1840_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1826_, v___y_1825_, v___y_1823_, v___y_1828_, v___y_1824_, v___f_1355_, v___x_1839_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1840_;
}
v___jp_1841_:
{
lean_object* v___x_1849_; double v___x_1850_; double v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1849_ = lean_io_get_num_heartbeats();
v___x_1850_ = lean_float_of_nat(v___y_1843_);
v___x_1851_ = lean_float_of_nat(v___x_1849_);
v___x_1852_ = lean_box_float(v___x_1850_);
v___x_1853_ = lean_box_float(v___x_1851_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v_a_1848_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
lean_inc_ref(v___y_1845_);
v___x_1856_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1846_, v___y_1845_, v___y_1842_, v___y_1847_, v___y_1844_, v___f_1355_, v___x_1855_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1856_;
}
v___jp_1857_:
{
lean_object* v___x_1865_; lean_object* v_a_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1865_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref(v___x_1865_);
v___x_1867_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1868_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1858_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_io_mono_nanos_now();
lean_inc(v_trace_991_);
v___x_1870_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1862_, v___y_1864_, v___y_1861_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 1);
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
v___y_1823_ = v___y_1858_;
v___y_1824_ = v_a_1866_;
v___y_1825_ = v___y_1859_;
v___y_1826_ = v___y_1860_;
v___y_1827_ = v___x_1869_;
v___y_1828_ = v___y_1863_;
v_a_1829_ = v___x_1876_;
goto v___jp_1822_;
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
v_a_1879_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1870_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1870_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
lean_ctor_set_tag(v___x_1881_, 0);
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
v___y_1823_ = v___y_1858_;
v___y_1824_ = v_a_1866_;
v___y_1825_ = v___y_1859_;
v___y_1826_ = v___y_1860_;
v___y_1827_ = v___x_1869_;
v___y_1828_ = v___y_1863_;
v_a_1829_ = v___x_1884_;
goto v___jp_1822_;
}
}
}
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_991_);
v___x_1888_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1862_, v___y_1864_, v___y_1861_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
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
v___y_1842_ = v___y_1858_;
v___y_1843_ = v___x_1887_;
v___y_1844_ = v_a_1866_;
v___y_1845_ = v___y_1859_;
v___y_1846_ = v___y_1860_;
v___y_1847_ = v___y_1863_;
v_a_1848_ = v___x_1894_;
goto v___jp_1841_;
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
v___y_1842_ = v___y_1858_;
v___y_1843_ = v___x_1887_;
v___y_1844_ = v_a_1866_;
v___y_1845_ = v___y_1859_;
v___y_1846_ = v___y_1860_;
v___y_1847_ = v___y_1863_;
v_a_1848_ = v___x_1902_;
goto v___jp_1841_;
}
}
}
}
}
v___jp_1907_:
{
lean_object* v___x_1913_; lean_object* v_a_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1913_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
v___x_1915_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1916_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1908_, v___x_1915_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_io_mono_nanos_now();
lean_inc(v_trace_991_);
v___x_1918_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v_n_1906_, v___y_1912_, v_acc_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 1);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
v___y_1321_ = v___y_1908_;
v___y_1322_ = v___y_1909_;
v___y_1323_ = v___x_1917_;
v___y_1324_ = v_a_1914_;
v___y_1325_ = v___y_1911_;
v___y_1326_ = v___y_1910_;
v_a_1327_ = v___x_1924_;
goto v___jp_1320_;
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
v_a_1927_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1918_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1918_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set_tag(v___x_1929_, 0);
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
v___y_1321_ = v___y_1908_;
v___y_1322_ = v___y_1909_;
v___y_1323_ = v___x_1917_;
v___y_1324_ = v_a_1914_;
v___y_1325_ = v___y_1911_;
v___y_1326_ = v___y_1910_;
v_a_1327_ = v___x_1932_;
goto v___jp_1320_;
}
}
}
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_991_);
v___x_1936_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v_n_1906_, v___y_1912_, v_acc_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
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
v___y_1340_ = v___y_1908_;
v___y_1341_ = v___y_1909_;
v___y_1342_ = v_a_1914_;
v___y_1343_ = v___y_1911_;
v___y_1344_ = v___y_1910_;
v___y_1345_ = v___x_1935_;
v_a_1346_ = v___x_1942_;
goto v___jp_1339_;
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
v___y_1340_ = v___y_1908_;
v___y_1341_ = v___y_1909_;
v___y_1342_ = v_a_1914_;
v___y_1343_ = v___y_1911_;
v___y_1344_ = v___y_1910_;
v___y_1345_ = v___x_1935_;
v_a_1346_ = v___x_1950_;
goto v___jp_1339_;
}
}
}
}
}
v___jp_1953_:
{
if (v___y_1963_ == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref(v___y_1960_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v___y_1961_);
v___x_1964_ = lean_apply_6(v___y_1959_, v___y_1961_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
if (lean_obj_tag(v_a_1965_) == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1966_ = lean_nat_add(v_n_1906_, v_one_1905_);
lean_dec(v_n_1906_);
v___x_1967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___y_1961_);
lean_ctor_set(v___x_1967_, 1, v_acc_996_);
v___x_1968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_1969_ = l_Lean_Name_append(v___x_1968_, v_trace_991_);
v___x_1970_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1957_, v___y_1954_, v___x_1969_);
lean_dec(v___x_1969_);
if (v___x_1970_ == 0)
{
if (v___y_1958_ == 0)
{
v_n_994_ = v___x_1966_;
v_curr_995_ = v___y_1962_;
v_acc_996_ = v___x_1967_;
goto _start;
}
else
{
v___y_1272_ = v___y_1954_;
v___y_1273_ = v___y_1955_;
v___y_1274_ = v___y_1956_;
v___y_1275_ = v___x_1970_;
v___y_1276_ = v___x_1967_;
v___y_1277_ = v___x_1966_;
v___y_1278_ = v___y_1962_;
goto v___jp_1271_;
}
}
else
{
v___y_1272_ = v___y_1954_;
v___y_1273_ = v___y_1955_;
v___y_1274_ = v___y_1956_;
v___y_1275_ = v___x_1970_;
v___y_1276_ = v___x_1967_;
v___y_1277_ = v___x_1966_;
v___y_1278_ = v___y_1962_;
goto v___jp_1271_;
}
}
else
{
lean_object* v_val_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
lean_dec(v___y_1961_);
v_val_1972_ = lean_ctor_get(v_a_1965_, 0);
lean_inc(v_val_1972_);
lean_dec_ref_known(v_a_1965_, 1);
v___x_1973_ = l_List_appendTR___redArg(v_val_1972_, v___y_1962_);
v___x_1974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_1975_ = l_Lean_Name_append(v___x_1974_, v_trace_991_);
v___x_1976_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1957_, v___y_1954_, v___x_1975_);
lean_dec(v___x_1975_);
if (v___x_1976_ == 0)
{
if (v___y_1958_ == 0)
{
v_n_994_ = v_n_1906_;
v_curr_995_ = v___x_1973_;
goto _start;
}
else
{
v___y_1908_ = v___y_1954_;
v___y_1909_ = v___y_1955_;
v___y_1910_ = v___y_1956_;
v___y_1911_ = v___x_1976_;
v___y_1912_ = v___x_1973_;
goto v___jp_1907_;
}
}
else
{
v___y_1908_ = v___y_1954_;
v___y_1909_ = v___y_1955_;
v___y_1910_ = v___y_1956_;
v___y_1911_ = v___x_1976_;
v___y_1912_ = v___x_1973_;
goto v___jp_1907_;
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
v_a_1978_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1964_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1964_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_dec(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1959_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
return v___y_1960_;
}
}
v___jp_1986_:
{
lean_object* v___x_1997_; 
v___x_1997_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
if (v___y_1992_ == 0)
{
lean_object* v_a_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref(v___x_1997_);
v___x_1999_ = lean_io_mono_nanos_now();
lean_inc(v_trace_991_);
v___x_2000_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v_n_1906_, v___y_1990_, v_acc_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set_tag(v___x_2003_, 1);
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
v___y_1685_ = v___y_1988_;
v___y_1686_ = v___y_1987_;
v___y_1687_ = v___y_1989_;
v___y_1688_ = v___y_1991_;
v___y_1689_ = v_a_1998_;
v___y_1690_ = v___y_1993_;
v___y_1691_ = v___x_1999_;
v___y_1692_ = v___y_1994_;
v___y_1693_ = v___y_1995_;
v___y_1694_ = v___y_1996_;
v_a_1695_ = v___x_2006_;
goto v___jp_1684_;
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
v_a_2009_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2000_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2000_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set_tag(v___x_2011_, 0);
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
v___y_1685_ = v___y_1988_;
v___y_1686_ = v___y_1987_;
v___y_1687_ = v___y_1989_;
v___y_1688_ = v___y_1991_;
v___y_1689_ = v_a_1998_;
v___y_1690_ = v___y_1993_;
v___y_1691_ = v___x_1999_;
v___y_1692_ = v___y_1994_;
v___y_1693_ = v___y_1995_;
v___y_1694_ = v___y_1996_;
v_a_1695_ = v___x_2014_;
goto v___jp_1684_;
}
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v_a_2017_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_2017_);
lean_dec_ref(v___x_1997_);
v___x_2018_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_991_);
v___x_2019_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v_n_1906_, v___y_1990_, v_acc_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 1);
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
v___y_1708_ = v___y_1988_;
v___y_1709_ = v___y_1987_;
v___y_1710_ = v___y_1989_;
v___y_1711_ = v___x_2018_;
v___y_1712_ = v___y_1991_;
v___y_1713_ = v_a_2017_;
v___y_1714_ = v___y_1993_;
v___y_1715_ = v___y_1994_;
v___y_1716_ = v___y_1995_;
v___y_1717_ = v___y_1996_;
v_a_1718_ = v___x_2025_;
goto v___jp_1707_;
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_a_2028_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2019_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2019_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 0);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
v___y_1708_ = v___y_1988_;
v___y_1709_ = v___y_1987_;
v___y_1710_ = v___y_1989_;
v___y_1711_ = v___x_2018_;
v___y_1712_ = v___y_1991_;
v___y_1713_ = v_a_2017_;
v___y_1714_ = v___y_1993_;
v___y_1715_ = v___y_1994_;
v___y_1716_ = v___y_1995_;
v___y_1717_ = v___y_1996_;
v_a_1718_ = v___x_2033_;
goto v___jp_1707_;
}
}
}
}
}
v___jp_2036_:
{
if (v___y_2050_ == 0)
{
lean_object* v___x_2051_; 
lean_dec_ref(v___y_2045_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v___y_2047_);
v___x_2051_ = lean_apply_6(v___y_2046_, v___y_2047_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
if (lean_obj_tag(v_a_2052_) == 0)
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2053_ = lean_nat_add(v_n_1906_, v_one_1905_);
lean_dec(v_n_1906_);
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___y_2047_);
lean_ctor_set(v___x_2054_, 1, v_acc_996_);
v___x_2055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_2056_ = l_Lean_Name_append(v___x_2055_, v_trace_991_);
v___x_2057_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2039_, v___y_2041_, v___x_2056_);
lean_dec(v___x_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2058_ = l_Lean_trace_profiler;
v___x_2059_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2041_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; 
lean_inc(v_trace_991_);
v___x_2060_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___x_2053_, v___y_2049_, v___x_2054_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1125_ = v___y_2041_;
v___y_1126_ = v___y_2037_;
v___y_1127_ = v___y_2038_;
v___y_1128_ = v___y_2043_;
v___y_1129_ = v___y_2044_;
v___y_1130_ = v___y_2040_;
v___y_1131_ = v___y_2048_;
v___y_1132_ = v___x_2060_;
goto v___jp_1124_;
}
else
{
v___y_1771_ = v___y_2037_;
v___y_1772_ = v___y_2038_;
v___y_1773_ = v___x_2053_;
v___y_1774_ = v___y_2040_;
v___y_1775_ = v___x_2054_;
v___y_1776_ = v___y_2041_;
v___y_1777_ = v___y_2042_;
v___y_1778_ = v___y_2043_;
v___y_1779_ = v___y_2044_;
v___y_1780_ = v___x_2057_;
v___y_1781_ = v___y_2048_;
v___y_1782_ = v___y_2049_;
goto v___jp_1770_;
}
}
else
{
v___y_1771_ = v___y_2037_;
v___y_1772_ = v___y_2038_;
v___y_1773_ = v___x_2053_;
v___y_1774_ = v___y_2040_;
v___y_1775_ = v___x_2054_;
v___y_1776_ = v___y_2041_;
v___y_1777_ = v___y_2042_;
v___y_1778_ = v___y_2043_;
v___y_1779_ = v___y_2044_;
v___y_1780_ = v___x_2057_;
v___y_1781_ = v___y_2048_;
v___y_1782_ = v___y_2049_;
goto v___jp_1770_;
}
}
else
{
lean_object* v_val_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
lean_dec(v___y_2047_);
v_val_2061_ = lean_ctor_get(v_a_2052_, 0);
lean_inc(v_val_2061_);
lean_dec_ref_known(v_a_2052_, 1);
v___x_2062_ = l_List_appendTR___redArg(v_val_2061_, v___y_2049_);
v___x_2063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_2064_ = l_Lean_Name_append(v___x_2063_, v_trace_991_);
v___x_2065_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2039_, v___y_2041_, v___x_2064_);
lean_dec(v___x_2064_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = l_Lean_trace_profiler;
v___x_2067_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2041_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; 
lean_inc(v_trace_991_);
v___x_2068_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v_n_1906_, v___x_2062_, v_acc_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1125_ = v___y_2041_;
v___y_1126_ = v___y_2037_;
v___y_1127_ = v___y_2038_;
v___y_1128_ = v___y_2043_;
v___y_1129_ = v___y_2044_;
v___y_1130_ = v___y_2040_;
v___y_1131_ = v___y_2048_;
v___y_1132_ = v___x_2068_;
goto v___jp_1124_;
}
else
{
v___y_1987_ = v___y_2041_;
v___y_1988_ = v___y_2037_;
v___y_1989_ = v___y_2038_;
v___y_1990_ = v___x_2062_;
v___y_1991_ = v___y_2043_;
v___y_1992_ = v___y_2042_;
v___y_1993_ = v___y_2044_;
v___y_1994_ = v___y_2040_;
v___y_1995_ = v___y_2048_;
v___y_1996_ = v___x_2065_;
goto v___jp_1986_;
}
}
else
{
v___y_1987_ = v___y_2041_;
v___y_1988_ = v___y_2037_;
v___y_1989_ = v___y_2038_;
v___y_1990_ = v___x_2062_;
v___y_1991_ = v___y_2043_;
v___y_1992_ = v___y_2042_;
v___y_1993_ = v___y_2044_;
v___y_1994_ = v___y_2040_;
v___y_1995_ = v___y_2048_;
v___y_1996_ = v___x_2065_;
goto v___jp_1986_;
}
}
}
else
{
lean_object* v_a_2069_; 
lean_dec(v___y_2049_);
lean_dec(v___y_2047_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec_ref(v_cfg_990_);
v_a_2069_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2051_, 1);
v___y_1115_ = v___y_2037_;
v___y_1116_ = v___y_2041_;
v___y_1117_ = v___y_2038_;
v___y_1118_ = v___y_2043_;
v___y_1119_ = v___y_2044_;
v___y_1120_ = v___y_2040_;
v___y_1121_ = v___y_2048_;
v_a_1122_ = v_a_2069_;
goto v___jp_1114_;
}
}
else
{
lean_dec(v___y_2049_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec_ref(v_cfg_990_);
v___y_1115_ = v___y_2037_;
v___y_1116_ = v___y_2041_;
v___y_1117_ = v___y_2038_;
v___y_1118_ = v___y_2043_;
v___y_1119_ = v___y_2044_;
v___y_1120_ = v___y_2040_;
v___y_1121_ = v___y_2048_;
v_a_1122_ = v___y_2045_;
goto v___jp_1114_;
}
}
v___jp_2070_:
{
lean_object* v___x_2081_; 
v___x_2081_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
if (v___y_2076_ == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref(v___x_2081_);
v___x_2083_ = lean_io_mono_nanos_now();
lean_inc(v_trace_991_);
v___x_2084_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v_n_1906_, v___y_2072_, v_acc_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 1);
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
v___y_1567_ = v___y_2071_;
v___y_1568_ = v___y_2074_;
v___y_1569_ = v___y_2073_;
v___y_1570_ = v___y_2075_;
v___y_1571_ = v___y_2077_;
v___y_1572_ = v___y_2078_;
v___y_1573_ = v___x_2083_;
v___y_1574_ = v___y_2079_;
v___y_1575_ = v___y_2080_;
v___y_1576_ = v_a_2082_;
v_a_1577_ = v___x_2090_;
goto v___jp_1566_;
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
v_a_2093_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2084_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2084_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set_tag(v___x_2095_, 0);
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
v___y_1567_ = v___y_2071_;
v___y_1568_ = v___y_2074_;
v___y_1569_ = v___y_2073_;
v___y_1570_ = v___y_2075_;
v___y_1571_ = v___y_2077_;
v___y_1572_ = v___y_2078_;
v___y_1573_ = v___x_2083_;
v___y_1574_ = v___y_2079_;
v___y_1575_ = v___y_2080_;
v___y_1576_ = v_a_2082_;
v_a_1577_ = v___x_2098_;
goto v___jp_1566_;
}
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_a_2101_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2081_);
v___x_2102_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_991_);
v___x_2103_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v_n_1906_, v___y_2072_, v_acc_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set_tag(v___x_2106_, 1);
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
v___y_1547_ = v___y_2071_;
v___y_1548_ = v___y_2074_;
v___y_1549_ = v___y_2073_;
v___y_1550_ = v___y_2075_;
v___y_1551_ = v___y_2077_;
v___y_1552_ = v___y_2078_;
v___y_1553_ = v___x_2102_;
v___y_1554_ = v___y_2079_;
v___y_1555_ = v___y_2080_;
v___y_1556_ = v_a_2101_;
v_a_1557_ = v___x_2109_;
goto v___jp_1546_;
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_a_2112_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2103_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2103_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set_tag(v___x_2114_, 0);
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
v___y_1547_ = v___y_2071_;
v___y_1548_ = v___y_2074_;
v___y_1549_ = v___y_2073_;
v___y_1550_ = v___y_2075_;
v___y_1551_ = v___y_2077_;
v___y_1552_ = v___y_2078_;
v___y_1553_ = v___x_2102_;
v___y_1554_ = v___y_2079_;
v___y_1555_ = v___y_2080_;
v___y_1556_ = v_a_2101_;
v_a_1557_ = v___x_2117_;
goto v___jp_1546_;
}
}
}
}
}
v___jp_2120_:
{
if (v___y_2134_ == 0)
{
lean_object* v___x_2135_; 
lean_dec_ref(v___y_2121_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v___y_2131_);
v___x_2135_ = lean_apply_6(v___y_2130_, v___y_2131_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
if (lean_obj_tag(v_a_2136_) == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2137_ = lean_nat_add(v_n_1906_, v_one_1905_);
lean_dec(v_n_1906_);
v___x_2138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___y_2131_);
lean_ctor_set(v___x_2138_, 1, v_acc_996_);
v___x_2139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_2140_ = l_Lean_Name_append(v___x_2139_, v_trace_991_);
v___x_2141_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2123_, v___y_2126_, v___x_2140_);
lean_dec(v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = l_Lean_trace_profiler;
v___x_2143_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2126_, v___x_2142_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; 
lean_inc(v_trace_991_);
v___x_2144_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___x_2137_, v___y_2133_, v___x_2138_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1176_ = v___y_2126_;
v___y_1177_ = v___y_2122_;
v___y_1178_ = v___y_2128_;
v___y_1179_ = v___y_2129_;
v___y_1180_ = v___y_2124_;
v___y_1181_ = v___y_2125_;
v___y_1182_ = v___y_2132_;
v___y_1183_ = v___x_2144_;
goto v___jp_1175_;
}
else
{
v___y_1495_ = v___y_2122_;
v___y_1496_ = v___y_2124_;
v___y_1497_ = v___x_2141_;
v___y_1498_ = v___y_2125_;
v___y_1499_ = v___x_2137_;
v___y_1500_ = v___y_2126_;
v___y_1501_ = v___y_2127_;
v___y_1502_ = v___y_2128_;
v___y_1503_ = v___y_2129_;
v___y_1504_ = v___x_2138_;
v___y_1505_ = v___y_2132_;
v___y_1506_ = v___y_2133_;
goto v___jp_1494_;
}
}
else
{
v___y_1495_ = v___y_2122_;
v___y_1496_ = v___y_2124_;
v___y_1497_ = v___x_2141_;
v___y_1498_ = v___y_2125_;
v___y_1499_ = v___x_2137_;
v___y_1500_ = v___y_2126_;
v___y_1501_ = v___y_2127_;
v___y_1502_ = v___y_2128_;
v___y_1503_ = v___y_2129_;
v___y_1504_ = v___x_2138_;
v___y_1505_ = v___y_2132_;
v___y_1506_ = v___y_2133_;
goto v___jp_1494_;
}
}
else
{
lean_object* v_val_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
lean_dec(v___y_2131_);
v_val_2145_ = lean_ctor_get(v_a_2136_, 0);
lean_inc(v_val_2145_);
lean_dec_ref_known(v_a_2136_, 1);
v___x_2146_ = l_List_appendTR___redArg(v_val_2145_, v___y_2133_);
v___x_2147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_2148_ = l_Lean_Name_append(v___x_2147_, v_trace_991_);
v___x_2149_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2123_, v___y_2126_, v___x_2148_);
lean_dec(v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = l_Lean_trace_profiler;
v___x_2151_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2126_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; 
lean_inc(v_trace_991_);
v___x_2152_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v_n_1906_, v___x_2146_, v_acc_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1176_ = v___y_2126_;
v___y_1177_ = v___y_2122_;
v___y_1178_ = v___y_2128_;
v___y_1179_ = v___y_2129_;
v___y_1180_ = v___y_2124_;
v___y_1181_ = v___y_2125_;
v___y_1182_ = v___y_2132_;
v___y_1183_ = v___x_2152_;
goto v___jp_1175_;
}
else
{
v___y_2071_ = v___y_2126_;
v___y_2072_ = v___x_2146_;
v___y_2073_ = v___y_2122_;
v___y_2074_ = v___x_2149_;
v___y_2075_ = v___y_2128_;
v___y_2076_ = v___y_2127_;
v___y_2077_ = v___y_2129_;
v___y_2078_ = v___y_2124_;
v___y_2079_ = v___y_2125_;
v___y_2080_ = v___y_2132_;
goto v___jp_2070_;
}
}
else
{
v___y_2071_ = v___y_2126_;
v___y_2072_ = v___x_2146_;
v___y_2073_ = v___y_2122_;
v___y_2074_ = v___x_2149_;
v___y_2075_ = v___y_2128_;
v___y_2076_ = v___y_2127_;
v___y_2077_ = v___y_2129_;
v___y_2078_ = v___y_2124_;
v___y_2079_ = v___y_2125_;
v___y_2080_ = v___y_2132_;
goto v___jp_2070_;
}
}
}
else
{
lean_object* v_a_2153_; 
lean_dec(v___y_2133_);
lean_dec(v___y_2131_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec_ref(v_cfg_990_);
v_a_2153_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2135_, 1);
v___y_1166_ = v___y_2126_;
v___y_1167_ = v___y_2122_;
v___y_1168_ = v___y_2128_;
v___y_1169_ = v___y_2129_;
v___y_1170_ = v___y_2124_;
v___y_1171_ = v___y_2125_;
v___y_1172_ = v___y_2132_;
v_a_1173_ = v_a_2153_;
goto v___jp_1165_;
}
}
else
{
lean_dec(v___y_2133_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec_ref(v_cfg_990_);
v___y_1166_ = v___y_2126_;
v___y_1167_ = v___y_2122_;
v___y_1168_ = v___y_2128_;
v___y_1169_ = v___y_2129_;
v___y_1170_ = v___y_2124_;
v___y_1171_ = v___y_2125_;
v___y_1172_ = v___y_2132_;
v_a_1173_ = v___y_2121_;
goto v___jp_1165_;
}
}
v___jp_2154_:
{
lean_object* v___x_2167_; lean_object* v_a_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2167_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref(v___x_2167_);
v___x_2169_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2170_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2159_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec_ref(v___y_2156_);
v___x_2171_ = lean_io_mono_nanos_now();
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v___y_2164_);
v___x_2172_ = lean_apply_6(v___y_2162_, v___y_2164_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; uint8_t v___x_2174_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = lean_unbox(v_a_2173_);
lean_dec(v_a_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; 
lean_inc_ref(v_next_992_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v___y_2164_);
v___x_2175_ = lean_apply_7(v_next_992_, v___y_2164_, v___y_2158_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; 
lean_dec(v___y_2166_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec_ref(v_cfg_990_);
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___y_1156_ = v___y_2159_;
v___y_1157_ = v___y_2155_;
v___y_1158_ = v___y_2160_;
v___y_1159_ = v___y_2161_;
v___y_1160_ = v___x_2171_;
v___y_1161_ = v_a_2168_;
v___y_1162_ = v___y_2165_;
v_a_1163_ = v_a_2176_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_2177_; uint8_t v___x_2178_; 
v_a_2177_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2178_ = l_Lean_Exception_isInterrupt(v_a_2177_);
if (v___x_2178_ == 0)
{
uint8_t v___x_2179_; 
lean_inc(v_a_2177_);
v___x_2179_ = l_Lean_Exception_isRuntime(v_a_2177_);
v___y_2121_ = v_a_2177_;
v___y_2122_ = v___y_2155_;
v___y_2123_ = v___y_2157_;
v___y_2124_ = v___x_2171_;
v___y_2125_ = v_a_2168_;
v___y_2126_ = v___y_2159_;
v___y_2127_ = v___x_2170_;
v___y_2128_ = v___y_2160_;
v___y_2129_ = v___y_2161_;
v___y_2130_ = v___y_2163_;
v___y_2131_ = v___y_2164_;
v___y_2132_ = v___y_2165_;
v___y_2133_ = v___y_2166_;
v___y_2134_ = v___x_2179_;
goto v___jp_2120_;
}
else
{
v___y_2121_ = v_a_2177_;
v___y_2122_ = v___y_2155_;
v___y_2123_ = v___y_2157_;
v___y_2124_ = v___x_2171_;
v___y_2125_ = v_a_2168_;
v___y_2126_ = v___y_2159_;
v___y_2127_ = v___x_2170_;
v___y_2128_ = v___y_2160_;
v___y_2129_ = v___y_2161_;
v___y_2130_ = v___y_2163_;
v___y_2131_ = v___y_2164_;
v___y_2132_ = v___y_2165_;
v___y_2133_ = v___y_2166_;
v___y_2134_ = v___x_2178_;
goto v___jp_2120_;
}
}
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
lean_dec_ref(v___y_2163_);
lean_dec_ref(v___y_2158_);
v___x_2180_ = lean_nat_add(v_n_1906_, v_one_1905_);
lean_dec(v_n_1906_);
v___x_2181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___y_2164_);
lean_ctor_set(v___x_2181_, 1, v_acc_996_);
v___x_2182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_2183_ = l_Lean_Name_append(v___x_2182_, v_trace_991_);
v___x_2184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2157_, v___y_2159_, v___x_2183_);
lean_dec(v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2185_ = l_Lean_trace_profiler;
v___x_2186_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2159_, v___x_2185_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; 
lean_inc(v_trace_991_);
v___x_2187_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___x_2180_, v___y_2166_, v___x_2181_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1176_ = v___y_2159_;
v___y_1177_ = v___y_2155_;
v___y_1178_ = v___y_2160_;
v___y_1179_ = v___y_2161_;
v___y_1180_ = v___x_2171_;
v___y_1181_ = v_a_2168_;
v___y_1182_ = v___y_2165_;
v___y_1183_ = v___x_2187_;
goto v___jp_1175_;
}
else
{
v___y_1633_ = v___y_2155_;
v___y_1634_ = v___x_2181_;
v___y_1635_ = v___x_2171_;
v___y_1636_ = v___x_2180_;
v___y_1637_ = v_a_2168_;
v___y_1638_ = v___x_2184_;
v___y_1639_ = v___y_2159_;
v___y_1640_ = v___x_2170_;
v___y_1641_ = v___y_2160_;
v___y_1642_ = v___y_2161_;
v___y_1643_ = v___y_2165_;
v___y_1644_ = v___y_2166_;
goto v___jp_1632_;
}
}
else
{
v___y_1633_ = v___y_2155_;
v___y_1634_ = v___x_2181_;
v___y_1635_ = v___x_2171_;
v___y_1636_ = v___x_2180_;
v___y_1637_ = v_a_2168_;
v___y_1638_ = v___x_2184_;
v___y_1639_ = v___y_2159_;
v___y_1640_ = v___x_2170_;
v___y_1641_ = v___y_2160_;
v___y_1642_ = v___y_2161_;
v___y_1643_ = v___y_2165_;
v___y_1644_ = v___y_2166_;
goto v___jp_1632_;
}
}
}
else
{
lean_object* v_a_2188_; 
lean_dec(v___y_2166_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec_ref(v___y_2158_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec_ref(v_cfg_990_);
v_a_2188_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2172_, 1);
v___y_1166_ = v___y_2159_;
v___y_1167_ = v___y_2155_;
v___y_1168_ = v___y_2160_;
v___y_1169_ = v___y_2161_;
v___y_1170_ = v___x_2171_;
v___y_1171_ = v_a_2168_;
v___y_1172_ = v___y_2165_;
v_a_1173_ = v_a_2188_;
goto v___jp_1165_;
}
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec_ref(v___y_2158_);
v___x_2189_ = lean_io_get_num_heartbeats();
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v___y_2164_);
v___x_2190_ = lean_apply_6(v___y_2162_, v___y_2164_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; uint8_t v___x_2192_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v___x_2192_ = lean_unbox(v_a_2191_);
lean_dec(v_a_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; 
lean_inc_ref(v_next_992_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v___y_2164_);
v___x_2193_ = lean_apply_7(v_next_992_, v___y_2164_, v___y_2156_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; 
lean_dec(v___y_2166_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec_ref(v_cfg_990_);
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2193_, 1);
v___y_1105_ = v___x_2189_;
v___y_1106_ = v___y_2159_;
v___y_1107_ = v___y_2155_;
v___y_1108_ = v___y_2160_;
v___y_1109_ = v___y_2161_;
v___y_1110_ = v_a_2168_;
v___y_1111_ = v___y_2165_;
v_a_1112_ = v_a_2194_;
goto v___jp_1104_;
}
else
{
lean_object* v_a_2195_; uint8_t v___x_2196_; 
v_a_2195_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2193_, 1);
v___x_2196_ = l_Lean_Exception_isInterrupt(v_a_2195_);
if (v___x_2196_ == 0)
{
uint8_t v___x_2197_; 
lean_inc(v_a_2195_);
v___x_2197_ = l_Lean_Exception_isRuntime(v_a_2195_);
v___y_2037_ = v___x_2189_;
v___y_2038_ = v___y_2155_;
v___y_2039_ = v___y_2157_;
v___y_2040_ = v_a_2168_;
v___y_2041_ = v___y_2159_;
v___y_2042_ = v___x_2170_;
v___y_2043_ = v___y_2160_;
v___y_2044_ = v___y_2161_;
v___y_2045_ = v_a_2195_;
v___y_2046_ = v___y_2163_;
v___y_2047_ = v___y_2164_;
v___y_2048_ = v___y_2165_;
v___y_2049_ = v___y_2166_;
v___y_2050_ = v___x_2197_;
goto v___jp_2036_;
}
else
{
v___y_2037_ = v___x_2189_;
v___y_2038_ = v___y_2155_;
v___y_2039_ = v___y_2157_;
v___y_2040_ = v_a_2168_;
v___y_2041_ = v___y_2159_;
v___y_2042_ = v___x_2170_;
v___y_2043_ = v___y_2160_;
v___y_2044_ = v___y_2161_;
v___y_2045_ = v_a_2195_;
v___y_2046_ = v___y_2163_;
v___y_2047_ = v___y_2164_;
v___y_2048_ = v___y_2165_;
v___y_2049_ = v___y_2166_;
v___y_2050_ = v___x_2196_;
goto v___jp_2036_;
}
}
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
lean_dec_ref(v___y_2163_);
lean_dec_ref(v___y_2156_);
v___x_2198_ = lean_nat_add(v_n_1906_, v_one_1905_);
lean_dec(v_n_1906_);
v___x_2199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___y_2164_);
lean_ctor_set(v___x_2199_, 1, v_acc_996_);
v___x_2200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_2201_ = l_Lean_Name_append(v___x_2200_, v_trace_991_);
v___x_2202_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2157_, v___y_2159_, v___x_2201_);
lean_dec(v___x_2201_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = l_Lean_trace_profiler;
v___x_2204_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2159_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; 
lean_inc(v_trace_991_);
v___x_2205_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___x_2198_, v___y_2166_, v___x_2199_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
v___y_1125_ = v___y_2159_;
v___y_1126_ = v___x_2189_;
v___y_1127_ = v___y_2155_;
v___y_1128_ = v___y_2160_;
v___y_1129_ = v___y_2161_;
v___y_1130_ = v_a_2168_;
v___y_1131_ = v___y_2165_;
v___y_1132_ = v___x_2205_;
goto v___jp_1124_;
}
else
{
v___y_1400_ = v___x_2189_;
v___y_1401_ = v___y_2155_;
v___y_1402_ = v_a_2168_;
v___y_1403_ = v___y_2159_;
v___y_1404_ = v___x_2170_;
v___y_1405_ = v___y_2160_;
v___y_1406_ = v___y_2161_;
v___y_1407_ = v___x_2202_;
v___y_1408_ = v___x_2198_;
v___y_1409_ = v___x_2199_;
v___y_1410_ = v___y_2165_;
v___y_1411_ = v___y_2166_;
goto v___jp_1399_;
}
}
else
{
v___y_1400_ = v___x_2189_;
v___y_1401_ = v___y_2155_;
v___y_1402_ = v_a_2168_;
v___y_1403_ = v___y_2159_;
v___y_1404_ = v___x_2170_;
v___y_1405_ = v___y_2160_;
v___y_1406_ = v___y_2161_;
v___y_1407_ = v___x_2202_;
v___y_1408_ = v___x_2198_;
v___y_1409_ = v___x_2199_;
v___y_1410_ = v___y_2165_;
v___y_1411_ = v___y_2166_;
goto v___jp_1399_;
}
}
}
else
{
lean_object* v_a_2206_; 
lean_dec(v___y_2166_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec_ref(v___y_2156_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec_ref(v_cfg_990_);
v_a_2206_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2190_, 1);
v___y_1115_ = v___x_2189_;
v___y_1116_ = v___y_2159_;
v___y_1117_ = v___y_2155_;
v___y_1118_ = v___y_2160_;
v___y_1119_ = v___y_2161_;
v___y_1120_ = v_a_2168_;
v___y_1121_ = v___y_2165_;
v_a_1122_ = v_a_2206_;
goto v___jp_1114_;
}
}
}
v___jp_2207_:
{
if (v___y_2212_ == 0)
{
lean_object* v___x_2213_; 
lean_dec_ref(v___y_2210_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v___y_2209_);
v___x_2213_ = lean_apply_6(v___y_2208_, v___y_2209_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v___x_2213_, 1);
if (lean_obj_tag(v_a_2214_) == 0)
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_nat_add(v_n_1906_, v_one_1905_);
lean_dec(v_n_1906_);
v___x_2216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___y_2209_);
lean_ctor_set(v___x_2216_, 1, v_acc_996_);
v_n_994_ = v___x_2215_;
v_curr_995_ = v___y_2211_;
v_acc_996_ = v___x_2216_;
goto _start;
}
else
{
lean_object* v_val_2218_; lean_object* v___x_2219_; 
lean_dec(v___y_2209_);
v_val_2218_ = lean_ctor_get(v_a_2214_, 0);
lean_inc(v_val_2218_);
lean_dec_ref_known(v_a_2214_, 1);
v___x_2219_ = l_List_appendTR___redArg(v_val_2218_, v___y_2211_);
v_n_994_ = v_n_1906_;
v_curr_995_ = v___x_2219_;
goto _start;
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec(v___y_2211_);
lean_dec(v___y_2209_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
v_a_2221_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2213_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2213_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
else
{
lean_dec(v___y_2211_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
return v___y_2210_;
}
}
v___jp_2229_:
{
if (lean_obj_tag(v_a_2230_) == 0)
{
if (lean_obj_tag(v_curr_995_) == 0)
{
lean_object* v_toCold_2231_; lean_object* v_options_2232_; lean_object* v_inheritedTraceOptions_2233_; uint8_t v_hasTrace_2234_; lean_object* v___x_2235_; 
lean_dec(v_n_1906_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec_ref(v_cfg_990_);
v_toCold_2231_ = lean_ctor_get(v_a_999_, 0);
v_options_2232_ = lean_ctor_get(v_toCold_2231_, 2);
v_inheritedTraceOptions_2233_ = lean_ctor_get(v_toCold_2231_, 11);
v_hasTrace_2234_ = lean_ctor_get_uint8(v_options_2232_, sizeof(void*)*1);
v___x_2235_ = l_List_reverse___redArg(v_acc_996_);
if (v_hasTrace_2234_ == 0)
{
lean_object* v___x_2236_; 
lean_dec(v_trace_991_);
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_2239_ = l_Lean_Name_append(v___x_2238_, v_trace_991_);
v___x_2240_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2233_, v_options_2232_, v___x_2239_);
lean_dec(v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = l_Lean_trace_profiler;
v___x_2242_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2232_, v___x_2241_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; 
lean_dec(v_trace_991_);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2235_);
return v___x_2243_;
}
else
{
v___y_1195_ = v___x_2237_;
v___y_1196_ = v___x_2235_;
v___y_1197_ = v_hasTrace_2234_;
v___y_1198_ = v___x_2240_;
v___y_1199_ = v_options_2232_;
goto v___jp_1194_;
}
}
else
{
v___y_1195_ = v___x_2237_;
v___y_1196_ = v___x_2235_;
v___y_1197_ = v_hasTrace_2234_;
v___y_1198_ = v___x_2240_;
v___y_1199_ = v_options_2232_;
goto v___jp_1194_;
}
}
}
else
{
lean_object* v_head_2244_; lean_object* v_tail_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2319_; 
v_head_2244_ = lean_ctor_get(v_curr_995_, 0);
v_tail_2245_ = lean_ctor_get(v_curr_995_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_curr_995_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2247_ = v_curr_995_;
v_isShared_2248_ = v_isSharedCheck_2319_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_tail_2245_);
lean_inc(v_head_2244_);
lean_dec(v_curr_995_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2319_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___f_2249_; lean_object* v___f_2250_; lean_object* v___f_2251_; lean_object* v___x_2252_; lean_object* v_a_2253_; uint8_t v___x_2254_; uint8_t v___x_2255_; 
lean_inc(v_acc_996_);
lean_inc(v_n_1906_);
lean_inc(v_goals_993_);
lean_inc_ref(v_next_992_);
lean_inc(v_trace_991_);
lean_inc_ref(v_cfg_990_);
lean_inc(v_tail_2245_);
v___f_2249_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2249_, 0, v_tail_2245_);
lean_closure_set(v___f_2249_, 1, v_cfg_990_);
lean_closure_set(v___f_2249_, 2, v_trace_991_);
lean_closure_set(v___f_2249_, 3, v_next_992_);
lean_closure_set(v___f_2249_, 4, v_goals_993_);
lean_closure_set(v___f_2249_, 5, v_n_1906_);
lean_closure_set(v___f_2249_, 6, v_acc_996_);
lean_inc_n(v_head_2244_, 2);
v___f_2250_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___boxed), 7, 1);
lean_closure_set(v___f_2250_, 0, v_head_2244_);
v___f_2251_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(v___f_2251_, 0, v_head_2244_);
v___x_2252_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2244_, v_a_998_);
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref(v___x_2252_);
v___x_2254_ = 1;
v___x_2255_ = lean_unbox(v_a_2253_);
lean_dec(v_a_2253_);
if (v___x_2255_ == 0)
{
lean_object* v_toCold_2256_; lean_object* v_options_2257_; uint8_t v_hasTrace_2258_; 
lean_dec_ref(v___f_2250_);
v_toCold_2256_ = lean_ctor_get(v_a_999_, 0);
v_options_2257_ = lean_ctor_get(v_toCold_2256_, 2);
v_hasTrace_2258_ = lean_ctor_get_uint8(v_options_2257_, sizeof(void*)*1);
if (v_hasTrace_2258_ == 0)
{
lean_object* v___x_2259_; 
lean_dec_ref(v___f_2251_);
lean_inc_ref(v_suspend_1191_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v_head_2244_);
v___x_2259_ = lean_apply_6(v_suspend_1191_, v_head_2244_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; uint8_t v___x_2261_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v___x_2259_, 1);
v___x_2261_ = lean_unbox(v_a_2260_);
lean_dec(v_a_2260_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; 
lean_del_object(v___x_2247_);
lean_inc_ref(v_next_992_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v_head_2244_);
v___x_2262_ = lean_apply_7(v_next_992_, v_head_2244_, v___f_2249_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_dec(v_tail_2245_);
lean_dec(v_head_2244_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
return v___x_2262_;
}
else
{
lean_object* v_a_2263_; uint8_t v___x_2264_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
v___x_2264_ = l_Lean_Exception_isInterrupt(v_a_2263_);
if (v___x_2264_ == 0)
{
uint8_t v___x_2265_; 
v___x_2265_ = l_Lean_Exception_isRuntime(v_a_2263_);
lean_inc_ref(v_discharge_1192_);
v___y_2208_ = v_discharge_1192_;
v___y_2209_ = v_head_2244_;
v___y_2210_ = v___x_2262_;
v___y_2211_ = v_tail_2245_;
v___y_2212_ = v___x_2265_;
goto v___jp_2207_;
}
else
{
lean_dec(v_a_2263_);
lean_inc_ref(v_discharge_1192_);
v___y_2208_ = v_discharge_1192_;
v___y_2209_ = v_head_2244_;
v___y_2210_ = v___x_2262_;
v___y_2211_ = v_tail_2245_;
v___y_2212_ = v___x_2264_;
goto v___jp_2207_;
}
}
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_dec_ref(v___f_2249_);
v___x_2266_ = lean_nat_add(v_n_1906_, v_one_1905_);
lean_dec(v_n_1906_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 1, v_acc_996_);
v___x_2268_ = v___x_2247_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_head_2244_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_acc_996_);
v___x_2268_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
v_n_994_ = v___x_2266_;
v_curr_995_ = v_tail_2245_;
v_acc_996_ = v___x_2268_;
goto _start;
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref(v___f_2249_);
lean_del_object(v___x_2247_);
lean_dec(v_tail_2245_);
lean_dec(v_head_2244_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
v_a_2271_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2259_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2259_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_inheritedTraceOptions_2279_ = lean_ctor_get(v_toCold_2256_, 11);
v___x_2280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_2282_ = l_Lean_Name_append(v___x_2281_, v_trace_991_);
v___x_2283_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2279_, v_options_2257_, v___x_2282_);
lean_dec(v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = l_Lean_trace_profiler;
v___x_2285_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2257_, v___x_2284_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; 
lean_dec_ref(v___f_2251_);
lean_inc_ref(v_suspend_1191_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v_head_2244_);
v___x_2286_ = lean_apply_6(v_suspend_1191_, v_head_2244_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; uint8_t v___x_2288_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = lean_unbox(v_a_2287_);
lean_dec(v_a_2287_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; 
lean_del_object(v___x_2247_);
lean_inc_ref(v_next_992_);
lean_inc(v_a_1000_);
lean_inc_ref(v_a_999_);
lean_inc(v_a_998_);
lean_inc_ref(v_a_997_);
lean_inc(v_head_2244_);
v___x_2289_ = lean_apply_7(v_next_992_, v_head_2244_, v___f_2249_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, lean_box(0));
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_dec(v_tail_2245_);
lean_dec(v_head_2244_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
return v___x_2289_;
}
else
{
lean_object* v_a_2290_; uint8_t v___x_2291_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
v___x_2291_ = l_Lean_Exception_isInterrupt(v_a_2290_);
if (v___x_2291_ == 0)
{
uint8_t v___x_2292_; 
v___x_2292_ = l_Lean_Exception_isRuntime(v_a_2290_);
lean_inc_ref(v_discharge_1192_);
v___y_1954_ = v_options_2257_;
v___y_1955_ = v___x_2280_;
v___y_1956_ = v___x_2254_;
v___y_1957_ = v_inheritedTraceOptions_2279_;
v___y_1958_ = v___x_2285_;
v___y_1959_ = v_discharge_1192_;
v___y_1960_ = v___x_2289_;
v___y_1961_ = v_head_2244_;
v___y_1962_ = v_tail_2245_;
v___y_1963_ = v___x_2292_;
goto v___jp_1953_;
}
else
{
lean_dec(v_a_2290_);
lean_inc_ref(v_discharge_1192_);
v___y_1954_ = v_options_2257_;
v___y_1955_ = v___x_2280_;
v___y_1956_ = v___x_2254_;
v___y_1957_ = v_inheritedTraceOptions_2279_;
v___y_1958_ = v___x_2285_;
v___y_1959_ = v_discharge_1192_;
v___y_1960_ = v___x_2289_;
v___y_1961_ = v_head_2244_;
v___y_1962_ = v_tail_2245_;
v___y_1963_ = v___x_2291_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
lean_dec_ref(v___f_2249_);
v___x_2293_ = lean_nat_add(v_n_1906_, v_one_1905_);
lean_dec(v_n_1906_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 1, v_acc_996_);
v___x_2295_ = v___x_2247_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_head_2244_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_acc_996_);
v___x_2295_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
if (v___x_2283_ == 0)
{
if (v___x_2285_ == 0)
{
v_n_994_ = v___x_2293_;
v_curr_995_ = v_tail_2245_;
v_acc_996_ = v___x_2295_;
goto _start;
}
else
{
v___y_1858_ = v_options_2257_;
v___y_1859_ = v___x_2280_;
v___y_1860_ = v___x_2254_;
v___y_1861_ = v___x_2295_;
v___y_1862_ = v___x_2293_;
v___y_1863_ = v___x_2283_;
v___y_1864_ = v_tail_2245_;
goto v___jp_1857_;
}
}
else
{
v___y_1858_ = v_options_2257_;
v___y_1859_ = v___x_2280_;
v___y_1860_ = v___x_2254_;
v___y_1861_ = v___x_2295_;
v___y_1862_ = v___x_2293_;
v___y_1863_ = v___x_2283_;
v___y_1864_ = v_tail_2245_;
goto v___jp_1857_;
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec_ref(v___f_2249_);
lean_del_object(v___x_2247_);
lean_dec(v_tail_2245_);
lean_dec(v_head_2244_);
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
v_a_2298_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2286_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2286_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_del_object(v___x_2247_);
lean_inc_ref(v_discharge_1192_);
lean_inc_ref(v_suspend_1191_);
lean_inc_ref(v___f_2249_);
v___y_2155_ = v___x_2280_;
v___y_2156_ = v___f_2249_;
v___y_2157_ = v_inheritedTraceOptions_2279_;
v___y_2158_ = v___f_2249_;
v___y_2159_ = v_options_2257_;
v___y_2160_ = v___x_2283_;
v___y_2161_ = v___x_2254_;
v___y_2162_ = v_suspend_1191_;
v___y_2163_ = v_discharge_1192_;
v___y_2164_ = v_head_2244_;
v___y_2165_ = v___f_2251_;
v___y_2166_ = v_tail_2245_;
goto v___jp_2154_;
}
}
else
{
lean_del_object(v___x_2247_);
lean_inc_ref(v_discharge_1192_);
lean_inc_ref(v_suspend_1191_);
lean_inc_ref(v___f_2249_);
v___y_2155_ = v___x_2280_;
v___y_2156_ = v___f_2249_;
v___y_2157_ = v_inheritedTraceOptions_2279_;
v___y_2158_ = v___f_2249_;
v___y_2159_ = v_options_2257_;
v___y_2160_ = v___x_2283_;
v___y_2161_ = v___x_2254_;
v___y_2162_ = v_suspend_1191_;
v___y_2163_ = v_discharge_1192_;
v___y_2164_ = v_head_2244_;
v___y_2165_ = v___f_2251_;
v___y_2166_ = v_tail_2245_;
goto v___jp_2154_;
}
}
}
else
{
lean_object* v_toCold_2306_; lean_object* v_options_2307_; lean_object* v_inheritedTraceOptions_2308_; uint8_t v_hasTrace_2309_; lean_object* v___x_2310_; 
lean_dec_ref(v___f_2251_);
lean_dec_ref(v___f_2249_);
lean_del_object(v___x_2247_);
lean_dec(v_head_2244_);
v_toCold_2306_ = lean_ctor_get(v_a_999_, 0);
v_options_2307_ = lean_ctor_get(v_toCold_2306_, 2);
v_inheritedTraceOptions_2308_ = lean_ctor_get(v_toCold_2306_, 11);
v_hasTrace_2309_ = lean_ctor_get_uint8(v_options_2307_, sizeof(void*)*1);
v___x_2310_ = lean_nat_add(v_n_1906_, v_one_1905_);
lean_dec(v_n_1906_);
if (v_hasTrace_2309_ == 0)
{
lean_dec_ref(v___f_2250_);
v_n_994_ = v___x_2310_;
v_curr_995_ = v_tail_2245_;
goto _start;
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_991_);
v___x_2314_ = l_Lean_Name_append(v___x_2313_, v_trace_991_);
v___x_2315_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2308_, v_options_2307_, v___x_2314_);
lean_dec(v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = l_Lean_trace_profiler;
v___x_2317_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2307_, v___x_2316_);
if (v___x_2317_ == 0)
{
lean_dec_ref(v___f_2250_);
v_n_994_ = v___x_2310_;
v_curr_995_ = v_tail_2245_;
goto _start;
}
else
{
v___y_1040_ = v_options_2307_;
v___y_1041_ = v___x_2254_;
v___y_1042_ = v___x_2312_;
v___y_1043_ = v___x_2310_;
v___y_1044_ = v___x_2315_;
v___y_1045_ = v___f_2250_;
v___y_1046_ = v_tail_2245_;
goto v___jp_1039_;
}
}
else
{
v___y_1040_ = v_options_2307_;
v___y_1041_ = v___x_2254_;
v___y_1042_ = v___x_2312_;
v___y_1043_ = v___x_2310_;
v___y_1044_ = v___x_2315_;
v___y_1045_ = v___f_2250_;
v___y_1046_ = v_tail_2245_;
goto v___jp_1039_;
}
}
}
}
}
}
else
{
lean_object* v_val_2320_; 
lean_dec(v_curr_995_);
v_val_2320_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_val_2320_);
lean_dec_ref_known(v_a_2230_, 1);
v_n_994_ = v_n_1906_;
v_curr_995_ = v_val_2320_;
goto _start;
}
}
v___jp_2322_:
{
if (lean_obj_tag(v___y_2323_) == 0)
{
lean_object* v_a_2324_; 
v_a_2324_ = lean_ctor_get(v___y_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___y_2323_, 1);
v_a_2230_ = v_a_2324_;
goto v___jp_2229_;
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_n_1906_);
lean_dec(v_acc_996_);
lean_dec(v_curr_995_);
lean_dec(v_goals_993_);
lean_dec_ref(v_next_992_);
lean_dec(v_trace_991_);
lean_dec_ref(v_cfg_990_);
v_a_2325_ = lean_ctor_get(v___y_2323_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___y_2323_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___y_2323_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___y_2323_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
v___jp_1002_:
{
lean_object* v___x_1011_; double v___x_1012_; double v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1011_ = lean_io_get_num_heartbeats();
v___x_1012_ = lean_float_of_nat(v___y_1009_);
v___x_1013_ = lean_float_of_nat(v___x_1011_);
v___x_1014_ = lean_box_float(v___x_1012_);
v___x_1015_ = lean_box_float(v___x_1013_);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v_a_1010_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
lean_inc_ref(v___y_1005_);
v___x_1018_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1004_, v___y_1005_, v___y_1003_, v___y_1006_, v___y_1008_, v___y_1007_, v___x_1017_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1018_;
}
v___jp_1019_:
{
lean_object* v___x_1028_; double v___x_1029_; double v___x_1030_; double v___x_1031_; double v___x_1032_; double v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1028_ = lean_io_mono_nanos_now();
v___x_1029_ = lean_float_of_nat(v___y_1021_);
v___x_1030_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1031_ = lean_float_div(v___x_1029_, v___x_1030_);
v___x_1032_ = lean_float_of_nat(v___x_1028_);
v___x_1033_ = lean_float_div(v___x_1032_, v___x_1030_);
v___x_1034_ = lean_box_float(v___x_1031_);
v___x_1035_ = lean_box_float(v___x_1033_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v_a_1027_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
lean_inc_ref(v___y_1023_);
v___x_1038_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1022_, v___y_1023_, v___y_1020_, v___y_1024_, v___y_1026_, v___y_1025_, v___x_1037_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1038_;
}
v___jp_1039_:
{
lean_object* v___x_1047_; lean_object* v_a_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1047_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_1000_);
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1050_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1040_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_io_mono_nanos_now();
lean_inc(v_trace_991_);
v___x_1052_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1043_, v___y_1046_, v_acc_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 1);
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
v___y_1020_ = v___y_1040_;
v___y_1021_ = v___x_1051_;
v___y_1022_ = v___y_1041_;
v___y_1023_ = v___y_1042_;
v___y_1024_ = v___y_1044_;
v___y_1025_ = v___y_1045_;
v___y_1026_ = v_a_1048_;
v_a_1027_ = v___x_1058_;
goto v___jp_1019_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
v_a_1061_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1052_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1052_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set_tag(v___x_1063_, 0);
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
v___y_1020_ = v___y_1040_;
v___y_1021_ = v___x_1051_;
v___y_1022_ = v___y_1041_;
v___y_1023_ = v___y_1042_;
v___y_1024_ = v___y_1044_;
v___y_1025_ = v___y_1045_;
v___y_1026_ = v_a_1048_;
v_a_1027_ = v___x_1066_;
goto v___jp_1019_;
}
}
}
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_991_);
v___x_1070_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v___y_1043_, v___y_1046_, v_acc_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
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
v___y_1003_ = v___y_1040_;
v___y_1004_ = v___y_1041_;
v___y_1005_ = v___y_1042_;
v___y_1006_ = v___y_1044_;
v___y_1007_ = v___y_1045_;
v___y_1008_ = v_a_1048_;
v___y_1009_ = v___x_1069_;
v_a_1010_ = v___x_1076_;
goto v___jp_1002_;
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
v___y_1003_ = v___y_1040_;
v___y_1004_ = v___y_1041_;
v___y_1005_ = v___y_1042_;
v___y_1006_ = v___y_1044_;
v___y_1007_ = v___y_1045_;
v___y_1008_ = v_a_1048_;
v___y_1009_ = v___x_1069_;
v_a_1010_ = v___x_1084_;
goto v___jp_1002_;
}
}
}
}
}
v___jp_1087_:
{
lean_object* v___x_1096_; double v___x_1097_; double v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1096_ = lean_io_get_num_heartbeats();
v___x_1097_ = lean_float_of_nat(v___y_1089_);
v___x_1098_ = lean_float_of_nat(v___x_1096_);
v___x_1099_ = lean_box_float(v___x_1097_);
v___x_1100_ = lean_box_float(v___x_1098_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v_a_1095_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
lean_inc_ref(v___y_1090_);
v___x_1103_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1092_, v___y_1090_, v___y_1088_, v___y_1091_, v___y_1093_, v___y_1094_, v___x_1102_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1103_;
}
v___jp_1104_:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_a_1112_);
v___y_1088_ = v___y_1106_;
v___y_1089_ = v___y_1105_;
v___y_1090_ = v___y_1107_;
v___y_1091_ = v___y_1108_;
v___y_1092_ = v___y_1109_;
v___y_1093_ = v___y_1110_;
v___y_1094_ = v___y_1111_;
v_a_1095_ = v___x_1113_;
goto v___jp_1087_;
}
v___jp_1114_:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_a_1122_);
v___y_1088_ = v___y_1116_;
v___y_1089_ = v___y_1115_;
v___y_1090_ = v___y_1117_;
v___y_1091_ = v___y_1118_;
v___y_1092_ = v___y_1119_;
v___y_1093_ = v___y_1120_;
v___y_1094_ = v___y_1121_;
v_a_1095_ = v___x_1123_;
goto v___jp_1087_;
}
v___jp_1124_:
{
if (lean_obj_tag(v___y_1132_) == 0)
{
lean_object* v_a_1133_; 
v_a_1133_ = lean_ctor_get(v___y_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___y_1132_, 1);
v___y_1105_ = v___y_1126_;
v___y_1106_ = v___y_1125_;
v___y_1107_ = v___y_1127_;
v___y_1108_ = v___y_1128_;
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___y_1130_;
v___y_1111_ = v___y_1131_;
v_a_1112_ = v_a_1133_;
goto v___jp_1104_;
}
else
{
lean_object* v_a_1134_; 
v_a_1134_ = lean_ctor_get(v___y_1132_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___y_1132_, 1);
v___y_1115_ = v___y_1126_;
v___y_1116_ = v___y_1125_;
v___y_1117_ = v___y_1127_;
v___y_1118_ = v___y_1128_;
v___y_1119_ = v___y_1129_;
v___y_1120_ = v___y_1130_;
v___y_1121_ = v___y_1131_;
v_a_1122_ = v_a_1134_;
goto v___jp_1114_;
}
}
v___jp_1135_:
{
lean_object* v___x_1144_; double v___x_1145_; double v___x_1146_; double v___x_1147_; double v___x_1148_; double v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1144_ = lean_io_mono_nanos_now();
v___x_1145_ = lean_float_of_nat(v___y_1140_);
v___x_1146_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1147_ = lean_float_div(v___x_1145_, v___x_1146_);
v___x_1148_ = lean_float_of_nat(v___x_1144_);
v___x_1149_ = lean_float_div(v___x_1148_, v___x_1146_);
v___x_1150_ = lean_box_float(v___x_1147_);
v___x_1151_ = lean_box_float(v___x_1149_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v_a_1143_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
lean_inc_ref(v___y_1137_);
v___x_1154_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_991_, v___y_1139_, v___y_1137_, v___y_1136_, v___y_1138_, v___y_1141_, v___y_1142_, v___x_1153_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
return v___x_1154_;
}
v___jp_1155_:
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1164_, 0, v_a_1163_);
v___y_1136_ = v___y_1156_;
v___y_1137_ = v___y_1157_;
v___y_1138_ = v___y_1158_;
v___y_1139_ = v___y_1159_;
v___y_1140_ = v___y_1160_;
v___y_1141_ = v___y_1161_;
v___y_1142_ = v___y_1162_;
v_a_1143_ = v___x_1164_;
goto v___jp_1135_;
}
v___jp_1165_:
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_a_1173_);
v___y_1136_ = v___y_1166_;
v___y_1137_ = v___y_1167_;
v___y_1138_ = v___y_1168_;
v___y_1139_ = v___y_1169_;
v___y_1140_ = v___y_1170_;
v___y_1141_ = v___y_1171_;
v___y_1142_ = v___y_1172_;
v_a_1143_ = v___x_1174_;
goto v___jp_1135_;
}
v___jp_1175_:
{
if (lean_obj_tag(v___y_1183_) == 0)
{
lean_object* v_a_1184_; 
v_a_1184_ = lean_ctor_get(v___y_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___y_1183_, 1);
v___y_1156_ = v___y_1176_;
v___y_1157_ = v___y_1177_;
v___y_1158_ = v___y_1178_;
v___y_1159_ = v___y_1179_;
v___y_1160_ = v___y_1180_;
v___y_1161_ = v___y_1181_;
v___y_1162_ = v___y_1182_;
v_a_1163_ = v_a_1184_;
goto v___jp_1155_;
}
else
{
lean_object* v_a_1185_; 
v_a_1185_ = lean_ctor_get(v___y_1183_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___y_1183_, 1);
v___y_1166_ = v___y_1176_;
v___y_1167_ = v___y_1177_;
v___y_1168_ = v___y_1178_;
v___y_1169_ = v___y_1179_;
v___y_1170_ = v___y_1180_;
v___y_1171_ = v___y_1181_;
v___y_1172_ = v___y_1182_;
v_a_1173_ = v_a_1185_;
goto v___jp_1165_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_990_ = stack[0].m_obj;
lean_object* v_trace_991_ = stack[1].m_obj;
lean_object* v_next_992_ = stack[2].m_obj;
lean_object* v_goals_993_ = stack[3].m_obj;
lean_object* v_n_994_ = stack[4].m_obj;
lean_object* v_curr_995_ = stack[5].m_obj;
lean_object* v_acc_996_ = stack[6].m_obj;
lean_object* v_a_997_ = stack[7].m_obj;
lean_object* v_a_998_ = stack[8].m_obj;
lean_object* v_a_999_ = stack[9].m_obj;
lean_object* v_a_1000_ = stack[10].m_obj;
lean_object* v_res_2404_;
v_res_2404_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_990_, v_trace_991_, v_next_992_, v_goals_993_, v_n_994_, v_curr_995_, v_acc_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
stack->m_obj
 = v_res_2404_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2405_, lean_object* v_trace_2406_, lean_object* v_next_2407_, lean_object* v_goals_2408_, lean_object* v_n_2409_, lean_object* v_curr_2410_, lean_object* v_acc_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2405_, v_trace_2406_, v_next_2407_, v_goals_2408_, v_n_2409_, v_curr_2410_, v_acc_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
return v_res_2417_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object* v_tail_2418_, lean_object* v_cfg_2419_, lean_object* v_trace_2420_, lean_object* v_next_2421_, lean_object* v_goals_2422_, lean_object* v_n_2423_, lean_object* v_acc_2424_, lean_object* v_r_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = l_List_appendTR___redArg(v_r_2425_, v_tail_2418_);
v___x_2432_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2432_, 0, v_cfg_2419_);
lean_closure_set(v___x_2432_, 1, v_trace_2420_);
lean_closure_set(v___x_2432_, 2, v_next_2421_);
lean_closure_set(v___x_2432_, 3, v_goals_2422_);
lean_closure_set(v___x_2432_, 4, v_n_2423_);
lean_closure_set(v___x_2432_, 5, v___x_2431_);
lean_closure_set(v___x_2432_, 6, v_acc_2424_);
v___x_2433_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v___x_2432_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
return v___x_2433_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_2418_ = stack[0].m_obj;
lean_object* v_cfg_2419_ = stack[1].m_obj;
lean_object* v_trace_2420_ = stack[2].m_obj;
lean_object* v_next_2421_ = stack[3].m_obj;
lean_object* v_goals_2422_ = stack[4].m_obj;
lean_object* v_n_2423_ = stack[5].m_obj;
lean_object* v_acc_2424_ = stack[6].m_obj;
lean_object* v_r_2425_ = stack[7].m_obj;
lean_object* v___y_2426_ = stack[8].m_obj;
lean_object* v___y_2427_ = stack[9].m_obj;
lean_object* v___y_2428_ = stack[10].m_obj;
lean_object* v___y_2429_ = stack[11].m_obj;
lean_object* v_res_2434_;
v_res_2434_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_2418_, v_cfg_2419_, v_trace_2420_, v_next_2421_, v_goals_2422_, v_n_2423_, v_acc_2424_, v_r_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
stack->m_obj
 = v_res_2434_;
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2435_, lean_object* v_msg_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
return v___x_2442_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2436_ = stack[1].m_obj;
lean_object* v___y_2437_ = stack[2].m_obj;
lean_object* v___y_2438_ = stack[3].m_obj;
lean_object* v___y_2439_ = stack[4].m_obj;
lean_object* v___y_2440_ = stack[5].m_obj;
lean_object* v_res_2443_;
v_res_2443_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_box(0), v_msg_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
stack->m_obj
 = v_res_2443_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2444_, lean_object* v_msg_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2444_, v_msg_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2451_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object* v_00_u03b1_2452_, lean_object* v_x_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_2453_);
return v___x_2459_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2453_ = stack[1].m_obj;
lean_object* v___y_2454_ = stack[2].m_obj;
lean_object* v___y_2455_ = stack[3].m_obj;
lean_object* v___y_2456_ = stack[4].m_obj;
lean_object* v___y_2457_ = stack[5].m_obj;
lean_object* v_res_2460_;
v_res_2460_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_box(0), v_x_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
stack->m_obj
 = v_res_2460_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2461_, lean_object* v_x_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_00_u03b1_2461_, v_x_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
return v_res_2468_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* v_mvarId_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_2469_, v___y_2471_);
return v___x_2475_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2469_ = stack[0].m_obj;
lean_object* v___y_2470_ = stack[1].m_obj;
lean_object* v___y_2471_ = stack[2].m_obj;
lean_object* v___y_2472_ = stack[3].m_obj;
lean_object* v___y_2473_ = stack[4].m_obj;
lean_object* v_res_2476_;
v_res_2476_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_mvarId_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
stack->m_obj
 = v_res_2476_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* v_mvarId_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_mvarId_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v_mvarId_2477_);
return v_res_2483_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_object* v_00_u03b2_2484_, lean_object* v_x_2485_, lean_object* v_x_2486_){
_start:
{
uint8_t v___x_2487_; 
v___x_2487_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_2485_, v_x_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2485_ = stack[1].m_obj;
lean_object* v_x_2486_ = stack[2].m_obj;
uint8_t v_res_2488_;
v_res_2488_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_box(0), v_x_2485_, v_x_2486_);
stack->m_num = v_res_2488_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2489_, lean_object* v_x_2490_, lean_object* v_x_2491_){
_start:
{
uint8_t v_res_2492_; lean_object* v_r_2493_; 
v_res_2492_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(v_00_u03b2_2489_, v_x_2490_, v_x_2491_);
lean_dec(v_x_2491_);
lean_dec_ref(v_x_2490_);
v_r_2493_ = lean_box(v_res_2492_);
return v_r_2493_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_2494_, lean_object* v_x_2495_, size_t v_x_2496_, lean_object* v_x_2497_){
_start:
{
uint8_t v___x_2498_; 
v___x_2498_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_2495_, v_x_2496_, v_x_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2495_ = stack[1].m_obj;
size_t v_x_2496_ = stack[2].m_num;
lean_object* v_x_2497_ = stack[3].m_obj;
uint8_t v_res_2499_;
v_res_2499_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_box(0), v_x_2495_, v_x_2496_, v_x_2497_);
stack->m_num = v_res_2499_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___boxed(lean_object* v_00_u03b2_2500_, lean_object* v_x_2501_, lean_object* v_x_2502_, lean_object* v_x_2503_){
_start:
{
size_t v_x_79756__boxed_2504_; uint8_t v_res_2505_; lean_object* v_r_2506_; 
v_x_79756__boxed_2504_ = lean_unbox_usize(v_x_2502_);
lean_dec(v_x_2502_);
v_res_2505_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2500_, v_x_2501_, v_x_79756__boxed_2504_, v_x_2503_);
lean_dec(v_x_2503_);
lean_dec_ref(v_x_2501_);
v_r_2506_ = lean_box(v_res_2505_);
return v_r_2506_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_object* v_00_u03b2_2507_, lean_object* v_keys_2508_, lean_object* v_vals_2509_, lean_object* v_heq_2510_, lean_object* v_i_2511_, lean_object* v_k_2512_){
_start:
{
uint8_t v___x_2513_; 
v___x_2513_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_2508_, v_i_2511_, v_k_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2508_ = stack[1].m_obj;
lean_object* v_vals_2509_ = stack[2].m_obj;
lean_object* v_i_2511_ = stack[4].m_obj;
lean_object* v_k_2512_ = stack[5].m_obj;
uint8_t v_res_2514_;
v_res_2514_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_box(0), v_keys_2508_, v_vals_2509_, lean_box(0), v_i_2511_, v_k_2512_);
stack->m_num = v_res_2514_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2515_, lean_object* v_keys_2516_, lean_object* v_vals_2517_, lean_object* v_heq_2518_, lean_object* v_i_2519_, lean_object* v_k_2520_){
_start:
{
uint8_t v_res_2521_; lean_object* v_r_2522_; 
v_res_2521_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(v_00_u03b2_2515_, v_keys_2516_, v_vals_2517_, v_heq_2518_, v_i_2519_, v_k_2520_);
lean_dec(v_k_2520_);
lean_dec_ref(v_vals_2517_);
lean_dec_ref(v_keys_2516_);
v_r_2522_ = lean_box(v_res_2521_);
return v_r_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2523_, lean_object* v_h__1_2524_, lean_object* v_h__2_2525_){
_start:
{
lean_object* v_zero_2526_; uint8_t v_isZero_2527_; 
v_zero_2526_ = lean_unsigned_to_nat(0u);
v_isZero_2527_ = lean_nat_dec_eq(v_n_2523_, v_zero_2526_);
if (v_isZero_2527_ == 1)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec(v_h__2_2525_);
v___x_2528_ = lean_box(0);
v___x_2529_ = lean_apply_1(v_h__1_2524_, v___x_2528_);
return v___x_2529_;
}
else
{
lean_object* v_one_2530_; lean_object* v_n_2531_; lean_object* v___x_2532_; 
lean_dec(v_h__1_2524_);
v_one_2530_ = lean_unsigned_to_nat(1u);
v_n_2531_ = lean_nat_sub(v_n_2523_, v_one_2530_);
v___x_2532_ = lean_apply_1(v_h__2_2525_, v_n_2531_);
return v___x_2532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2533_, lean_object* v_h__1_2534_, lean_object* v_h__2_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2533_, v_h__1_2534_, v_h__2_2535_);
lean_dec(v_n_2533_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2537_, lean_object* v_n_2538_, lean_object* v_h__1_2539_, lean_object* v_h__2_2540_){
_start:
{
lean_object* v_zero_2541_; uint8_t v_isZero_2542_; 
v_zero_2541_ = lean_unsigned_to_nat(0u);
v_isZero_2542_ = lean_nat_dec_eq(v_n_2538_, v_zero_2541_);
if (v_isZero_2542_ == 1)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec(v_h__2_2540_);
v___x_2543_ = lean_box(0);
v___x_2544_ = lean_apply_1(v_h__1_2539_, v___x_2543_);
return v___x_2544_;
}
else
{
lean_object* v_one_2545_; lean_object* v_n_2546_; lean_object* v___x_2547_; 
lean_dec(v_h__1_2539_);
v_one_2545_ = lean_unsigned_to_nat(1u);
v_n_2546_ = lean_nat_sub(v_n_2538_, v_one_2545_);
v___x_2547_ = lean_apply_1(v_h__2_2540_, v_n_2546_);
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* v_motive_2548_, lean_object* v_n_2549_, lean_object* v_h__1_2550_, lean_object* v_h__2_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(v_motive_2548_, v_n_2549_, v_h__1_2550_, v_h__2_2551_);
lean_dec(v_n_2549_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* v_procResult_x3f_2553_, lean_object* v_h__1_2554_, lean_object* v_h__2_2555_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2553_) == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec(v_h__1_2554_);
v___x_2556_ = lean_box(0);
v___x_2557_ = lean_apply_1(v_h__2_2555_, v___x_2556_);
return v___x_2557_;
}
else
{
lean_object* v_val_2558_; lean_object* v___x_2559_; 
lean_dec(v_h__2_2555_);
v_val_2558_ = lean_ctor_get(v_procResult_x3f_2553_, 0);
lean_inc(v_val_2558_);
lean_dec_ref_known(v_procResult_x3f_2553_, 1);
v___x_2559_ = lean_apply_1(v_h__1_2554_, v_val_2558_);
return v___x_2559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* v_motive_2560_, lean_object* v_procResult_x3f_2561_, lean_object* v_h__1_2562_, lean_object* v_h__2_2563_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2561_) == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec(v_h__1_2562_);
v___x_2564_ = lean_box(0);
v___x_2565_ = lean_apply_1(v_h__2_2563_, v___x_2564_);
return v___x_2565_;
}
else
{
lean_object* v_val_2566_; lean_object* v___x_2567_; 
lean_dec(v_h__2_2563_);
v_val_2566_ = lean_ctor_get(v_procResult_x3f_2561_, 0);
lean_inc(v_val_2566_);
lean_dec_ref_known(v_procResult_x3f_2561_, 1);
v___x_2567_ = lean_apply_1(v_h__1_2562_, v_val_2566_);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2568_, lean_object* v_h__1_2569_, lean_object* v_h__2_2570_){
_start:
{
if (lean_obj_tag(v_curr_2568_) == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec(v_h__2_2570_);
v___x_2571_ = lean_box(0);
v___x_2572_ = lean_apply_1(v_h__1_2569_, v___x_2571_);
return v___x_2572_;
}
else
{
lean_object* v_head_2573_; lean_object* v_tail_2574_; lean_object* v___x_2575_; 
lean_dec(v_h__1_2569_);
v_head_2573_ = lean_ctor_get(v_curr_2568_, 0);
lean_inc(v_head_2573_);
v_tail_2574_ = lean_ctor_get(v_curr_2568_, 1);
lean_inc(v_tail_2574_);
lean_dec_ref_known(v_curr_2568_, 2);
v___x_2575_ = lean_apply_2(v_h__2_2570_, v_head_2573_, v_tail_2574_);
return v___x_2575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2576_, lean_object* v_curr_2577_, lean_object* v_h__1_2578_, lean_object* v_h__2_2579_){
_start:
{
if (lean_obj_tag(v_curr_2577_) == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec(v_h__2_2579_);
v___x_2580_ = lean_box(0);
v___x_2581_ = lean_apply_1(v_h__1_2578_, v___x_2580_);
return v___x_2581_;
}
else
{
lean_object* v_head_2582_; lean_object* v_tail_2583_; lean_object* v___x_2584_; 
lean_dec(v_h__1_2578_);
v_head_2582_ = lean_ctor_get(v_curr_2577_, 0);
lean_inc(v_head_2582_);
v_tail_2583_ = lean_ctor_get(v_curr_2577_, 1);
lean_inc(v_tail_2583_);
lean_dec_ref_known(v_curr_2577_, 2);
v___x_2584_ = lean_apply_2(v_h__2_2579_, v_head_2582_, v_tail_2583_);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2585_, lean_object* v_h__1_2586_, lean_object* v_h__2_2587_){
_start:
{
if (lean_obj_tag(v_____do__lift_2585_) == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec(v_h__2_2587_);
v___x_2588_ = lean_box(0);
v___x_2589_ = lean_apply_1(v_h__1_2586_, v___x_2588_);
return v___x_2589_;
}
else
{
lean_object* v_val_2590_; lean_object* v___x_2591_; 
lean_dec(v_h__1_2586_);
v_val_2590_ = lean_ctor_get(v_____do__lift_2585_, 0);
lean_inc(v_val_2590_);
lean_dec_ref_known(v_____do__lift_2585_, 1);
v___x_2591_ = lean_apply_1(v_h__2_2587_, v_val_2590_);
return v___x_2591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_2592_, lean_object* v_____do__lift_2593_, lean_object* v_h__1_2594_, lean_object* v_h__2_2595_){
_start:
{
if (lean_obj_tag(v_____do__lift_2593_) == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
lean_dec(v_h__2_2595_);
v___x_2596_ = lean_box(0);
v___x_2597_ = lean_apply_1(v_h__1_2594_, v___x_2596_);
return v___x_2597_;
}
else
{
lean_object* v_val_2598_; lean_object* v___x_2599_; 
lean_dec(v_h__1_2594_);
v_val_2598_ = lean_ctor_get(v_____do__lift_2593_, 0);
lean_inc(v_val_2598_);
lean_dec_ref_known(v_____do__lift_2593_, 1);
v___x_2599_ = lean_apply_1(v_h__2_2595_, v_val_2598_);
return v___x_2599_;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_2600_, lean_object* v_trace_2601_, lean_object* v_next_2602_, lean_object* v_orig_2603_, lean_object* v_g_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_maxDepth_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v_maxDepth_2610_ = lean_ctor_get(v_cfg_2600_, 0);
lean_inc(v_maxDepth_2610_);
v___x_2611_ = lean_box(0);
v___x_2612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2612_, 0, v_g_2604_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2600_, v_trace_2601_, v_next_2602_, v_orig_2603_, v_maxDepth_2610_, v___x_2612_, v___x_2611_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2613_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2600_ = stack[0].m_obj;
lean_object* v_trace_2601_ = stack[1].m_obj;
lean_object* v_next_2602_ = stack[2].m_obj;
lean_object* v_orig_2603_ = stack[3].m_obj;
lean_object* v_g_2604_ = stack[4].m_obj;
lean_object* v___y_2605_ = stack[5].m_obj;
lean_object* v___y_2606_ = stack[6].m_obj;
lean_object* v___y_2607_ = stack[7].m_obj;
lean_object* v___y_2608_ = stack[8].m_obj;
lean_object* v_res_2614_;
v_res_2614_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2600_, v_trace_2601_, v_next_2602_, v_orig_2603_, v_g_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
stack->m_obj
 = v_res_2614_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_2615_, lean_object* v_trace_2616_, lean_object* v_next_2617_, lean_object* v_orig_2618_, lean_object* v_g_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2615_, v_trace_2616_, v_next_2617_, v_orig_2618_, v_g_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
if (lean_obj_tag(v_a_2626_) == 0)
{
lean_object* v___x_2628_; 
v___x_2628_ = l_List_reverse___redArg(v_a_2627_);
return v___x_2628_;
}
else
{
lean_object* v_head_2629_; lean_object* v_tail_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2639_; 
v_head_2629_ = lean_ctor_get(v_a_2626_, 0);
v_tail_2630_ = lean_ctor_get(v_a_2626_, 1);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_a_2626_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2632_ = v_a_2626_;
v_isShared_2633_ = v_isSharedCheck_2639_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_tail_2630_);
lean_inc(v_head_2629_);
lean_dec(v_a_2626_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2639_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2634_ = l_Lean_MessageData_ofFormat(v_head_2629_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 1, v_a_2627_);
lean_ctor_set(v___x_2632_, 0, v___x_2634_);
v___x_2636_ = v___x_2632_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_a_2627_);
v___x_2636_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
v_a_2626_ = v_tail_2630_;
v_a_2627_ = v___x_2636_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_2642_ = l_Lean_stringToMessageData(v___x_2641_);
return v___x_2642_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_2645_ = l_Lean_stringToMessageData(v___x_2644_);
return v___x_2645_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_2648_ = l_Lean_stringToMessageData(v___x_2647_);
return v___x_2648_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_2649_, lean_object* v_snd_2650_, lean_object* v_x_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2649_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2659_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_2650_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2679_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2679_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2679_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_2665_ = lean_box(0);
v___x_2666_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2658_, v___x_2665_);
v___x_2667_ = l_Lean_MessageData_ofList(v___x_2666_);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2664_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2668_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_2672_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2660_, v___x_2665_);
v___x_2673_ = l_Lean_MessageData_ofList(v___x_2672_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2671_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2670_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2675_);
v___x_2677_ = v___x_2662_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec(v_a_2658_);
v_a_2680_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2659_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2659_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_snd_2650_);
v_a_2688_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2657_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2657_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2649_ = stack[0].m_obj;
lean_object* v_snd_2650_ = stack[1].m_obj;
lean_object* v_x_2651_ = stack[2].m_obj;
lean_object* v___y_2652_ = stack[3].m_obj;
lean_object* v___y_2653_ = stack[4].m_obj;
lean_object* v___y_2654_ = stack[5].m_obj;
lean_object* v___y_2655_ = stack[6].m_obj;
lean_object* v_res_2696_;
v_res_2696_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2649_, v_snd_2650_, v_x_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
stack->m_obj
 = v_res_2696_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_2697_, lean_object* v_snd_2698_, lean_object* v_x_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2697_, v_snd_2698_, v_x_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec_ref(v_x_2699_);
return v_res_2705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_2708_ = l_Lean_stringToMessageData(v___x_2707_);
return v___x_2708_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_2711_ = l_Lean_stringToMessageData(v___x_2710_);
return v___x_2711_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_2712_, lean_object* v___x_2713_, lean_object* v_x_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2712_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2722_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v___x_2722_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_2713_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2740_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2725_ = v___x_2722_;
v_isShared_2726_ = v_isSharedCheck_2740_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2740_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2727_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_2728_ = lean_box(0);
v___x_2729_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2721_, v___x_2728_);
v___x_2730_ = l_Lean_MessageData_ofList(v___x_2729_);
v___x_2731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2727_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_2733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2731_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
v___x_2734_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2723_, v___x_2728_);
v___x_2735_ = l_Lean_MessageData_ofList(v___x_2734_);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2733_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 0, v___x_2736_);
v___x_2738_ = v___x_2725_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_a_2721_);
v_a_2741_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2722_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2722_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec(v___x_2713_);
v_a_2749_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2720_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2720_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2712_ = stack[0].m_obj;
lean_object* v___x_2713_ = stack[1].m_obj;
lean_object* v_x_2714_ = stack[2].m_obj;
lean_object* v___y_2715_ = stack[3].m_obj;
lean_object* v___y_2716_ = stack[4].m_obj;
lean_object* v___y_2717_ = stack[5].m_obj;
lean_object* v___y_2718_ = stack[6].m_obj;
lean_object* v_res_2757_;
v_res_2757_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2712_, v___x_2713_, v_x_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
stack->m_obj
 = v_res_2757_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_2758_, lean_object* v___x_2759_, lean_object* v_x_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2758_, v___x_2759_, v_x_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec_ref(v_x_2760_);
return v_res_2766_;
}
}
lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t v___x_2767_, lean_object* v_x_2768_, lean_object* v_x_2769_, lean_object* v___y_2770_){
_start:
{
if (lean_obj_tag(v_x_2768_) == 0)
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_x_2769_);
return v___x_2772_;
}
else
{
lean_object* v_head_2773_; lean_object* v_tail_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2789_; 
v_head_2773_ = lean_ctor_get(v_x_2768_, 0);
v_tail_2774_ = lean_ctor_get(v_x_2768_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_x_2768_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2776_ = v_x_2768_;
v_isShared_2777_ = v_isSharedCheck_2789_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_tail_2774_);
lean_inc(v_head_2773_);
lean_dec(v_x_2768_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2789_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
uint8_t v_a_2784_; lean_object* v___x_2786_; lean_object* v_a_2787_; uint8_t v___x_2788_; 
v___x_2786_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2773_, v___y_2770_);
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = lean_unbox(v_a_2787_);
lean_dec(v_a_2787_);
if (v___x_2788_ == 0)
{
goto v___jp_2778_;
}
else
{
v_a_2784_ = v___x_2767_;
goto v___jp_2783_;
}
v___jp_2778_:
{
lean_object* v___x_2780_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v_x_2769_);
v___x_2780_ = v___x_2776_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_head_2773_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v_x_2769_);
v___x_2780_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
v_x_2768_ = v_tail_2774_;
v_x_2769_ = v___x_2780_;
goto _start;
}
}
v___jp_2783_:
{
if (v_a_2784_ == 0)
{
lean_del_object(v___x_2776_);
lean_dec(v_head_2773_);
v_x_2768_ = v_tail_2774_;
goto _start;
}
else
{
goto v___jp_2778_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2767_ = stack[0].m_num;
lean_object* v_x_2768_ = stack[1].m_obj;
lean_object* v_x_2769_ = stack[2].m_obj;
lean_object* v___y_2770_ = stack[3].m_obj;
lean_object* v_res_2790_;
v_res_2790_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_2767_, v_x_2768_, v_x_2769_, v___y_2770_);
stack->m_obj
 = v_res_2790_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v___x_2791_, lean_object* v_x_2792_, lean_object* v_x_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
uint8_t v___x_45862__boxed_2796_; lean_object* v_res_2797_; 
v___x_45862__boxed_2796_ = lean_unbox(v___x_2791_);
v_res_2797_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_45862__boxed_2796_, v_x_2792_, v_x_2793_, v___y_2794_);
lean_dec(v___y_2794_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
if (lean_obj_tag(v_a_2798_) == 0)
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_array_to_list(v_a_2799_);
return v___x_2800_;
}
else
{
lean_object* v_head_2801_; lean_object* v_tail_2802_; lean_object* v___x_2803_; 
v_head_2801_ = lean_ctor_get(v_a_2798_, 0);
lean_inc(v_head_2801_);
v_tail_2802_ = lean_ctor_get(v_a_2798_, 1);
lean_inc(v_tail_2802_);
lean_dec_ref_known(v_a_2798_, 2);
v___x_2803_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2799_, v_head_2801_);
v_a_2798_ = v_tail_2802_;
v_a_2799_ = v___x_2803_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
if (lean_obj_tag(v_a_2806_) == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
lean_dec(v_goals_2805_);
v___x_2814_ = lean_array_to_list(v_a_2807_);
v___x_2815_ = lean_array_to_list(v_a_2808_);
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2814_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
return v___x_2817_;
}
else
{
lean_object* v_head_2818_; lean_object* v_tail_2819_; lean_object* v___x_2820_; 
v_head_2818_ = lean_ctor_get(v_a_2806_, 0);
lean_inc_n(v_head_2818_, 2);
v_tail_2819_ = lean_ctor_get(v_a_2806_, 1);
lean_inc(v_tail_2819_);
lean_dec_ref_known(v_a_2806_, 2);
lean_inc(v_goals_2805_);
v___x_2820_ = l_Lean_MVarId_isIndependentOf(v_goals_2805_, v_head_2818_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; uint8_t v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = lean_unbox(v_a_2821_);
lean_dec(v_a_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; 
v___x_2823_ = lean_array_push(v_a_2808_, v_head_2818_);
v_a_2806_ = v_tail_2819_;
v_a_2808_ = v___x_2823_;
goto _start;
}
else
{
lean_object* v___x_2825_; 
v___x_2825_ = lean_array_push(v_a_2807_, v_head_2818_);
v_a_2806_ = v_tail_2819_;
v_a_2807_ = v___x_2825_;
goto _start;
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec(v_tail_2819_);
lean_dec(v_head_2818_);
lean_dec_ref(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_goals_2805_);
v_a_2827_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2820_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2820_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_goals_2805_ = stack[0].m_obj;
lean_object* v_a_2806_ = stack[1].m_obj;
lean_object* v_a_2807_ = stack[2].m_obj;
lean_object* v_a_2808_ = stack[3].m_obj;
lean_object* v___y_2809_ = stack[4].m_obj;
lean_object* v___y_2810_ = stack[5].m_obj;
lean_object* v___y_2811_ = stack[6].m_obj;
lean_object* v___y_2812_ = stack[7].m_obj;
lean_object* v_res_2835_;
v_res_2835_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
stack->m_obj
 = v_res_2835_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
if (lean_obj_tag(v_a_2846_) == 0)
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_array_to_list(v_a_2847_);
return v___x_2848_;
}
else
{
lean_object* v_head_2849_; 
v_head_2849_ = lean_ctor_get(v_a_2846_, 0);
if (lean_obj_tag(v_head_2849_) == 0)
{
lean_object* v_tail_2850_; lean_object* v_val_2851_; lean_object* v___x_2852_; 
lean_inc_ref(v_head_2849_);
v_tail_2850_ = lean_ctor_get(v_a_2846_, 1);
lean_inc(v_tail_2850_);
lean_dec_ref_known(v_a_2846_, 2);
v_val_2851_ = lean_ctor_get(v_head_2849_, 0);
lean_inc(v_val_2851_);
lean_dec_ref_known(v_head_2849_, 1);
v___x_2852_ = lean_array_push(v_a_2847_, v_val_2851_);
v_a_2846_ = v_tail_2850_;
v_a_2847_ = v___x_2852_;
goto _start;
}
else
{
lean_object* v_tail_2854_; 
v_tail_2854_ = lean_ctor_get(v_a_2846_, 1);
lean_inc(v_tail_2854_);
lean_dec_ref_known(v_a_2846_, 2);
v_a_2846_ = v_tail_2854_;
goto _start;
}
}
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_2856_, lean_object* v_x_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
if (lean_obj_tag(v_x_2857_) == 0)
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec_ref(v_f_2856_);
v___x_2864_ = l_List_reverse___redArg(v_x_2858_);
v___x_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
return v___x_2865_;
}
else
{
lean_object* v_head_2866_; lean_object* v_tail_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2912_; 
v_head_2866_ = lean_ctor_get(v_x_2857_, 0);
v_tail_2867_ = lean_ctor_get(v_x_2857_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_x_2857_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2869_ = v_x_2857_;
v_isShared_2870_ = v_isSharedCheck_2912_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_tail_2867_);
lean_inc(v_head_2866_);
lean_dec(v_x_2857_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2912_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v_a_2872_; lean_object* v___x_2877_; 
v___x_2877_ = l_Lean_Meta_saveState___redArg(v___y_2860_, v___y_2862_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2879_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
lean_inc_ref(v_f_2856_);
lean_inc(v___y_2862_);
lean_inc_ref(v___y_2861_);
lean_inc(v___y_2860_);
lean_inc_ref(v___y_2859_);
lean_inc(v_head_2866_);
v___x_2879_ = lean_apply_6(v_f_2856_, v_head_2866_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, lean_box(0));
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; 
lean_dec(v_a_2878_);
lean_dec(v_head_2866_);
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2879_, 1);
v___x_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2881_, 0, v_a_2880_);
v_a_2872_ = v___x_2881_;
goto v___jp_2871_;
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2903_; 
v_a_2882_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2884_ = v___x_2879_;
v_isShared_2885_ = v_isSharedCheck_2903_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2879_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2903_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
uint8_t v___y_2887_; uint8_t v___x_2901_; 
v___x_2901_ = l_Lean_Exception_isInterrupt(v_a_2882_);
if (v___x_2901_ == 0)
{
uint8_t v___x_2902_; 
lean_inc(v_a_2882_);
v___x_2902_ = l_Lean_Exception_isRuntime(v_a_2882_);
v___y_2887_ = v___x_2902_;
goto v___jp_2886_;
}
else
{
v___y_2887_ = v___x_2901_;
goto v___jp_2886_;
}
v___jp_2886_:
{
if (v___y_2887_ == 0)
{
lean_object* v___x_2888_; 
lean_del_object(v___x_2884_);
lean_dec(v_a_2882_);
v___x_2888_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2878_, v___y_2860_, v___y_2862_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v___x_2889_; 
lean_dec_ref_known(v___x_2888_, 1);
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v_head_2866_);
v_a_2872_ = v___x_2889_;
goto v___jp_2871_;
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_del_object(v___x_2869_);
lean_dec(v_tail_2867_);
lean_dec(v_head_2866_);
lean_dec(v_x_2858_);
lean_dec_ref(v_f_2856_);
v_a_2890_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2888_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2888_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_object* v___x_2899_; 
lean_dec(v_a_2878_);
lean_del_object(v___x_2869_);
lean_dec(v_tail_2867_);
lean_dec(v_head_2866_);
lean_dec(v_x_2858_);
lean_dec_ref(v_f_2856_);
if (v_isShared_2885_ == 0)
{
v___x_2899_ = v___x_2884_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2882_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_del_object(v___x_2869_);
lean_dec(v_tail_2867_);
lean_dec(v_head_2866_);
lean_dec(v_x_2858_);
lean_dec_ref(v_f_2856_);
v_a_2904_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2877_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2877_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
v___jp_2871_:
{
lean_object* v___x_2874_; 
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 1, v_x_2858_);
lean_ctor_set(v___x_2869_, 0, v_a_2872_);
v___x_2874_ = v___x_2869_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2872_);
lean_ctor_set(v_reuseFailAlloc_2876_, 1, v_x_2858_);
v___x_2874_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
v_x_2857_ = v_tail_2867_;
v_x_2858_ = v___x_2874_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2856_ = stack[0].m_obj;
lean_object* v_x_2857_ = stack[1].m_obj;
lean_object* v_x_2858_ = stack[2].m_obj;
lean_object* v___y_2859_ = stack[3].m_obj;
lean_object* v___y_2860_ = stack[4].m_obj;
lean_object* v___y_2861_ = stack[5].m_obj;
lean_object* v___y_2862_ = stack[6].m_obj;
lean_object* v_res_2913_;
v_res_2913_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2856_, v_x_2857_, v_x_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
stack->m_obj
 = v_res_2913_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2914_, v_x_2915_, v_x_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
if (lean_obj_tag(v_a_2923_) == 0)
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_array_to_list(v_a_2924_);
return v___x_2925_;
}
else
{
lean_object* v_head_2926_; 
v_head_2926_ = lean_ctor_get(v_a_2923_, 0);
if (lean_obj_tag(v_head_2926_) == 1)
{
lean_object* v_tail_2927_; lean_object* v_val_2928_; lean_object* v___x_2929_; 
lean_inc_ref(v_head_2926_);
v_tail_2927_ = lean_ctor_get(v_a_2923_, 1);
lean_inc(v_tail_2927_);
lean_dec_ref_known(v_a_2923_, 2);
v_val_2928_ = lean_ctor_get(v_head_2926_, 0);
lean_inc(v_val_2928_);
lean_dec_ref_known(v_head_2926_, 1);
v___x_2929_ = lean_array_push(v_a_2924_, v_val_2928_);
v_a_2923_ = v_tail_2927_;
v_a_2924_ = v___x_2929_;
goto _start;
}
else
{
lean_object* v_tail_2931_; 
v_tail_2931_ = lean_ctor_get(v_a_2923_, 1);
lean_inc(v_tail_2931_);
lean_dec_ref_known(v_a_2923_, 2);
v_a_2923_ = v_tail_2931_;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_2933_, lean_object* v_f_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = lean_box(0);
v___x_2941_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2934_, v_L_2933_, v___x_2940_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2953_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2944_ = v___x_2941_;
v_isShared_2945_ = v_isSharedCheck_2953_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2941_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2953_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2946_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_2942_);
v___x_2947_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_2942_, v___x_2946_);
v___x_2948_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_2942_, v___x_2946_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2947_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v___x_2949_);
v___x_2951_ = v___x_2944_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
v_a_2954_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2941_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2941_);
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
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_L_2933_ = stack[0].m_obj;
lean_object* v_f_2934_ = stack[1].m_obj;
lean_object* v___y_2935_ = stack[2].m_obj;
lean_object* v___y_2936_ = stack[3].m_obj;
lean_object* v___y_2937_ = stack[4].m_obj;
lean_object* v___y_2938_ = stack[5].m_obj;
lean_object* v_res_2962_;
v_res_2962_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_2933_, v_f_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
stack->m_obj
 = v_res_2962_;
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
lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t v___x_2971_, uint8_t v___x_2972_, lean_object* v_x_2973_, lean_object* v_x_2974_, lean_object* v___y_2975_){
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
LEAN_EXPORT void l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2971_ = stack[0].m_num;
uint8_t v___x_2972_ = stack[1].m_num;
lean_object* v_x_2973_ = stack[2].m_obj;
lean_object* v_x_2974_ = stack[3].m_obj;
lean_object* v___y_2975_ = stack[4].m_obj;
lean_object* v_res_2994_;
v_res_2994_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_2971_, v___x_2972_, v_x_2973_, v_x_2974_, v___y_2975_);
stack->m_obj
 = v_res_2994_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* v___x_2995_, lean_object* v___x_2996_, lean_object* v_x_2997_, lean_object* v_x_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
uint8_t v___x_46403__boxed_3001_; uint8_t v___x_46404__boxed_3002_; lean_object* v_res_3003_; 
v___x_46403__boxed_3001_ = lean_unbox(v___x_2995_);
v___x_46404__boxed_3002_ = lean_unbox(v___x_2996_);
v_res_3003_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_46403__boxed_3001_, v___x_46404__boxed_3002_, v_x_2997_, v_x_2998_, v___y_2999_);
lean_dec(v___y_2999_);
return v_res_3003_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1));
v___x_3008_ = l_Lean_stringToMessageData(v___x_3007_);
return v___x_3008_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_3009_, lean_object* v_trace_3010_, lean_object* v_next_3011_, lean_object* v_orig_3012_, lean_object* v_goals_3013_, lean_object* v_remaining_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v___f_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_inc(v_orig_3012_);
lean_inc_ref(v_next_3011_);
lean_inc(v_trace_3010_);
lean_inc_ref(v_cfg_3009_);
v___f_3020_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3020_, 0, v_cfg_3009_);
lean_closure_set(v___f_3020_, 1, v_trace_3010_);
lean_closure_set(v___f_3020_, 2, v_next_3011_);
lean_closure_set(v___f_3020_, 3, v_orig_3012_);
v___x_3021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
lean_inc(v_remaining_3014_);
lean_inc(v_goals_3013_);
v___x_3022_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_3013_, v_remaining_3014_, v___x_3021_, v___x_3021_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v_fst_3024_; lean_object* v_snd_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_4225_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v_fst_3024_ = lean_ctor_get(v_a_3023_, 0);
v_snd_3025_ = lean_ctor_get(v_a_3023_, 1);
v_isSharedCheck_4225_ = !lean_is_exclusive(v_a_3023_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_3027_ = v_a_3023_;
v_isShared_3028_ = v_isSharedCheck_4225_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_snd_3025_);
lean_inc(v_fst_3024_);
lean_dec(v_a_3023_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_4225_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
uint8_t v___x_3029_; 
v___x_3029_ = l_List_isEmpty___redArg(v_fst_3024_);
if (v___x_3029_ == 0)
{
lean_object* v_toCold_3030_; lean_object* v_options_3031_; uint8_t v_hasTrace_3032_; 
lean_dec(v_remaining_3014_);
v_toCold_3030_ = lean_ctor_get(v_a_3017_, 0);
v_options_3031_ = lean_ctor_get(v_toCold_3030_, 2);
v_hasTrace_3032_ = lean_ctor_get_uint8(v_options_3031_, sizeof(void*)*1);
if (v_hasTrace_3032_ == 0)
{
lean_object* v___x_3033_; 
lean_del_object(v___x_3027_);
v___x_3033_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3024_, v___f_3020_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3106_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3036_ = v___x_3033_;
v_isShared_3037_ = v_isSharedCheck_3106_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3106_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v_fst_3038_; lean_object* v_snd_3039_; lean_object* v___x_3040_; lean_object* v_a_3042_; lean_object* v___y_3049_; lean_object* v___y_3052_; lean_object* v___y_3053_; uint8_t v___y_3054_; lean_object* v___y_3065_; lean_object* v___y_3081_; uint8_t v___y_3082_; lean_object* v_a_3097_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v_fst_3038_ = lean_ctor_get(v_a_3034_, 0);
lean_inc(v_fst_3038_);
v_snd_3039_ = lean_ctor_get(v_a_3034_, 1);
lean_inc(v_snd_3039_);
lean_dec(v_a_3034_);
v___x_3040_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3039_, v___x_3021_);
v___x_3101_ = lean_box(0);
v___x_3102_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_3029_, v_goals_3013_, v___x_3101_, v_a_3016_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3104_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
v___x_3104_ = l_List_reverse___redArg(v_a_3103_);
v_a_3097_ = v___x_3104_;
goto v___jp_3096_;
}
else
{
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3105_; 
v_a_3105_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3102_, 1);
v_a_3097_ = v_a_3105_;
goto v___jp_3096_;
}
else
{
lean_dec(v___x_3040_);
lean_dec(v_fst_3038_);
lean_del_object(v___x_3036_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec(v_trace_3010_);
lean_dec_ref(v_cfg_3009_);
return v___x_3102_;
}
}
v___jp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3043_ = l_List_appendTR___redArg(v___x_3040_, v_fst_3038_);
v___x_3044_ = l_List_appendTR___redArg(v___x_3043_, v_a_3042_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3044_);
v___x_3046_ = v___x_3036_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
v___jp_3048_:
{
if (lean_obj_tag(v___y_3049_) == 0)
{
lean_object* v_a_3050_; 
v_a_3050_ = lean_ctor_get(v___y_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref_known(v___y_3049_, 1);
v_a_3042_ = v_a_3050_;
goto v___jp_3041_;
}
else
{
lean_dec(v___x_3040_);
lean_dec(v_fst_3038_);
lean_del_object(v___x_3036_);
return v___y_3049_;
}
}
v___jp_3051_:
{
if (v___y_3054_ == 0)
{
lean_object* v___x_3055_; 
lean_dec_ref(v___y_3053_);
v___x_3055_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3052_, v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_dec_ref_known(v___x_3055_, 1);
v_a_3042_ = v_snd_3025_;
goto v___jp_3041_;
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v___x_3040_);
lean_dec(v_fst_3038_);
lean_del_object(v___x_3036_);
lean_dec(v_snd_3025_);
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3055_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_dec_ref(v___y_3052_);
lean_dec(v_snd_3025_);
v___y_3049_ = v___y_3053_;
goto v___jp_3048_;
}
}
v___jp_3064_:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_Meta_saveState___redArg(v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3068_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___x_3066_, 1);
lean_inc(v_snd_3025_);
v___x_3068_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3065_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_dec(v_a_3067_);
lean_dec(v_snd_3025_);
v___y_3049_ = v___x_3068_;
goto v___jp_3048_;
}
else
{
lean_object* v_a_3069_; uint8_t v___x_3070_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v___x_3070_ = l_Lean_Exception_isInterrupt(v_a_3069_);
if (v___x_3070_ == 0)
{
uint8_t v___x_3071_; 
lean_inc(v_a_3069_);
v___x_3071_ = l_Lean_Exception_isRuntime(v_a_3069_);
v___y_3052_ = v_a_3067_;
v___y_3053_ = v___x_3068_;
v___y_3054_ = v___x_3071_;
goto v___jp_3051_;
}
else
{
v___y_3052_ = v_a_3067_;
v___y_3053_ = v___x_3068_;
v___y_3054_ = v___x_3070_;
goto v___jp_3051_;
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v___y_3065_);
lean_dec(v___x_3040_);
lean_dec(v_fst_3038_);
lean_del_object(v___x_3036_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec(v_trace_3010_);
lean_dec_ref(v_cfg_3009_);
v_a_3072_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3066_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3066_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
v___jp_3080_:
{
if (v___y_3082_ == 0)
{
uint8_t v___x_3083_; 
lean_del_object(v___x_3036_);
v___x_3083_ = l_List_isEmpty___redArg(v_fst_3038_);
lean_dec(v_fst_3038_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
lean_dec(v___y_3081_);
lean_dec(v___x_3040_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec(v_trace_3010_);
lean_dec_ref(v_cfg_3009_);
v___x_3084_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3085_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3084_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_3085_;
}
else
{
lean_object* v___x_3086_; 
v___x_3086_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3081_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3095_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3089_ = v___x_3086_;
v_isShared_3090_ = v_isSharedCheck_3095_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3095_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3091_ = l_List_appendTR___redArg(v___x_3040_, v_a_3087_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3091_);
v___x_3093_ = v___x_3089_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
else
{
lean_dec(v___x_3040_);
return v___x_3086_;
}
}
}
else
{
v___y_3065_ = v___y_3081_;
goto v___jp_3064_;
}
}
v___jp_3096_:
{
uint8_t v_commitIndependentGoals_3098_; lean_object* v___x_3099_; 
v_commitIndependentGoals_3098_ = lean_ctor_get_uint8(v_cfg_3009_, sizeof(void*)*4);
lean_inc(v___x_3040_);
v___x_3099_ = l_List_appendTR___redArg(v_a_3097_, v___x_3040_);
if (v_commitIndependentGoals_3098_ == 0)
{
v___y_3081_ = v___x_3099_;
v___y_3082_ = v___x_3029_;
goto v___jp_3080_;
}
else
{
uint8_t v___x_3100_; 
v___x_3100_ = l_List_isEmpty___redArg(v___x_3040_);
if (v___x_3100_ == 0)
{
v___y_3065_ = v___x_3099_;
goto v___jp_3064_;
}
else
{
v___y_3081_ = v___x_3099_;
v___y_3082_ = v___x_3029_;
goto v___jp_3080_;
}
}
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec(v_snd_3025_);
lean_dec(v_goals_3013_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec(v_trace_3010_);
lean_dec_ref(v_cfg_3009_);
v_a_3107_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3033_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3033_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3115_; lean_object* v___f_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v_a_3124_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v_a_3138_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v_a_3143_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v_a_3150_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; uint8_t v___y_3168_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v_a_3197_; lean_object* v___y_3210_; uint8_t v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v_a_3216_; lean_object* v___y_3219_; uint8_t v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v_a_3225_; lean_object* v___y_3228_; lean_object* v___y_3229_; uint8_t v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v_a_3236_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; uint8_t v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; uint8_t v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; uint8_t v___y_3262_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; uint8_t v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; uint8_t v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; uint8_t v___y_3302_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; uint8_t v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v_a_3318_; uint8_t v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v_a_3329_; uint8_t v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v_a_3345_; uint8_t v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v_a_3354_; lean_object* v___y_3357_; lean_object* v___y_3358_; uint8_t v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v_a_3365_; lean_object* v___y_3369_; lean_object* v___y_3370_; uint8_t v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3381_; lean_object* v___y_3382_; uint8_t v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; uint8_t v___y_3391_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; uint8_t v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; uint8_t v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3422_; lean_object* v___y_3423_; uint8_t v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; uint8_t v___y_3437_; uint8_t v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; uint8_t v___y_3444_; lean_object* v___y_3449_; lean_object* v___y_3450_; uint8_t v___y_3451_; uint8_t v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v_a_3458_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; uint8_t v___y_3466_; uint8_t v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; uint8_t v___y_3493_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v_a_3505_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v_a_3512_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v_a_3527_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v_a_3532_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v_a_3539_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; uint8_t v___y_3557_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3580_; uint8_t v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v_a_3586_; lean_object* v___y_3596_; uint8_t v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v_a_3602_; lean_object* v___y_3605_; lean_object* v___y_3606_; uint8_t v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v_a_3613_; lean_object* v___y_3617_; uint8_t v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v_a_3623_; lean_object* v___y_3626_; uint8_t v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3636_; lean_object* v___y_3637_; uint8_t v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3648_; lean_object* v___y_3649_; uint8_t v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; uint8_t v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; uint8_t v___y_3670_; lean_object* v___y_3674_; lean_object* v___y_3675_; uint8_t v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3691_; lean_object* v___y_3692_; uint8_t v___y_3693_; uint8_t v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; uint8_t v___y_3701_; lean_object* v___y_3706_; lean_object* v___y_3707_; uint8_t v___y_3708_; uint8_t v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v_a_3715_; uint8_t v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v_a_3726_; lean_object* v___y_3739_; uint8_t v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v_a_3745_; lean_object* v___y_3748_; uint8_t v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v_a_3754_; lean_object* v___y_3757_; uint8_t v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v_a_3765_; lean_object* v___y_3769_; lean_object* v___y_3770_; uint8_t v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3781_; lean_object* v___y_3782_; uint8_t v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; uint8_t v___y_3791_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; uint8_t v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3822_; lean_object* v___y_3823_; uint8_t v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; uint8_t v___y_3831_; lean_object* v___y_3839_; lean_object* v___y_3840_; uint8_t v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v_a_3847_; lean_object* v___y_3852_; uint8_t v___y_3853_; uint8_t v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; uint8_t v___y_3882_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v_a_3894_; 
v_inheritedTraceOptions_3115_ = lean_ctor_get(v_toCold_3030_, 11);
lean_inc(v_snd_3025_);
lean_inc(v_fst_3024_);
v___f_3116_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3116_, 0, v_fst_3024_);
lean_closure_set(v___f_3116_, 1, v_snd_3025_);
v___x_3117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_3118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_3010_);
v___x_3119_ = l_Lean_Name_append(v___x_3118_, v_trace_3010_);
v___x_3120_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3115_, v_options_3031_, v___x_3119_);
lean_dec(v___x_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3943_; uint8_t v___x_3944_; 
v___x_3943_ = l_Lean_trace_profiler;
v___x_3944_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3031_, v___x_3943_);
if (v___x_3944_ == 0)
{
lean_object* v___x_3945_; 
lean_dec_ref(v___f_3116_);
lean_del_object(v___x_3027_);
v___x_3945_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3024_, v___f_3020_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_4213_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_3948_ = v___x_3945_;
v_isShared_3949_ = v_isSharedCheck_4213_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3945_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_4213_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v_fst_3950_; lean_object* v_snd_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_4212_; 
v_fst_3950_ = lean_ctor_get(v_a_3946_, 0);
v_snd_3951_ = lean_ctor_get(v_a_3946_, 1);
v_isSharedCheck_4212_ = !lean_is_exclusive(v_a_3946_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_3953_ = v_a_3946_;
v_isShared_3954_ = v_isSharedCheck_4212_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_snd_3951_);
lean_inc(v_fst_3950_);
lean_dec(v_a_3946_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_4212_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3955_; lean_object* v_a_3957_; lean_object* v___y_3964_; lean_object* v___y_3967_; lean_object* v___y_3968_; uint8_t v___y_3969_; lean_object* v___y_3980_; lean_object* v___y_3996_; uint8_t v___y_3997_; lean_object* v_a_4012_; lean_object* v___f_4016_; lean_object* v___x_4017_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v_a_4021_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v_a_4038_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v_a_4043_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v_a_4049_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; uint8_t v___y_4068_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; uint8_t v___y_4086_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v_a_4096_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v_a_4103_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v_a_4115_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v_a_4120_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v_a_4125_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; uint8_t v___y_4139_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; uint8_t v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; uint8_t v___y_4171_; uint8_t v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v_a_4179_; 
v___x_3955_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3951_, v___x_3021_);
lean_inc(v___x_3955_);
lean_inc(v_fst_3950_);
v___f_4016_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_4016_, 0, v_fst_3950_);
lean_closure_set(v___f_4016_, 1, v___x_3955_);
v___x_4017_ = lean_box(0);
if (v___x_3120_ == 0)
{
if (v___x_3944_ == 0)
{
lean_object* v___x_4208_; 
lean_dec_ref(v___f_4016_);
lean_del_object(v___x_3953_);
v___x_4208_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3032_, v___x_3029_, v_goals_3013_, v___x_4017_, v_a_3016_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4210_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref_known(v___x_4208_, 1);
v___x_4210_ = l_List_reverse___redArg(v_a_4209_);
v_a_4012_ = v___x_4210_;
goto v___jp_4011_;
}
else
{
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4211_; 
v_a_4211_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4211_);
lean_dec_ref_known(v___x_4208_, 1);
v_a_4012_ = v_a_4211_;
goto v___jp_4011_;
}
else
{
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
lean_del_object(v___x_3948_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec(v_trace_3010_);
lean_dec_ref(v_cfg_3009_);
return v___x_4208_;
}
}
}
else
{
lean_del_object(v___x_3948_);
goto v___jp_4183_;
}
}
else
{
lean_del_object(v___x_3948_);
goto v___jp_4183_;
}
v___jp_3956_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3958_ = l_List_appendTR___redArg(v___x_3955_, v_fst_3950_);
v___x_3959_ = l_List_appendTR___redArg(v___x_3958_, v_a_3957_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 0, v___x_3959_);
v___x_3961_ = v___x_3948_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3959_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
v___jp_3963_:
{
if (lean_obj_tag(v___y_3964_) == 0)
{
lean_object* v_a_3965_; 
v_a_3965_ = lean_ctor_get(v___y_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___y_3964_, 1);
v_a_3957_ = v_a_3965_;
goto v___jp_3956_;
}
else
{
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
lean_del_object(v___x_3948_);
return v___y_3964_;
}
}
v___jp_3966_:
{
if (v___y_3969_ == 0)
{
lean_object* v___x_3970_; 
lean_dec_ref(v___y_3967_);
v___x_3970_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3968_, v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_dec_ref_known(v___x_3970_, 1);
v_a_3957_ = v_snd_3025_;
goto v___jp_3956_;
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
lean_del_object(v___x_3948_);
lean_dec(v_snd_3025_);
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3970_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
else
{
lean_dec_ref(v___y_3968_);
lean_dec(v_snd_3025_);
v___y_3964_ = v___y_3967_;
goto v___jp_3963_;
}
}
v___jp_3979_:
{
lean_object* v___x_3981_; 
v___x_3981_ = l_Lean_Meta_saveState___redArg(v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3983_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3981_, 1);
lean_inc(v_snd_3025_);
v___x_3983_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3980_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_dec(v_a_3982_);
lean_dec(v_snd_3025_);
v___y_3964_ = v___x_3983_;
goto v___jp_3963_;
}
else
{
lean_object* v_a_3984_; uint8_t v___x_3985_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
v___x_3985_ = l_Lean_Exception_isInterrupt(v_a_3984_);
if (v___x_3985_ == 0)
{
uint8_t v___x_3986_; 
lean_inc(v_a_3984_);
v___x_3986_ = l_Lean_Exception_isRuntime(v_a_3984_);
v___y_3967_ = v___x_3983_;
v___y_3968_ = v_a_3982_;
v___y_3969_ = v___x_3986_;
goto v___jp_3966_;
}
else
{
v___y_3967_ = v___x_3983_;
v___y_3968_ = v_a_3982_;
v___y_3969_ = v___x_3985_;
goto v___jp_3966_;
}
}
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_dec(v___y_3980_);
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
lean_del_object(v___x_3948_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec(v_trace_3010_);
lean_dec_ref(v_cfg_3009_);
v_a_3987_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3981_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3981_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
v___jp_3995_:
{
if (v___y_3997_ == 0)
{
uint8_t v___x_3998_; 
lean_del_object(v___x_3948_);
v___x_3998_ = l_List_isEmpty___redArg(v_fst_3950_);
lean_dec(v_fst_3950_);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
lean_dec(v___y_3996_);
lean_dec(v___x_3955_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec(v_trace_3010_);
lean_dec_ref(v_cfg_3009_);
v___x_3999_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4000_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3999_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_4000_;
}
else
{
lean_object* v___x_4001_; 
v___x_4001_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3996_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4010_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4004_ = v___x_4001_;
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_4001_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4010_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4006_; lean_object* v___x_4008_; 
v___x_4006_ = l_List_appendTR___redArg(v___x_3955_, v_a_4002_);
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 0, v___x_4006_);
v___x_4008_ = v___x_4004_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_4006_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
else
{
lean_dec(v___x_3955_);
return v___x_4001_;
}
}
}
else
{
v___y_3980_ = v___y_3996_;
goto v___jp_3979_;
}
}
v___jp_4011_:
{
uint8_t v_commitIndependentGoals_4013_; lean_object* v___x_4014_; 
v_commitIndependentGoals_4013_ = lean_ctor_get_uint8(v_cfg_3009_, sizeof(void*)*4);
lean_inc(v___x_3955_);
v___x_4014_ = l_List_appendTR___redArg(v_a_4012_, v___x_3955_);
if (v_commitIndependentGoals_4013_ == 0)
{
v___y_3996_ = v___x_4014_;
v___y_3997_ = v___x_3029_;
goto v___jp_3995_;
}
else
{
uint8_t v___x_4015_; 
v___x_4015_ = l_List_isEmpty___redArg(v___x_3955_);
if (v___x_4015_ == 0)
{
v___y_3980_ = v___x_4014_;
goto v___jp_3979_;
}
else
{
v___y_3996_ = v___x_4014_;
v___y_3997_ = v___x_3029_;
goto v___jp_3995_;
}
}
}
v___jp_4018_:
{
lean_object* v___x_4022_; double v___x_4023_; double v___x_4024_; double v___x_4025_; double v___x_4026_; double v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4031_; 
v___x_4022_ = lean_io_mono_nanos_now();
v___x_4023_ = lean_float_of_nat(v___y_4019_);
v___x_4024_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_4025_ = lean_float_div(v___x_4023_, v___x_4024_);
v___x_4026_ = lean_float_of_nat(v___x_4022_);
v___x_4027_ = lean_float_div(v___x_4026_, v___x_4024_);
v___x_4028_ = lean_box_float(v___x_4025_);
v___x_4029_ = lean_box_float(v___x_4027_);
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 1, v___x_4029_);
lean_ctor_set(v___x_3953_, 0, v___x_4028_);
v___x_4031_ = v___x_3953_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v___x_4029_);
v___x_4031_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4032_, 0, v_a_4021_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3010_, v_hasTrace_3032_, v___x_3117_, v_options_3031_, v___x_3120_, v___y_4020_, v___f_4016_, v___x_4032_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_4033_;
}
}
v___jp_4035_:
{
lean_object* v___x_4039_; 
v___x_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4039_, 0, v_a_4038_);
v___y_4019_ = v___y_4036_;
v___y_4020_ = v___y_4037_;
v_a_4021_ = v___x_4039_;
goto v___jp_4018_;
}
v___jp_4040_:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = l_List_appendTR___redArg(v___x_3955_, v_fst_3950_);
v___x_4045_ = l_List_appendTR___redArg(v___x_4044_, v_a_4043_);
v___y_4036_ = v___y_4041_;
v___y_4037_ = v___y_4042_;
v_a_4038_ = v___x_4045_;
goto v___jp_4035_;
}
v___jp_4046_:
{
lean_object* v___x_4050_; 
v___x_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4050_, 0, v_a_4049_);
v___y_4019_ = v___y_4047_;
v___y_4020_ = v___y_4048_;
v_a_4021_ = v___x_4050_;
goto v___jp_4018_;
}
v___jp_4051_:
{
if (lean_obj_tag(v___y_4054_) == 0)
{
lean_object* v_a_4055_; 
v_a_4055_ = lean_ctor_get(v___y_4054_, 0);
lean_inc(v_a_4055_);
lean_dec_ref_known(v___y_4054_, 1);
v___y_4036_ = v___y_4052_;
v___y_4037_ = v___y_4053_;
v_a_4038_ = v_a_4055_;
goto v___jp_4035_;
}
else
{
lean_object* v_a_4056_; 
v_a_4056_ = lean_ctor_get(v___y_4054_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___y_4054_, 1);
v___y_4047_ = v___y_4052_;
v___y_4048_ = v___y_4053_;
v_a_4049_ = v_a_4056_;
goto v___jp_4046_;
}
}
v___jp_4057_:
{
if (lean_obj_tag(v___y_4060_) == 0)
{
lean_object* v_a_4061_; 
v_a_4061_ = lean_ctor_get(v___y_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___y_4060_, 1);
v___y_4041_ = v___y_4058_;
v___y_4042_ = v___y_4059_;
v_a_4043_ = v_a_4061_;
goto v___jp_4040_;
}
else
{
lean_object* v_a_4062_; 
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
v_a_4062_ = lean_ctor_get(v___y_4060_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___y_4060_, 1);
v___y_4047_ = v___y_4058_;
v___y_4048_ = v___y_4059_;
v_a_4049_ = v_a_4062_;
goto v___jp_4046_;
}
}
v___jp_4063_:
{
if (v___y_4068_ == 0)
{
lean_object* v___x_4069_; 
lean_dec_ref(v___y_4064_);
v___x_4069_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4067_, v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_dec_ref_known(v___x_4069_, 1);
v___y_4041_ = v___y_4065_;
v___y_4042_ = v___y_4066_;
v_a_4043_ = v_snd_3025_;
goto v___jp_4040_;
}
else
{
lean_object* v_a_4070_; 
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
lean_dec(v_snd_3025_);
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4069_, 1);
v___y_4047_ = v___y_4065_;
v___y_4048_ = v___y_4066_;
v_a_4049_ = v_a_4070_;
goto v___jp_4046_;
}
}
else
{
lean_dec_ref(v___y_4067_);
lean_dec(v_snd_3025_);
v___y_4058_ = v___y_4065_;
v___y_4059_ = v___y_4066_;
v___y_4060_ = v___y_4064_;
goto v___jp_4057_;
}
}
v___jp_4071_:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_Meta_saveState___redArg(v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4077_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___x_4075_, 1);
lean_inc(v_snd_3025_);
lean_inc(v_trace_3010_);
v___x_4077_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_4074_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_dec(v_a_4076_);
lean_dec(v_snd_3025_);
v___y_4058_ = v___y_4072_;
v___y_4059_ = v___y_4073_;
v___y_4060_ = v___x_4077_;
goto v___jp_4057_;
}
else
{
lean_object* v_a_4078_; uint8_t v___x_4079_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v___x_4079_ = l_Lean_Exception_isInterrupt(v_a_4078_);
if (v___x_4079_ == 0)
{
uint8_t v___x_4080_; 
lean_inc(v_a_4078_);
v___x_4080_ = l_Lean_Exception_isRuntime(v_a_4078_);
v___y_4064_ = v___x_4077_;
v___y_4065_ = v___y_4072_;
v___y_4066_ = v___y_4073_;
v___y_4067_ = v_a_4076_;
v___y_4068_ = v___x_4080_;
goto v___jp_4063_;
}
else
{
v___y_4064_ = v___x_4077_;
v___y_4065_ = v___y_4072_;
v___y_4066_ = v___y_4073_;
v___y_4067_ = v_a_4076_;
v___y_4068_ = v___x_4079_;
goto v___jp_4063_;
}
}
}
else
{
lean_object* v_a_4081_; 
lean_dec(v___y_4074_);
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_4081_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4075_, 1);
v___y_4047_ = v___y_4072_;
v___y_4048_ = v___y_4073_;
v_a_4049_ = v_a_4081_;
goto v___jp_4046_;
}
}
v___jp_4082_:
{
if (v___y_4086_ == 0)
{
uint8_t v___x_4087_; 
v___x_4087_ = l_List_isEmpty___redArg(v_fst_3950_);
lean_dec(v_fst_3950_);
if (v___x_4087_ == 0)
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
lean_dec(v___y_4085_);
lean_dec(v___x_3955_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v___x_4088_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4089_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4088_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_4052_ = v___y_4083_;
v___y_4053_ = v___y_4084_;
v___y_4054_ = v___x_4089_;
goto v___jp_4051_;
}
else
{
lean_object* v___x_4090_; 
lean_inc(v_trace_3010_);
v___x_4090_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_4085_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4092_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref_known(v___x_4090_, 1);
v___x_4092_ = l_List_appendTR___redArg(v___x_3955_, v_a_4091_);
v___y_4036_ = v___y_4083_;
v___y_4037_ = v___y_4084_;
v_a_4038_ = v___x_4092_;
goto v___jp_4035_;
}
else
{
lean_dec(v___x_3955_);
v___y_4052_ = v___y_4083_;
v___y_4053_ = v___y_4084_;
v___y_4054_ = v___x_4090_;
goto v___jp_4051_;
}
}
}
else
{
v___y_4072_ = v___y_4083_;
v___y_4073_ = v___y_4084_;
v___y_4074_ = v___y_4085_;
goto v___jp_4071_;
}
}
v___jp_4093_:
{
uint8_t v_commitIndependentGoals_4097_; lean_object* v___x_4098_; 
v_commitIndependentGoals_4097_ = lean_ctor_get_uint8(v_cfg_3009_, sizeof(void*)*4);
lean_inc(v___x_3955_);
v___x_4098_ = l_List_appendTR___redArg(v_a_4096_, v___x_3955_);
if (v_commitIndependentGoals_4097_ == 0)
{
v___y_4083_ = v___y_4094_;
v___y_4084_ = v___y_4095_;
v___y_4085_ = v___x_4098_;
v___y_4086_ = v___x_3029_;
goto v___jp_4082_;
}
else
{
uint8_t v___x_4099_; 
v___x_4099_ = l_List_isEmpty___redArg(v___x_3955_);
if (v___x_4099_ == 0)
{
v___y_4072_ = v___y_4094_;
v___y_4073_ = v___y_4095_;
v___y_4074_ = v___x_4098_;
goto v___jp_4071_;
}
else
{
v___y_4083_ = v___y_4094_;
v___y_4084_ = v___y_4095_;
v___y_4085_ = v___x_4098_;
v___y_4086_ = v___x_3029_;
goto v___jp_4082_;
}
}
}
v___jp_4100_:
{
lean_object* v___x_4104_; double v___x_4105_; double v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4104_ = lean_io_get_num_heartbeats();
v___x_4105_ = lean_float_of_nat(v___y_4102_);
v___x_4106_ = lean_float_of_nat(v___x_4104_);
v___x_4107_ = lean_box_float(v___x_4105_);
v___x_4108_ = lean_box_float(v___x_4106_);
v___x_4109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4107_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4110_, 0, v_a_4103_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3010_, v_hasTrace_3032_, v___x_3117_, v_options_3031_, v___x_3120_, v___y_4101_, v___f_4016_, v___x_4110_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_4111_;
}
v___jp_4112_:
{
lean_object* v___x_4116_; 
v___x_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4116_, 0, v_a_4115_);
v___y_4101_ = v___y_4114_;
v___y_4102_ = v___y_4113_;
v_a_4103_ = v___x_4116_;
goto v___jp_4100_;
}
v___jp_4117_:
{
lean_object* v___x_4121_; 
v___x_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4121_, 0, v_a_4120_);
v___y_4101_ = v___y_4119_;
v___y_4102_ = v___y_4118_;
v_a_4103_ = v___x_4121_;
goto v___jp_4100_;
}
v___jp_4122_:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = l_List_appendTR___redArg(v___x_3955_, v_fst_3950_);
v___x_4127_ = l_List_appendTR___redArg(v___x_4126_, v_a_4125_);
v___y_4118_ = v___y_4124_;
v___y_4119_ = v___y_4123_;
v_a_4120_ = v___x_4127_;
goto v___jp_4117_;
}
v___jp_4128_:
{
if (lean_obj_tag(v___y_4131_) == 0)
{
lean_object* v_a_4132_; 
v_a_4132_ = lean_ctor_get(v___y_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___y_4131_, 1);
v___y_4123_ = v___y_4130_;
v___y_4124_ = v___y_4129_;
v_a_4125_ = v_a_4132_;
goto v___jp_4122_;
}
else
{
lean_object* v_a_4133_; 
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
v_a_4133_ = lean_ctor_get(v___y_4131_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___y_4131_, 1);
v___y_4113_ = v___y_4129_;
v___y_4114_ = v___y_4130_;
v_a_4115_ = v_a_4133_;
goto v___jp_4112_;
}
}
v___jp_4134_:
{
if (v___y_4139_ == 0)
{
lean_object* v___x_4140_; 
lean_dec_ref(v___y_4136_);
v___x_4140_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4135_, v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_dec_ref_known(v___x_4140_, 1);
v___y_4123_ = v___y_4138_;
v___y_4124_ = v___y_4137_;
v_a_4125_ = v_snd_3025_;
goto v___jp_4122_;
}
else
{
lean_object* v_a_4141_; 
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
lean_dec(v_snd_3025_);
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v___y_4113_ = v___y_4137_;
v___y_4114_ = v___y_4138_;
v_a_4115_ = v_a_4141_;
goto v___jp_4112_;
}
}
else
{
lean_dec_ref(v___y_4135_);
lean_dec(v_snd_3025_);
v___y_4129_ = v___y_4137_;
v___y_4130_ = v___y_4138_;
v___y_4131_ = v___y_4136_;
goto v___jp_4128_;
}
}
v___jp_4142_:
{
lean_object* v___x_4146_; 
v___x_4146_ = l_Lean_Meta_saveState___redArg(v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; lean_object* v___x_4148_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4146_, 1);
lean_inc(v_snd_3025_);
lean_inc(v_trace_3010_);
v___x_4148_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_4145_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_dec(v_a_4147_);
lean_dec(v_snd_3025_);
v___y_4129_ = v___y_4144_;
v___y_4130_ = v___y_4143_;
v___y_4131_ = v___x_4148_;
goto v___jp_4128_;
}
else
{
lean_object* v_a_4149_; uint8_t v___x_4150_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
v___x_4150_ = l_Lean_Exception_isInterrupt(v_a_4149_);
if (v___x_4150_ == 0)
{
uint8_t v___x_4151_; 
lean_inc(v_a_4149_);
v___x_4151_ = l_Lean_Exception_isRuntime(v_a_4149_);
v___y_4135_ = v_a_4147_;
v___y_4136_ = v___x_4148_;
v___y_4137_ = v___y_4144_;
v___y_4138_ = v___y_4143_;
v___y_4139_ = v___x_4151_;
goto v___jp_4134_;
}
else
{
v___y_4135_ = v_a_4147_;
v___y_4136_ = v___x_4148_;
v___y_4137_ = v___y_4144_;
v___y_4138_ = v___y_4143_;
v___y_4139_ = v___x_4150_;
goto v___jp_4134_;
}
}
}
else
{
lean_object* v_a_4152_; 
lean_dec(v___y_4145_);
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_4152_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4146_, 1);
v___y_4113_ = v___y_4144_;
v___y_4114_ = v___y_4143_;
v_a_4115_ = v_a_4152_;
goto v___jp_4112_;
}
}
v___jp_4153_:
{
if (lean_obj_tag(v___y_4156_) == 0)
{
lean_object* v_a_4157_; 
v_a_4157_ = lean_ctor_get(v___y_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___y_4156_, 1);
v___y_4118_ = v___y_4155_;
v___y_4119_ = v___y_4154_;
v_a_4120_ = v_a_4157_;
goto v___jp_4117_;
}
else
{
lean_object* v_a_4158_; 
v_a_4158_ = lean_ctor_get(v___y_4156_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___y_4156_, 1);
v___y_4113_ = v___y_4155_;
v___y_4114_ = v___y_4154_;
v_a_4115_ = v_a_4158_;
goto v___jp_4112_;
}
}
v___jp_4159_:
{
lean_object* v___x_4163_; 
lean_inc(v_trace_3010_);
v___x_4163_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_4162_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4165_; 
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4163_, 1);
v___x_4165_ = l_List_appendTR___redArg(v___x_3955_, v_a_4164_);
v___y_4118_ = v___y_4161_;
v___y_4119_ = v___y_4160_;
v_a_4120_ = v___x_4165_;
goto v___jp_4117_;
}
else
{
lean_dec(v___x_3955_);
v___y_4154_ = v___y_4160_;
v___y_4155_ = v___y_4161_;
v___y_4156_ = v___x_4163_;
goto v___jp_4153_;
}
}
v___jp_4166_:
{
if (v___y_4171_ == 0)
{
uint8_t v___x_4172_; 
v___x_4172_ = l_List_isEmpty___redArg(v_fst_3950_);
lean_dec(v_fst_3950_);
if (v___x_4172_ == 0)
{
if (v___y_4167_ == 0)
{
v___y_4160_ = v___y_4169_;
v___y_4161_ = v___y_4168_;
v___y_4162_ = v___y_4170_;
goto v___jp_4159_;
}
else
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
lean_dec(v___y_4170_);
lean_dec(v___x_3955_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v___x_4173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4174_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4173_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_4154_ = v___y_4169_;
v___y_4155_ = v___y_4168_;
v___y_4156_ = v___x_4174_;
goto v___jp_4153_;
}
}
else
{
v___y_4160_ = v___y_4169_;
v___y_4161_ = v___y_4168_;
v___y_4162_ = v___y_4170_;
goto v___jp_4159_;
}
}
else
{
v___y_4143_ = v___y_4169_;
v___y_4144_ = v___y_4168_;
v___y_4145_ = v___y_4170_;
goto v___jp_4142_;
}
}
v___jp_4175_:
{
uint8_t v_commitIndependentGoals_4180_; lean_object* v___x_4181_; 
v_commitIndependentGoals_4180_ = lean_ctor_get_uint8(v_cfg_3009_, sizeof(void*)*4);
lean_inc(v___x_3955_);
v___x_4181_ = l_List_appendTR___redArg(v_a_4179_, v___x_3955_);
if (v_commitIndependentGoals_4180_ == 0)
{
v___y_4167_ = v___y_4176_;
v___y_4168_ = v___y_4177_;
v___y_4169_ = v___y_4178_;
v___y_4170_ = v___x_4181_;
v___y_4171_ = v___x_3029_;
goto v___jp_4166_;
}
else
{
uint8_t v___x_4182_; 
v___x_4182_ = l_List_isEmpty___redArg(v___x_3955_);
if (v___x_4182_ == 0)
{
v___y_4143_ = v___y_4178_;
v___y_4144_ = v___y_4177_;
v___y_4145_ = v___x_4181_;
goto v___jp_4142_;
}
else
{
v___y_4167_ = v___y_4176_;
v___y_4168_ = v___y_4177_;
v___y_4169_ = v___y_4178_;
v___y_4170_ = v___x_4181_;
v___y_4171_ = v___x_3029_;
goto v___jp_4166_;
}
}
}
v___jp_4183_:
{
lean_object* v___x_4184_; 
v___x_4184_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3018_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v_a_4185_; lean_object* v___x_4186_; uint8_t v___x_4187_; 
v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4185_);
lean_dec_ref_known(v___x_4184_, 1);
v___x_4186_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4187_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3031_, v___x_4186_);
if (v___x_4187_ == 0)
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4188_ = lean_io_mono_nanos_now();
v___x_4189_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3032_, v___x_3029_, v_goals_3013_, v___x_4017_, v_a_3016_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4191_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___x_4191_ = l_List_reverse___redArg(v_a_4190_);
v___y_4094_ = v___x_4188_;
v___y_4095_ = v_a_4185_;
v_a_4096_ = v___x_4191_;
goto v___jp_4093_;
}
else
{
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4192_; 
v_a_4192_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4192_);
lean_dec_ref_known(v___x_4189_, 1);
v___y_4094_ = v___x_4188_;
v___y_4095_ = v_a_4185_;
v_a_4096_ = v_a_4192_;
goto v___jp_4093_;
}
else
{
lean_object* v_a_4193_; 
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_4193_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4189_, 1);
v___y_4047_ = v___x_4188_;
v___y_4048_ = v_a_4185_;
v_a_4049_ = v_a_4193_;
goto v___jp_4046_;
}
}
}
else
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
lean_del_object(v___x_3953_);
v___x_4194_ = lean_io_get_num_heartbeats();
v___x_4195_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3032_, v___x_3029_, v_goals_3013_, v___x_4017_, v_a_3016_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4197_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
lean_dec_ref_known(v___x_4195_, 1);
v___x_4197_ = l_List_reverse___redArg(v_a_4196_);
v___y_4176_ = v___x_4187_;
v___y_4177_ = v___x_4194_;
v___y_4178_ = v_a_4185_;
v_a_4179_ = v___x_4197_;
goto v___jp_4175_;
}
else
{
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4198_; 
v_a_4198_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4198_);
lean_dec_ref_known(v___x_4195_, 1);
v___y_4176_ = v___x_4187_;
v___y_4177_ = v___x_4194_;
v___y_4178_ = v_a_4185_;
v_a_4179_ = v_a_4198_;
goto v___jp_4175_;
}
else
{
lean_object* v_a_4199_; 
lean_dec(v___x_3955_);
lean_dec(v_fst_3950_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_4199_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4195_, 1);
v___y_4113_ = v___x_4194_;
v___y_4114_ = v_a_4185_;
v_a_4115_ = v_a_4199_;
goto v___jp_4112_;
}
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec_ref(v___f_4016_);
lean_dec(v___x_3955_);
lean_del_object(v___x_3953_);
lean_dec(v_fst_3950_);
lean_dec(v_snd_3025_);
lean_dec(v_goals_3013_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec(v_trace_3010_);
lean_dec_ref(v_cfg_3009_);
v_a_4200_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4184_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4184_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_dec(v_snd_3025_);
lean_dec(v_goals_3013_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec(v_trace_3010_);
lean_dec_ref(v_cfg_3009_);
v_a_4214_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_3945_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_3945_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
else
{
goto v___jp_3898_;
}
}
else
{
goto v___jp_3898_;
}
v___jp_3121_:
{
lean_object* v___x_3125_; double v___x_3126_; double v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3131_; 
v___x_3125_ = lean_io_get_num_heartbeats();
v___x_3126_ = lean_float_of_nat(v___y_3123_);
v___x_3127_ = lean_float_of_nat(v___x_3125_);
v___x_3128_ = lean_box_float(v___x_3126_);
v___x_3129_ = lean_box_float(v___x_3127_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 1, v___x_3129_);
lean_ctor_set(v___x_3027_, 0, v___x_3128_);
v___x_3131_ = v___x_3027_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3128_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v___x_3129_);
v___x_3131_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v_a_3124_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3010_, v_hasTrace_3032_, v___x_3117_, v_options_3031_, v___x_3120_, v___y_3122_, v___f_3116_, v___x_3132_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_3133_;
}
}
v___jp_3135_:
{
lean_object* v___x_3139_; 
v___x_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3139_, 0, v_a_3138_);
v___y_3122_ = v___y_3136_;
v___y_3123_ = v___y_3137_;
v_a_3124_ = v___x_3139_;
goto v___jp_3121_;
}
v___jp_3140_:
{
lean_object* v___x_3144_; 
v___x_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3144_, 0, v_a_3143_);
v___y_3122_ = v___y_3141_;
v___y_3123_ = v___y_3142_;
v_a_3124_ = v___x_3144_;
goto v___jp_3121_;
}
v___jp_3145_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = l_List_appendTR___redArg(v___y_3146_, v___y_3147_);
v___x_3152_ = l_List_appendTR___redArg(v___x_3151_, v_a_3150_);
v___y_3141_ = v___y_3148_;
v___y_3142_ = v___y_3149_;
v_a_3143_ = v___x_3152_;
goto v___jp_3140_;
}
v___jp_3153_:
{
if (lean_obj_tag(v___y_3158_) == 0)
{
lean_object* v_a_3159_; 
v_a_3159_ = lean_ctor_get(v___y_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___y_3158_, 1);
v___y_3146_ = v___y_3154_;
v___y_3147_ = v___y_3155_;
v___y_3148_ = v___y_3156_;
v___y_3149_ = v___y_3157_;
v_a_3150_ = v_a_3159_;
goto v___jp_3145_;
}
else
{
lean_object* v_a_3160_; 
lean_dec(v___y_3155_);
lean_dec(v___y_3154_);
v_a_3160_ = lean_ctor_get(v___y_3158_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___y_3158_, 1);
v___y_3136_ = v___y_3156_;
v___y_3137_ = v___y_3157_;
v_a_3138_ = v_a_3160_;
goto v___jp_3135_;
}
}
v___jp_3161_:
{
if (v___y_3168_ == 0)
{
lean_object* v___x_3169_; 
lean_dec_ref(v___y_3165_);
v___x_3169_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3164_, v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_dec_ref_known(v___x_3169_, 1);
v___y_3146_ = v___y_3162_;
v___y_3147_ = v___y_3163_;
v___y_3148_ = v___y_3166_;
v___y_3149_ = v___y_3167_;
v_a_3150_ = v_snd_3025_;
goto v___jp_3145_;
}
else
{
lean_object* v_a_3170_; 
lean_dec(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec(v_snd_3025_);
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref_known(v___x_3169_, 1);
v___y_3136_ = v___y_3166_;
v___y_3137_ = v___y_3167_;
v_a_3138_ = v_a_3170_;
goto v___jp_3135_;
}
}
else
{
lean_dec_ref(v___y_3164_);
lean_dec(v_snd_3025_);
v___y_3154_ = v___y_3162_;
v___y_3155_ = v___y_3163_;
v___y_3156_ = v___y_3166_;
v___y_3157_ = v___y_3167_;
v___y_3158_ = v___y_3165_;
goto v___jp_3153_;
}
}
v___jp_3171_:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Lean_Meta_saveState___redArg(v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3179_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3177_, 1);
lean_inc(v_snd_3025_);
lean_inc(v_trace_3010_);
v___x_3179_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3174_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_dec(v_a_3178_);
lean_dec(v_snd_3025_);
v___y_3154_ = v___y_3172_;
v___y_3155_ = v___y_3173_;
v___y_3156_ = v___y_3175_;
v___y_3157_ = v___y_3176_;
v___y_3158_ = v___x_3179_;
goto v___jp_3153_;
}
else
{
lean_object* v_a_3180_; uint8_t v___x_3181_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
v___x_3181_ = l_Lean_Exception_isInterrupt(v_a_3180_);
if (v___x_3181_ == 0)
{
uint8_t v___x_3182_; 
lean_inc(v_a_3180_);
v___x_3182_ = l_Lean_Exception_isRuntime(v_a_3180_);
v___y_3162_ = v___y_3172_;
v___y_3163_ = v___y_3173_;
v___y_3164_ = v_a_3178_;
v___y_3165_ = v___x_3179_;
v___y_3166_ = v___y_3175_;
v___y_3167_ = v___y_3176_;
v___y_3168_ = v___x_3182_;
goto v___jp_3161_;
}
else
{
v___y_3162_ = v___y_3172_;
v___y_3163_ = v___y_3173_;
v___y_3164_ = v_a_3178_;
v___y_3165_ = v___x_3179_;
v___y_3166_ = v___y_3175_;
v___y_3167_ = v___y_3176_;
v___y_3168_ = v___x_3181_;
goto v___jp_3161_;
}
}
}
else
{
lean_object* v_a_3183_; 
lean_dec(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3183_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_a_3183_);
lean_dec_ref_known(v___x_3177_, 1);
v___y_3136_ = v___y_3175_;
v___y_3137_ = v___y_3176_;
v_a_3138_ = v_a_3183_;
goto v___jp_3135_;
}
}
v___jp_3184_:
{
if (lean_obj_tag(v___y_3187_) == 0)
{
lean_object* v_a_3188_; 
v_a_3188_ = lean_ctor_get(v___y_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___y_3187_, 1);
v___y_3141_ = v___y_3185_;
v___y_3142_ = v___y_3186_;
v_a_3143_ = v_a_3188_;
goto v___jp_3140_;
}
else
{
lean_object* v_a_3189_; 
v_a_3189_ = lean_ctor_get(v___y_3187_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___y_3187_, 1);
v___y_3136_ = v___y_3185_;
v___y_3137_ = v___y_3186_;
v_a_3138_ = v_a_3189_;
goto v___jp_3135_;
}
}
v___jp_3190_:
{
lean_object* v___x_3198_; double v___x_3199_; double v___x_3200_; double v___x_3201_; double v___x_3202_; double v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3198_ = lean_io_mono_nanos_now();
v___x_3199_ = lean_float_of_nat(v___y_3192_);
v___x_3200_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3201_ = lean_float_div(v___x_3199_, v___x_3200_);
v___x_3202_ = lean_float_of_nat(v___x_3198_);
v___x_3203_ = lean_float_div(v___x_3202_, v___x_3200_);
v___x_3204_ = lean_box_float(v___x_3201_);
v___x_3205_ = lean_box_float(v___x_3203_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3204_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3207_, 0, v_a_3197_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
lean_inc(v_trace_3010_);
v___x_3208_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3010_, v_hasTrace_3032_, v___x_3117_, v_options_3031_, v___y_3191_, v___y_3194_, v___y_3193_, v___x_3207_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_3185_ = v___y_3195_;
v___y_3186_ = v___y_3196_;
v___y_3187_ = v___x_3208_;
goto v___jp_3184_;
}
v___jp_3209_:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v_a_3216_);
v___y_3191_ = v___y_3211_;
v___y_3192_ = v___y_3210_;
v___y_3193_ = v___y_3213_;
v___y_3194_ = v___y_3212_;
v___y_3195_ = v___y_3214_;
v___y_3196_ = v___y_3215_;
v_a_3197_ = v___x_3217_;
goto v___jp_3190_;
}
v___jp_3218_:
{
lean_object* v___x_3226_; 
v___x_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3226_, 0, v_a_3225_);
v___y_3191_ = v___y_3220_;
v___y_3192_ = v___y_3219_;
v___y_3193_ = v___y_3222_;
v___y_3194_ = v___y_3221_;
v___y_3195_ = v___y_3223_;
v___y_3196_ = v___y_3224_;
v_a_3197_ = v___x_3226_;
goto v___jp_3190_;
}
v___jp_3227_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = l_List_appendTR___redArg(v___y_3228_, v___y_3229_);
v___x_3238_ = l_List_appendTR___redArg(v___x_3237_, v_a_3236_);
v___y_3219_ = v___y_3231_;
v___y_3220_ = v___y_3230_;
v___y_3221_ = v___y_3233_;
v___y_3222_ = v___y_3232_;
v___y_3223_ = v___y_3234_;
v___y_3224_ = v___y_3235_;
v_a_3225_ = v___x_3238_;
goto v___jp_3218_;
}
v___jp_3239_:
{
if (lean_obj_tag(v___y_3248_) == 0)
{
lean_object* v_a_3249_; 
v_a_3249_ = lean_ctor_get(v___y_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___y_3248_, 1);
v___y_3228_ = v___y_3240_;
v___y_3229_ = v___y_3241_;
v___y_3230_ = v___y_3243_;
v___y_3231_ = v___y_3242_;
v___y_3232_ = v___y_3245_;
v___y_3233_ = v___y_3244_;
v___y_3234_ = v___y_3246_;
v___y_3235_ = v___y_3247_;
v_a_3236_ = v_a_3249_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3250_; 
lean_dec(v___y_3241_);
lean_dec(v___y_3240_);
v_a_3250_ = lean_ctor_get(v___y_3248_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___y_3248_, 1);
v___y_3210_ = v___y_3242_;
v___y_3211_ = v___y_3243_;
v___y_3212_ = v___y_3244_;
v___y_3213_ = v___y_3245_;
v___y_3214_ = v___y_3246_;
v___y_3215_ = v___y_3247_;
v_a_3216_ = v_a_3250_;
goto v___jp_3209_;
}
}
v___jp_3251_:
{
if (v___y_3262_ == 0)
{
lean_object* v___x_3263_; 
lean_dec_ref(v___y_3256_);
v___x_3263_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3260_, v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_dec_ref_known(v___x_3263_, 1);
v___y_3228_ = v___y_3252_;
v___y_3229_ = v___y_3253_;
v___y_3230_ = v___y_3255_;
v___y_3231_ = v___y_3254_;
v___y_3232_ = v___y_3258_;
v___y_3233_ = v___y_3257_;
v___y_3234_ = v___y_3259_;
v___y_3235_ = v___y_3261_;
v_a_3236_ = v_snd_3025_;
goto v___jp_3227_;
}
else
{
lean_object* v_a_3264_; 
lean_dec(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v_snd_3025_);
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref_known(v___x_3263_, 1);
v___y_3210_ = v___y_3254_;
v___y_3211_ = v___y_3255_;
v___y_3212_ = v___y_3257_;
v___y_3213_ = v___y_3258_;
v___y_3214_ = v___y_3259_;
v___y_3215_ = v___y_3261_;
v_a_3216_ = v_a_3264_;
goto v___jp_3209_;
}
}
else
{
lean_dec_ref(v___y_3260_);
lean_dec(v_snd_3025_);
v___y_3240_ = v___y_3252_;
v___y_3241_ = v___y_3253_;
v___y_3242_ = v___y_3254_;
v___y_3243_ = v___y_3255_;
v___y_3244_ = v___y_3257_;
v___y_3245_ = v___y_3258_;
v___y_3246_ = v___y_3259_;
v___y_3247_ = v___y_3261_;
v___y_3248_ = v___y_3256_;
goto v___jp_3239_;
}
}
v___jp_3265_:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Lean_Meta_saveState___redArg(v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3277_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3275_, 1);
lean_inc(v_snd_3025_);
lean_inc(v_trace_3010_);
v___x_3277_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3270_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_dec(v_a_3276_);
lean_dec(v_snd_3025_);
v___y_3240_ = v___y_3266_;
v___y_3241_ = v___y_3267_;
v___y_3242_ = v___y_3269_;
v___y_3243_ = v___y_3268_;
v___y_3244_ = v___y_3272_;
v___y_3245_ = v___y_3271_;
v___y_3246_ = v___y_3273_;
v___y_3247_ = v___y_3274_;
v___y_3248_ = v___x_3277_;
goto v___jp_3239_;
}
else
{
lean_object* v_a_3278_; uint8_t v___x_3279_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v___x_3279_ = l_Lean_Exception_isInterrupt(v_a_3278_);
if (v___x_3279_ == 0)
{
uint8_t v___x_3280_; 
lean_inc(v_a_3278_);
v___x_3280_ = l_Lean_Exception_isRuntime(v_a_3278_);
v___y_3252_ = v___y_3266_;
v___y_3253_ = v___y_3267_;
v___y_3254_ = v___y_3269_;
v___y_3255_ = v___y_3268_;
v___y_3256_ = v___x_3277_;
v___y_3257_ = v___y_3272_;
v___y_3258_ = v___y_3271_;
v___y_3259_ = v___y_3273_;
v___y_3260_ = v_a_3276_;
v___y_3261_ = v___y_3274_;
v___y_3262_ = v___x_3280_;
goto v___jp_3251_;
}
else
{
v___y_3252_ = v___y_3266_;
v___y_3253_ = v___y_3267_;
v___y_3254_ = v___y_3269_;
v___y_3255_ = v___y_3268_;
v___y_3256_ = v___x_3277_;
v___y_3257_ = v___y_3272_;
v___y_3258_ = v___y_3271_;
v___y_3259_ = v___y_3273_;
v___y_3260_ = v_a_3276_;
v___y_3261_ = v___y_3274_;
v___y_3262_ = v___x_3279_;
goto v___jp_3251_;
}
}
}
else
{
lean_object* v_a_3281_; 
lean_dec(v___y_3270_);
lean_dec(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3281_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v___x_3275_, 1);
v___y_3210_ = v___y_3269_;
v___y_3211_ = v___y_3268_;
v___y_3212_ = v___y_3272_;
v___y_3213_ = v___y_3271_;
v___y_3214_ = v___y_3273_;
v___y_3215_ = v___y_3274_;
v_a_3216_ = v_a_3281_;
goto v___jp_3209_;
}
}
v___jp_3282_:
{
if (lean_obj_tag(v___y_3289_) == 0)
{
lean_object* v_a_3290_; 
v_a_3290_ = lean_ctor_get(v___y_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref_known(v___y_3289_, 1);
v___y_3219_ = v___y_3284_;
v___y_3220_ = v___y_3283_;
v___y_3221_ = v___y_3286_;
v___y_3222_ = v___y_3285_;
v___y_3223_ = v___y_3287_;
v___y_3224_ = v___y_3288_;
v_a_3225_ = v_a_3290_;
goto v___jp_3218_;
}
else
{
lean_object* v_a_3291_; 
v_a_3291_ = lean_ctor_get(v___y_3289_, 0);
lean_inc(v_a_3291_);
lean_dec_ref_known(v___y_3289_, 1);
v___y_3210_ = v___y_3284_;
v___y_3211_ = v___y_3283_;
v___y_3212_ = v___y_3286_;
v___y_3213_ = v___y_3285_;
v___y_3214_ = v___y_3287_;
v___y_3215_ = v___y_3288_;
v_a_3216_ = v_a_3291_;
goto v___jp_3209_;
}
}
v___jp_3292_:
{
if (v___y_3302_ == 0)
{
uint8_t v___x_3303_; 
v___x_3303_ = l_List_isEmpty___redArg(v___y_3294_);
lean_dec(v___y_3294_);
if (v___x_3303_ == 0)
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec(v___y_3297_);
lean_dec(v___y_3293_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v___x_3304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3305_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3304_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_3283_ = v___y_3296_;
v___y_3284_ = v___y_3295_;
v___y_3285_ = v___y_3299_;
v___y_3286_ = v___y_3298_;
v___y_3287_ = v___y_3300_;
v___y_3288_ = v___y_3301_;
v___y_3289_ = v___x_3305_;
goto v___jp_3282_;
}
else
{
lean_object* v___x_3306_; 
lean_inc(v_trace_3010_);
v___x_3306_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3297_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3308_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = l_List_appendTR___redArg(v___y_3293_, v_a_3307_);
v___y_3219_ = v___y_3295_;
v___y_3220_ = v___y_3296_;
v___y_3221_ = v___y_3298_;
v___y_3222_ = v___y_3299_;
v___y_3223_ = v___y_3300_;
v___y_3224_ = v___y_3301_;
v_a_3225_ = v___x_3308_;
goto v___jp_3218_;
}
else
{
lean_dec(v___y_3293_);
v___y_3283_ = v___y_3296_;
v___y_3284_ = v___y_3295_;
v___y_3285_ = v___y_3299_;
v___y_3286_ = v___y_3298_;
v___y_3287_ = v___y_3300_;
v___y_3288_ = v___y_3301_;
v___y_3289_ = v___x_3306_;
goto v___jp_3282_;
}
}
}
else
{
v___y_3266_ = v___y_3293_;
v___y_3267_ = v___y_3294_;
v___y_3268_ = v___y_3296_;
v___y_3269_ = v___y_3295_;
v___y_3270_ = v___y_3297_;
v___y_3271_ = v___y_3299_;
v___y_3272_ = v___y_3298_;
v___y_3273_ = v___y_3300_;
v___y_3274_ = v___y_3301_;
goto v___jp_3265_;
}
}
v___jp_3309_:
{
uint8_t v_commitIndependentGoals_3319_; lean_object* v___x_3320_; 
v_commitIndependentGoals_3319_ = lean_ctor_get_uint8(v_cfg_3009_, sizeof(void*)*4);
lean_inc(v___y_3310_);
v___x_3320_ = l_List_appendTR___redArg(v_a_3318_, v___y_3310_);
if (v_commitIndependentGoals_3319_ == 0)
{
v___y_3293_ = v___y_3310_;
v___y_3294_ = v___y_3311_;
v___y_3295_ = v___y_3312_;
v___y_3296_ = v___y_3313_;
v___y_3297_ = v___x_3320_;
v___y_3298_ = v___y_3314_;
v___y_3299_ = v___y_3315_;
v___y_3300_ = v___y_3316_;
v___y_3301_ = v___y_3317_;
v___y_3302_ = v___x_3029_;
goto v___jp_3292_;
}
else
{
uint8_t v___x_3321_; 
v___x_3321_ = l_List_isEmpty___redArg(v___y_3310_);
if (v___x_3321_ == 0)
{
v___y_3266_ = v___y_3310_;
v___y_3267_ = v___y_3311_;
v___y_3268_ = v___y_3313_;
v___y_3269_ = v___y_3312_;
v___y_3270_ = v___x_3320_;
v___y_3271_ = v___y_3315_;
v___y_3272_ = v___y_3314_;
v___y_3273_ = v___y_3316_;
v___y_3274_ = v___y_3317_;
goto v___jp_3265_;
}
else
{
v___y_3293_ = v___y_3310_;
v___y_3294_ = v___y_3311_;
v___y_3295_ = v___y_3312_;
v___y_3296_ = v___y_3313_;
v___y_3297_ = v___x_3320_;
v___y_3298_ = v___y_3314_;
v___y_3299_ = v___y_3315_;
v___y_3300_ = v___y_3316_;
v___y_3301_ = v___y_3317_;
v___y_3302_ = v___x_3029_;
goto v___jp_3292_;
}
}
}
v___jp_3322_:
{
lean_object* v___x_3330_; double v___x_3331_; double v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3330_ = lean_io_get_num_heartbeats();
v___x_3331_ = lean_float_of_nat(v___y_3326_);
v___x_3332_ = lean_float_of_nat(v___x_3330_);
v___x_3333_ = lean_box_float(v___x_3331_);
v___x_3334_ = lean_box_float(v___x_3332_);
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3336_, 0, v_a_3329_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
lean_inc(v_trace_3010_);
v___x_3337_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3010_, v_hasTrace_3032_, v___x_3117_, v_options_3031_, v___y_3323_, v___y_3325_, v___y_3324_, v___x_3336_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_3185_ = v___y_3327_;
v___y_3186_ = v___y_3328_;
v___y_3187_ = v___x_3337_;
goto v___jp_3184_;
}
v___jp_3338_:
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3346_, 0, v_a_3345_);
v___y_3323_ = v___y_3339_;
v___y_3324_ = v___y_3341_;
v___y_3325_ = v___y_3340_;
v___y_3326_ = v___y_3342_;
v___y_3327_ = v___y_3343_;
v___y_3328_ = v___y_3344_;
v_a_3329_ = v___x_3346_;
goto v___jp_3322_;
}
v___jp_3347_:
{
lean_object* v___x_3355_; 
v___x_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3355_, 0, v_a_3354_);
v___y_3323_ = v___y_3348_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___y_3349_;
v___y_3326_ = v___y_3351_;
v___y_3327_ = v___y_3352_;
v___y_3328_ = v___y_3353_;
v_a_3329_ = v___x_3355_;
goto v___jp_3322_;
}
v___jp_3356_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = l_List_appendTR___redArg(v___y_3357_, v___y_3358_);
v___x_3367_ = l_List_appendTR___redArg(v___x_3366_, v_a_3365_);
v___y_3348_ = v___y_3359_;
v___y_3349_ = v___y_3361_;
v___y_3350_ = v___y_3360_;
v___y_3351_ = v___y_3362_;
v___y_3352_ = v___y_3363_;
v___y_3353_ = v___y_3364_;
v_a_3354_ = v___x_3367_;
goto v___jp_3347_;
}
v___jp_3368_:
{
if (lean_obj_tag(v___y_3377_) == 0)
{
lean_object* v_a_3378_; 
v_a_3378_ = lean_ctor_get(v___y_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___y_3377_, 1);
v___y_3357_ = v___y_3369_;
v___y_3358_ = v___y_3370_;
v___y_3359_ = v___y_3371_;
v___y_3360_ = v___y_3373_;
v___y_3361_ = v___y_3372_;
v___y_3362_ = v___y_3374_;
v___y_3363_ = v___y_3375_;
v___y_3364_ = v___y_3376_;
v_a_3365_ = v_a_3378_;
goto v___jp_3356_;
}
else
{
lean_object* v_a_3379_; 
lean_dec(v___y_3370_);
lean_dec(v___y_3369_);
v_a_3379_ = lean_ctor_get(v___y_3377_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___y_3377_, 1);
v___y_3339_ = v___y_3371_;
v___y_3340_ = v___y_3372_;
v___y_3341_ = v___y_3373_;
v___y_3342_ = v___y_3374_;
v___y_3343_ = v___y_3375_;
v___y_3344_ = v___y_3376_;
v_a_3345_ = v_a_3379_;
goto v___jp_3338_;
}
}
v___jp_3380_:
{
if (v___y_3391_ == 0)
{
lean_object* v___x_3392_; 
lean_dec_ref(v___y_3389_);
v___x_3392_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3387_, v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_dec_ref_known(v___x_3392_, 1);
v___y_3357_ = v___y_3381_;
v___y_3358_ = v___y_3382_;
v___y_3359_ = v___y_3383_;
v___y_3360_ = v___y_3385_;
v___y_3361_ = v___y_3384_;
v___y_3362_ = v___y_3386_;
v___y_3363_ = v___y_3388_;
v___y_3364_ = v___y_3390_;
v_a_3365_ = v_snd_3025_;
goto v___jp_3356_;
}
else
{
lean_object* v_a_3393_; 
lean_dec(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec(v_snd_3025_);
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
v___y_3339_ = v___y_3383_;
v___y_3340_ = v___y_3384_;
v___y_3341_ = v___y_3385_;
v___y_3342_ = v___y_3386_;
v___y_3343_ = v___y_3388_;
v___y_3344_ = v___y_3390_;
v_a_3345_ = v_a_3393_;
goto v___jp_3338_;
}
}
else
{
lean_dec_ref(v___y_3387_);
lean_dec(v_snd_3025_);
v___y_3369_ = v___y_3381_;
v___y_3370_ = v___y_3382_;
v___y_3371_ = v___y_3383_;
v___y_3372_ = v___y_3384_;
v___y_3373_ = v___y_3385_;
v___y_3374_ = v___y_3386_;
v___y_3375_ = v___y_3388_;
v___y_3376_ = v___y_3390_;
v___y_3377_ = v___y_3389_;
goto v___jp_3368_;
}
}
v___jp_3394_:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_Meta_saveState___redArg(v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3406_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref_known(v___x_3404_, 1);
lean_inc(v_snd_3025_);
lean_inc(v_trace_3010_);
v___x_3406_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3396_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_dec(v_a_3405_);
lean_dec(v_snd_3025_);
v___y_3369_ = v___y_3395_;
v___y_3370_ = v___y_3397_;
v___y_3371_ = v___y_3398_;
v___y_3372_ = v___y_3400_;
v___y_3373_ = v___y_3399_;
v___y_3374_ = v___y_3401_;
v___y_3375_ = v___y_3402_;
v___y_3376_ = v___y_3403_;
v___y_3377_ = v___x_3406_;
goto v___jp_3368_;
}
else
{
lean_object* v_a_3407_; uint8_t v___x_3408_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v___x_3408_ = l_Lean_Exception_isInterrupt(v_a_3407_);
if (v___x_3408_ == 0)
{
uint8_t v___x_3409_; 
lean_inc(v_a_3407_);
v___x_3409_ = l_Lean_Exception_isRuntime(v_a_3407_);
v___y_3381_ = v___y_3395_;
v___y_3382_ = v___y_3397_;
v___y_3383_ = v___y_3398_;
v___y_3384_ = v___y_3400_;
v___y_3385_ = v___y_3399_;
v___y_3386_ = v___y_3401_;
v___y_3387_ = v_a_3405_;
v___y_3388_ = v___y_3402_;
v___y_3389_ = v___x_3406_;
v___y_3390_ = v___y_3403_;
v___y_3391_ = v___x_3409_;
goto v___jp_3380_;
}
else
{
v___y_3381_ = v___y_3395_;
v___y_3382_ = v___y_3397_;
v___y_3383_ = v___y_3398_;
v___y_3384_ = v___y_3400_;
v___y_3385_ = v___y_3399_;
v___y_3386_ = v___y_3401_;
v___y_3387_ = v_a_3405_;
v___y_3388_ = v___y_3402_;
v___y_3389_ = v___x_3406_;
v___y_3390_ = v___y_3403_;
v___y_3391_ = v___x_3408_;
goto v___jp_3380_;
}
}
}
else
{
lean_object* v_a_3410_; 
lean_dec(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3410_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3410_);
lean_dec_ref_known(v___x_3404_, 1);
v___y_3339_ = v___y_3398_;
v___y_3340_ = v___y_3400_;
v___y_3341_ = v___y_3399_;
v___y_3342_ = v___y_3401_;
v___y_3343_ = v___y_3402_;
v___y_3344_ = v___y_3403_;
v_a_3345_ = v_a_3410_;
goto v___jp_3338_;
}
}
v___jp_3411_:
{
if (lean_obj_tag(v___y_3418_) == 0)
{
lean_object* v_a_3419_; 
v_a_3419_ = lean_ctor_get(v___y_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___y_3418_, 1);
v___y_3348_ = v___y_3412_;
v___y_3349_ = v___y_3414_;
v___y_3350_ = v___y_3413_;
v___y_3351_ = v___y_3415_;
v___y_3352_ = v___y_3416_;
v___y_3353_ = v___y_3417_;
v_a_3354_ = v_a_3419_;
goto v___jp_3347_;
}
else
{
lean_object* v_a_3420_; 
v_a_3420_ = lean_ctor_get(v___y_3418_, 0);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___y_3418_, 1);
v___y_3339_ = v___y_3412_;
v___y_3340_ = v___y_3414_;
v___y_3341_ = v___y_3413_;
v___y_3342_ = v___y_3415_;
v___y_3343_ = v___y_3416_;
v___y_3344_ = v___y_3417_;
v_a_3345_ = v_a_3420_;
goto v___jp_3338_;
}
}
v___jp_3421_:
{
lean_object* v___x_3430_; 
lean_inc(v_trace_3010_);
v___x_3430_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3423_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3432_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3432_ = l_List_appendTR___redArg(v___y_3422_, v_a_3431_);
v___y_3348_ = v___y_3424_;
v___y_3349_ = v___y_3426_;
v___y_3350_ = v___y_3425_;
v___y_3351_ = v___y_3427_;
v___y_3352_ = v___y_3428_;
v___y_3353_ = v___y_3429_;
v_a_3354_ = v___x_3432_;
goto v___jp_3347_;
}
else
{
lean_dec(v___y_3422_);
v___y_3412_ = v___y_3424_;
v___y_3413_ = v___y_3425_;
v___y_3414_ = v___y_3426_;
v___y_3415_ = v___y_3427_;
v___y_3416_ = v___y_3428_;
v___y_3417_ = v___y_3429_;
v___y_3418_ = v___x_3430_;
goto v___jp_3411_;
}
}
v___jp_3433_:
{
if (v___y_3444_ == 0)
{
uint8_t v___x_3445_; 
v___x_3445_ = l_List_isEmpty___redArg(v___y_3436_);
lean_dec(v___y_3436_);
if (v___x_3445_ == 0)
{
if (v___y_3438_ == 0)
{
v___y_3422_ = v___y_3434_;
v___y_3423_ = v___y_3435_;
v___y_3424_ = v___y_3437_;
v___y_3425_ = v___y_3440_;
v___y_3426_ = v___y_3439_;
v___y_3427_ = v___y_3441_;
v___y_3428_ = v___y_3442_;
v___y_3429_ = v___y_3443_;
goto v___jp_3421_;
}
else
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
lean_dec(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v___x_3446_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3447_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3446_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_3412_ = v___y_3437_;
v___y_3413_ = v___y_3440_;
v___y_3414_ = v___y_3439_;
v___y_3415_ = v___y_3441_;
v___y_3416_ = v___y_3442_;
v___y_3417_ = v___y_3443_;
v___y_3418_ = v___x_3447_;
goto v___jp_3411_;
}
}
else
{
v___y_3422_ = v___y_3434_;
v___y_3423_ = v___y_3435_;
v___y_3424_ = v___y_3437_;
v___y_3425_ = v___y_3440_;
v___y_3426_ = v___y_3439_;
v___y_3427_ = v___y_3441_;
v___y_3428_ = v___y_3442_;
v___y_3429_ = v___y_3443_;
goto v___jp_3421_;
}
}
else
{
v___y_3395_ = v___y_3434_;
v___y_3396_ = v___y_3435_;
v___y_3397_ = v___y_3436_;
v___y_3398_ = v___y_3437_;
v___y_3399_ = v___y_3440_;
v___y_3400_ = v___y_3439_;
v___y_3401_ = v___y_3441_;
v___y_3402_ = v___y_3442_;
v___y_3403_ = v___y_3443_;
goto v___jp_3394_;
}
}
v___jp_3448_:
{
uint8_t v_commitIndependentGoals_3459_; lean_object* v___x_3460_; 
v_commitIndependentGoals_3459_ = lean_ctor_get_uint8(v_cfg_3009_, sizeof(void*)*4);
lean_inc(v___y_3449_);
v___x_3460_ = l_List_appendTR___redArg(v_a_3458_, v___y_3449_);
if (v_commitIndependentGoals_3459_ == 0)
{
v___y_3434_ = v___y_3449_;
v___y_3435_ = v___x_3460_;
v___y_3436_ = v___y_3450_;
v___y_3437_ = v___y_3451_;
v___y_3438_ = v___y_3452_;
v___y_3439_ = v___y_3453_;
v___y_3440_ = v___y_3454_;
v___y_3441_ = v___y_3455_;
v___y_3442_ = v___y_3456_;
v___y_3443_ = v___y_3457_;
v___y_3444_ = v___x_3029_;
goto v___jp_3433_;
}
else
{
uint8_t v___x_3461_; 
v___x_3461_ = l_List_isEmpty___redArg(v___y_3449_);
if (v___x_3461_ == 0)
{
v___y_3395_ = v___y_3449_;
v___y_3396_ = v___x_3460_;
v___y_3397_ = v___y_3450_;
v___y_3398_ = v___y_3451_;
v___y_3399_ = v___y_3454_;
v___y_3400_ = v___y_3453_;
v___y_3401_ = v___y_3455_;
v___y_3402_ = v___y_3456_;
v___y_3403_ = v___y_3457_;
goto v___jp_3394_;
}
else
{
v___y_3434_ = v___y_3449_;
v___y_3435_ = v___x_3460_;
v___y_3436_ = v___y_3450_;
v___y_3437_ = v___y_3451_;
v___y_3438_ = v___y_3452_;
v___y_3439_ = v___y_3453_;
v___y_3440_ = v___y_3454_;
v___y_3441_ = v___y_3455_;
v___y_3442_ = v___y_3456_;
v___y_3443_ = v___y_3457_;
v___y_3444_ = v___x_3029_;
goto v___jp_3433_;
}
}
}
v___jp_3462_:
{
lean_object* v___x_3471_; 
v___x_3471_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3018_);
if (lean_obj_tag(v___x_3471_) == 0)
{
if (v___y_3467_ == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v___x_3473_ = lean_io_mono_nanos_now();
v___x_3474_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3467_, v___x_3029_, v_goals_3013_, v___y_3465_, v_a_3016_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3476_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v___x_3474_, 1);
v___x_3476_ = l_List_reverse___redArg(v_a_3475_);
v___y_3310_ = v___y_3463_;
v___y_3311_ = v___y_3464_;
v___y_3312_ = v___x_3473_;
v___y_3313_ = v___y_3466_;
v___y_3314_ = v_a_3472_;
v___y_3315_ = v___y_3468_;
v___y_3316_ = v___y_3469_;
v___y_3317_ = v___y_3470_;
v_a_3318_ = v___x_3476_;
goto v___jp_3309_;
}
else
{
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3477_; 
v_a_3477_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v___x_3474_, 1);
v___y_3310_ = v___y_3463_;
v___y_3311_ = v___y_3464_;
v___y_3312_ = v___x_3473_;
v___y_3313_ = v___y_3466_;
v___y_3314_ = v_a_3472_;
v___y_3315_ = v___y_3468_;
v___y_3316_ = v___y_3469_;
v___y_3317_ = v___y_3470_;
v_a_3318_ = v_a_3477_;
goto v___jp_3309_;
}
else
{
lean_object* v_a_3478_; 
lean_dec(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3478_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3474_, 1);
v___y_3210_ = v___x_3473_;
v___y_3211_ = v___y_3466_;
v___y_3212_ = v_a_3472_;
v___y_3213_ = v___y_3468_;
v___y_3214_ = v___y_3469_;
v___y_3215_ = v___y_3470_;
v_a_3216_ = v_a_3478_;
goto v___jp_3209_;
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v_a_3479_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3479_);
lean_dec_ref_known(v___x_3471_, 1);
v___x_3480_ = lean_io_get_num_heartbeats();
v___x_3481_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3467_, v___x_3029_, v_goals_3013_, v___y_3465_, v_a_3016_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3483_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3481_, 1);
v___x_3483_ = l_List_reverse___redArg(v_a_3482_);
v___y_3449_ = v___y_3463_;
v___y_3450_ = v___y_3464_;
v___y_3451_ = v___y_3466_;
v___y_3452_ = v___y_3467_;
v___y_3453_ = v_a_3479_;
v___y_3454_ = v___y_3468_;
v___y_3455_ = v___x_3480_;
v___y_3456_ = v___y_3469_;
v___y_3457_ = v___y_3470_;
v_a_3458_ = v___x_3483_;
goto v___jp_3448_;
}
else
{
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3484_; 
v_a_3484_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3481_, 1);
v___y_3449_ = v___y_3463_;
v___y_3450_ = v___y_3464_;
v___y_3451_ = v___y_3466_;
v___y_3452_ = v___y_3467_;
v___y_3453_ = v_a_3479_;
v___y_3454_ = v___y_3468_;
v___y_3455_ = v___x_3480_;
v___y_3456_ = v___y_3469_;
v___y_3457_ = v___y_3470_;
v_a_3458_ = v_a_3484_;
goto v___jp_3448_;
}
else
{
lean_object* v_a_3485_; 
lean_dec(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3485_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3485_);
lean_dec_ref_known(v___x_3481_, 1);
v___y_3339_ = v___y_3466_;
v___y_3340_ = v_a_3479_;
v___y_3341_ = v___y_3468_;
v___y_3342_ = v___x_3480_;
v___y_3343_ = v___y_3469_;
v___y_3344_ = v___y_3470_;
v_a_3345_ = v_a_3485_;
goto v___jp_3338_;
}
}
}
}
else
{
lean_object* v_a_3486_; 
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec(v_snd_3025_);
lean_dec(v_goals_3013_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3486_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3471_, 1);
v___y_3136_ = v___y_3469_;
v___y_3137_ = v___y_3470_;
v_a_3138_ = v_a_3486_;
goto v___jp_3135_;
}
}
v___jp_3487_:
{
if (v___y_3493_ == 0)
{
uint8_t v___x_3494_; 
v___x_3494_ = l_List_isEmpty___redArg(v___y_3489_);
lean_dec(v___y_3489_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
lean_dec(v___y_3490_);
lean_dec(v___y_3488_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v___x_3495_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3496_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3495_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_3185_ = v___y_3491_;
v___y_3186_ = v___y_3492_;
v___y_3187_ = v___x_3496_;
goto v___jp_3184_;
}
else
{
lean_object* v___x_3497_; 
lean_inc(v_trace_3010_);
v___x_3497_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3490_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v___x_3499_ = l_List_appendTR___redArg(v___y_3488_, v_a_3498_);
v___y_3141_ = v___y_3491_;
v___y_3142_ = v___y_3492_;
v_a_3143_ = v___x_3499_;
goto v___jp_3140_;
}
else
{
lean_dec(v___y_3488_);
v___y_3185_ = v___y_3491_;
v___y_3186_ = v___y_3492_;
v___y_3187_ = v___x_3497_;
goto v___jp_3184_;
}
}
}
else
{
v___y_3172_ = v___y_3488_;
v___y_3173_ = v___y_3489_;
v___y_3174_ = v___y_3490_;
v___y_3175_ = v___y_3491_;
v___y_3176_ = v___y_3492_;
goto v___jp_3171_;
}
}
v___jp_3500_:
{
uint8_t v_commitIndependentGoals_3506_; lean_object* v___x_3507_; 
v_commitIndependentGoals_3506_ = lean_ctor_get_uint8(v_cfg_3009_, sizeof(void*)*4);
lean_inc(v___y_3501_);
v___x_3507_ = l_List_appendTR___redArg(v_a_3505_, v___y_3501_);
if (v_commitIndependentGoals_3506_ == 0)
{
v___y_3488_ = v___y_3501_;
v___y_3489_ = v___y_3502_;
v___y_3490_ = v___x_3507_;
v___y_3491_ = v___y_3503_;
v___y_3492_ = v___y_3504_;
v___y_3493_ = v___x_3029_;
goto v___jp_3487_;
}
else
{
uint8_t v___x_3508_; 
v___x_3508_ = l_List_isEmpty___redArg(v___y_3501_);
if (v___x_3508_ == 0)
{
v___y_3172_ = v___y_3501_;
v___y_3173_ = v___y_3502_;
v___y_3174_ = v___x_3507_;
v___y_3175_ = v___y_3503_;
v___y_3176_ = v___y_3504_;
goto v___jp_3171_;
}
else
{
v___y_3488_ = v___y_3501_;
v___y_3489_ = v___y_3502_;
v___y_3490_ = v___x_3507_;
v___y_3491_ = v___y_3503_;
v___y_3492_ = v___y_3504_;
v___y_3493_ = v___x_3029_;
goto v___jp_3487_;
}
}
}
v___jp_3509_:
{
lean_object* v___x_3513_; double v___x_3514_; double v___x_3515_; double v___x_3516_; double v___x_3517_; double v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3513_ = lean_io_mono_nanos_now();
v___x_3514_ = lean_float_of_nat(v___y_3510_);
v___x_3515_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3516_ = lean_float_div(v___x_3514_, v___x_3515_);
v___x_3517_ = lean_float_of_nat(v___x_3513_);
v___x_3518_ = lean_float_div(v___x_3517_, v___x_3515_);
v___x_3519_ = lean_box_float(v___x_3516_);
v___x_3520_ = lean_box_float(v___x_3518_);
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3519_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v_a_3512_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3010_, v_hasTrace_3032_, v___x_3117_, v_options_3031_, v___x_3120_, v___y_3511_, v___f_3116_, v___x_3522_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_3523_;
}
v___jp_3524_:
{
lean_object* v___x_3528_; 
v___x_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3528_, 0, v_a_3527_);
v___y_3510_ = v___y_3525_;
v___y_3511_ = v___y_3526_;
v_a_3512_ = v___x_3528_;
goto v___jp_3509_;
}
v___jp_3529_:
{
lean_object* v___x_3533_; 
v___x_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3533_, 0, v_a_3532_);
v___y_3510_ = v___y_3530_;
v___y_3511_ = v___y_3531_;
v_a_3512_ = v___x_3533_;
goto v___jp_3509_;
}
v___jp_3534_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = l_List_appendTR___redArg(v___y_3535_, v___y_3537_);
v___x_3541_ = l_List_appendTR___redArg(v___x_3540_, v_a_3539_);
v___y_3530_ = v___y_3536_;
v___y_3531_ = v___y_3538_;
v_a_3532_ = v___x_3541_;
goto v___jp_3529_;
}
v___jp_3542_:
{
if (lean_obj_tag(v___y_3547_) == 0)
{
lean_object* v_a_3548_; 
v_a_3548_ = lean_ctor_get(v___y_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___y_3547_, 1);
v___y_3535_ = v___y_3543_;
v___y_3536_ = v___y_3545_;
v___y_3537_ = v___y_3544_;
v___y_3538_ = v___y_3546_;
v_a_3539_ = v_a_3548_;
goto v___jp_3534_;
}
else
{
lean_object* v_a_3549_; 
lean_dec(v___y_3544_);
lean_dec(v___y_3543_);
v_a_3549_ = lean_ctor_get(v___y_3547_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___y_3547_, 1);
v___y_3525_ = v___y_3545_;
v___y_3526_ = v___y_3546_;
v_a_3527_ = v_a_3549_;
goto v___jp_3524_;
}
}
v___jp_3550_:
{
if (v___y_3557_ == 0)
{
lean_object* v___x_3558_; 
lean_dec_ref(v___y_3553_);
v___x_3558_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3552_, v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_dec_ref_known(v___x_3558_, 1);
v___y_3535_ = v___y_3551_;
v___y_3536_ = v___y_3555_;
v___y_3537_ = v___y_3554_;
v___y_3538_ = v___y_3556_;
v_a_3539_ = v_snd_3025_;
goto v___jp_3534_;
}
else
{
lean_object* v_a_3559_; 
lean_dec(v___y_3554_);
lean_dec(v___y_3551_);
lean_dec(v_snd_3025_);
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___x_3558_, 1);
v___y_3525_ = v___y_3555_;
v___y_3526_ = v___y_3556_;
v_a_3527_ = v_a_3559_;
goto v___jp_3524_;
}
}
else
{
lean_dec_ref(v___y_3552_);
lean_dec(v_snd_3025_);
v___y_3543_ = v___y_3551_;
v___y_3544_ = v___y_3554_;
v___y_3545_ = v___y_3555_;
v___y_3546_ = v___y_3556_;
v___y_3547_ = v___y_3553_;
goto v___jp_3542_;
}
}
v___jp_3560_:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Lean_Meta_saveState___redArg(v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3568_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3566_, 1);
lean_inc(v_snd_3025_);
lean_inc(v_trace_3010_);
v___x_3568_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3562_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_dec(v_a_3567_);
lean_dec(v_snd_3025_);
v___y_3543_ = v___y_3561_;
v___y_3544_ = v___y_3564_;
v___y_3545_ = v___y_3563_;
v___y_3546_ = v___y_3565_;
v___y_3547_ = v___x_3568_;
goto v___jp_3542_;
}
else
{
lean_object* v_a_3569_; uint8_t v___x_3570_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
v___x_3570_ = l_Lean_Exception_isInterrupt(v_a_3569_);
if (v___x_3570_ == 0)
{
uint8_t v___x_3571_; 
lean_inc(v_a_3569_);
v___x_3571_ = l_Lean_Exception_isRuntime(v_a_3569_);
v___y_3551_ = v___y_3561_;
v___y_3552_ = v_a_3567_;
v___y_3553_ = v___x_3568_;
v___y_3554_ = v___y_3564_;
v___y_3555_ = v___y_3563_;
v___y_3556_ = v___y_3565_;
v___y_3557_ = v___x_3571_;
goto v___jp_3550_;
}
else
{
v___y_3551_ = v___y_3561_;
v___y_3552_ = v_a_3567_;
v___y_3553_ = v___x_3568_;
v___y_3554_ = v___y_3564_;
v___y_3555_ = v___y_3563_;
v___y_3556_ = v___y_3565_;
v___y_3557_ = v___x_3570_;
goto v___jp_3550_;
}
}
}
else
{
lean_object* v_a_3572_; 
lean_dec(v___y_3564_);
lean_dec(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3572_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3572_);
lean_dec_ref_known(v___x_3566_, 1);
v___y_3525_ = v___y_3563_;
v___y_3526_ = v___y_3565_;
v_a_3527_ = v_a_3572_;
goto v___jp_3524_;
}
}
v___jp_3573_:
{
if (lean_obj_tag(v___y_3576_) == 0)
{
lean_object* v_a_3577_; 
v_a_3577_ = lean_ctor_get(v___y_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___y_3576_, 1);
v___y_3530_ = v___y_3574_;
v___y_3531_ = v___y_3575_;
v_a_3532_ = v_a_3577_;
goto v___jp_3529_;
}
else
{
lean_object* v_a_3578_; 
v_a_3578_ = lean_ctor_get(v___y_3576_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___y_3576_, 1);
v___y_3525_ = v___y_3574_;
v___y_3526_ = v___y_3575_;
v_a_3527_ = v_a_3578_;
goto v___jp_3524_;
}
}
v___jp_3579_:
{
lean_object* v___x_3587_; double v___x_3588_; double v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3587_ = lean_io_get_num_heartbeats();
v___x_3588_ = lean_float_of_nat(v___y_3580_);
v___x_3589_ = lean_float_of_nat(v___x_3587_);
v___x_3590_ = lean_box_float(v___x_3588_);
v___x_3591_ = lean_box_float(v___x_3589_);
v___x_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3590_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
v___x_3593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3593_, 0, v_a_3586_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
lean_inc(v_trace_3010_);
v___x_3594_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3010_, v_hasTrace_3032_, v___x_3117_, v_options_3031_, v___y_3581_, v___y_3584_, v___y_3585_, v___x_3593_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_3574_ = v___y_3582_;
v___y_3575_ = v___y_3583_;
v___y_3576_ = v___x_3594_;
goto v___jp_3573_;
}
v___jp_3595_:
{
lean_object* v___x_3603_; 
v___x_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3603_, 0, v_a_3602_);
v___y_3580_ = v___y_3596_;
v___y_3581_ = v___y_3597_;
v___y_3582_ = v___y_3598_;
v___y_3583_ = v___y_3599_;
v___y_3584_ = v___y_3600_;
v___y_3585_ = v___y_3601_;
v_a_3586_ = v___x_3603_;
goto v___jp_3579_;
}
v___jp_3604_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = l_List_appendTR___redArg(v___y_3605_, v___y_3609_);
v___x_3615_ = l_List_appendTR___redArg(v___x_3614_, v_a_3613_);
v___y_3596_ = v___y_3606_;
v___y_3597_ = v___y_3607_;
v___y_3598_ = v___y_3608_;
v___y_3599_ = v___y_3610_;
v___y_3600_ = v___y_3611_;
v___y_3601_ = v___y_3612_;
v_a_3602_ = v___x_3615_;
goto v___jp_3595_;
}
v___jp_3616_:
{
lean_object* v___x_3624_; 
v___x_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3624_, 0, v_a_3623_);
v___y_3580_ = v___y_3617_;
v___y_3581_ = v___y_3618_;
v___y_3582_ = v___y_3619_;
v___y_3583_ = v___y_3620_;
v___y_3584_ = v___y_3621_;
v___y_3585_ = v___y_3622_;
v_a_3586_ = v___x_3624_;
goto v___jp_3579_;
}
v___jp_3625_:
{
if (lean_obj_tag(v___y_3632_) == 0)
{
lean_object* v_a_3633_; 
v_a_3633_ = lean_ctor_get(v___y_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref_known(v___y_3632_, 1);
v___y_3596_ = v___y_3626_;
v___y_3597_ = v___y_3627_;
v___y_3598_ = v___y_3628_;
v___y_3599_ = v___y_3629_;
v___y_3600_ = v___y_3630_;
v___y_3601_ = v___y_3631_;
v_a_3602_ = v_a_3633_;
goto v___jp_3595_;
}
else
{
lean_object* v_a_3634_; 
v_a_3634_ = lean_ctor_get(v___y_3632_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___y_3632_, 1);
v___y_3617_ = v___y_3626_;
v___y_3618_ = v___y_3627_;
v___y_3619_ = v___y_3628_;
v___y_3620_ = v___y_3629_;
v___y_3621_ = v___y_3630_;
v___y_3622_ = v___y_3631_;
v_a_3623_ = v_a_3634_;
goto v___jp_3616_;
}
}
v___jp_3635_:
{
lean_object* v___x_3644_; 
lean_inc(v_trace_3010_);
v___x_3644_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3639_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3646_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v___x_3646_ = l_List_appendTR___redArg(v___y_3636_, v_a_3645_);
v___y_3596_ = v___y_3637_;
v___y_3597_ = v___y_3638_;
v___y_3598_ = v___y_3640_;
v___y_3599_ = v___y_3641_;
v___y_3600_ = v___y_3642_;
v___y_3601_ = v___y_3643_;
v_a_3602_ = v___x_3646_;
goto v___jp_3595_;
}
else
{
lean_dec(v___y_3636_);
v___y_3626_ = v___y_3637_;
v___y_3627_ = v___y_3638_;
v___y_3628_ = v___y_3640_;
v___y_3629_ = v___y_3641_;
v___y_3630_ = v___y_3642_;
v___y_3631_ = v___y_3643_;
v___y_3632_ = v___x_3644_;
goto v___jp_3625_;
}
}
v___jp_3647_:
{
if (lean_obj_tag(v___y_3656_) == 0)
{
lean_object* v_a_3657_; 
v_a_3657_ = lean_ctor_get(v___y_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v___y_3656_, 1);
v___y_3605_ = v___y_3648_;
v___y_3606_ = v___y_3649_;
v___y_3607_ = v___y_3650_;
v___y_3608_ = v___y_3652_;
v___y_3609_ = v___y_3651_;
v___y_3610_ = v___y_3653_;
v___y_3611_ = v___y_3654_;
v___y_3612_ = v___y_3655_;
v_a_3613_ = v_a_3657_;
goto v___jp_3604_;
}
else
{
lean_object* v_a_3658_; 
lean_dec(v___y_3651_);
lean_dec(v___y_3648_);
v_a_3658_ = lean_ctor_get(v___y_3656_, 0);
lean_inc(v_a_3658_);
lean_dec_ref_known(v___y_3656_, 1);
v___y_3617_ = v___y_3649_;
v___y_3618_ = v___y_3650_;
v___y_3619_ = v___y_3652_;
v___y_3620_ = v___y_3653_;
v___y_3621_ = v___y_3654_;
v___y_3622_ = v___y_3655_;
v_a_3623_ = v_a_3658_;
goto v___jp_3616_;
}
}
v___jp_3659_:
{
if (v___y_3670_ == 0)
{
lean_object* v___x_3671_; 
lean_dec_ref(v___y_3661_);
v___x_3671_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3663_, v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_dec_ref_known(v___x_3671_, 1);
v___y_3605_ = v___y_3660_;
v___y_3606_ = v___y_3662_;
v___y_3607_ = v___y_3664_;
v___y_3608_ = v___y_3666_;
v___y_3609_ = v___y_3665_;
v___y_3610_ = v___y_3667_;
v___y_3611_ = v___y_3668_;
v___y_3612_ = v___y_3669_;
v_a_3613_ = v_snd_3025_;
goto v___jp_3604_;
}
else
{
lean_object* v_a_3672_; 
lean_dec(v___y_3665_);
lean_dec(v___y_3660_);
lean_dec(v_snd_3025_);
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_a_3672_);
lean_dec_ref_known(v___x_3671_, 1);
v___y_3617_ = v___y_3662_;
v___y_3618_ = v___y_3664_;
v___y_3619_ = v___y_3666_;
v___y_3620_ = v___y_3667_;
v___y_3621_ = v___y_3668_;
v___y_3622_ = v___y_3669_;
v_a_3623_ = v_a_3672_;
goto v___jp_3616_;
}
}
else
{
lean_dec_ref(v___y_3663_);
lean_dec(v_snd_3025_);
v___y_3648_ = v___y_3660_;
v___y_3649_ = v___y_3662_;
v___y_3650_ = v___y_3664_;
v___y_3651_ = v___y_3665_;
v___y_3652_ = v___y_3666_;
v___y_3653_ = v___y_3667_;
v___y_3654_ = v___y_3668_;
v___y_3655_ = v___y_3669_;
v___y_3656_ = v___y_3661_;
goto v___jp_3647_;
}
}
v___jp_3673_:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_Meta_saveState___redArg(v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3685_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3683_, 1);
lean_inc(v_snd_3025_);
lean_inc(v_trace_3010_);
v___x_3685_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3677_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_dec(v_a_3684_);
lean_dec(v_snd_3025_);
v___y_3648_ = v___y_3674_;
v___y_3649_ = v___y_3675_;
v___y_3650_ = v___y_3676_;
v___y_3651_ = v___y_3679_;
v___y_3652_ = v___y_3678_;
v___y_3653_ = v___y_3680_;
v___y_3654_ = v___y_3681_;
v___y_3655_ = v___y_3682_;
v___y_3656_ = v___x_3685_;
goto v___jp_3647_;
}
else
{
lean_object* v_a_3686_; uint8_t v___x_3687_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
v___x_3687_ = l_Lean_Exception_isInterrupt(v_a_3686_);
if (v___x_3687_ == 0)
{
uint8_t v___x_3688_; 
lean_inc(v_a_3686_);
v___x_3688_ = l_Lean_Exception_isRuntime(v_a_3686_);
v___y_3660_ = v___y_3674_;
v___y_3661_ = v___x_3685_;
v___y_3662_ = v___y_3675_;
v___y_3663_ = v_a_3684_;
v___y_3664_ = v___y_3676_;
v___y_3665_ = v___y_3679_;
v___y_3666_ = v___y_3678_;
v___y_3667_ = v___y_3680_;
v___y_3668_ = v___y_3681_;
v___y_3669_ = v___y_3682_;
v___y_3670_ = v___x_3688_;
goto v___jp_3659_;
}
else
{
v___y_3660_ = v___y_3674_;
v___y_3661_ = v___x_3685_;
v___y_3662_ = v___y_3675_;
v___y_3663_ = v_a_3684_;
v___y_3664_ = v___y_3676_;
v___y_3665_ = v___y_3679_;
v___y_3666_ = v___y_3678_;
v___y_3667_ = v___y_3680_;
v___y_3668_ = v___y_3681_;
v___y_3669_ = v___y_3682_;
v___y_3670_ = v___x_3687_;
goto v___jp_3659_;
}
}
}
else
{
lean_object* v_a_3689_; 
lean_dec(v___y_3679_);
lean_dec(v___y_3677_);
lean_dec(v___y_3674_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3689_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3689_);
lean_dec_ref_known(v___x_3683_, 1);
v___y_3617_ = v___y_3675_;
v___y_3618_ = v___y_3676_;
v___y_3619_ = v___y_3678_;
v___y_3620_ = v___y_3680_;
v___y_3621_ = v___y_3681_;
v___y_3622_ = v___y_3682_;
v_a_3623_ = v_a_3689_;
goto v___jp_3616_;
}
}
v___jp_3690_:
{
if (v___y_3701_ == 0)
{
uint8_t v___x_3702_; 
v___x_3702_ = l_List_isEmpty___redArg(v___y_3697_);
lean_dec(v___y_3697_);
if (v___x_3702_ == 0)
{
if (v___y_3694_ == 0)
{
v___y_3636_ = v___y_3691_;
v___y_3637_ = v___y_3692_;
v___y_3638_ = v___y_3693_;
v___y_3639_ = v___y_3695_;
v___y_3640_ = v___y_3696_;
v___y_3641_ = v___y_3698_;
v___y_3642_ = v___y_3699_;
v___y_3643_ = v___y_3700_;
goto v___jp_3635_;
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
lean_dec(v___y_3695_);
lean_dec(v___y_3691_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v___x_3703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3704_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3703_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_3626_ = v___y_3692_;
v___y_3627_ = v___y_3693_;
v___y_3628_ = v___y_3696_;
v___y_3629_ = v___y_3698_;
v___y_3630_ = v___y_3699_;
v___y_3631_ = v___y_3700_;
v___y_3632_ = v___x_3704_;
goto v___jp_3625_;
}
}
else
{
v___y_3636_ = v___y_3691_;
v___y_3637_ = v___y_3692_;
v___y_3638_ = v___y_3693_;
v___y_3639_ = v___y_3695_;
v___y_3640_ = v___y_3696_;
v___y_3641_ = v___y_3698_;
v___y_3642_ = v___y_3699_;
v___y_3643_ = v___y_3700_;
goto v___jp_3635_;
}
}
else
{
v___y_3674_ = v___y_3691_;
v___y_3675_ = v___y_3692_;
v___y_3676_ = v___y_3693_;
v___y_3677_ = v___y_3695_;
v___y_3678_ = v___y_3696_;
v___y_3679_ = v___y_3697_;
v___y_3680_ = v___y_3698_;
v___y_3681_ = v___y_3699_;
v___y_3682_ = v___y_3700_;
goto v___jp_3673_;
}
}
v___jp_3705_:
{
uint8_t v_commitIndependentGoals_3716_; lean_object* v___x_3717_; 
v_commitIndependentGoals_3716_ = lean_ctor_get_uint8(v_cfg_3009_, sizeof(void*)*4);
lean_inc(v___y_3706_);
v___x_3717_ = l_List_appendTR___redArg(v_a_3715_, v___y_3706_);
if (v_commitIndependentGoals_3716_ == 0)
{
v___y_3691_ = v___y_3706_;
v___y_3692_ = v___y_3707_;
v___y_3693_ = v___y_3709_;
v___y_3694_ = v___y_3708_;
v___y_3695_ = v___x_3717_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3710_;
v___y_3698_ = v___y_3712_;
v___y_3699_ = v___y_3713_;
v___y_3700_ = v___y_3714_;
v___y_3701_ = v___x_3029_;
goto v___jp_3690_;
}
else
{
uint8_t v___x_3718_; 
v___x_3718_ = l_List_isEmpty___redArg(v___y_3706_);
if (v___x_3718_ == 0)
{
v___y_3674_ = v___y_3706_;
v___y_3675_ = v___y_3707_;
v___y_3676_ = v___y_3709_;
v___y_3677_ = v___x_3717_;
v___y_3678_ = v___y_3711_;
v___y_3679_ = v___y_3710_;
v___y_3680_ = v___y_3712_;
v___y_3681_ = v___y_3713_;
v___y_3682_ = v___y_3714_;
goto v___jp_3673_;
}
else
{
v___y_3691_ = v___y_3706_;
v___y_3692_ = v___y_3707_;
v___y_3693_ = v___y_3709_;
v___y_3694_ = v___y_3708_;
v___y_3695_ = v___x_3717_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3710_;
v___y_3698_ = v___y_3712_;
v___y_3699_ = v___y_3713_;
v___y_3700_ = v___y_3714_;
v___y_3701_ = v___x_3029_;
goto v___jp_3690_;
}
}
}
v___jp_3719_:
{
lean_object* v___x_3727_; double v___x_3728_; double v___x_3729_; double v___x_3730_; double v___x_3731_; double v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3727_ = lean_io_mono_nanos_now();
v___x_3728_ = lean_float_of_nat(v___y_3721_);
v___x_3729_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3730_ = lean_float_div(v___x_3728_, v___x_3729_);
v___x_3731_ = lean_float_of_nat(v___x_3727_);
v___x_3732_ = lean_float_div(v___x_3731_, v___x_3729_);
v___x_3733_ = lean_box_float(v___x_3730_);
v___x_3734_ = lean_box_float(v___x_3732_);
v___x_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v_a_3726_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
lean_inc(v_trace_3010_);
v___x_3737_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3010_, v_hasTrace_3032_, v___x_3117_, v_options_3031_, v___y_3720_, v___y_3724_, v___y_3725_, v___x_3736_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_3574_ = v___y_3722_;
v___y_3575_ = v___y_3723_;
v___y_3576_ = v___x_3737_;
goto v___jp_3573_;
}
v___jp_3738_:
{
lean_object* v___x_3746_; 
v___x_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3746_, 0, v_a_3745_);
v___y_3720_ = v___y_3740_;
v___y_3721_ = v___y_3739_;
v___y_3722_ = v___y_3741_;
v___y_3723_ = v___y_3742_;
v___y_3724_ = v___y_3743_;
v___y_3725_ = v___y_3744_;
v_a_3726_ = v___x_3746_;
goto v___jp_3719_;
}
v___jp_3747_:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3755_, 0, v_a_3754_);
v___y_3720_ = v___y_3749_;
v___y_3721_ = v___y_3748_;
v___y_3722_ = v___y_3750_;
v___y_3723_ = v___y_3751_;
v___y_3724_ = v___y_3752_;
v___y_3725_ = v___y_3753_;
v_a_3726_ = v___x_3755_;
goto v___jp_3719_;
}
v___jp_3756_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3766_ = l_List_appendTR___redArg(v___y_3757_, v___y_3761_);
v___x_3767_ = l_List_appendTR___redArg(v___x_3766_, v_a_3765_);
v___y_3748_ = v___y_3759_;
v___y_3749_ = v___y_3758_;
v___y_3750_ = v___y_3760_;
v___y_3751_ = v___y_3762_;
v___y_3752_ = v___y_3763_;
v___y_3753_ = v___y_3764_;
v_a_3754_ = v___x_3767_;
goto v___jp_3747_;
}
v___jp_3768_:
{
if (lean_obj_tag(v___y_3777_) == 0)
{
lean_object* v_a_3778_; 
v_a_3778_ = lean_ctor_get(v___y_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v___y_3777_, 1);
v___y_3757_ = v___y_3769_;
v___y_3758_ = v___y_3771_;
v___y_3759_ = v___y_3770_;
v___y_3760_ = v___y_3773_;
v___y_3761_ = v___y_3772_;
v___y_3762_ = v___y_3774_;
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v_a_3765_ = v_a_3778_;
goto v___jp_3756_;
}
else
{
lean_object* v_a_3779_; 
lean_dec(v___y_3772_);
lean_dec(v___y_3769_);
v_a_3779_ = lean_ctor_get(v___y_3777_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v___y_3777_, 1);
v___y_3739_ = v___y_3770_;
v___y_3740_ = v___y_3771_;
v___y_3741_ = v___y_3773_;
v___y_3742_ = v___y_3774_;
v___y_3743_ = v___y_3775_;
v___y_3744_ = v___y_3776_;
v_a_3745_ = v_a_3779_;
goto v___jp_3738_;
}
}
v___jp_3780_:
{
if (v___y_3791_ == 0)
{
lean_object* v___x_3792_; 
lean_dec_ref(v___y_3788_);
v___x_3792_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3784_, v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_dec_ref_known(v___x_3792_, 1);
v___y_3757_ = v___y_3781_;
v___y_3758_ = v___y_3783_;
v___y_3759_ = v___y_3782_;
v___y_3760_ = v___y_3786_;
v___y_3761_ = v___y_3785_;
v___y_3762_ = v___y_3787_;
v___y_3763_ = v___y_3789_;
v___y_3764_ = v___y_3790_;
v_a_3765_ = v_snd_3025_;
goto v___jp_3756_;
}
else
{
lean_object* v_a_3793_; 
lean_dec(v___y_3785_);
lean_dec(v___y_3781_);
lean_dec(v_snd_3025_);
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v___y_3739_ = v___y_3782_;
v___y_3740_ = v___y_3783_;
v___y_3741_ = v___y_3786_;
v___y_3742_ = v___y_3787_;
v___y_3743_ = v___y_3789_;
v___y_3744_ = v___y_3790_;
v_a_3745_ = v_a_3793_;
goto v___jp_3738_;
}
}
else
{
lean_dec_ref(v___y_3784_);
lean_dec(v_snd_3025_);
v___y_3769_ = v___y_3781_;
v___y_3770_ = v___y_3782_;
v___y_3771_ = v___y_3783_;
v___y_3772_ = v___y_3785_;
v___y_3773_ = v___y_3786_;
v___y_3774_ = v___y_3787_;
v___y_3775_ = v___y_3789_;
v___y_3776_ = v___y_3790_;
v___y_3777_ = v___y_3788_;
goto v___jp_3768_;
}
}
v___jp_3794_:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_Lean_Meta_saveState___redArg(v_a_3016_, v_a_3018_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3806_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
lean_inc(v_snd_3025_);
lean_inc(v_trace_3010_);
v___x_3806_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3802_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_dec(v_a_3805_);
lean_dec(v_snd_3025_);
v___y_3769_ = v___y_3795_;
v___y_3770_ = v___y_3797_;
v___y_3771_ = v___y_3796_;
v___y_3772_ = v___y_3799_;
v___y_3773_ = v___y_3798_;
v___y_3774_ = v___y_3800_;
v___y_3775_ = v___y_3801_;
v___y_3776_ = v___y_3803_;
v___y_3777_ = v___x_3806_;
goto v___jp_3768_;
}
else
{
lean_object* v_a_3807_; uint8_t v___x_3808_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
v___x_3808_ = l_Lean_Exception_isInterrupt(v_a_3807_);
if (v___x_3808_ == 0)
{
uint8_t v___x_3809_; 
lean_inc(v_a_3807_);
v___x_3809_ = l_Lean_Exception_isRuntime(v_a_3807_);
v___y_3781_ = v___y_3795_;
v___y_3782_ = v___y_3797_;
v___y_3783_ = v___y_3796_;
v___y_3784_ = v_a_3805_;
v___y_3785_ = v___y_3799_;
v___y_3786_ = v___y_3798_;
v___y_3787_ = v___y_3800_;
v___y_3788_ = v___x_3806_;
v___y_3789_ = v___y_3801_;
v___y_3790_ = v___y_3803_;
v___y_3791_ = v___x_3809_;
goto v___jp_3780_;
}
else
{
v___y_3781_ = v___y_3795_;
v___y_3782_ = v___y_3797_;
v___y_3783_ = v___y_3796_;
v___y_3784_ = v_a_3805_;
v___y_3785_ = v___y_3799_;
v___y_3786_ = v___y_3798_;
v___y_3787_ = v___y_3800_;
v___y_3788_ = v___x_3806_;
v___y_3789_ = v___y_3801_;
v___y_3790_ = v___y_3803_;
v___y_3791_ = v___x_3808_;
goto v___jp_3780_;
}
}
}
else
{
lean_object* v_a_3810_; 
lean_dec(v___y_3802_);
lean_dec(v___y_3799_);
lean_dec(v___y_3795_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3810_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3804_, 1);
v___y_3739_ = v___y_3797_;
v___y_3740_ = v___y_3796_;
v___y_3741_ = v___y_3798_;
v___y_3742_ = v___y_3800_;
v___y_3743_ = v___y_3801_;
v___y_3744_ = v___y_3803_;
v_a_3745_ = v_a_3810_;
goto v___jp_3738_;
}
}
v___jp_3811_:
{
if (lean_obj_tag(v___y_3818_) == 0)
{
lean_object* v_a_3819_; 
v_a_3819_ = lean_ctor_get(v___y_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref_known(v___y_3818_, 1);
v___y_3748_ = v___y_3813_;
v___y_3749_ = v___y_3812_;
v___y_3750_ = v___y_3814_;
v___y_3751_ = v___y_3815_;
v___y_3752_ = v___y_3816_;
v___y_3753_ = v___y_3817_;
v_a_3754_ = v_a_3819_;
goto v___jp_3747_;
}
else
{
lean_object* v_a_3820_; 
v_a_3820_ = lean_ctor_get(v___y_3818_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___y_3818_, 1);
v___y_3739_ = v___y_3813_;
v___y_3740_ = v___y_3812_;
v___y_3741_ = v___y_3814_;
v___y_3742_ = v___y_3815_;
v___y_3743_ = v___y_3816_;
v___y_3744_ = v___y_3817_;
v_a_3745_ = v_a_3820_;
goto v___jp_3738_;
}
}
v___jp_3821_:
{
if (v___y_3831_ == 0)
{
uint8_t v___x_3832_; 
v___x_3832_ = l_List_isEmpty___redArg(v___y_3826_);
lean_dec(v___y_3826_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_dec(v___y_3828_);
lean_dec(v___y_3822_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v___x_3833_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3834_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3833_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_3812_ = v___y_3824_;
v___y_3813_ = v___y_3823_;
v___y_3814_ = v___y_3825_;
v___y_3815_ = v___y_3827_;
v___y_3816_ = v___y_3829_;
v___y_3817_ = v___y_3830_;
v___y_3818_ = v___x_3834_;
goto v___jp_3811_;
}
else
{
lean_object* v___x_3835_; 
lean_inc(v_trace_3010_);
v___x_3835_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3828_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3837_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref_known(v___x_3835_, 1);
v___x_3837_ = l_List_appendTR___redArg(v___y_3822_, v_a_3836_);
v___y_3748_ = v___y_3823_;
v___y_3749_ = v___y_3824_;
v___y_3750_ = v___y_3825_;
v___y_3751_ = v___y_3827_;
v___y_3752_ = v___y_3829_;
v___y_3753_ = v___y_3830_;
v_a_3754_ = v___x_3837_;
goto v___jp_3747_;
}
else
{
lean_dec(v___y_3822_);
v___y_3812_ = v___y_3824_;
v___y_3813_ = v___y_3823_;
v___y_3814_ = v___y_3825_;
v___y_3815_ = v___y_3827_;
v___y_3816_ = v___y_3829_;
v___y_3817_ = v___y_3830_;
v___y_3818_ = v___x_3835_;
goto v___jp_3811_;
}
}
}
else
{
v___y_3795_ = v___y_3822_;
v___y_3796_ = v___y_3824_;
v___y_3797_ = v___y_3823_;
v___y_3798_ = v___y_3825_;
v___y_3799_ = v___y_3826_;
v___y_3800_ = v___y_3827_;
v___y_3801_ = v___y_3829_;
v___y_3802_ = v___y_3828_;
v___y_3803_ = v___y_3830_;
goto v___jp_3794_;
}
}
v___jp_3838_:
{
uint8_t v_commitIndependentGoals_3848_; lean_object* v___x_3849_; 
v_commitIndependentGoals_3848_ = lean_ctor_get_uint8(v_cfg_3009_, sizeof(void*)*4);
lean_inc(v___y_3839_);
v___x_3849_ = l_List_appendTR___redArg(v_a_3847_, v___y_3839_);
if (v_commitIndependentGoals_3848_ == 0)
{
v___y_3822_ = v___y_3839_;
v___y_3823_ = v___y_3840_;
v___y_3824_ = v___y_3841_;
v___y_3825_ = v___y_3843_;
v___y_3826_ = v___y_3842_;
v___y_3827_ = v___y_3844_;
v___y_3828_ = v___x_3849_;
v___y_3829_ = v___y_3845_;
v___y_3830_ = v___y_3846_;
v___y_3831_ = v___x_3029_;
goto v___jp_3821_;
}
else
{
uint8_t v___x_3850_; 
v___x_3850_ = l_List_isEmpty___redArg(v___y_3839_);
if (v___x_3850_ == 0)
{
v___y_3795_ = v___y_3839_;
v___y_3796_ = v___y_3841_;
v___y_3797_ = v___y_3840_;
v___y_3798_ = v___y_3843_;
v___y_3799_ = v___y_3842_;
v___y_3800_ = v___y_3844_;
v___y_3801_ = v___y_3845_;
v___y_3802_ = v___x_3849_;
v___y_3803_ = v___y_3846_;
goto v___jp_3794_;
}
else
{
v___y_3822_ = v___y_3839_;
v___y_3823_ = v___y_3840_;
v___y_3824_ = v___y_3841_;
v___y_3825_ = v___y_3843_;
v___y_3826_ = v___y_3842_;
v___y_3827_ = v___y_3844_;
v___y_3828_ = v___x_3849_;
v___y_3829_ = v___y_3845_;
v___y_3830_ = v___y_3846_;
v___y_3831_ = v___x_3029_;
goto v___jp_3821_;
}
}
}
v___jp_3851_:
{
lean_object* v___x_3860_; 
v___x_3860_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3018_);
if (lean_obj_tag(v___x_3860_) == 0)
{
if (v___y_3854_ == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v___x_3862_ = lean_io_mono_nanos_now();
v___x_3863_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3032_, v___x_3029_, v_goals_3013_, v___y_3857_, v_a_3016_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3865_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v___x_3863_, 1);
v___x_3865_ = l_List_reverse___redArg(v_a_3864_);
v___y_3839_ = v___y_3852_;
v___y_3840_ = v___x_3862_;
v___y_3841_ = v___y_3853_;
v___y_3842_ = v___y_3855_;
v___y_3843_ = v___y_3856_;
v___y_3844_ = v___y_3858_;
v___y_3845_ = v_a_3861_;
v___y_3846_ = v___y_3859_;
v_a_3847_ = v___x_3865_;
goto v___jp_3838_;
}
else
{
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3866_; 
v_a_3866_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3866_);
lean_dec_ref_known(v___x_3863_, 1);
v___y_3839_ = v___y_3852_;
v___y_3840_ = v___x_3862_;
v___y_3841_ = v___y_3853_;
v___y_3842_ = v___y_3855_;
v___y_3843_ = v___y_3856_;
v___y_3844_ = v___y_3858_;
v___y_3845_ = v_a_3861_;
v___y_3846_ = v___y_3859_;
v_a_3847_ = v_a_3866_;
goto v___jp_3838_;
}
else
{
lean_object* v_a_3867_; 
lean_dec(v___y_3855_);
lean_dec(v___y_3852_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3867_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3863_, 1);
v___y_3739_ = v___x_3862_;
v___y_3740_ = v___y_3853_;
v___y_3741_ = v___y_3856_;
v___y_3742_ = v___y_3858_;
v___y_3743_ = v_a_3861_;
v___y_3744_ = v___y_3859_;
v_a_3745_ = v_a_3867_;
goto v___jp_3738_;
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v_a_3868_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___x_3860_, 1);
v___x_3869_ = lean_io_get_num_heartbeats();
v___x_3870_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3032_, v___x_3029_, v_goals_3013_, v___y_3857_, v_a_3016_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3872_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v___x_3872_ = l_List_reverse___redArg(v_a_3871_);
v___y_3706_ = v___y_3852_;
v___y_3707_ = v___x_3869_;
v___y_3708_ = v___y_3854_;
v___y_3709_ = v___y_3853_;
v___y_3710_ = v___y_3855_;
v___y_3711_ = v___y_3856_;
v___y_3712_ = v___y_3858_;
v___y_3713_ = v_a_3868_;
v___y_3714_ = v___y_3859_;
v_a_3715_ = v___x_3872_;
goto v___jp_3705_;
}
else
{
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3873_; 
v_a_3873_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3870_, 1);
v___y_3706_ = v___y_3852_;
v___y_3707_ = v___x_3869_;
v___y_3708_ = v___y_3854_;
v___y_3709_ = v___y_3853_;
v___y_3710_ = v___y_3855_;
v___y_3711_ = v___y_3856_;
v___y_3712_ = v___y_3858_;
v___y_3713_ = v_a_3868_;
v___y_3714_ = v___y_3859_;
v_a_3715_ = v_a_3873_;
goto v___jp_3705_;
}
else
{
lean_object* v_a_3874_; 
lean_dec(v___y_3855_);
lean_dec(v___y_3852_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3874_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3870_, 1);
v___y_3617_ = v___x_3869_;
v___y_3618_ = v___y_3853_;
v___y_3619_ = v___y_3856_;
v___y_3620_ = v___y_3858_;
v___y_3621_ = v_a_3868_;
v___y_3622_ = v___y_3859_;
v_a_3623_ = v_a_3874_;
goto v___jp_3616_;
}
}
}
}
else
{
lean_object* v_a_3875_; 
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3857_);
lean_dec(v___y_3855_);
lean_dec(v___y_3852_);
lean_dec(v_snd_3025_);
lean_dec(v_goals_3013_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3875_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3860_, 1);
v___y_3525_ = v___y_3856_;
v___y_3526_ = v___y_3858_;
v_a_3527_ = v_a_3875_;
goto v___jp_3524_;
}
}
v___jp_3876_:
{
if (v___y_3882_ == 0)
{
uint8_t v___x_3883_; 
v___x_3883_ = l_List_isEmpty___redArg(v___y_3880_);
lean_dec(v___y_3880_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
lean_dec(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v___x_3884_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3885_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3884_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___y_3574_ = v___y_3879_;
v___y_3575_ = v___y_3881_;
v___y_3576_ = v___x_3885_;
goto v___jp_3573_;
}
else
{
lean_object* v___x_3886_; 
lean_inc(v_trace_3010_);
v___x_3886_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v___y_3878_, v_snd_3025_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = l_List_appendTR___redArg(v___y_3877_, v_a_3887_);
v___y_3530_ = v___y_3879_;
v___y_3531_ = v___y_3881_;
v_a_3532_ = v___x_3888_;
goto v___jp_3529_;
}
else
{
lean_dec(v___y_3877_);
v___y_3574_ = v___y_3879_;
v___y_3575_ = v___y_3881_;
v___y_3576_ = v___x_3886_;
goto v___jp_3573_;
}
}
}
else
{
v___y_3561_ = v___y_3877_;
v___y_3562_ = v___y_3878_;
v___y_3563_ = v___y_3879_;
v___y_3564_ = v___y_3880_;
v___y_3565_ = v___y_3881_;
goto v___jp_3560_;
}
}
v___jp_3889_:
{
uint8_t v_commitIndependentGoals_3895_; lean_object* v___x_3896_; 
v_commitIndependentGoals_3895_ = lean_ctor_get_uint8(v_cfg_3009_, sizeof(void*)*4);
lean_inc(v___y_3890_);
v___x_3896_ = l_List_appendTR___redArg(v_a_3894_, v___y_3890_);
if (v_commitIndependentGoals_3895_ == 0)
{
v___y_3877_ = v___y_3890_;
v___y_3878_ = v___x_3896_;
v___y_3879_ = v___y_3892_;
v___y_3880_ = v___y_3891_;
v___y_3881_ = v___y_3893_;
v___y_3882_ = v___x_3029_;
goto v___jp_3876_;
}
else
{
uint8_t v___x_3897_; 
v___x_3897_ = l_List_isEmpty___redArg(v___y_3890_);
if (v___x_3897_ == 0)
{
v___y_3561_ = v___y_3890_;
v___y_3562_ = v___x_3896_;
v___y_3563_ = v___y_3892_;
v___y_3564_ = v___y_3891_;
v___y_3565_ = v___y_3893_;
goto v___jp_3560_;
}
else
{
v___y_3877_ = v___y_3890_;
v___y_3878_ = v___x_3896_;
v___y_3879_ = v___y_3892_;
v___y_3880_ = v___y_3891_;
v___y_3881_ = v___y_3893_;
v___y_3882_ = v___x_3029_;
goto v___jp_3876_;
}
}
}
v___jp_3898_:
{
lean_object* v___x_3899_; 
v___x_3899_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3018_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3901_; uint8_t v___x_3902_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref_known(v___x_3899_, 1);
v___x_3901_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3902_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3031_, v___x_3901_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_del_object(v___x_3027_);
v___x_3903_ = lean_io_mono_nanos_now();
v___x_3904_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3024_, v___f_3020_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v_fst_3906_; lean_object* v_snd_3907_; lean_object* v___x_3908_; lean_object* v___f_3909_; lean_object* v___x_3910_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3904_, 1);
v_fst_3906_ = lean_ctor_get(v_a_3905_, 0);
lean_inc_n(v_fst_3906_, 2);
v_snd_3907_ = lean_ctor_get(v_a_3905_, 1);
lean_inc(v_snd_3907_);
lean_dec(v_a_3905_);
v___x_3908_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3907_, v___x_3021_);
lean_inc(v___x_3908_);
v___f_3909_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3909_, 0, v_fst_3906_);
lean_closure_set(v___f_3909_, 1, v___x_3908_);
v___x_3910_ = lean_box(0);
if (v___x_3120_ == 0)
{
lean_object* v___x_3911_; uint8_t v___x_3912_; 
v___x_3911_ = l_Lean_trace_profiler;
v___x_3912_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3031_, v___x_3911_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; 
lean_dec_ref(v___f_3909_);
v___x_3913_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_3032_, v___x_3029_, v_goals_3013_, v___x_3910_, v_a_3016_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v___x_3915_ = l_List_reverse___redArg(v_a_3914_);
v___y_3890_ = v___x_3908_;
v___y_3891_ = v_fst_3906_;
v___y_3892_ = v___x_3903_;
v___y_3893_ = v_a_3900_;
v_a_3894_ = v___x_3915_;
goto v___jp_3889_;
}
else
{
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3916_; 
v_a_3916_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3913_, 1);
v___y_3890_ = v___x_3908_;
v___y_3891_ = v_fst_3906_;
v___y_3892_ = v___x_3903_;
v___y_3893_ = v_a_3900_;
v_a_3894_ = v_a_3916_;
goto v___jp_3889_;
}
else
{
lean_object* v_a_3917_; 
lean_dec(v___x_3908_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3917_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3913_, 1);
v___y_3525_ = v___x_3903_;
v___y_3526_ = v_a_3900_;
v_a_3527_ = v_a_3917_;
goto v___jp_3524_;
}
}
}
else
{
v___y_3852_ = v___x_3908_;
v___y_3853_ = v___x_3120_;
v___y_3854_ = v___x_3902_;
v___y_3855_ = v_fst_3906_;
v___y_3856_ = v___x_3903_;
v___y_3857_ = v___x_3910_;
v___y_3858_ = v_a_3900_;
v___y_3859_ = v___f_3909_;
goto v___jp_3851_;
}
}
else
{
v___y_3852_ = v___x_3908_;
v___y_3853_ = v___x_3120_;
v___y_3854_ = v___x_3902_;
v___y_3855_ = v_fst_3906_;
v___y_3856_ = v___x_3903_;
v___y_3857_ = v___x_3910_;
v___y_3858_ = v_a_3900_;
v___y_3859_ = v___f_3909_;
goto v___jp_3851_;
}
}
else
{
lean_object* v_a_3918_; 
lean_dec(v_snd_3025_);
lean_dec(v_goals_3013_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3918_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3904_, 1);
v___y_3525_ = v___x_3903_;
v___y_3526_ = v_a_3900_;
v_a_3527_ = v_a_3918_;
goto v___jp_3524_;
}
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = lean_io_get_num_heartbeats();
v___x_3920_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3024_, v___f_3020_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v_fst_3922_; lean_object* v_snd_3923_; lean_object* v___x_3924_; lean_object* v___f_3925_; lean_object* v___x_3926_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_a_3921_);
lean_dec_ref_known(v___x_3920_, 1);
v_fst_3922_ = lean_ctor_get(v_a_3921_, 0);
lean_inc_n(v_fst_3922_, 2);
v_snd_3923_ = lean_ctor_get(v_a_3921_, 1);
lean_inc(v_snd_3923_);
lean_dec(v_a_3921_);
v___x_3924_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3923_, v___x_3021_);
lean_inc(v___x_3924_);
v___f_3925_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3925_, 0, v_fst_3922_);
lean_closure_set(v___f_3925_, 1, v___x_3924_);
v___x_3926_ = lean_box(0);
if (v___x_3120_ == 0)
{
lean_object* v___x_3927_; uint8_t v___x_3928_; 
v___x_3927_ = l_Lean_trace_profiler;
v___x_3928_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3031_, v___x_3927_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; 
lean_dec_ref(v___f_3925_);
v___x_3929_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3902_, v___x_3029_, v_goals_3013_, v___x_3926_, v_a_3016_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v___x_3931_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3930_);
lean_dec_ref_known(v___x_3929_, 1);
v___x_3931_ = l_List_reverse___redArg(v_a_3930_);
v___y_3501_ = v___x_3924_;
v___y_3502_ = v_fst_3922_;
v___y_3503_ = v_a_3900_;
v___y_3504_ = v___x_3919_;
v_a_3505_ = v___x_3931_;
goto v___jp_3500_;
}
else
{
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3932_; 
v_a_3932_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3929_, 1);
v___y_3501_ = v___x_3924_;
v___y_3502_ = v_fst_3922_;
v___y_3503_ = v_a_3900_;
v___y_3504_ = v___x_3919_;
v_a_3505_ = v_a_3932_;
goto v___jp_3500_;
}
else
{
lean_object* v_a_3933_; 
lean_dec(v___x_3924_);
lean_dec(v_fst_3922_);
lean_dec(v_snd_3025_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3933_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3933_);
lean_dec_ref_known(v___x_3929_, 1);
v___y_3136_ = v_a_3900_;
v___y_3137_ = v___x_3919_;
v_a_3138_ = v_a_3933_;
goto v___jp_3135_;
}
}
}
else
{
v___y_3463_ = v___x_3924_;
v___y_3464_ = v_fst_3922_;
v___y_3465_ = v___x_3926_;
v___y_3466_ = v___x_3120_;
v___y_3467_ = v___x_3902_;
v___y_3468_ = v___f_3925_;
v___y_3469_ = v_a_3900_;
v___y_3470_ = v___x_3919_;
goto v___jp_3462_;
}
}
else
{
v___y_3463_ = v___x_3924_;
v___y_3464_ = v_fst_3922_;
v___y_3465_ = v___x_3926_;
v___y_3466_ = v___x_3120_;
v___y_3467_ = v___x_3902_;
v___y_3468_ = v___f_3925_;
v___y_3469_ = v_a_3900_;
v___y_3470_ = v___x_3919_;
goto v___jp_3462_;
}
}
else
{
lean_object* v_a_3934_; 
lean_dec(v_snd_3025_);
lean_dec(v_goals_3013_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec_ref(v_cfg_3009_);
v_a_3934_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_a_3934_);
lean_dec_ref_known(v___x_3920_, 1);
v___y_3136_ = v_a_3900_;
v___y_3137_ = v___x_3919_;
v_a_3138_ = v_a_3934_;
goto v___jp_3135_;
}
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec_ref(v___f_3116_);
lean_del_object(v___x_3027_);
lean_dec(v_snd_3025_);
lean_dec(v_fst_3024_);
lean_dec_ref(v___f_3020_);
lean_dec(v_goals_3013_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec(v_trace_3010_);
lean_dec_ref(v_cfg_3009_);
v_a_3935_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3899_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3899_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
}
else
{
lean_object* v_maxDepth_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
lean_del_object(v___x_3027_);
lean_dec(v_snd_3025_);
lean_dec(v_fst_3024_);
lean_dec_ref(v___f_3020_);
lean_dec(v_goals_3013_);
v_maxDepth_4222_ = lean_ctor_get(v_cfg_3009_, 0);
lean_inc(v_maxDepth_4222_);
v___x_4223_ = lean_box(0);
v___x_4224_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v_maxDepth_4222_, v_remaining_3014_, v___x_4223_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
return v___x_4224_;
}
}
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec_ref(v___f_3020_);
lean_dec(v_remaining_3014_);
lean_dec(v_goals_3013_);
lean_dec(v_orig_3012_);
lean_dec_ref(v_next_3011_);
lean_dec(v_trace_3010_);
lean_dec_ref(v_cfg_3009_);
v_a_4226_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_3022_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_3022_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_3009_ = stack[0].m_obj;
lean_object* v_trace_3010_ = stack[1].m_obj;
lean_object* v_next_3011_ = stack[2].m_obj;
lean_object* v_orig_3012_ = stack[3].m_obj;
lean_object* v_goals_3013_ = stack[4].m_obj;
lean_object* v_remaining_3014_ = stack[5].m_obj;
lean_object* v_a_3015_ = stack[6].m_obj;
lean_object* v_a_3016_ = stack[7].m_obj;
lean_object* v_a_3017_ = stack[8].m_obj;
lean_object* v_a_3018_ = stack[9].m_obj;
lean_object* v_res_4234_;
v_res_4234_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3009_, v_trace_3010_, v_next_3011_, v_orig_3012_, v_goals_3013_, v_remaining_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
stack->m_obj
 = v_res_4234_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_4235_, lean_object* v_trace_4236_, lean_object* v_next_4237_, lean_object* v_orig_4238_, lean_object* v_goals_4239_, lean_object* v_remaining_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4235_, v_trace_4236_, v_next_4237_, v_orig_4238_, v_goals_4239_, v_remaining_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_);
lean_dec(v_a_4244_);
lean_dec_ref(v_a_4243_);
lean_dec(v_a_4242_);
lean_dec_ref(v_a_4241_);
return v_res_4246_;
}
}
lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_4247_, lean_object* v_00_u03b2_4248_, lean_object* v_L_4249_, lean_object* v_f_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v___x_4256_; 
v___x_4256_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_4249_, v_f_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
return v___x_4256_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_L_4249_ = stack[2].m_obj;
lean_object* v_f_4250_ = stack[3].m_obj;
lean_object* v___y_4251_ = stack[4].m_obj;
lean_object* v___y_4252_ = stack[5].m_obj;
lean_object* v___y_4253_ = stack[6].m_obj;
lean_object* v___y_4254_ = stack[7].m_obj;
lean_object* v_res_4257_;
v_res_4257_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_box(0), lean_box(0), v_L_4249_, v_f_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
stack->m_obj
 = v_res_4257_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_4258_, lean_object* v_00_u03b2_4259_, lean_object* v_L_4260_, lean_object* v_f_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_4258_, v_00_u03b2_4259_, v_L_4260_, v_f_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
return v_res_4267_;
}
}
lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_4268_, lean_object* v_x_4269_, lean_object* v_x_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_4268_, v_x_4269_, v_x_4270_, v___y_4272_);
return v___x_4276_;
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4268_ = stack[0].m_num;
lean_object* v_x_4269_ = stack[1].m_obj;
lean_object* v_x_4270_ = stack[2].m_obj;
lean_object* v___y_4271_ = stack[3].m_obj;
lean_object* v___y_4272_ = stack[4].m_obj;
lean_object* v___y_4273_ = stack[5].m_obj;
lean_object* v___y_4274_ = stack[6].m_obj;
lean_object* v_res_4277_;
v_res_4277_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_4268_, v_x_4269_, v_x_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
stack->m_obj
 = v_res_4277_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_4278_, lean_object* v_x_4279_, lean_object* v_x_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
uint8_t v___x_50208__boxed_4286_; lean_object* v_res_4287_; 
v___x_50208__boxed_4286_ = lean_unbox(v___x_4278_);
v_res_4287_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_50208__boxed_4286_, v_x_4279_, v_x_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
return v_res_4287_;
}
}
lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_4288_, uint8_t v___x_4289_, lean_object* v_x_4290_, lean_object* v_x_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_4288_, v___x_4289_, v_x_4290_, v_x_4291_, v___y_4293_);
return v___x_4297_;
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4288_ = stack[0].m_num;
uint8_t v___x_4289_ = stack[1].m_num;
lean_object* v_x_4290_ = stack[2].m_obj;
lean_object* v_x_4291_ = stack[3].m_obj;
lean_object* v___y_4292_ = stack[4].m_obj;
lean_object* v___y_4293_ = stack[5].m_obj;
lean_object* v___y_4294_ = stack[6].m_obj;
lean_object* v___y_4295_ = stack[7].m_obj;
lean_object* v_res_4298_;
v_res_4298_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_4288_, v___x_4289_, v_x_4290_, v_x_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
stack->m_obj
 = v_res_4298_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_4299_, lean_object* v___x_4300_, lean_object* v_x_4301_, lean_object* v_x_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
uint8_t v___x_50251__boxed_4308_; uint8_t v___x_50252__boxed_4309_; lean_object* v_res_4310_; 
v___x_50251__boxed_4308_ = lean_unbox(v___x_4299_);
v___x_50252__boxed_4309_ = lean_unbox(v___x_4300_);
v_res_4310_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_50251__boxed_4308_, v___x_50252__boxed_4309_, v_x_4301_, v_x_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
return v_res_4310_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_4311_, lean_object* v_00_u03b2_4312_, lean_object* v_f_4313_, lean_object* v_x_4314_, lean_object* v_x_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_4313_, v_x_4314_, v_x_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
return v___x_4321_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4313_ = stack[2].m_obj;
lean_object* v_x_4314_ = stack[3].m_obj;
lean_object* v_x_4315_ = stack[4].m_obj;
lean_object* v___y_4316_ = stack[5].m_obj;
lean_object* v___y_4317_ = stack[6].m_obj;
lean_object* v___y_4318_ = stack[7].m_obj;
lean_object* v___y_4319_ = stack[8].m_obj;
lean_object* v_res_4322_;
v_res_4322_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_box(0), lean_box(0), v_f_4313_, v_x_4314_, v_x_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
stack->m_obj
 = v_res_4322_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4323_, lean_object* v_00_u03b2_4324_, lean_object* v_f_4325_, lean_object* v_x_4326_, lean_object* v_x_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_4323_, v_00_u03b2_4324_, v_f_4325_, v_x_4326_, v_x_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
return v_res_4333_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_4334_, lean_object* v_00_u03b2_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_){
_start:
{
lean_object* v___x_4338_; 
v___x_4338_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_4336_, v_a_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_4339_, lean_object* v_00_u03b2_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_){
_start:
{
lean_object* v___x_4343_; 
v___x_4343_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_4341_, v_a_4342_);
return v___x_4343_;
}
}
lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_4344_, lean_object* v_g_4345_, lean_object* v_f_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v___x_4352_; 
lean_inc(v___y_4350_);
lean_inc_ref(v___y_4349_);
lean_inc(v___y_4348_);
lean_inc_ref(v___y_4347_);
v___x_4352_ = lean_apply_6(v_next_4344_, v_g_4345_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, lean_box(0));
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4354_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
v___x_4354_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_4353_, v_f_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
return v___x_4354_;
}
else
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
lean_dec_ref(v_f_4346_);
v_a_4355_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4352_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4352_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_next_4344_ = stack[0].m_obj;
lean_object* v_g_4345_ = stack[1].m_obj;
lean_object* v_f_4346_ = stack[2].m_obj;
lean_object* v___y_4347_ = stack[3].m_obj;
lean_object* v___y_4348_ = stack[4].m_obj;
lean_object* v___y_4349_ = stack[5].m_obj;
lean_object* v___y_4350_ = stack[6].m_obj;
lean_object* v_res_4363_;
v_res_4363_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_4344_, v_g_4345_, v_f_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
stack->m_obj
 = v_res_4363_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_4364_, lean_object* v_g_4365_, lean_object* v_f_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_4364_, v_g_4365_, v_f_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
return v_res_4372_;
}
}
lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_4373_, lean_object* v_trace_4374_, lean_object* v_next_4375_, lean_object* v_goals_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v_resolve_4382_; lean_object* v___x_4383_; 
v_resolve_4382_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_4382_, 0, v_next_4375_);
lean_inc_n(v_goals_4376_, 2);
v___x_4383_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4373_, v_trace_4374_, v_resolve_4382_, v_goals_4376_, v_goals_4376_, v_goals_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_);
return v___x_4383_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Backtrack_backtrack_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_4373_ = stack[0].m_obj;
lean_object* v_trace_4374_ = stack[1].m_obj;
lean_object* v_next_4375_ = stack[2].m_obj;
lean_object* v_goals_4376_ = stack[3].m_obj;
lean_object* v_a_4377_ = stack[4].m_obj;
lean_object* v_a_4378_ = stack[5].m_obj;
lean_object* v_a_4379_ = stack[6].m_obj;
lean_object* v_a_4380_ = stack[7].m_obj;
lean_object* v_res_4384_;
v_res_4384_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_4373_, v_trace_4374_, v_next_4375_, v_goals_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_);
stack->m_obj
 = v_res_4384_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_4385_, lean_object* v_trace_4386_, lean_object* v_next_4387_, lean_object* v_goals_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_4385_, v_trace_4386_, v_next_4387_, v_goals_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
lean_dec(v_a_4392_);
lean_dec_ref(v_a_4391_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
return v_res_4394_;
}
}
lean_object* runtime_initialize_Lean_Meta_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_IndependentOf(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_IndependentOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
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

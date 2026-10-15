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
lean_dec_ref_known(v___x_39_, 1);
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
lean_object* v___x_165_; lean_object* v_traceState_166_; lean_object* v_traces_167_; lean_object* v___x_168_; lean_object* v_traceState_169_; lean_object* v_env_170_; lean_object* v_nextMacroScope_171_; lean_object* v_ngen_172_; lean_object* v_auxDeclNGen_173_; lean_object* v_cache_174_; lean_object* v_recordedDeps_175_; lean_object* v_messages_176_; lean_object* v_infoState_177_; lean_object* v_snapshotTasks_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_197_; 
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
v_recordedDeps_175_ = lean_ctor_get(v___x_168_, 6);
v_messages_176_ = lean_ctor_get(v___x_168_, 7);
v_infoState_177_ = lean_ctor_get(v___x_168_, 8);
v_snapshotTasks_178_ = lean_ctor_get(v___x_168_, 9);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_197_ == 0)
{
v___x_180_ = v___x_168_;
v_isShared_181_ = v_isSharedCheck_197_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_snapshotTasks_178_);
lean_inc(v_infoState_177_);
lean_inc(v_messages_176_);
lean_inc(v_recordedDeps_175_);
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
lean_ctor_set(v_reuseFailAlloc_193_, 6, v_recordedDeps_175_);
lean_ctor_set(v_reuseFailAlloc_193_, 7, v_messages_176_);
lean_ctor_set(v_reuseFailAlloc_193_, 8, v_infoState_177_);
lean_ctor_set(v_reuseFailAlloc_193_, 9, v_snapshotTasks_178_);
v___x_190_ = v_reuseFailAlloc_193_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_st_ref_put(v___y_163_, v___x_190_);
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
lean_dec_ref_known(v___x_218_, 1);
if (lean_obj_tag(v_val_220_) == 1)
{
uint8_t v_v_221_; 
v_v_221_ = lean_ctor_get_uint8(v_val_220_, 0);
lean_dec_ref_known(v_val_220_, 0);
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
lean_dec_ref_known(v___x_233_, 1);
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
lean_object* v___x_312_; lean_object* v_env_313_; uint8_t v___x_314_; lean_object* v_env_315_; lean_object* v___x_316_; lean_object* v_toCold_317_; lean_object* v_mctx_318_; lean_object* v_lctx_319_; lean_object* v_options_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_312_ = lean_st_ref_get(v___y_310_);
v_env_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc_ref(v_env_313_);
lean_dec(v___x_312_);
v___x_314_ = 0;
v_env_315_ = l_Lean_Environment_setRecordingDeps(v_env_313_, v___x_314_);
v___x_316_ = lean_st_ref_get(v___y_308_);
v_toCold_317_ = lean_ctor_get(v___y_309_, 0);
v_mctx_318_ = lean_ctor_get(v___x_316_, 0);
lean_inc_ref(v_mctx_318_);
lean_dec(v___x_316_);
v_lctx_319_ = lean_ctor_get(v___y_307_, 2);
v_options_320_ = lean_ctor_get(v_toCold_317_, 2);
lean_inc_ref(v_options_320_);
lean_inc_ref(v_lctx_319_);
v___x_321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_321_, 0, v_env_315_);
lean_ctor_set(v___x_321_, 1, v_mctx_318_);
lean_ctor_set(v___x_321_, 2, v_lctx_319_);
lean_ctor_set(v___x_321_, 3, v_options_320_);
v___x_322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v_msgData_306_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___boxed(lean_object* v_msgData_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msgData_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0));
v___x_333_ = l_Lean_stringToMessageData(v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object* v_x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object* v_x_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(v_x_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec_ref(v_x_342_);
return v_res_348_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0));
v___x_351_ = l_Lean_stringToMessageData(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object* v_x_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(v_x_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v_x_360_);
return v_res_366_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0));
v___x_369_ = l_Lean_stringToMessageData(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object* v_x_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object* v_x_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(v_x_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec_ref(v_x_378_);
return v_res_384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0));
v___x_387_ = l_Lean_stringToMessageData(v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object* v_x_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object* v_x_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(v_x_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec_ref(v_x_396_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(lean_object* v_opts_403_, lean_object* v_opt_404_){
_start:
{
lean_object* v_name_405_; lean_object* v_defValue_406_; lean_object* v_map_407_; lean_object* v___x_408_; 
v_name_405_ = lean_ctor_get(v_opt_404_, 0);
v_defValue_406_ = lean_ctor_get(v_opt_404_, 1);
v_map_407_ = lean_ctor_get(v_opts_403_, 0);
v___x_408_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_407_, v_name_405_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_inc(v_defValue_406_);
return v_defValue_406_;
}
else
{
lean_object* v_val_409_; 
v_val_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_val_409_);
lean_dec_ref_known(v___x_408_, 1);
if (lean_obj_tag(v_val_409_) == 3)
{
lean_object* v_v_410_; 
v_v_410_ = lean_ctor_get(v_val_409_, 0);
lean_inc(v_v_410_);
lean_dec_ref_known(v_val_409_, 1);
return v_v_410_;
}
else
{
lean_dec(v_val_409_);
lean_inc(v_defValue_406_);
return v_defValue_406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6___boxed(lean_object* v_opts_411_, lean_object* v_opt_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_411_, v_opt_412_);
lean_dec_ref(v_opt_412_);
lean_dec_ref(v_opts_411_);
return v_res_413_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object* v_e_414_){
_start:
{
if (lean_obj_tag(v_e_414_) == 0)
{
uint8_t v___x_415_; 
v___x_415_ = 2;
return v___x_415_;
}
else
{
lean_object* v_a_416_; 
v_a_416_ = lean_ctor_get(v_e_414_, 0);
if (lean_obj_tag(v_a_416_) == 0)
{
uint8_t v___x_417_; 
v___x_417_ = 1;
return v___x_417_;
}
else
{
uint8_t v___x_418_; 
v___x_418_ = 0;
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object* v_e_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_e_419_);
lean_dec_ref(v_e_419_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_a_424_ = lean_ctor_get(v_x_422_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_422_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v_x_422_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v_x_422_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set_tag(v___x_426_, 1);
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_a_432_ = lean_ctor_get(v_x_422_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_x_422_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v_x_422_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v_x_422_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 0);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg___boxed(lean_object* v_x_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(size_t v_sz_443_, size_t v_i_444_, lean_object* v_bs_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = lean_usize_dec_lt(v_i_444_, v_sz_443_);
if (v___x_446_ == 0)
{
return v_bs_445_;
}
else
{
lean_object* v_v_447_; lean_object* v_msg_448_; lean_object* v___x_449_; lean_object* v_bs_x27_450_; size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; 
v_v_447_ = lean_array_uget_borrowed(v_bs_445_, v_i_444_);
v_msg_448_ = lean_ctor_get(v_v_447_, 1);
lean_inc_ref(v_msg_448_);
v___x_449_ = lean_unsigned_to_nat(0u);
v_bs_x27_450_ = lean_array_uset(v_bs_445_, v_i_444_, v___x_449_);
v___x_451_ = ((size_t)1ULL);
v___x_452_ = lean_usize_add(v_i_444_, v___x_451_);
v___x_453_ = lean_array_uset(v_bs_x27_450_, v_i_444_, v_msg_448_);
v_i_444_ = v___x_452_;
v_bs_445_ = v___x_453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6___boxed(lean_object* v_sz_455_, lean_object* v_i_456_, lean_object* v_bs_457_){
_start:
{
size_t v_sz_boxed_458_; size_t v_i_boxed_459_; lean_object* v_res_460_; 
v_sz_boxed_458_ = lean_unbox_usize(v_sz_455_);
lean_dec(v_sz_455_);
v_i_boxed_459_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_boxed_458_, v_i_boxed_459_, v_bs_457_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object* v_oldTraces_461_, lean_object* v_data_462_, lean_object* v_ref_463_, lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_toCold_470_; lean_object* v_currRecDepth_471_; lean_object* v_ref_472_; uint16_t v_optionFlags_473_; uint8_t v_suppressElabErrors_474_; uint8_t v_isRecordingDeps_475_; lean_object* v_ref_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_traceState_479_; lean_object* v_traces_480_; lean_object* v___x_481_; size_t v_sz_482_; size_t v___x_483_; lean_object* v___x_484_; lean_object* v_msg_485_; lean_object* v___x_486_; lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_525_; 
v_toCold_470_ = lean_ctor_get(v___y_467_, 0);
v_currRecDepth_471_ = lean_ctor_get(v___y_467_, 1);
v_ref_472_ = lean_ctor_get(v___y_467_, 2);
v_optionFlags_473_ = lean_ctor_get_uint16(v___y_467_, sizeof(void*)*3);
v_suppressElabErrors_474_ = lean_ctor_get_uint8(v___y_467_, sizeof(void*)*3 + 2);
v_isRecordingDeps_475_ = lean_ctor_get_uint8(v___y_467_, sizeof(void*)*3 + 3);
v_ref_476_ = l_Lean_replaceRef(v_ref_463_, v_ref_472_);
lean_inc(v_currRecDepth_471_);
lean_inc_ref(v_toCold_470_);
v___x_477_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_477_, 0, v_toCold_470_);
lean_ctor_set(v___x_477_, 1, v_currRecDepth_471_);
lean_ctor_set(v___x_477_, 2, v_ref_476_);
lean_ctor_set_uint16(v___x_477_, sizeof(void*)*3, v_optionFlags_473_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*3 + 2, v_suppressElabErrors_474_);
lean_ctor_set_uint8(v___x_477_, sizeof(void*)*3 + 3, v_isRecordingDeps_475_);
v___x_478_ = lean_st_ref_get(v___y_468_);
v_traceState_479_ = lean_ctor_get(v___x_478_, 4);
lean_inc_ref(v_traceState_479_);
lean_dec(v___x_478_);
v_traces_480_ = lean_ctor_get(v_traceState_479_, 0);
lean_inc_ref(v_traces_480_);
lean_dec_ref(v_traceState_479_);
v___x_481_ = l_Lean_PersistentArray_toArray___redArg(v_traces_480_);
lean_dec_ref(v_traces_480_);
v_sz_482_ = lean_array_size(v___x_481_);
v___x_483_ = ((size_t)0ULL);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_482_, v___x_483_, v___x_481_);
v_msg_485_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_485_, 0, v_data_462_);
lean_ctor_set(v_msg_485_, 1, v_msg_464_);
lean_ctor_set(v_msg_485_, 2, v___x_484_);
v___x_486_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_485_, v___y_465_, v___y_466_, v___x_477_, v___y_468_);
lean_dec_ref_known(v___x_477_, 3);
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_525_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_525_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_525_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v_traceState_492_; lean_object* v_env_493_; lean_object* v_nextMacroScope_494_; lean_object* v_ngen_495_; lean_object* v_auxDeclNGen_496_; lean_object* v_cache_497_; lean_object* v_recordedDeps_498_; lean_object* v_messages_499_; lean_object* v_infoState_500_; lean_object* v_snapshotTasks_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_524_; 
v___x_491_ = lean_st_ref_take(v___y_468_);
v_traceState_492_ = lean_ctor_get(v___x_491_, 4);
v_env_493_ = lean_ctor_get(v___x_491_, 0);
v_nextMacroScope_494_ = lean_ctor_get(v___x_491_, 1);
v_ngen_495_ = lean_ctor_get(v___x_491_, 2);
v_auxDeclNGen_496_ = lean_ctor_get(v___x_491_, 3);
v_cache_497_ = lean_ctor_get(v___x_491_, 5);
v_recordedDeps_498_ = lean_ctor_get(v___x_491_, 6);
v_messages_499_ = lean_ctor_get(v___x_491_, 7);
v_infoState_500_ = lean_ctor_get(v___x_491_, 8);
v_snapshotTasks_501_ = lean_ctor_get(v___x_491_, 9);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_524_ == 0)
{
v___x_503_ = v___x_491_;
v_isShared_504_ = v_isSharedCheck_524_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_snapshotTasks_501_);
lean_inc(v_infoState_500_);
lean_inc(v_messages_499_);
lean_inc(v_recordedDeps_498_);
lean_inc(v_cache_497_);
lean_inc(v_traceState_492_);
lean_inc(v_auxDeclNGen_496_);
lean_inc(v_ngen_495_);
lean_inc(v_nextMacroScope_494_);
lean_inc(v_env_493_);
lean_dec(v___x_491_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_524_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
uint64_t v_tid_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_522_; 
v_tid_505_ = lean_ctor_get_uint64(v_traceState_492_, sizeof(void*)*1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_traceState_492_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v_traceState_492_, 0);
lean_dec(v_unused_523_);
v___x_507_ = v_traceState_492_;
v_isShared_508_ = v_isSharedCheck_522_;
goto v_resetjp_506_;
}
else
{
lean_dec(v_traceState_492_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_522_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_509_ = lean_box(0);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v_ref_463_);
lean_ctor_set(v___x_510_, 1, v_a_487_);
v___x_511_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_461_, v___x_510_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_511_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_511_);
lean_ctor_set_uint64(v_reuseFailAlloc_521_, sizeof(void*)*1, v_tid_505_);
v___x_513_ = v_reuseFailAlloc_521_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 4, v___x_513_);
v___x_515_ = v___x_503_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_env_493_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_nextMacroScope_494_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v_ngen_495_);
lean_ctor_set(v_reuseFailAlloc_520_, 3, v_auxDeclNGen_496_);
lean_ctor_set(v_reuseFailAlloc_520_, 4, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_520_, 5, v_cache_497_);
lean_ctor_set(v_reuseFailAlloc_520_, 6, v_recordedDeps_498_);
lean_ctor_set(v_reuseFailAlloc_520_, 7, v_messages_499_);
lean_ctor_set(v_reuseFailAlloc_520_, 8, v_infoState_500_);
lean_ctor_set(v_reuseFailAlloc_520_, 9, v_snapshotTasks_501_);
v___x_515_ = v_reuseFailAlloc_520_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_st_ref_put(v___y_468_, v___x_515_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_509_);
v___x_518_ = v___x_489_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_509_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object* v_oldTraces_526_, lean_object* v_data_527_, lean_object* v_ref_528_, lean_object* v_msg_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_526_, v_data_527_, v_ref_528_, v_msg_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_535_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0(void){
_start:
{
lean_object* v___x_536_; double v___x_537_; 
v___x_536_ = lean_unsigned_to_nat(0u);
v___x_537_ = lean_float_of_nat(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3(void){
_start:
{
lean_object* v___x_541_; double v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(1000u);
v___x_542_ = lean_float_of_nat(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_cls_543_, uint8_t v_collapsed_544_, lean_object* v_tag_545_, lean_object* v_opts_546_, uint8_t v_clsEnabled_547_, lean_object* v_oldTraces_548_, lean_object* v_msg_549_, lean_object* v_resStartStop_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v_data_561_; lean_object* v_fst_572_; lean_object* v_snd_573_; lean_object* v___x_574_; uint8_t v___x_575_; lean_object* v___y_577_; lean_object* v_a_578_; uint8_t v___y_593_; double v___y_625_; 
v_fst_556_ = lean_ctor_get(v_resStartStop_550_, 0);
lean_inc(v_fst_556_);
v_snd_557_ = lean_ctor_get(v_resStartStop_550_, 1);
lean_inc(v_snd_557_);
lean_dec_ref(v_resStartStop_550_);
v_fst_572_ = lean_ctor_get(v_snd_557_, 0);
lean_inc(v_fst_572_);
v_snd_573_ = lean_ctor_get(v_snd_557_, 1);
lean_inc(v_snd_573_);
lean_dec(v_snd_557_);
v___x_574_ = l_Lean_trace_profiler;
v___x_575_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_546_, v___x_574_);
if (v___x_575_ == 0)
{
v___y_593_ = v___x_575_;
goto v___jp_592_;
}
else
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = l_Lean_trace_profiler_useHeartbeats;
v___x_631_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_546_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; double v___x_634_; double v___x_635_; double v___x_636_; 
v___x_632_ = l_Lean_trace_profiler_threshold;
v___x_633_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_546_, v___x_632_);
v___x_634_ = lean_float_of_nat(v___x_633_);
v___x_635_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_636_ = lean_float_div(v___x_634_, v___x_635_);
v___y_625_ = v___x_636_;
goto v___jp_624_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; double v___x_639_; 
v___x_637_ = l_Lean_trace_profiler_threshold;
v___x_638_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_546_, v___x_637_);
v___x_639_ = lean_float_of_nat(v___x_638_);
v___y_625_ = v___x_639_;
goto v___jp_624_;
}
}
v___jp_558_:
{
lean_object* v___x_562_; 
lean_inc(v___y_560_);
v___x_562_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_548_, v_data_561_, v___y_560_, v___y_559_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; 
lean_dec_ref_known(v___x_562_, 1);
v___x_563_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_556_);
return v___x_563_;
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec(v_fst_556_);
v_a_564_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_562_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_562_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
v___jp_576_:
{
uint8_t v_result_579_; lean_object* v___x_580_; lean_object* v___x_581_; double v___x_582_; lean_object* v_data_583_; 
v_result_579_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_fst_556_);
v___x_580_ = lean_box(v_result_579_);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
v___x_582_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_545_);
lean_inc_ref(v___x_581_);
lean_inc(v_cls_543_);
v_data_583_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_583_, 0, v_cls_543_);
lean_ctor_set(v_data_583_, 1, v___x_581_);
lean_ctor_set(v_data_583_, 2, v_tag_545_);
lean_ctor_set_float(v_data_583_, sizeof(void*)*3, v___x_582_);
lean_ctor_set_float(v_data_583_, sizeof(void*)*3 + 8, v___x_582_);
lean_ctor_set_uint8(v_data_583_, sizeof(void*)*3 + 16, v_collapsed_544_);
if (v___x_575_ == 0)
{
lean_dec_ref_known(v___x_581_, 1);
lean_dec(v_snd_573_);
lean_dec(v_fst_572_);
lean_dec_ref(v_tag_545_);
lean_dec(v_cls_543_);
v___y_559_ = v_a_578_;
v___y_560_ = v___y_577_;
v_data_561_ = v_data_583_;
goto v___jp_558_;
}
else
{
lean_object* v_data_584_; double v___x_585_; double v___x_586_; 
lean_dec_ref_known(v_data_583_, 3);
v_data_584_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_584_, 0, v_cls_543_);
lean_ctor_set(v_data_584_, 1, v___x_581_);
lean_ctor_set(v_data_584_, 2, v_tag_545_);
v___x_585_ = lean_unbox_float(v_fst_572_);
lean_dec(v_fst_572_);
lean_ctor_set_float(v_data_584_, sizeof(void*)*3, v___x_585_);
v___x_586_ = lean_unbox_float(v_snd_573_);
lean_dec(v_snd_573_);
lean_ctor_set_float(v_data_584_, sizeof(void*)*3 + 8, v___x_586_);
lean_ctor_set_uint8(v_data_584_, sizeof(void*)*3 + 16, v_collapsed_544_);
v___y_559_ = v_a_578_;
v___y_560_ = v___y_577_;
v_data_561_ = v_data_584_;
goto v___jp_558_;
}
}
v___jp_587_:
{
lean_object* v_ref_588_; lean_object* v___x_589_; 
v_ref_588_ = lean_ctor_get(v___y_553_, 2);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc(v_fst_556_);
v___x_589_ = lean_apply_6(v_msg_549_, v_fst_556_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, lean_box(0));
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___y_577_ = v_ref_588_;
v_a_578_ = v_a_590_;
goto v___jp_576_;
}
else
{
lean_object* v___x_591_; 
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_577_ = v_ref_588_;
v_a_578_ = v___x_591_;
goto v___jp_576_;
}
}
v___jp_592_:
{
if (v_clsEnabled_547_ == 0)
{
if (v___y_593_ == 0)
{
lean_object* v___x_594_; lean_object* v_traceState_595_; lean_object* v_env_596_; lean_object* v_nextMacroScope_597_; lean_object* v_ngen_598_; lean_object* v_auxDeclNGen_599_; lean_object* v_cache_600_; lean_object* v_recordedDeps_601_; lean_object* v_messages_602_; lean_object* v_infoState_603_; lean_object* v_snapshotTasks_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_snd_573_);
lean_dec(v_fst_572_);
lean_dec_ref(v_msg_549_);
lean_dec_ref(v_tag_545_);
lean_dec(v_cls_543_);
v___x_594_ = lean_st_ref_take(v___y_554_);
v_traceState_595_ = lean_ctor_get(v___x_594_, 4);
v_env_596_ = lean_ctor_get(v___x_594_, 0);
v_nextMacroScope_597_ = lean_ctor_get(v___x_594_, 1);
v_ngen_598_ = lean_ctor_get(v___x_594_, 2);
v_auxDeclNGen_599_ = lean_ctor_get(v___x_594_, 3);
v_cache_600_ = lean_ctor_get(v___x_594_, 5);
v_recordedDeps_601_ = lean_ctor_get(v___x_594_, 6);
v_messages_602_ = lean_ctor_get(v___x_594_, 7);
v_infoState_603_ = lean_ctor_get(v___x_594_, 8);
v_snapshotTasks_604_ = lean_ctor_get(v___x_594_, 9);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_623_ == 0)
{
v___x_606_ = v___x_594_;
v_isShared_607_ = v_isSharedCheck_623_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_snapshotTasks_604_);
lean_inc(v_infoState_603_);
lean_inc(v_messages_602_);
lean_inc(v_recordedDeps_601_);
lean_inc(v_cache_600_);
lean_inc(v_traceState_595_);
lean_inc(v_auxDeclNGen_599_);
lean_inc(v_ngen_598_);
lean_inc(v_nextMacroScope_597_);
lean_inc(v_env_596_);
lean_dec(v___x_594_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_623_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
uint64_t v_tid_608_; lean_object* v_traces_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_622_; 
v_tid_608_ = lean_ctor_get_uint64(v_traceState_595_, sizeof(void*)*1);
v_traces_609_ = lean_ctor_get(v_traceState_595_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v_traceState_595_);
if (v_isSharedCheck_622_ == 0)
{
v___x_611_ = v_traceState_595_;
v_isShared_612_ = v_isSharedCheck_622_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_traces_609_);
lean_dec(v_traceState_595_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_622_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_548_, v_traces_609_);
lean_dec_ref(v_traces_609_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_613_);
lean_ctor_set_uint64(v_reuseFailAlloc_621_, sizeof(void*)*1, v_tid_608_);
v___x_615_ = v_reuseFailAlloc_621_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_617_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 4, v___x_615_);
v___x_617_ = v___x_606_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_env_596_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_nextMacroScope_597_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_ngen_598_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_auxDeclNGen_599_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_620_, 5, v_cache_600_);
lean_ctor_set(v_reuseFailAlloc_620_, 6, v_recordedDeps_601_);
lean_ctor_set(v_reuseFailAlloc_620_, 7, v_messages_602_);
lean_ctor_set(v_reuseFailAlloc_620_, 8, v_infoState_603_);
lean_ctor_set(v_reuseFailAlloc_620_, 9, v_snapshotTasks_604_);
v___x_617_ = v_reuseFailAlloc_620_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_st_ref_put(v___y_554_, v___x_617_);
v___x_619_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_556_);
return v___x_619_;
}
}
}
}
}
else
{
goto v___jp_587_;
}
}
else
{
goto v___jp_587_;
}
}
v___jp_624_:
{
double v___x_626_; double v___x_627_; double v___x_628_; uint8_t v___x_629_; 
v___x_626_ = lean_unbox_float(v_snd_573_);
v___x_627_ = lean_unbox_float(v_fst_572_);
v___x_628_ = lean_float_sub(v___x_626_, v___x_627_);
v___x_629_ = lean_float_decLt(v___y_625_, v___x_628_);
v___y_593_ = v___x_629_;
goto v___jp_592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_cls_640_, lean_object* v_collapsed_641_, lean_object* v_tag_642_, lean_object* v_opts_643_, lean_object* v_clsEnabled_644_, lean_object* v_oldTraces_645_, lean_object* v_msg_646_, lean_object* v_resStartStop_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
uint8_t v_collapsed_boxed_653_; uint8_t v_clsEnabled_boxed_654_; lean_object* v_res_655_; 
v_collapsed_boxed_653_ = lean_unbox(v_collapsed_641_);
v_clsEnabled_boxed_654_ = lean_unbox(v_clsEnabled_644_);
v_res_655_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_cls_640_, v_collapsed_boxed_653_, v_tag_642_, v_opts_643_, v_clsEnabled_boxed_654_, v_oldTraces_645_, v_msg_646_, v_resStartStop_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v_opts_643_);
return v_res_655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* v_head_659_, lean_object* v_x_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_677_; 
v___x_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_666_, 0, v_head_659_);
v___x_667_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v___x_666_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_677_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v_a_668_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_673_);
v___x_675_ = v___x_670_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* v_head_678_, lean_object* v_x_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_head_678_, v_x_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec_ref(v_x_679_);
return v_res_685_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object* v_keys_686_, lean_object* v_i_687_, lean_object* v_k_688_){
_start:
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_array_get_size(v_keys_686_);
v___x_690_ = lean_nat_dec_lt(v_i_687_, v___x_689_);
if (v___x_690_ == 0)
{
lean_dec(v_i_687_);
return v___x_690_;
}
else
{
lean_object* v_k_x27_691_; uint8_t v___x_692_; 
v_k_x27_691_ = lean_array_fget_borrowed(v_keys_686_, v_i_687_);
v___x_692_ = l_Lean_instBEqMVarId_beq(v_k_688_, v_k_x27_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(1u);
v___x_694_ = lean_nat_add(v_i_687_, v___x_693_);
lean_dec(v_i_687_);
v_i_687_ = v___x_694_;
goto _start;
}
else
{
lean_dec(v_i_687_);
return v___x_690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object* v_keys_696_, lean_object* v_i_697_, lean_object* v_k_698_){
_start:
{
uint8_t v_res_699_; lean_object* v_r_700_; 
v_res_699_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_696_, v_i_697_, v_k_698_);
lean_dec(v_k_698_);
lean_dec_ref(v_keys_696_);
v_r_700_ = lean_box(v_res_699_);
return v_r_700_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_701_, size_t v_x_702_, lean_object* v_x_703_){
_start:
{
if (lean_obj_tag(v_x_701_) == 0)
{
lean_object* v_es_704_; lean_object* v___x_705_; size_t v___x_706_; size_t v___x_707_; lean_object* v_j_708_; lean_object* v___x_709_; 
v_es_704_ = lean_ctor_get(v_x_701_, 0);
v___x_705_ = lean_box(2);
v___x_706_ = ((size_t)31ULL);
v___x_707_ = lean_usize_land(v_x_702_, v___x_706_);
v_j_708_ = lean_usize_to_nat(v___x_707_);
v___x_709_ = lean_array_get_borrowed(v___x_705_, v_es_704_, v_j_708_);
lean_dec(v_j_708_);
switch(lean_obj_tag(v___x_709_))
{
case 0:
{
lean_object* v_key_710_; uint8_t v___x_711_; 
v_key_710_ = lean_ctor_get(v___x_709_, 0);
v___x_711_ = l_Lean_instBEqMVarId_beq(v_x_703_, v_key_710_);
return v___x_711_;
}
case 1:
{
lean_object* v_node_712_; size_t v___x_713_; size_t v___x_714_; 
v_node_712_ = lean_ctor_get(v___x_709_, 0);
v___x_713_ = ((size_t)5ULL);
v___x_714_ = lean_usize_shift_right(v_x_702_, v___x_713_);
v_x_701_ = v_node_712_;
v_x_702_ = v___x_714_;
goto _start;
}
default: 
{
uint8_t v___x_716_; 
v___x_716_ = 0;
return v___x_716_;
}
}
}
else
{
lean_object* v_ks_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_ks_717_ = lean_ctor_get(v_x_701_, 0);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_ks_717_, v___x_718_, v_x_703_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_x_722_){
_start:
{
size_t v_x_74414__boxed_723_; uint8_t v_res_724_; lean_object* v_r_725_; 
v_x_74414__boxed_723_ = lean_unbox_usize(v_x_721_);
lean_dec(v_x_721_);
v_res_724_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_720_, v_x_74414__boxed_723_, v_x_722_);
lean_dec(v_x_722_);
lean_dec_ref(v_x_720_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
uint64_t v___x_728_; size_t v___x_729_; uint8_t v___x_730_; 
v___x_728_ = l_Lean_instHashableMVarId_hash(v_x_727_);
v___x_729_ = lean_uint64_to_usize(v___x_728_);
v___x_730_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_726_, v___x_729_, v_x_727_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
uint8_t v_res_733_; lean_object* v_r_734_; 
v_res_733_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_731_, v_x_732_);
lean_dec(v_x_732_);
lean_dec_ref(v_x_731_);
v_r_734_ = lean_box(v_res_733_);
return v_r_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object* v_mvarId_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; lean_object* v_mctx_739_; lean_object* v_eAssignment_740_; uint8_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_738_ = lean_st_ref_get(v___y_736_);
v_mctx_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc_ref(v_mctx_739_);
lean_dec(v___x_738_);
v_eAssignment_740_ = lean_ctor_get(v_mctx_739_, 8);
lean_inc_ref(v_eAssignment_740_);
lean_dec_ref(v_mctx_739_);
v___x_741_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_eAssignment_740_, v_mvarId_735_);
lean_dec_ref(v_eAssignment_740_);
v___x_742_ = lean_box(v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object* v_mvarId_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec(v_mvarId_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_ref_754_; lean_object* v___x_755_; lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_764_; 
v_ref_754_ = lean_ctor_get(v___y_751_, 2);
v___x_755_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_764_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
lean_inc(v_ref_754_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v_ref_754_);
lean_ctor_set(v___x_760_, 1, v_a_756_);
if (v_isShared_759_ == 0)
{
lean_ctor_set_tag(v___x_758_, 1);
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_774_ = l_Lean_stringToMessageData(v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_a_775_, lean_object* v_x_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_783_ = l_Lean_Exception_toMessageData(v_a_775_);
v___x_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_a_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_a_786_, v_x_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec_ref(v_x_787_);
return v_res_793_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_e_794_){
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
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_e_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_e_797_);
lean_dec_ref(v_e_797_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_800_, uint8_t v_collapsed_801_, lean_object* v_tag_802_, lean_object* v_opts_803_, uint8_t v_clsEnabled_804_, lean_object* v_oldTraces_805_, lean_object* v_msg_806_, lean_object* v_resStartStop_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_fst_813_; lean_object* v_snd_814_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v_data_818_; lean_object* v_fst_829_; lean_object* v_snd_830_; lean_object* v___x_831_; uint8_t v___x_832_; lean_object* v___y_834_; lean_object* v_a_835_; uint8_t v___y_850_; double v___y_882_; 
v_fst_813_ = lean_ctor_get(v_resStartStop_807_, 0);
lean_inc(v_fst_813_);
v_snd_814_ = lean_ctor_get(v_resStartStop_807_, 1);
lean_inc(v_snd_814_);
lean_dec_ref(v_resStartStop_807_);
v_fst_829_ = lean_ctor_get(v_snd_814_, 0);
lean_inc(v_fst_829_);
v_snd_830_ = lean_ctor_get(v_snd_814_, 1);
lean_inc(v_snd_830_);
lean_dec(v_snd_814_);
v___x_831_ = l_Lean_trace_profiler;
v___x_832_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_803_, v___x_831_);
if (v___x_832_ == 0)
{
v___y_850_ = v___x_832_;
goto v___jp_849_;
}
else
{
lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_887_ = l_Lean_trace_profiler_useHeartbeats;
v___x_888_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_803_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; double v___x_891_; double v___x_892_; double v___x_893_; 
v___x_889_ = l_Lean_trace_profiler_threshold;
v___x_890_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_803_, v___x_889_);
v___x_891_ = lean_float_of_nat(v___x_890_);
v___x_892_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_893_ = lean_float_div(v___x_891_, v___x_892_);
v___y_882_ = v___x_893_;
goto v___jp_881_;
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; double v___x_896_; 
v___x_894_ = l_Lean_trace_profiler_threshold;
v___x_895_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_803_, v___x_894_);
v___x_896_ = lean_float_of_nat(v___x_895_);
v___y_882_ = v___x_896_;
goto v___jp_881_;
}
}
v___jp_815_:
{
lean_object* v___x_819_; 
lean_inc(v___y_816_);
v___x_819_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_805_, v_data_818_, v___y_816_, v___y_817_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v___x_820_; 
lean_dec_ref_known(v___x_819_, 1);
v___x_820_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_813_);
return v___x_820_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_fst_813_);
v_a_821_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_819_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
v___jp_833_:
{
uint8_t v_result_836_; lean_object* v___x_837_; lean_object* v___x_838_; double v___x_839_; lean_object* v_data_840_; 
v_result_836_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_fst_813_);
v___x_837_ = lean_box(v_result_836_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
v___x_839_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_802_);
lean_inc_ref(v___x_838_);
lean_inc(v_cls_800_);
v_data_840_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_840_, 0, v_cls_800_);
lean_ctor_set(v_data_840_, 1, v___x_838_);
lean_ctor_set(v_data_840_, 2, v_tag_802_);
lean_ctor_set_float(v_data_840_, sizeof(void*)*3, v___x_839_);
lean_ctor_set_float(v_data_840_, sizeof(void*)*3 + 8, v___x_839_);
lean_ctor_set_uint8(v_data_840_, sizeof(void*)*3 + 16, v_collapsed_801_);
if (v___x_832_ == 0)
{
lean_dec_ref_known(v___x_838_, 1);
lean_dec(v_snd_830_);
lean_dec(v_fst_829_);
lean_dec_ref(v_tag_802_);
lean_dec(v_cls_800_);
v___y_816_ = v___y_834_;
v___y_817_ = v_a_835_;
v_data_818_ = v_data_840_;
goto v___jp_815_;
}
else
{
lean_object* v_data_841_; double v___x_842_; double v___x_843_; 
lean_dec_ref_known(v_data_840_, 3);
v_data_841_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_841_, 0, v_cls_800_);
lean_ctor_set(v_data_841_, 1, v___x_838_);
lean_ctor_set(v_data_841_, 2, v_tag_802_);
v___x_842_ = lean_unbox_float(v_fst_829_);
lean_dec(v_fst_829_);
lean_ctor_set_float(v_data_841_, sizeof(void*)*3, v___x_842_);
v___x_843_ = lean_unbox_float(v_snd_830_);
lean_dec(v_snd_830_);
lean_ctor_set_float(v_data_841_, sizeof(void*)*3 + 8, v___x_843_);
lean_ctor_set_uint8(v_data_841_, sizeof(void*)*3 + 16, v_collapsed_801_);
v___y_816_ = v___y_834_;
v___y_817_ = v_a_835_;
v_data_818_ = v_data_841_;
goto v___jp_815_;
}
}
v___jp_844_:
{
lean_object* v_ref_845_; lean_object* v___x_846_; 
v_ref_845_ = lean_ctor_get(v___y_810_, 2);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
lean_inc(v_fst_813_);
v___x_846_ = lean_apply_6(v_msg_806_, v_fst_813_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, lean_box(0));
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___y_834_ = v_ref_845_;
v_a_835_ = v_a_847_;
goto v___jp_833_;
}
else
{
lean_object* v___x_848_; 
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_834_ = v_ref_845_;
v_a_835_ = v___x_848_;
goto v___jp_833_;
}
}
v___jp_849_:
{
if (v_clsEnabled_804_ == 0)
{
if (v___y_850_ == 0)
{
lean_object* v___x_851_; lean_object* v_traceState_852_; lean_object* v_env_853_; lean_object* v_nextMacroScope_854_; lean_object* v_ngen_855_; lean_object* v_auxDeclNGen_856_; lean_object* v_cache_857_; lean_object* v_recordedDeps_858_; lean_object* v_messages_859_; lean_object* v_infoState_860_; lean_object* v_snapshotTasks_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_snd_830_);
lean_dec(v_fst_829_);
lean_dec_ref(v_msg_806_);
lean_dec_ref(v_tag_802_);
lean_dec(v_cls_800_);
v___x_851_ = lean_st_ref_take(v___y_811_);
v_traceState_852_ = lean_ctor_get(v___x_851_, 4);
v_env_853_ = lean_ctor_get(v___x_851_, 0);
v_nextMacroScope_854_ = lean_ctor_get(v___x_851_, 1);
v_ngen_855_ = lean_ctor_get(v___x_851_, 2);
v_auxDeclNGen_856_ = lean_ctor_get(v___x_851_, 3);
v_cache_857_ = lean_ctor_get(v___x_851_, 5);
v_recordedDeps_858_ = lean_ctor_get(v___x_851_, 6);
v_messages_859_ = lean_ctor_get(v___x_851_, 7);
v_infoState_860_ = lean_ctor_get(v___x_851_, 8);
v_snapshotTasks_861_ = lean_ctor_get(v___x_851_, 9);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_880_ == 0)
{
v___x_863_ = v___x_851_;
v_isShared_864_ = v_isSharedCheck_880_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_snapshotTasks_861_);
lean_inc(v_infoState_860_);
lean_inc(v_messages_859_);
lean_inc(v_recordedDeps_858_);
lean_inc(v_cache_857_);
lean_inc(v_traceState_852_);
lean_inc(v_auxDeclNGen_856_);
lean_inc(v_ngen_855_);
lean_inc(v_nextMacroScope_854_);
lean_inc(v_env_853_);
lean_dec(v___x_851_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_880_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
uint64_t v_tid_865_; lean_object* v_traces_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_879_; 
v_tid_865_ = lean_ctor_get_uint64(v_traceState_852_, sizeof(void*)*1);
v_traces_866_ = lean_ctor_get(v_traceState_852_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v_traceState_852_);
if (v_isSharedCheck_879_ == 0)
{
v___x_868_ = v_traceState_852_;
v_isShared_869_ = v_isSharedCheck_879_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_traces_866_);
lean_dec(v_traceState_852_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_879_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_805_, v_traces_866_);
lean_dec_ref(v_traces_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_870_);
lean_ctor_set_uint64(v_reuseFailAlloc_878_, sizeof(void*)*1, v_tid_865_);
v___x_872_ = v_reuseFailAlloc_878_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 4, v___x_872_);
v___x_874_ = v___x_863_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_env_853_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_nextMacroScope_854_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_ngen_855_);
lean_ctor_set(v_reuseFailAlloc_877_, 3, v_auxDeclNGen_856_);
lean_ctor_set(v_reuseFailAlloc_877_, 4, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_877_, 5, v_cache_857_);
lean_ctor_set(v_reuseFailAlloc_877_, 6, v_recordedDeps_858_);
lean_ctor_set(v_reuseFailAlloc_877_, 7, v_messages_859_);
lean_ctor_set(v_reuseFailAlloc_877_, 8, v_infoState_860_);
lean_ctor_set(v_reuseFailAlloc_877_, 9, v_snapshotTasks_861_);
v___x_874_ = v_reuseFailAlloc_877_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_st_ref_put(v___y_811_, v___x_874_);
v___x_876_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_813_);
return v___x_876_;
}
}
}
}
}
else
{
goto v___jp_844_;
}
}
else
{
goto v___jp_844_;
}
}
v___jp_881_:
{
double v___x_883_; double v___x_884_; double v___x_885_; uint8_t v___x_886_; 
v___x_883_ = lean_unbox_float(v_snd_830_);
v___x_884_ = lean_unbox_float(v_fst_829_);
v___x_885_ = lean_float_sub(v___x_883_, v___x_884_);
v___x_886_ = lean_float_decLt(v___y_882_, v___x_885_);
v___y_850_ = v___x_886_;
goto v___jp_849_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_897_, lean_object* v_collapsed_898_, lean_object* v_tag_899_, lean_object* v_opts_900_, lean_object* v_clsEnabled_901_, lean_object* v_oldTraces_902_, lean_object* v_msg_903_, lean_object* v_resStartStop_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
uint8_t v_collapsed_boxed_910_; uint8_t v_clsEnabled_boxed_911_; lean_object* v_res_912_; 
v_collapsed_boxed_910_ = lean_unbox(v_collapsed_898_);
v_clsEnabled_boxed_911_ = lean_unbox(v_clsEnabled_901_);
v_res_912_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_897_, v_collapsed_boxed_910_, v_tag_899_, v_opts_900_, v_clsEnabled_boxed_911_, v_oldTraces_902_, v_msg_903_, v_resStartStop_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec_ref(v_opts_900_);
return v_res_912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__0));
v___x_915_ = l_Lean_stringToMessageData(v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(lean_object* v_head_916_, lean_object* v_x_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_923_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1);
v___x_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_924_, 0, v_head_916_);
v___x_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___boxed(lean_object* v_head_927_, lean_object* v_x_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(v_head_927_, v_x_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec_ref(v_x_928_);
return v_res_934_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_935_; double v___x_936_; 
v___x_935_ = lean_unsigned_to_nat(1000000000u);
v___x_936_ = lean_float_of_nat(v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* v_tail_948_, lean_object* v_cfg_949_, lean_object* v_trace_950_, lean_object* v_next_951_, lean_object* v_goals_952_, lean_object* v_n_953_, lean_object* v_acc_954_, lean_object* v_r_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_948_, v_cfg_949_, v_trace_950_, v_next_951_, v_goals_952_, v_n_953_, v_acc_954_, v_r_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_962_, lean_object* v_trace_963_, lean_object* v_next_964_, lean_object* v_goals_965_, lean_object* v_n_966_, lean_object* v_curr_967_, lean_object* v_acc_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___y_975_; uint8_t v___y_976_; lean_object* v___y_977_; uint8_t v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v_a_982_; lean_object* v___y_992_; lean_object* v___y_993_; uint8_t v___y_994_; lean_object* v___y_995_; uint8_t v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v_a_999_; lean_object* v___y_1012_; uint8_t v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; uint8_t v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; uint8_t v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v_a_1067_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; uint8_t v___y_1080_; uint8_t v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v_a_1084_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; uint8_t v___y_1090_; uint8_t v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v_a_1094_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; uint8_t v___y_1100_; uint8_t v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1108_; lean_object* v___y_1109_; uint8_t v___y_1110_; uint8_t v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v_a_1115_; lean_object* v___y_1128_; lean_object* v___y_1129_; uint8_t v___y_1130_; uint8_t v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v_a_1135_; lean_object* v___y_1138_; lean_object* v___y_1139_; uint8_t v___y_1140_; uint8_t v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v_a_1145_; lean_object* v___y_1148_; lean_object* v___y_1149_; uint8_t v___y_1150_; uint8_t v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v_zero_1158_; uint8_t v_isZero_1159_; 
v_zero_1158_ = lean_unsigned_to_nat(0u);
v_isZero_1159_ = lean_nat_dec_eq(v_n_966_, v_zero_1158_);
if (v_isZero_1159_ == 1)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_acc_968_);
lean_dec(v_curr_967_);
lean_dec(v_n_966_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
v___x_1160_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1161_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1160_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1161_;
}
else
{
lean_object* v_proc_1162_; lean_object* v_suspend_1163_; lean_object* v_discharge_1164_; lean_object* v___f_1165_; lean_object* v___y_1167_; lean_object* v___y_1168_; uint8_t v___y_1169_; uint8_t v___y_1170_; lean_object* v___y_1171_; lean_object* v___f_1207_; lean_object* v___y_1209_; lean_object* v___y_1210_; uint8_t v___y_1211_; uint8_t v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v_a_1215_; lean_object* v___y_1225_; lean_object* v___y_1226_; uint8_t v___y_1227_; uint8_t v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v_a_1231_; lean_object* v___y_1244_; lean_object* v___y_1245_; uint8_t v___y_1246_; uint8_t v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___f_1291_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; uint8_t v___y_1297_; uint8_t v___y_1298_; lean_object* v_a_1299_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; uint8_t v___y_1315_; uint8_t v___y_1316_; lean_object* v___y_1317_; lean_object* v_a_1318_; lean_object* v___f_1327_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; uint8_t v___y_1333_; uint8_t v___y_1334_; uint8_t v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v_a_1339_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; uint8_t v___y_1355_; uint8_t v___y_1356_; uint8_t v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v_a_1362_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; uint8_t v___y_1376_; uint8_t v___y_1377_; uint8_t v___y_1378_; uint8_t v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1424_; lean_object* v___y_1425_; uint8_t v___y_1426_; uint8_t v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; uint8_t v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v_a_1434_; lean_object* v___y_1447_; lean_object* v___y_1448_; uint8_t v___y_1449_; uint8_t v___y_1450_; lean_object* v___y_1451_; uint8_t v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v_a_1457_; lean_object* v___y_1467_; lean_object* v___y_1468_; uint8_t v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; uint8_t v___y_1473_; uint8_t v___y_1474_; uint8_t v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1519_; uint8_t v___y_1520_; lean_object* v___y_1521_; uint8_t v___y_1522_; uint8_t v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v_a_1529_; lean_object* v___y_1539_; uint8_t v___y_1540_; lean_object* v___y_1541_; uint8_t v___y_1542_; uint8_t v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v_a_1549_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; uint8_t v___y_1566_; uint8_t v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; uint8_t v___y_1571_; lean_object* v_a_1572_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; uint8_t v___y_1586_; uint8_t v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; uint8_t v___y_1591_; lean_object* v_a_1592_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; uint8_t v___y_1610_; lean_object* v___y_1611_; uint8_t v___y_1612_; uint8_t v___y_1613_; uint8_t v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; uint8_t v___y_1660_; lean_object* v___y_1661_; uint8_t v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; uint8_t v___y_1666_; lean_object* v_a_1667_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; uint8_t v___y_1684_; lean_object* v___y_1685_; uint8_t v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; uint8_t v___y_1689_; lean_object* v_a_1690_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; uint8_t v___y_1703_; uint8_t v___y_1704_; uint8_t v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v_a_1710_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; uint8_t v___y_1726_; lean_object* v___y_1727_; uint8_t v___y_1728_; uint8_t v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v_a_1733_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; uint8_t v___y_1749_; uint8_t v___y_1750_; uint8_t v___y_1751_; uint8_t v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1799_; uint8_t v___y_1800_; lean_object* v_a_1801_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; uint8_t v___y_1818_; uint8_t v___y_1819_; lean_object* v_a_1820_; lean_object* v___y_1830_; lean_object* v___y_1831_; uint8_t v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; uint8_t v___y_1835_; lean_object* v___y_1836_; lean_object* v_one_1877_; lean_object* v_n_1878_; lean_object* v___y_1880_; lean_object* v___y_1881_; uint8_t v___y_1882_; uint8_t v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1926_; lean_object* v___y_1927_; uint8_t v___y_1928_; lean_object* v___y_1929_; uint8_t v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; uint8_t v___y_1935_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; uint8_t v___y_1963_; uint8_t v___y_1964_; uint8_t v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; uint8_t v___y_1968_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; uint8_t v___y_2014_; uint8_t v___y_2015_; uint8_t v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; uint8_t v___y_2046_; uint8_t v___y_2047_; uint8_t v___y_2048_; uint8_t v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; uint8_t v___y_2099_; uint8_t v___y_2100_; uint8_t v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; uint8_t v___y_2106_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; uint8_t v___y_2132_; uint8_t v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; uint8_t v___y_2184_; lean_object* v_a_2202_; lean_object* v___y_2295_; lean_object* v___x_2305_; 
v_proc_1162_ = lean_ctor_get(v_cfg_962_, 1);
v_suspend_1163_ = lean_ctor_get(v_cfg_962_, 2);
v_discharge_1164_ = lean_ctor_get(v_cfg_962_, 3);
v___f_1165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1877_ = lean_unsigned_to_nat(1u);
v_n_1878_ = lean_nat_sub(v_n_966_, v_one_1877_);
lean_dec(v_n_966_);
lean_inc_ref(v_proc_1162_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_curr_967_);
lean_inc(v_goals_965_);
v___x_2305_ = lean_apply_7(v_proc_1162_, v_goals_965_, v_curr_967_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v_a_2202_ = v_a_2306_;
goto v___jp_2201_;
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2375_; 
v_a_2307_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2309_ = v___x_2305_;
v_isShared_2310_ = v_isSharedCheck_2375_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2305_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2375_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___f_2311_; uint8_t v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; uint8_t v___y_2316_; uint8_t v___y_2353_; uint8_t v___x_2373_; 
lean_inc(v_a_2307_);
v___f_2311_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2311_, 0, v_a_2307_);
v___x_2373_ = l_Lean_Exception_isInterrupt(v_a_2307_);
if (v___x_2373_ == 0)
{
uint8_t v___x_2374_; 
lean_inc(v_a_2307_);
v___x_2374_ = l_Lean_Exception_isRuntime(v_a_2307_);
v___y_2353_ = v___x_2374_;
goto v___jp_2352_;
}
else
{
v___y_2353_ = v___x_2373_;
goto v___jp_2352_;
}
v___jp_2312_:
{
lean_object* v___x_2317_; lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2351_; 
v___x_2317_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2351_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2351_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2323_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2314_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2324_ = lean_io_mono_nanos_now();
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v_a_2307_);
v___x_2326_ = v___x_2320_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2307_);
v___x_2326_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2327_; double v___x_2328_; double v___x_2329_; double v___x_2330_; double v___x_2331_; double v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2327_ = lean_io_mono_nanos_now();
v___x_2328_ = lean_float_of_nat(v___x_2324_);
v___x_2329_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2330_ = lean_float_div(v___x_2328_, v___x_2329_);
v___x_2331_ = lean_float_of_nat(v___x_2327_);
v___x_2332_ = lean_float_div(v___x_2331_, v___x_2329_);
v___x_2333_ = lean_box_float(v___x_2330_);
v___x_2334_ = lean_box_float(v___x_2332_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2326_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
lean_inc_ref(v___y_2315_);
lean_inc(v_trace_963_);
v___x_2337_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_963_, v___y_2316_, v___y_2315_, v___y_2314_, v___y_2313_, v_a_2318_, v___f_2311_, v___x_2336_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_2295_ = v___x_2337_;
goto v___jp_2294_;
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2339_ = lean_io_get_num_heartbeats();
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v_a_2307_);
v___x_2341_ = v___x_2320_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2307_);
v___x_2341_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; double v___x_2343_; double v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2342_ = lean_io_get_num_heartbeats();
v___x_2343_ = lean_float_of_nat(v___x_2339_);
v___x_2344_ = lean_float_of_nat(v___x_2342_);
v___x_2345_ = lean_box_float(v___x_2343_);
v___x_2346_ = lean_box_float(v___x_2344_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2341_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
lean_inc_ref(v___y_2315_);
lean_inc(v_trace_963_);
v___x_2349_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_963_, v___y_2316_, v___y_2315_, v___y_2314_, v___y_2313_, v_a_2318_, v___f_2311_, v___x_2348_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_2295_ = v___x_2349_;
goto v___jp_2294_;
}
}
}
}
v___jp_2352_:
{
if (v___y_2353_ == 0)
{
lean_object* v_toCold_2354_; lean_object* v_options_2355_; uint8_t v_hasTrace_2356_; 
v_toCold_2354_ = lean_ctor_get(v_a_971_, 0);
v_options_2355_ = lean_ctor_get(v_toCold_2354_, 2);
v_hasTrace_2356_ = lean_ctor_get_uint8(v_options_2355_, sizeof(void*)*1);
if (v_hasTrace_2356_ == 0)
{
lean_object* v___x_2358_; 
lean_dec_ref(v___f_2311_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_curr_967_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
if (v_isShared_2310_ == 0)
{
v___x_2358_ = v___x_2309_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2307_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v_inheritedTraceOptions_2360_ = lean_ctor_get(v_toCold_2354_, 11);
v___x_2361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_2363_ = l_Lean_Name_append(v___x_2362_, v_trace_963_);
v___x_2364_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2360_, v_options_2355_, v___x_2363_);
lean_dec(v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = l_Lean_trace_profiler;
v___x_2366_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2355_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2368_; 
lean_dec_ref(v___f_2311_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_curr_967_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
if (v_isShared_2310_ == 0)
{
v___x_2368_ = v___x_2309_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2307_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
else
{
lean_del_object(v___x_2309_);
v___y_2313_ = v___x_2364_;
v___y_2314_ = v_options_2355_;
v___y_2315_ = v___x_2361_;
v___y_2316_ = v_hasTrace_2356_;
goto v___jp_2312_;
}
}
else
{
lean_del_object(v___x_2309_);
v___y_2313_ = v___x_2364_;
v___y_2314_ = v_options_2355_;
v___y_2315_ = v___x_2361_;
v___y_2316_ = v_hasTrace_2356_;
goto v___jp_2312_;
}
}
}
else
{
lean_object* v___x_2371_; 
lean_dec_ref(v___f_2311_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_curr_967_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
if (v_isShared_2310_ == 0)
{
v___x_2371_ = v___x_2309_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2307_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
v___jp_1166_:
{
lean_object* v___x_1172_; lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1206_; 
v___x_1172_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1206_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1206_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1178_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1171_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_io_mono_nanos_now();
if (v_isShared_1176_ == 0)
{
lean_ctor_set_tag(v___x_1175_, 1);
lean_ctor_set(v___x_1175_, 0, v___y_1168_);
v___x_1181_ = v___x_1175_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___y_1168_);
v___x_1181_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; double v___x_1183_; double v___x_1184_; double v___x_1185_; double v___x_1186_; double v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1182_ = lean_io_mono_nanos_now();
v___x_1183_ = lean_float_of_nat(v___x_1179_);
v___x_1184_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1185_ = lean_float_div(v___x_1183_, v___x_1184_);
v___x_1186_ = lean_float_of_nat(v___x_1182_);
v___x_1187_ = lean_float_div(v___x_1186_, v___x_1184_);
v___x_1188_ = lean_box_float(v___x_1185_);
v___x_1189_ = lean_box_float(v___x_1187_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1188_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1181_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
lean_inc_ref(v___y_1167_);
v___x_1192_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1169_, v___y_1167_, v___y_1171_, v___y_1170_, v_a_1173_, v___f_1165_, v___x_1191_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1192_;
}
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_io_get_num_heartbeats();
if (v_isShared_1176_ == 0)
{
lean_ctor_set_tag(v___x_1175_, 1);
lean_ctor_set(v___x_1175_, 0, v___y_1168_);
v___x_1196_ = v___x_1175_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___y_1168_);
v___x_1196_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; double v___x_1198_; double v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1197_ = lean_io_get_num_heartbeats();
v___x_1198_ = lean_float_of_nat(v___x_1194_);
v___x_1199_ = lean_float_of_nat(v___x_1197_);
v___x_1200_ = lean_box_float(v___x_1198_);
v___x_1201_ = lean_box_float(v___x_1199_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1196_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
lean_inc_ref(v___y_1167_);
v___x_1204_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1169_, v___y_1167_, v___y_1171_, v___y_1170_, v_a_1173_, v___f_1165_, v___x_1203_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1204_;
}
}
}
}
v___jp_1208_:
{
lean_object* v___x_1216_; double v___x_1217_; double v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1216_ = lean_io_get_num_heartbeats();
v___x_1217_ = lean_float_of_nat(v___y_1214_);
v___x_1218_ = lean_float_of_nat(v___x_1216_);
v___x_1219_ = lean_box_float(v___x_1217_);
v___x_1220_ = lean_box_float(v___x_1218_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_a_1215_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
lean_inc_ref(v___y_1210_);
v___x_1223_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1211_, v___y_1210_, v___y_1209_, v___y_1212_, v___y_1213_, v___f_1207_, v___x_1222_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1223_;
}
v___jp_1224_:
{
lean_object* v___x_1232_; double v___x_1233_; double v___x_1234_; double v___x_1235_; double v___x_1236_; double v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1232_ = lean_io_mono_nanos_now();
v___x_1233_ = lean_float_of_nat(v___y_1230_);
v___x_1234_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1235_ = lean_float_div(v___x_1233_, v___x_1234_);
v___x_1236_ = lean_float_of_nat(v___x_1232_);
v___x_1237_ = lean_float_div(v___x_1236_, v___x_1234_);
v___x_1238_ = lean_box_float(v___x_1235_);
v___x_1239_ = lean_box_float(v___x_1237_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1238_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_a_1231_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
lean_inc_ref(v___y_1226_);
v___x_1242_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1227_, v___y_1226_, v___y_1225_, v___y_1228_, v___y_1229_, v___f_1207_, v___x_1241_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1242_;
}
v___jp_1243_:
{
lean_object* v___x_1251_; lean_object* v_a_1252_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1251_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1254_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1244_, v___x_1253_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_io_mono_nanos_now();
lean_inc(v_trace_963_);
v___x_1256_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1249_, v___y_1250_, v___y_1248_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set_tag(v___x_1259_, 1);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
v___y_1225_ = v___y_1244_;
v___y_1226_ = v___y_1245_;
v___y_1227_ = v___y_1246_;
v___y_1228_ = v___y_1247_;
v___y_1229_ = v_a_1252_;
v___y_1230_ = v___x_1255_;
v_a_1231_ = v___x_1262_;
goto v___jp_1224_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
v_a_1265_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1256_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1256_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 0);
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
v___y_1225_ = v___y_1244_;
v___y_1226_ = v___y_1245_;
v___y_1227_ = v___y_1246_;
v___y_1228_ = v___y_1247_;
v___y_1229_ = v_a_1252_;
v___y_1230_ = v___x_1255_;
v_a_1231_ = v___x_1270_;
goto v___jp_1224_;
}
}
}
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_963_);
v___x_1274_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1249_, v___y_1250_, v___y_1248_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set_tag(v___x_1277_, 1);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
v___y_1209_ = v___y_1244_;
v___y_1210_ = v___y_1245_;
v___y_1211_ = v___y_1246_;
v___y_1212_ = v___y_1247_;
v___y_1213_ = v_a_1252_;
v___y_1214_ = v___x_1273_;
v_a_1215_ = v___x_1280_;
goto v___jp_1208_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
v_a_1283_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1274_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1274_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set_tag(v___x_1285_, 0);
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
v___y_1209_ = v___y_1244_;
v___y_1210_ = v___y_1245_;
v___y_1211_ = v___y_1246_;
v___y_1212_ = v___y_1247_;
v___y_1213_ = v_a_1252_;
v___y_1214_ = v___x_1273_;
v_a_1215_ = v___x_1288_;
goto v___jp_1208_;
}
}
}
}
}
v___jp_1292_:
{
lean_object* v___x_1300_; double v___x_1301_; double v___x_1302_; double v___x_1303_; double v___x_1304_; double v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1300_ = lean_io_mono_nanos_now();
v___x_1301_ = lean_float_of_nat(v___y_1295_);
v___x_1302_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1303_ = lean_float_div(v___x_1301_, v___x_1302_);
v___x_1304_ = lean_float_of_nat(v___x_1300_);
v___x_1305_ = lean_float_div(v___x_1304_, v___x_1302_);
v___x_1306_ = lean_box_float(v___x_1303_);
v___x_1307_ = lean_box_float(v___x_1305_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1306_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_a_1299_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
lean_inc_ref(v___y_1294_);
v___x_1310_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1298_, v___y_1294_, v___y_1293_, v___y_1297_, v___y_1296_, v___f_1291_, v___x_1309_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1310_;
}
v___jp_1311_:
{
lean_object* v___x_1319_; double v___x_1320_; double v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1319_ = lean_io_get_num_heartbeats();
v___x_1320_ = lean_float_of_nat(v___y_1317_);
v___x_1321_ = lean_float_of_nat(v___x_1319_);
v___x_1322_ = lean_box_float(v___x_1320_);
v___x_1323_ = lean_box_float(v___x_1321_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1325_, 0, v_a_1318_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
lean_inc_ref(v___y_1313_);
v___x_1326_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1316_, v___y_1313_, v___y_1312_, v___y_1315_, v___y_1314_, v___f_1291_, v___x_1325_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1326_;
}
v___jp_1328_:
{
lean_object* v___x_1340_; double v___x_1341_; double v___x_1342_; double v___x_1343_; double v___x_1344_; double v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1340_ = lean_io_mono_nanos_now();
v___x_1341_ = lean_float_of_nat(v___y_1331_);
v___x_1342_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1343_ = lean_float_div(v___x_1341_, v___x_1342_);
v___x_1344_ = lean_float_of_nat(v___x_1340_);
v___x_1345_ = lean_float_div(v___x_1344_, v___x_1342_);
v___x_1346_ = lean_box_float(v___x_1343_);
v___x_1347_ = lean_box_float(v___x_1345_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1346_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_a_1339_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
lean_inc_ref(v___y_1332_);
lean_inc(v_trace_963_);
v___x_1350_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1334_, v___y_1332_, v___y_1330_, v___y_1335_, v___y_1336_, v___f_1327_, v___x_1349_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1097_ = v___y_1330_;
v___y_1098_ = v___y_1329_;
v___y_1099_ = v___y_1332_;
v___y_1100_ = v___y_1333_;
v___y_1101_ = v___y_1334_;
v___y_1102_ = v___y_1337_;
v___y_1103_ = v___y_1338_;
v___y_1104_ = v___x_1350_;
goto v___jp_1096_;
}
v___jp_1351_:
{
lean_object* v___x_1363_; double v___x_1364_; double v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1363_ = lean_io_get_num_heartbeats();
v___x_1364_ = lean_float_of_nat(v___y_1361_);
v___x_1365_ = lean_float_of_nat(v___x_1363_);
v___x_1366_ = lean_box_float(v___x_1364_);
v___x_1367_ = lean_box_float(v___x_1365_);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_a_1362_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
lean_inc_ref(v___y_1354_);
lean_inc(v_trace_963_);
v___x_1370_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1356_, v___y_1354_, v___y_1353_, v___y_1357_, v___y_1358_, v___f_1327_, v___x_1369_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1097_ = v___y_1353_;
v___y_1098_ = v___y_1352_;
v___y_1099_ = v___y_1354_;
v___y_1100_ = v___y_1355_;
v___y_1101_ = v___y_1356_;
v___y_1102_ = v___y_1359_;
v___y_1103_ = v___y_1360_;
v___y_1104_ = v___x_1370_;
goto v___jp_1096_;
}
v___jp_1371_:
{
lean_object* v___x_1384_; 
v___x_1384_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
if (v___y_1376_ == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref(v___x_1384_);
v___x_1386_ = lean_io_mono_nanos_now();
lean_inc(v_trace_963_);
v___x_1387_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1380_, v___y_1383_, v___y_1381_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set_tag(v___x_1390_, 1);
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
v___y_1329_ = v___y_1372_;
v___y_1330_ = v___y_1375_;
v___y_1331_ = v___x_1386_;
v___y_1332_ = v___y_1373_;
v___y_1333_ = v___y_1377_;
v___y_1334_ = v___y_1378_;
v___y_1335_ = v___y_1379_;
v___y_1336_ = v_a_1385_;
v___y_1337_ = v___y_1374_;
v___y_1338_ = v___y_1382_;
v_a_1339_ = v___x_1393_;
goto v___jp_1328_;
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
v_a_1396_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1387_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1387_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set_tag(v___x_1398_, 0);
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
v___y_1329_ = v___y_1372_;
v___y_1330_ = v___y_1375_;
v___y_1331_ = v___x_1386_;
v___y_1332_ = v___y_1373_;
v___y_1333_ = v___y_1377_;
v___y_1334_ = v___y_1378_;
v___y_1335_ = v___y_1379_;
v___y_1336_ = v_a_1385_;
v___y_1337_ = v___y_1374_;
v___y_1338_ = v___y_1382_;
v_a_1339_ = v___x_1401_;
goto v___jp_1328_;
}
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v_a_1404_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1404_);
lean_dec_ref(v___x_1384_);
v___x_1405_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_963_);
v___x_1406_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1380_, v___y_1383_, v___y_1381_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 1);
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
v___y_1352_ = v___y_1372_;
v___y_1353_ = v___y_1375_;
v___y_1354_ = v___y_1373_;
v___y_1355_ = v___y_1377_;
v___y_1356_ = v___y_1378_;
v___y_1357_ = v___y_1379_;
v___y_1358_ = v_a_1404_;
v___y_1359_ = v___y_1374_;
v___y_1360_ = v___y_1382_;
v___y_1361_ = v___x_1405_;
v_a_1362_ = v___x_1412_;
goto v___jp_1351_;
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
v_a_1415_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1406_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1406_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 0);
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
v___y_1352_ = v___y_1372_;
v___y_1353_ = v___y_1375_;
v___y_1354_ = v___y_1373_;
v___y_1355_ = v___y_1377_;
v___y_1356_ = v___y_1378_;
v___y_1357_ = v___y_1379_;
v___y_1358_ = v_a_1404_;
v___y_1359_ = v___y_1374_;
v___y_1360_ = v___y_1382_;
v___y_1361_ = v___x_1405_;
v_a_1362_ = v___x_1420_;
goto v___jp_1351_;
}
}
}
}
}
v___jp_1423_:
{
lean_object* v___x_1435_; double v___x_1436_; double v___x_1437_; double v___x_1438_; double v___x_1439_; double v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1435_ = lean_io_mono_nanos_now();
v___x_1436_ = lean_float_of_nat(v___y_1428_);
v___x_1437_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1438_ = lean_float_div(v___x_1436_, v___x_1437_);
v___x_1439_ = lean_float_of_nat(v___x_1435_);
v___x_1440_ = lean_float_div(v___x_1439_, v___x_1437_);
v___x_1441_ = lean_box_float(v___x_1438_);
v___x_1442_ = lean_box_float(v___x_1440_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_a_1434_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
lean_inc_ref(v___y_1425_);
lean_inc(v_trace_963_);
v___x_1445_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1427_, v___y_1425_, v___y_1424_, v___y_1430_, v___y_1431_, v___f_1207_, v___x_1444_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1148_ = v___y_1424_;
v___y_1149_ = v___y_1425_;
v___y_1150_ = v___y_1426_;
v___y_1151_ = v___y_1427_;
v___y_1152_ = v___y_1429_;
v___y_1153_ = v___y_1432_;
v___y_1154_ = v___y_1433_;
v___y_1155_ = v___x_1445_;
goto v___jp_1147_;
}
v___jp_1446_:
{
lean_object* v___x_1458_; double v___x_1459_; double v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1458_ = lean_io_get_num_heartbeats();
v___x_1459_ = lean_float_of_nat(v___y_1454_);
v___x_1460_ = lean_float_of_nat(v___x_1458_);
v___x_1461_ = lean_box_float(v___x_1459_);
v___x_1462_ = lean_box_float(v___x_1460_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1464_, 0, v_a_1457_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
lean_inc_ref(v___y_1448_);
lean_inc(v_trace_963_);
v___x_1465_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1450_, v___y_1448_, v___y_1447_, v___y_1452_, v___y_1453_, v___f_1207_, v___x_1464_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1148_ = v___y_1447_;
v___y_1149_ = v___y_1448_;
v___y_1150_ = v___y_1449_;
v___y_1151_ = v___y_1450_;
v___y_1152_ = v___y_1451_;
v___y_1153_ = v___y_1455_;
v___y_1154_ = v___y_1456_;
v___y_1155_ = v___x_1465_;
goto v___jp_1147_;
}
v___jp_1466_:
{
lean_object* v___x_1479_; 
v___x_1479_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
if (v___y_1473_ == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref(v___x_1479_);
v___x_1481_ = lean_io_mono_nanos_now();
lean_inc(v_trace_963_);
v___x_1482_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1471_, v___y_1478_, v___y_1476_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set_tag(v___x_1485_, 1);
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
v___y_1424_ = v___y_1472_;
v___y_1425_ = v___y_1467_;
v___y_1426_ = v___y_1474_;
v___y_1427_ = v___y_1475_;
v___y_1428_ = v___x_1481_;
v___y_1429_ = v___y_1468_;
v___y_1430_ = v___y_1469_;
v___y_1431_ = v_a_1480_;
v___y_1432_ = v___y_1470_;
v___y_1433_ = v___y_1477_;
v_a_1434_ = v___x_1488_;
goto v___jp_1423_;
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
v_a_1491_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1482_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1482_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set_tag(v___x_1493_, 0);
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
v___y_1424_ = v___y_1472_;
v___y_1425_ = v___y_1467_;
v___y_1426_ = v___y_1474_;
v___y_1427_ = v___y_1475_;
v___y_1428_ = v___x_1481_;
v___y_1429_ = v___y_1468_;
v___y_1430_ = v___y_1469_;
v___y_1431_ = v_a_1480_;
v___y_1432_ = v___y_1470_;
v___y_1433_ = v___y_1477_;
v_a_1434_ = v___x_1496_;
goto v___jp_1423_;
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v_a_1499_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1499_);
lean_dec_ref(v___x_1479_);
v___x_1500_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_963_);
v___x_1501_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1471_, v___y_1478_, v___y_1476_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
lean_ctor_set_tag(v___x_1504_, 1);
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
v___y_1447_ = v___y_1472_;
v___y_1448_ = v___y_1467_;
v___y_1449_ = v___y_1474_;
v___y_1450_ = v___y_1475_;
v___y_1451_ = v___y_1468_;
v___y_1452_ = v___y_1469_;
v___y_1453_ = v_a_1499_;
v___y_1454_ = v___x_1500_;
v___y_1455_ = v___y_1470_;
v___y_1456_ = v___y_1477_;
v_a_1457_ = v___x_1507_;
goto v___jp_1446_;
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
v_a_1510_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1501_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1501_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set_tag(v___x_1512_, 0);
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
v___y_1447_ = v___y_1472_;
v___y_1448_ = v___y_1467_;
v___y_1449_ = v___y_1474_;
v___y_1450_ = v___y_1475_;
v___y_1451_ = v___y_1468_;
v___y_1452_ = v___y_1469_;
v___y_1453_ = v_a_1499_;
v___y_1454_ = v___x_1500_;
v___y_1455_ = v___y_1470_;
v___y_1456_ = v___y_1477_;
v_a_1457_ = v___x_1515_;
goto v___jp_1446_;
}
}
}
}
}
v___jp_1518_:
{
lean_object* v___x_1530_; double v___x_1531_; double v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1530_ = lean_io_get_num_heartbeats();
v___x_1531_ = lean_float_of_nat(v___y_1525_);
v___x_1532_ = lean_float_of_nat(v___x_1530_);
v___x_1533_ = lean_box_float(v___x_1531_);
v___x_1534_ = lean_box_float(v___x_1532_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v_a_1529_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
lean_inc_ref(v___y_1521_);
lean_inc(v_trace_963_);
v___x_1537_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1523_, v___y_1521_, v___y_1519_, v___y_1520_, v___y_1528_, v___f_1291_, v___x_1536_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1148_ = v___y_1519_;
v___y_1149_ = v___y_1521_;
v___y_1150_ = v___y_1522_;
v___y_1151_ = v___y_1523_;
v___y_1152_ = v___y_1524_;
v___y_1153_ = v___y_1526_;
v___y_1154_ = v___y_1527_;
v___y_1155_ = v___x_1537_;
goto v___jp_1147_;
}
v___jp_1538_:
{
lean_object* v___x_1550_; double v___x_1551_; double v___x_1552_; double v___x_1553_; double v___x_1554_; double v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1550_ = lean_io_mono_nanos_now();
v___x_1551_ = lean_float_of_nat(v___y_1545_);
v___x_1552_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1553_ = lean_float_div(v___x_1551_, v___x_1552_);
v___x_1554_ = lean_float_of_nat(v___x_1550_);
v___x_1555_ = lean_float_div(v___x_1554_, v___x_1552_);
v___x_1556_ = lean_box_float(v___x_1553_);
v___x_1557_ = lean_box_float(v___x_1555_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_a_1549_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
lean_inc_ref(v___y_1541_);
lean_inc(v_trace_963_);
v___x_1560_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1543_, v___y_1541_, v___y_1539_, v___y_1540_, v___y_1548_, v___f_1291_, v___x_1559_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1148_ = v___y_1539_;
v___y_1149_ = v___y_1541_;
v___y_1150_ = v___y_1542_;
v___y_1151_ = v___y_1543_;
v___y_1152_ = v___y_1544_;
v___y_1153_ = v___y_1546_;
v___y_1154_ = v___y_1547_;
v___y_1155_ = v___x_1560_;
goto v___jp_1147_;
}
v___jp_1561_:
{
lean_object* v___x_1573_; double v___x_1574_; double v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1573_ = lean_io_get_num_heartbeats();
v___x_1574_ = lean_float_of_nat(v___y_1564_);
v___x_1575_ = lean_float_of_nat(v___x_1573_);
v___x_1576_ = lean_box_float(v___x_1574_);
v___x_1577_ = lean_box_float(v___x_1575_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1579_, 0, v_a_1572_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
lean_inc_ref(v___y_1565_);
lean_inc(v_trace_963_);
v___x_1580_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1567_, v___y_1565_, v___y_1562_, v___y_1571_, v___y_1563_, v___f_1327_, v___x_1579_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1148_ = v___y_1562_;
v___y_1149_ = v___y_1565_;
v___y_1150_ = v___y_1566_;
v___y_1151_ = v___y_1567_;
v___y_1152_ = v___y_1568_;
v___y_1153_ = v___y_1569_;
v___y_1154_ = v___y_1570_;
v___y_1155_ = v___x_1580_;
goto v___jp_1147_;
}
v___jp_1581_:
{
lean_object* v___x_1593_; double v___x_1594_; double v___x_1595_; double v___x_1596_; double v___x_1597_; double v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1593_ = lean_io_mono_nanos_now();
v___x_1594_ = lean_float_of_nat(v___y_1585_);
v___x_1595_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1596_ = lean_float_div(v___x_1594_, v___x_1595_);
v___x_1597_ = lean_float_of_nat(v___x_1593_);
v___x_1598_ = lean_float_div(v___x_1597_, v___x_1595_);
v___x_1599_ = lean_box_float(v___x_1596_);
v___x_1600_ = lean_box_float(v___x_1598_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_a_1592_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
lean_inc_ref(v___y_1584_);
lean_inc(v_trace_963_);
v___x_1603_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1587_, v___y_1584_, v___y_1582_, v___y_1591_, v___y_1583_, v___f_1327_, v___x_1602_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1148_ = v___y_1582_;
v___y_1149_ = v___y_1584_;
v___y_1150_ = v___y_1586_;
v___y_1151_ = v___y_1587_;
v___y_1152_ = v___y_1588_;
v___y_1153_ = v___y_1589_;
v___y_1154_ = v___y_1590_;
v___y_1155_ = v___x_1603_;
goto v___jp_1147_;
}
v___jp_1604_:
{
lean_object* v___x_1617_; 
v___x_1617_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
if (v___y_1612_ == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = lean_io_mono_nanos_now();
lean_inc(v_trace_963_);
v___x_1620_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1608_, v___y_1616_, v___y_1606_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set_tag(v___x_1623_, 1);
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
v___y_1582_ = v___y_1611_;
v___y_1583_ = v_a_1618_;
v___y_1584_ = v___y_1605_;
v___y_1585_ = v___x_1619_;
v___y_1586_ = v___y_1613_;
v___y_1587_ = v___y_1614_;
v___y_1588_ = v___y_1607_;
v___y_1589_ = v___y_1609_;
v___y_1590_ = v___y_1615_;
v___y_1591_ = v___y_1610_;
v_a_1592_ = v___x_1626_;
goto v___jp_1581_;
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
v_a_1629_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1620_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1620_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set_tag(v___x_1631_, 0);
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
v___y_1582_ = v___y_1611_;
v___y_1583_ = v_a_1618_;
v___y_1584_ = v___y_1605_;
v___y_1585_ = v___x_1619_;
v___y_1586_ = v___y_1613_;
v___y_1587_ = v___y_1614_;
v___y_1588_ = v___y_1607_;
v___y_1589_ = v___y_1609_;
v___y_1590_ = v___y_1615_;
v___y_1591_ = v___y_1610_;
v_a_1592_ = v___x_1634_;
goto v___jp_1581_;
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_a_1637_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v___x_1617_);
v___x_1638_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_963_);
v___x_1639_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1608_, v___y_1616_, v___y_1606_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 1);
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
v___y_1562_ = v___y_1611_;
v___y_1563_ = v_a_1637_;
v___y_1564_ = v___x_1638_;
v___y_1565_ = v___y_1605_;
v___y_1566_ = v___y_1613_;
v___y_1567_ = v___y_1614_;
v___y_1568_ = v___y_1607_;
v___y_1569_ = v___y_1609_;
v___y_1570_ = v___y_1615_;
v___y_1571_ = v___y_1610_;
v_a_1572_ = v___x_1645_;
goto v___jp_1561_;
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_a_1648_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1639_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1639_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 0);
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
v___y_1562_ = v___y_1611_;
v___y_1563_ = v_a_1637_;
v___y_1564_ = v___x_1638_;
v___y_1565_ = v___y_1605_;
v___y_1566_ = v___y_1613_;
v___y_1567_ = v___y_1614_;
v___y_1568_ = v___y_1607_;
v___y_1569_ = v___y_1609_;
v___y_1570_ = v___y_1615_;
v___y_1571_ = v___y_1610_;
v_a_1572_ = v___x_1653_;
goto v___jp_1561_;
}
}
}
}
}
v___jp_1656_:
{
lean_object* v___x_1668_; double v___x_1669_; double v___x_1670_; double v___x_1671_; double v___x_1672_; double v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1668_ = lean_io_mono_nanos_now();
v___x_1669_ = lean_float_of_nat(v___y_1663_);
v___x_1670_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1671_ = lean_float_div(v___x_1669_, v___x_1670_);
v___x_1672_ = lean_float_of_nat(v___x_1668_);
v___x_1673_ = lean_float_div(v___x_1672_, v___x_1670_);
v___x_1674_ = lean_box_float(v___x_1671_);
v___x_1675_ = lean_box_float(v___x_1673_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v_a_1667_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
lean_inc_ref(v___y_1659_);
lean_inc(v_trace_963_);
v___x_1678_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1662_, v___y_1659_, v___y_1658_, v___y_1666_, v___y_1661_, v___f_1291_, v___x_1677_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1097_ = v___y_1658_;
v___y_1098_ = v___y_1657_;
v___y_1099_ = v___y_1659_;
v___y_1100_ = v___y_1660_;
v___y_1101_ = v___y_1662_;
v___y_1102_ = v___y_1664_;
v___y_1103_ = v___y_1665_;
v___y_1104_ = v___x_1678_;
goto v___jp_1096_;
}
v___jp_1679_:
{
lean_object* v___x_1691_; double v___x_1692_; double v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1691_ = lean_io_get_num_heartbeats();
v___x_1692_ = lean_float_of_nat(v___y_1683_);
v___x_1693_ = lean_float_of_nat(v___x_1691_);
v___x_1694_ = lean_box_float(v___x_1692_);
v___x_1695_ = lean_box_float(v___x_1693_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v_a_1690_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
lean_inc_ref(v___y_1682_);
lean_inc(v_trace_963_);
v___x_1698_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1686_, v___y_1682_, v___y_1681_, v___y_1689_, v___y_1685_, v___f_1291_, v___x_1697_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1097_ = v___y_1681_;
v___y_1098_ = v___y_1680_;
v___y_1099_ = v___y_1682_;
v___y_1100_ = v___y_1684_;
v___y_1101_ = v___y_1686_;
v___y_1102_ = v___y_1687_;
v___y_1103_ = v___y_1688_;
v___y_1104_ = v___x_1698_;
goto v___jp_1096_;
}
v___jp_1699_:
{
lean_object* v___x_1711_; double v___x_1712_; double v___x_1713_; double v___x_1714_; double v___x_1715_; double v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1711_ = lean_io_mono_nanos_now();
v___x_1712_ = lean_float_of_nat(v___y_1706_);
v___x_1713_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1714_ = lean_float_div(v___x_1712_, v___x_1713_);
v___x_1715_ = lean_float_of_nat(v___x_1711_);
v___x_1716_ = lean_float_div(v___x_1715_, v___x_1713_);
v___x_1717_ = lean_box_float(v___x_1714_);
v___x_1718_ = lean_box_float(v___x_1716_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_a_1710_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
lean_inc_ref(v___y_1702_);
lean_inc(v_trace_963_);
v___x_1721_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1704_, v___y_1702_, v___y_1701_, v___y_1705_, v___y_1709_, v___f_1207_, v___x_1720_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1097_ = v___y_1701_;
v___y_1098_ = v___y_1700_;
v___y_1099_ = v___y_1702_;
v___y_1100_ = v___y_1703_;
v___y_1101_ = v___y_1704_;
v___y_1102_ = v___y_1707_;
v___y_1103_ = v___y_1708_;
v___y_1104_ = v___x_1721_;
goto v___jp_1096_;
}
v___jp_1722_:
{
lean_object* v___x_1734_; double v___x_1735_; double v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1734_ = lean_io_get_num_heartbeats();
v___x_1735_ = lean_float_of_nat(v___y_1727_);
v___x_1736_ = lean_float_of_nat(v___x_1734_);
v___x_1737_ = lean_box_float(v___x_1735_);
v___x_1738_ = lean_box_float(v___x_1736_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1737_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v_a_1733_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
lean_inc_ref(v___y_1725_);
lean_inc(v_trace_963_);
v___x_1741_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1728_, v___y_1725_, v___y_1724_, v___y_1729_, v___y_1732_, v___f_1207_, v___x_1740_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1097_ = v___y_1724_;
v___y_1098_ = v___y_1723_;
v___y_1099_ = v___y_1725_;
v___y_1100_ = v___y_1726_;
v___y_1101_ = v___y_1728_;
v___y_1102_ = v___y_1730_;
v___y_1103_ = v___y_1731_;
v___y_1104_ = v___x_1741_;
goto v___jp_1096_;
}
v___jp_1742_:
{
lean_object* v___x_1755_; 
v___x_1755_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
if (v___y_1749_ == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = lean_io_mono_nanos_now();
lean_inc(v_trace_963_);
v___x_1758_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1745_, v___y_1754_, v___y_1747_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set_tag(v___x_1761_, 1);
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
v___y_1700_ = v___y_1743_;
v___y_1701_ = v___y_1748_;
v___y_1702_ = v___y_1744_;
v___y_1703_ = v___y_1750_;
v___y_1704_ = v___y_1751_;
v___y_1705_ = v___y_1752_;
v___y_1706_ = v___x_1757_;
v___y_1707_ = v___y_1746_;
v___y_1708_ = v___y_1753_;
v___y_1709_ = v_a_1756_;
v_a_1710_ = v___x_1764_;
goto v___jp_1699_;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
v_a_1767_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1758_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1758_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set_tag(v___x_1769_, 0);
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
v___y_1700_ = v___y_1743_;
v___y_1701_ = v___y_1748_;
v___y_1702_ = v___y_1744_;
v___y_1703_ = v___y_1750_;
v___y_1704_ = v___y_1751_;
v___y_1705_ = v___y_1752_;
v___y_1706_ = v___x_1757_;
v___y_1707_ = v___y_1746_;
v___y_1708_ = v___y_1753_;
v___y_1709_ = v_a_1756_;
v_a_1710_ = v___x_1772_;
goto v___jp_1699_;
}
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_a_1775_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1755_);
v___x_1776_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_963_);
v___x_1777_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1745_, v___y_1754_, v___y_1747_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 1);
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
v___y_1723_ = v___y_1743_;
v___y_1724_ = v___y_1748_;
v___y_1725_ = v___y_1744_;
v___y_1726_ = v___y_1750_;
v___y_1727_ = v___x_1776_;
v___y_1728_ = v___y_1751_;
v___y_1729_ = v___y_1752_;
v___y_1730_ = v___y_1746_;
v___y_1731_ = v___y_1753_;
v___y_1732_ = v_a_1775_;
v_a_1733_ = v___x_1783_;
goto v___jp_1722_;
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_a_1786_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1777_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1777_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set_tag(v___x_1788_, 0);
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
v___y_1723_ = v___y_1743_;
v___y_1724_ = v___y_1748_;
v___y_1725_ = v___y_1744_;
v___y_1726_ = v___y_1750_;
v___y_1727_ = v___x_1776_;
v___y_1728_ = v___y_1751_;
v___y_1729_ = v___y_1752_;
v___y_1730_ = v___y_1746_;
v___y_1731_ = v___y_1753_;
v___y_1732_ = v_a_1775_;
v_a_1733_ = v___x_1791_;
goto v___jp_1722_;
}
}
}
}
}
v___jp_1794_:
{
lean_object* v___x_1802_; double v___x_1803_; double v___x_1804_; double v___x_1805_; double v___x_1806_; double v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1802_ = lean_io_mono_nanos_now();
v___x_1803_ = lean_float_of_nat(v___y_1799_);
v___x_1804_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1805_ = lean_float_div(v___x_1803_, v___x_1804_);
v___x_1806_ = lean_float_of_nat(v___x_1802_);
v___x_1807_ = lean_float_div(v___x_1806_, v___x_1804_);
v___x_1808_ = lean_box_float(v___x_1805_);
v___x_1809_ = lean_box_float(v___x_1807_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v_a_1801_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
lean_inc_ref(v___y_1797_);
v___x_1812_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1798_, v___y_1797_, v___y_1795_, v___y_1800_, v___y_1796_, v___f_1327_, v___x_1811_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1812_;
}
v___jp_1813_:
{
lean_object* v___x_1821_; double v___x_1822_; double v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1821_ = lean_io_get_num_heartbeats();
v___x_1822_ = lean_float_of_nat(v___y_1815_);
v___x_1823_ = lean_float_of_nat(v___x_1821_);
v___x_1824_ = lean_box_float(v___x_1822_);
v___x_1825_ = lean_box_float(v___x_1823_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v_a_1820_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
lean_inc_ref(v___y_1817_);
v___x_1828_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1818_, v___y_1817_, v___y_1814_, v___y_1819_, v___y_1816_, v___f_1327_, v___x_1827_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1828_;
}
v___jp_1829_:
{
lean_object* v___x_1837_; lean_object* v_a_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1837_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1840_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1830_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_io_mono_nanos_now();
lean_inc(v_trace_963_);
v___x_1842_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1834_, v___y_1836_, v___y_1833_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set_tag(v___x_1845_, 1);
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
v___y_1795_ = v___y_1830_;
v___y_1796_ = v_a_1838_;
v___y_1797_ = v___y_1831_;
v___y_1798_ = v___y_1832_;
v___y_1799_ = v___x_1841_;
v___y_1800_ = v___y_1835_;
v_a_1801_ = v___x_1848_;
goto v___jp_1794_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_a_1851_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1842_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1842_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 0);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
v___y_1795_ = v___y_1830_;
v___y_1796_ = v_a_1838_;
v___y_1797_ = v___y_1831_;
v___y_1798_ = v___y_1832_;
v___y_1799_ = v___x_1841_;
v___y_1800_ = v___y_1835_;
v_a_1801_ = v___x_1856_;
goto v___jp_1794_;
}
}
}
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_963_);
v___x_1860_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1834_, v___y_1836_, v___y_1833_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set_tag(v___x_1863_, 1);
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
v___y_1814_ = v___y_1830_;
v___y_1815_ = v___x_1859_;
v___y_1816_ = v_a_1838_;
v___y_1817_ = v___y_1831_;
v___y_1818_ = v___y_1832_;
v___y_1819_ = v___y_1835_;
v_a_1820_ = v___x_1866_;
goto v___jp_1813_;
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
v_a_1869_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1860_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1860_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set_tag(v___x_1871_, 0);
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
v___y_1814_ = v___y_1830_;
v___y_1815_ = v___x_1859_;
v___y_1816_ = v_a_1838_;
v___y_1817_ = v___y_1831_;
v___y_1818_ = v___y_1832_;
v___y_1819_ = v___y_1835_;
v_a_1820_ = v___x_1874_;
goto v___jp_1813_;
}
}
}
}
}
v___jp_1879_:
{
lean_object* v___x_1885_; lean_object* v_a_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1885_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1885_);
v___x_1887_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1888_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1880_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_io_mono_nanos_now();
lean_inc(v_trace_963_);
v___x_1890_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v_n_1878_, v___y_1884_, v_acc_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set_tag(v___x_1893_, 1);
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
v___y_1293_ = v___y_1880_;
v___y_1294_ = v___y_1881_;
v___y_1295_ = v___x_1889_;
v___y_1296_ = v_a_1886_;
v___y_1297_ = v___y_1883_;
v___y_1298_ = v___y_1882_;
v_a_1299_ = v___x_1896_;
goto v___jp_1292_;
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
v_a_1899_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1890_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1890_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set_tag(v___x_1901_, 0);
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
v___y_1293_ = v___y_1880_;
v___y_1294_ = v___y_1881_;
v___y_1295_ = v___x_1889_;
v___y_1296_ = v_a_1886_;
v___y_1297_ = v___y_1883_;
v___y_1298_ = v___y_1882_;
v_a_1299_ = v___x_1904_;
goto v___jp_1292_;
}
}
}
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_963_);
v___x_1908_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v_n_1878_, v___y_1884_, v_acc_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 1);
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
v___y_1312_ = v___y_1880_;
v___y_1313_ = v___y_1881_;
v___y_1314_ = v_a_1886_;
v___y_1315_ = v___y_1883_;
v___y_1316_ = v___y_1882_;
v___y_1317_ = v___x_1907_;
v_a_1318_ = v___x_1914_;
goto v___jp_1311_;
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
v_a_1917_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1908_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1908_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 0);
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
v___y_1312_ = v___y_1880_;
v___y_1313_ = v___y_1881_;
v___y_1314_ = v_a_1886_;
v___y_1315_ = v___y_1883_;
v___y_1316_ = v___y_1882_;
v___y_1317_ = v___x_1907_;
v_a_1318_ = v___x_1922_;
goto v___jp_1311_;
}
}
}
}
}
v___jp_1925_:
{
if (v___y_1935_ == 0)
{
lean_object* v___x_1936_; 
lean_dec_ref(v___y_1932_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v___y_1933_);
v___x_1936_ = lean_apply_6(v___y_1931_, v___y_1933_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
if (lean_obj_tag(v_a_1937_) == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1938_ = lean_nat_add(v_n_1878_, v_one_1877_);
lean_dec(v_n_1878_);
v___x_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___y_1933_);
lean_ctor_set(v___x_1939_, 1, v_acc_968_);
v___x_1940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_1941_ = l_Lean_Name_append(v___x_1940_, v_trace_963_);
v___x_1942_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1929_, v___y_1926_, v___x_1941_);
lean_dec(v___x_1941_);
if (v___x_1942_ == 0)
{
if (v___y_1930_ == 0)
{
v_n_966_ = v___x_1938_;
v_curr_967_ = v___y_1934_;
v_acc_968_ = v___x_1939_;
goto _start;
}
else
{
v___y_1244_ = v___y_1926_;
v___y_1245_ = v___y_1927_;
v___y_1246_ = v___y_1928_;
v___y_1247_ = v___x_1942_;
v___y_1248_ = v___x_1939_;
v___y_1249_ = v___x_1938_;
v___y_1250_ = v___y_1934_;
goto v___jp_1243_;
}
}
else
{
v___y_1244_ = v___y_1926_;
v___y_1245_ = v___y_1927_;
v___y_1246_ = v___y_1928_;
v___y_1247_ = v___x_1942_;
v___y_1248_ = v___x_1939_;
v___y_1249_ = v___x_1938_;
v___y_1250_ = v___y_1934_;
goto v___jp_1243_;
}
}
else
{
lean_object* v_val_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
lean_dec(v___y_1933_);
v_val_1944_ = lean_ctor_get(v_a_1937_, 0);
lean_inc(v_val_1944_);
lean_dec_ref_known(v_a_1937_, 1);
v___x_1945_ = l_List_appendTR___redArg(v_val_1944_, v___y_1934_);
v___x_1946_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_1947_ = l_Lean_Name_append(v___x_1946_, v_trace_963_);
v___x_1948_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1929_, v___y_1926_, v___x_1947_);
lean_dec(v___x_1947_);
if (v___x_1948_ == 0)
{
if (v___y_1930_ == 0)
{
v_n_966_ = v_n_1878_;
v_curr_967_ = v___x_1945_;
goto _start;
}
else
{
v___y_1880_ = v___y_1926_;
v___y_1881_ = v___y_1927_;
v___y_1882_ = v___y_1928_;
v___y_1883_ = v___x_1948_;
v___y_1884_ = v___x_1945_;
goto v___jp_1879_;
}
}
else
{
v___y_1880_ = v___y_1926_;
v___y_1881_ = v___y_1927_;
v___y_1882_ = v___y_1928_;
v___y_1883_ = v___x_1948_;
v___y_1884_ = v___x_1945_;
goto v___jp_1879_;
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
v_a_1950_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1936_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1936_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_dec(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1931_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
return v___y_1932_;
}
}
v___jp_1958_:
{
lean_object* v___x_1969_; 
v___x_1969_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
if (v___y_1964_ == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref(v___x_1969_);
v___x_1971_ = lean_io_mono_nanos_now();
lean_inc(v_trace_963_);
v___x_1972_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v_n_1878_, v___y_1962_, v_acc_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set_tag(v___x_1975_, 1);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
v___y_1657_ = v___y_1960_;
v___y_1658_ = v___y_1959_;
v___y_1659_ = v___y_1961_;
v___y_1660_ = v___y_1963_;
v___y_1661_ = v_a_1970_;
v___y_1662_ = v___y_1965_;
v___y_1663_ = v___x_1971_;
v___y_1664_ = v___y_1966_;
v___y_1665_ = v___y_1967_;
v___y_1666_ = v___y_1968_;
v_a_1667_ = v___x_1978_;
goto v___jp_1656_;
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_a_1981_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1972_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1972_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 0);
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
v___y_1657_ = v___y_1960_;
v___y_1658_ = v___y_1959_;
v___y_1659_ = v___y_1961_;
v___y_1660_ = v___y_1963_;
v___y_1661_ = v_a_1970_;
v___y_1662_ = v___y_1965_;
v___y_1663_ = v___x_1971_;
v___y_1664_ = v___y_1966_;
v___y_1665_ = v___y_1967_;
v___y_1666_ = v___y_1968_;
v_a_1667_ = v___x_1986_;
goto v___jp_1656_;
}
}
}
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_a_1989_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1989_);
lean_dec_ref(v___x_1969_);
v___x_1990_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_963_);
v___x_1991_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v_n_1878_, v___y_1962_, v_acc_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
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
v___y_1680_ = v___y_1960_;
v___y_1681_ = v___y_1959_;
v___y_1682_ = v___y_1961_;
v___y_1683_ = v___x_1990_;
v___y_1684_ = v___y_1963_;
v___y_1685_ = v_a_1989_;
v___y_1686_ = v___y_1965_;
v___y_1687_ = v___y_1966_;
v___y_1688_ = v___y_1967_;
v___y_1689_ = v___y_1968_;
v_a_1690_ = v___x_1997_;
goto v___jp_1679_;
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
v___y_1680_ = v___y_1960_;
v___y_1681_ = v___y_1959_;
v___y_1682_ = v___y_1961_;
v___y_1683_ = v___x_1990_;
v___y_1684_ = v___y_1963_;
v___y_1685_ = v_a_1989_;
v___y_1686_ = v___y_1965_;
v___y_1687_ = v___y_1966_;
v___y_1688_ = v___y_1967_;
v___y_1689_ = v___y_1968_;
v_a_1690_ = v___x_2005_;
goto v___jp_1679_;
}
}
}
}
}
v___jp_2008_:
{
if (v___y_2022_ == 0)
{
lean_object* v___x_2023_; 
lean_dec_ref(v___y_2017_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v___y_2019_);
v___x_2023_ = lean_apply_6(v___y_2018_, v___y_2019_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
if (lean_obj_tag(v_a_2024_) == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2025_ = lean_nat_add(v_n_1878_, v_one_1877_);
lean_dec(v_n_1878_);
v___x_2026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___y_2019_);
lean_ctor_set(v___x_2026_, 1, v_acc_968_);
v___x_2027_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_2028_ = l_Lean_Name_append(v___x_2027_, v_trace_963_);
v___x_2029_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2011_, v___y_2013_, v___x_2028_);
lean_dec(v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2030_ = l_Lean_trace_profiler;
v___x_2031_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2013_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; 
lean_inc(v_trace_963_);
v___x_2032_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___x_2025_, v___y_2021_, v___x_2026_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1097_ = v___y_2013_;
v___y_1098_ = v___y_2009_;
v___y_1099_ = v___y_2010_;
v___y_1100_ = v___y_2015_;
v___y_1101_ = v___y_2016_;
v___y_1102_ = v___y_2012_;
v___y_1103_ = v___y_2020_;
v___y_1104_ = v___x_2032_;
goto v___jp_1096_;
}
else
{
v___y_1743_ = v___y_2009_;
v___y_1744_ = v___y_2010_;
v___y_1745_ = v___x_2025_;
v___y_1746_ = v___y_2012_;
v___y_1747_ = v___x_2026_;
v___y_1748_ = v___y_2013_;
v___y_1749_ = v___y_2014_;
v___y_1750_ = v___y_2015_;
v___y_1751_ = v___y_2016_;
v___y_1752_ = v___x_2029_;
v___y_1753_ = v___y_2020_;
v___y_1754_ = v___y_2021_;
goto v___jp_1742_;
}
}
else
{
v___y_1743_ = v___y_2009_;
v___y_1744_ = v___y_2010_;
v___y_1745_ = v___x_2025_;
v___y_1746_ = v___y_2012_;
v___y_1747_ = v___x_2026_;
v___y_1748_ = v___y_2013_;
v___y_1749_ = v___y_2014_;
v___y_1750_ = v___y_2015_;
v___y_1751_ = v___y_2016_;
v___y_1752_ = v___x_2029_;
v___y_1753_ = v___y_2020_;
v___y_1754_ = v___y_2021_;
goto v___jp_1742_;
}
}
else
{
lean_object* v_val_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
lean_dec(v___y_2019_);
v_val_2033_ = lean_ctor_get(v_a_2024_, 0);
lean_inc(v_val_2033_);
lean_dec_ref_known(v_a_2024_, 1);
v___x_2034_ = l_List_appendTR___redArg(v_val_2033_, v___y_2021_);
v___x_2035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_2036_ = l_Lean_Name_append(v___x_2035_, v_trace_963_);
v___x_2037_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2011_, v___y_2013_, v___x_2036_);
lean_dec(v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = l_Lean_trace_profiler;
v___x_2039_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2013_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
lean_inc(v_trace_963_);
v___x_2040_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v_n_1878_, v___x_2034_, v_acc_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1097_ = v___y_2013_;
v___y_1098_ = v___y_2009_;
v___y_1099_ = v___y_2010_;
v___y_1100_ = v___y_2015_;
v___y_1101_ = v___y_2016_;
v___y_1102_ = v___y_2012_;
v___y_1103_ = v___y_2020_;
v___y_1104_ = v___x_2040_;
goto v___jp_1096_;
}
else
{
v___y_1959_ = v___y_2013_;
v___y_1960_ = v___y_2009_;
v___y_1961_ = v___y_2010_;
v___y_1962_ = v___x_2034_;
v___y_1963_ = v___y_2015_;
v___y_1964_ = v___y_2014_;
v___y_1965_ = v___y_2016_;
v___y_1966_ = v___y_2012_;
v___y_1967_ = v___y_2020_;
v___y_1968_ = v___x_2037_;
goto v___jp_1958_;
}
}
else
{
v___y_1959_ = v___y_2013_;
v___y_1960_ = v___y_2009_;
v___y_1961_ = v___y_2010_;
v___y_1962_ = v___x_2034_;
v___y_1963_ = v___y_2015_;
v___y_1964_ = v___y_2014_;
v___y_1965_ = v___y_2016_;
v___y_1966_ = v___y_2012_;
v___y_1967_ = v___y_2020_;
v___y_1968_ = v___x_2037_;
goto v___jp_1958_;
}
}
}
else
{
lean_object* v_a_2041_; 
lean_dec(v___y_2021_);
lean_dec(v___y_2019_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec_ref(v_cfg_962_);
v_a_2041_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2023_, 1);
v___y_1087_ = v___y_2009_;
v___y_1088_ = v___y_2013_;
v___y_1089_ = v___y_2010_;
v___y_1090_ = v___y_2015_;
v___y_1091_ = v___y_2016_;
v___y_1092_ = v___y_2012_;
v___y_1093_ = v___y_2020_;
v_a_1094_ = v_a_2041_;
goto v___jp_1086_;
}
}
else
{
lean_dec(v___y_2021_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec_ref(v_cfg_962_);
v___y_1087_ = v___y_2009_;
v___y_1088_ = v___y_2013_;
v___y_1089_ = v___y_2010_;
v___y_1090_ = v___y_2015_;
v___y_1091_ = v___y_2016_;
v___y_1092_ = v___y_2012_;
v___y_1093_ = v___y_2020_;
v_a_1094_ = v___y_2017_;
goto v___jp_1086_;
}
}
v___jp_2042_:
{
lean_object* v___x_2053_; 
v___x_2053_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
if (v___y_2048_ == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref(v___x_2053_);
v___x_2055_ = lean_io_mono_nanos_now();
lean_inc(v_trace_963_);
v___x_2056_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v_n_1878_, v___y_2044_, v_acc_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 1);
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
v___y_1539_ = v___y_2043_;
v___y_1540_ = v___y_2046_;
v___y_1541_ = v___y_2045_;
v___y_1542_ = v___y_2047_;
v___y_1543_ = v___y_2049_;
v___y_1544_ = v___y_2050_;
v___y_1545_ = v___x_2055_;
v___y_1546_ = v___y_2051_;
v___y_1547_ = v___y_2052_;
v___y_1548_ = v_a_2054_;
v_a_1549_ = v___x_2062_;
goto v___jp_1538_;
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
v_a_2065_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2056_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2056_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
lean_ctor_set_tag(v___x_2067_, 0);
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
v___y_1539_ = v___y_2043_;
v___y_1540_ = v___y_2046_;
v___y_1541_ = v___y_2045_;
v___y_1542_ = v___y_2047_;
v___y_1543_ = v___y_2049_;
v___y_1544_ = v___y_2050_;
v___y_1545_ = v___x_2055_;
v___y_1546_ = v___y_2051_;
v___y_1547_ = v___y_2052_;
v___y_1548_ = v_a_2054_;
v_a_1549_ = v___x_2070_;
goto v___jp_1538_;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v_a_2073_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2073_);
lean_dec_ref(v___x_2053_);
v___x_2074_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_963_);
v___x_2075_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v_n_1878_, v___y_2044_, v_acc_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 1);
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
v___y_1519_ = v___y_2043_;
v___y_1520_ = v___y_2046_;
v___y_1521_ = v___y_2045_;
v___y_1522_ = v___y_2047_;
v___y_1523_ = v___y_2049_;
v___y_1524_ = v___y_2050_;
v___y_1525_ = v___x_2074_;
v___y_1526_ = v___y_2051_;
v___y_1527_ = v___y_2052_;
v___y_1528_ = v_a_2073_;
v_a_1529_ = v___x_2081_;
goto v___jp_1518_;
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
v_a_2084_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2075_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2075_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
lean_ctor_set_tag(v___x_2086_, 0);
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
v___y_1519_ = v___y_2043_;
v___y_1520_ = v___y_2046_;
v___y_1521_ = v___y_2045_;
v___y_1522_ = v___y_2047_;
v___y_1523_ = v___y_2049_;
v___y_1524_ = v___y_2050_;
v___y_1525_ = v___x_2074_;
v___y_1526_ = v___y_2051_;
v___y_1527_ = v___y_2052_;
v___y_1528_ = v_a_2073_;
v_a_1529_ = v___x_2089_;
goto v___jp_1518_;
}
}
}
}
}
v___jp_2092_:
{
if (v___y_2106_ == 0)
{
lean_object* v___x_2107_; 
lean_dec_ref(v___y_2093_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v___y_2103_);
v___x_2107_ = lean_apply_6(v___y_2102_, v___y_2103_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
if (lean_obj_tag(v_a_2108_) == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2109_ = lean_nat_add(v_n_1878_, v_one_1877_);
lean_dec(v_n_1878_);
v___x_2110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___y_2103_);
lean_ctor_set(v___x_2110_, 1, v_acc_968_);
v___x_2111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_2112_ = l_Lean_Name_append(v___x_2111_, v_trace_963_);
v___x_2113_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2095_, v___y_2098_, v___x_2112_);
lean_dec(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = l_Lean_trace_profiler;
v___x_2115_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2098_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; 
lean_inc(v_trace_963_);
v___x_2116_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___x_2109_, v___y_2105_, v___x_2110_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1148_ = v___y_2098_;
v___y_1149_ = v___y_2094_;
v___y_1150_ = v___y_2100_;
v___y_1151_ = v___y_2101_;
v___y_1152_ = v___y_2096_;
v___y_1153_ = v___y_2097_;
v___y_1154_ = v___y_2104_;
v___y_1155_ = v___x_2116_;
goto v___jp_1147_;
}
else
{
v___y_1467_ = v___y_2094_;
v___y_1468_ = v___y_2096_;
v___y_1469_ = v___x_2113_;
v___y_1470_ = v___y_2097_;
v___y_1471_ = v___x_2109_;
v___y_1472_ = v___y_2098_;
v___y_1473_ = v___y_2099_;
v___y_1474_ = v___y_2100_;
v___y_1475_ = v___y_2101_;
v___y_1476_ = v___x_2110_;
v___y_1477_ = v___y_2104_;
v___y_1478_ = v___y_2105_;
goto v___jp_1466_;
}
}
else
{
v___y_1467_ = v___y_2094_;
v___y_1468_ = v___y_2096_;
v___y_1469_ = v___x_2113_;
v___y_1470_ = v___y_2097_;
v___y_1471_ = v___x_2109_;
v___y_1472_ = v___y_2098_;
v___y_1473_ = v___y_2099_;
v___y_1474_ = v___y_2100_;
v___y_1475_ = v___y_2101_;
v___y_1476_ = v___x_2110_;
v___y_1477_ = v___y_2104_;
v___y_1478_ = v___y_2105_;
goto v___jp_1466_;
}
}
else
{
lean_object* v_val_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
lean_dec(v___y_2103_);
v_val_2117_ = lean_ctor_get(v_a_2108_, 0);
lean_inc(v_val_2117_);
lean_dec_ref_known(v_a_2108_, 1);
v___x_2118_ = l_List_appendTR___redArg(v_val_2117_, v___y_2105_);
v___x_2119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_2120_ = l_Lean_Name_append(v___x_2119_, v_trace_963_);
v___x_2121_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2095_, v___y_2098_, v___x_2120_);
lean_dec(v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = l_Lean_trace_profiler;
v___x_2123_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2098_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; 
lean_inc(v_trace_963_);
v___x_2124_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v_n_1878_, v___x_2118_, v_acc_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1148_ = v___y_2098_;
v___y_1149_ = v___y_2094_;
v___y_1150_ = v___y_2100_;
v___y_1151_ = v___y_2101_;
v___y_1152_ = v___y_2096_;
v___y_1153_ = v___y_2097_;
v___y_1154_ = v___y_2104_;
v___y_1155_ = v___x_2124_;
goto v___jp_1147_;
}
else
{
v___y_2043_ = v___y_2098_;
v___y_2044_ = v___x_2118_;
v___y_2045_ = v___y_2094_;
v___y_2046_ = v___x_2121_;
v___y_2047_ = v___y_2100_;
v___y_2048_ = v___y_2099_;
v___y_2049_ = v___y_2101_;
v___y_2050_ = v___y_2096_;
v___y_2051_ = v___y_2097_;
v___y_2052_ = v___y_2104_;
goto v___jp_2042_;
}
}
else
{
v___y_2043_ = v___y_2098_;
v___y_2044_ = v___x_2118_;
v___y_2045_ = v___y_2094_;
v___y_2046_ = v___x_2121_;
v___y_2047_ = v___y_2100_;
v___y_2048_ = v___y_2099_;
v___y_2049_ = v___y_2101_;
v___y_2050_ = v___y_2096_;
v___y_2051_ = v___y_2097_;
v___y_2052_ = v___y_2104_;
goto v___jp_2042_;
}
}
}
else
{
lean_object* v_a_2125_; 
lean_dec(v___y_2105_);
lean_dec(v___y_2103_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec_ref(v_cfg_962_);
v_a_2125_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2107_, 1);
v___y_1138_ = v___y_2098_;
v___y_1139_ = v___y_2094_;
v___y_1140_ = v___y_2100_;
v___y_1141_ = v___y_2101_;
v___y_1142_ = v___y_2096_;
v___y_1143_ = v___y_2097_;
v___y_1144_ = v___y_2104_;
v_a_1145_ = v_a_2125_;
goto v___jp_1137_;
}
}
else
{
lean_dec(v___y_2105_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec_ref(v_cfg_962_);
v___y_1138_ = v___y_2098_;
v___y_1139_ = v___y_2094_;
v___y_1140_ = v___y_2100_;
v___y_1141_ = v___y_2101_;
v___y_1142_ = v___y_2096_;
v___y_1143_ = v___y_2097_;
v___y_1144_ = v___y_2104_;
v_a_1145_ = v___y_2093_;
goto v___jp_1137_;
}
}
v___jp_2126_:
{
lean_object* v___x_2139_; lean_object* v_a_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2139_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref(v___x_2139_);
v___x_2141_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2142_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2131_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
lean_dec_ref(v___y_2128_);
v___x_2143_ = lean_io_mono_nanos_now();
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v___y_2136_);
v___x_2144_ = lean_apply_6(v___y_2134_, v___y_2136_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; uint8_t v___x_2146_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = lean_unbox(v_a_2145_);
lean_dec(v_a_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_inc_ref(v_next_964_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v___y_2136_);
v___x_2147_ = lean_apply_7(v_next_964_, v___y_2136_, v___y_2130_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; 
lean_dec(v___y_2138_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec_ref(v_cfg_962_);
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v___y_1128_ = v___y_2131_;
v___y_1129_ = v___y_2127_;
v___y_1130_ = v___y_2132_;
v___y_1131_ = v___y_2133_;
v___y_1132_ = v___x_2143_;
v___y_1133_ = v_a_2140_;
v___y_1134_ = v___y_2137_;
v_a_1135_ = v_a_2148_;
goto v___jp_1127_;
}
else
{
lean_object* v_a_2149_; uint8_t v___x_2150_; 
v_a_2149_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2147_, 1);
v___x_2150_ = l_Lean_Exception_isInterrupt(v_a_2149_);
if (v___x_2150_ == 0)
{
uint8_t v___x_2151_; 
lean_inc(v_a_2149_);
v___x_2151_ = l_Lean_Exception_isRuntime(v_a_2149_);
v___y_2093_ = v_a_2149_;
v___y_2094_ = v___y_2127_;
v___y_2095_ = v___y_2129_;
v___y_2096_ = v___x_2143_;
v___y_2097_ = v_a_2140_;
v___y_2098_ = v___y_2131_;
v___y_2099_ = v___x_2142_;
v___y_2100_ = v___y_2132_;
v___y_2101_ = v___y_2133_;
v___y_2102_ = v___y_2135_;
v___y_2103_ = v___y_2136_;
v___y_2104_ = v___y_2137_;
v___y_2105_ = v___y_2138_;
v___y_2106_ = v___x_2151_;
goto v___jp_2092_;
}
else
{
v___y_2093_ = v_a_2149_;
v___y_2094_ = v___y_2127_;
v___y_2095_ = v___y_2129_;
v___y_2096_ = v___x_2143_;
v___y_2097_ = v_a_2140_;
v___y_2098_ = v___y_2131_;
v___y_2099_ = v___x_2142_;
v___y_2100_ = v___y_2132_;
v___y_2101_ = v___y_2133_;
v___y_2102_ = v___y_2135_;
v___y_2103_ = v___y_2136_;
v___y_2104_ = v___y_2137_;
v___y_2105_ = v___y_2138_;
v___y_2106_ = v___x_2150_;
goto v___jp_2092_;
}
}
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
lean_dec_ref(v___y_2135_);
lean_dec_ref(v___y_2130_);
v___x_2152_ = lean_nat_add(v_n_1878_, v_one_1877_);
lean_dec(v_n_1878_);
v___x_2153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___y_2136_);
lean_ctor_set(v___x_2153_, 1, v_acc_968_);
v___x_2154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_2155_ = l_Lean_Name_append(v___x_2154_, v_trace_963_);
v___x_2156_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2129_, v___y_2131_, v___x_2155_);
lean_dec(v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = l_Lean_trace_profiler;
v___x_2158_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2131_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; 
lean_inc(v_trace_963_);
v___x_2159_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___x_2152_, v___y_2138_, v___x_2153_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1148_ = v___y_2131_;
v___y_1149_ = v___y_2127_;
v___y_1150_ = v___y_2132_;
v___y_1151_ = v___y_2133_;
v___y_1152_ = v___x_2143_;
v___y_1153_ = v_a_2140_;
v___y_1154_ = v___y_2137_;
v___y_1155_ = v___x_2159_;
goto v___jp_1147_;
}
else
{
v___y_1605_ = v___y_2127_;
v___y_1606_ = v___x_2153_;
v___y_1607_ = v___x_2143_;
v___y_1608_ = v___x_2152_;
v___y_1609_ = v_a_2140_;
v___y_1610_ = v___x_2156_;
v___y_1611_ = v___y_2131_;
v___y_1612_ = v___x_2142_;
v___y_1613_ = v___y_2132_;
v___y_1614_ = v___y_2133_;
v___y_1615_ = v___y_2137_;
v___y_1616_ = v___y_2138_;
goto v___jp_1604_;
}
}
else
{
v___y_1605_ = v___y_2127_;
v___y_1606_ = v___x_2153_;
v___y_1607_ = v___x_2143_;
v___y_1608_ = v___x_2152_;
v___y_1609_ = v_a_2140_;
v___y_1610_ = v___x_2156_;
v___y_1611_ = v___y_2131_;
v___y_1612_ = v___x_2142_;
v___y_1613_ = v___y_2132_;
v___y_1614_ = v___y_2133_;
v___y_1615_ = v___y_2137_;
v___y_1616_ = v___y_2138_;
goto v___jp_1604_;
}
}
}
else
{
lean_object* v_a_2160_; 
lean_dec(v___y_2138_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec_ref(v___y_2130_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec_ref(v_cfg_962_);
v_a_2160_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2144_, 1);
v___y_1138_ = v___y_2131_;
v___y_1139_ = v___y_2127_;
v___y_1140_ = v___y_2132_;
v___y_1141_ = v___y_2133_;
v___y_1142_ = v___x_2143_;
v___y_1143_ = v_a_2140_;
v___y_1144_ = v___y_2137_;
v_a_1145_ = v_a_2160_;
goto v___jp_1137_;
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec_ref(v___y_2130_);
v___x_2161_ = lean_io_get_num_heartbeats();
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v___y_2136_);
v___x_2162_ = lean_apply_6(v___y_2134_, v___y_2136_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; uint8_t v___x_2164_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2164_ = lean_unbox(v_a_2163_);
lean_dec(v_a_2163_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; 
lean_inc_ref(v_next_964_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v___y_2136_);
v___x_2165_ = lean_apply_7(v_next_964_, v___y_2136_, v___y_2128_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; 
lean_dec(v___y_2138_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec_ref(v_cfg_962_);
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v___y_1077_ = v___x_2161_;
v___y_1078_ = v___y_2131_;
v___y_1079_ = v___y_2127_;
v___y_1080_ = v___y_2132_;
v___y_1081_ = v___y_2133_;
v___y_1082_ = v_a_2140_;
v___y_1083_ = v___y_2137_;
v_a_1084_ = v_a_2166_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_2167_; uint8_t v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2168_ = l_Lean_Exception_isInterrupt(v_a_2167_);
if (v___x_2168_ == 0)
{
uint8_t v___x_2169_; 
lean_inc(v_a_2167_);
v___x_2169_ = l_Lean_Exception_isRuntime(v_a_2167_);
v___y_2009_ = v___x_2161_;
v___y_2010_ = v___y_2127_;
v___y_2011_ = v___y_2129_;
v___y_2012_ = v_a_2140_;
v___y_2013_ = v___y_2131_;
v___y_2014_ = v___x_2142_;
v___y_2015_ = v___y_2132_;
v___y_2016_ = v___y_2133_;
v___y_2017_ = v_a_2167_;
v___y_2018_ = v___y_2135_;
v___y_2019_ = v___y_2136_;
v___y_2020_ = v___y_2137_;
v___y_2021_ = v___y_2138_;
v___y_2022_ = v___x_2169_;
goto v___jp_2008_;
}
else
{
v___y_2009_ = v___x_2161_;
v___y_2010_ = v___y_2127_;
v___y_2011_ = v___y_2129_;
v___y_2012_ = v_a_2140_;
v___y_2013_ = v___y_2131_;
v___y_2014_ = v___x_2142_;
v___y_2015_ = v___y_2132_;
v___y_2016_ = v___y_2133_;
v___y_2017_ = v_a_2167_;
v___y_2018_ = v___y_2135_;
v___y_2019_ = v___y_2136_;
v___y_2020_ = v___y_2137_;
v___y_2021_ = v___y_2138_;
v___y_2022_ = v___x_2168_;
goto v___jp_2008_;
}
}
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
lean_dec_ref(v___y_2135_);
lean_dec_ref(v___y_2128_);
v___x_2170_ = lean_nat_add(v_n_1878_, v_one_1877_);
lean_dec(v_n_1878_);
v___x_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___y_2136_);
lean_ctor_set(v___x_2171_, 1, v_acc_968_);
v___x_2172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_2173_ = l_Lean_Name_append(v___x_2172_, v_trace_963_);
v___x_2174_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2129_, v___y_2131_, v___x_2173_);
lean_dec(v___x_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2175_ = l_Lean_trace_profiler;
v___x_2176_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2131_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; 
lean_inc(v_trace_963_);
v___x_2177_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___x_2170_, v___y_2138_, v___x_2171_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
v___y_1097_ = v___y_2131_;
v___y_1098_ = v___x_2161_;
v___y_1099_ = v___y_2127_;
v___y_1100_ = v___y_2132_;
v___y_1101_ = v___y_2133_;
v___y_1102_ = v_a_2140_;
v___y_1103_ = v___y_2137_;
v___y_1104_ = v___x_2177_;
goto v___jp_1096_;
}
else
{
v___y_1372_ = v___x_2161_;
v___y_1373_ = v___y_2127_;
v___y_1374_ = v_a_2140_;
v___y_1375_ = v___y_2131_;
v___y_1376_ = v___x_2142_;
v___y_1377_ = v___y_2132_;
v___y_1378_ = v___y_2133_;
v___y_1379_ = v___x_2174_;
v___y_1380_ = v___x_2170_;
v___y_1381_ = v___x_2171_;
v___y_1382_ = v___y_2137_;
v___y_1383_ = v___y_2138_;
goto v___jp_1371_;
}
}
else
{
v___y_1372_ = v___x_2161_;
v___y_1373_ = v___y_2127_;
v___y_1374_ = v_a_2140_;
v___y_1375_ = v___y_2131_;
v___y_1376_ = v___x_2142_;
v___y_1377_ = v___y_2132_;
v___y_1378_ = v___y_2133_;
v___y_1379_ = v___x_2174_;
v___y_1380_ = v___x_2170_;
v___y_1381_ = v___x_2171_;
v___y_1382_ = v___y_2137_;
v___y_1383_ = v___y_2138_;
goto v___jp_1371_;
}
}
}
else
{
lean_object* v_a_2178_; 
lean_dec(v___y_2138_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec_ref(v___y_2128_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec_ref(v_cfg_962_);
v_a_2178_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2162_, 1);
v___y_1087_ = v___x_2161_;
v___y_1088_ = v___y_2131_;
v___y_1089_ = v___y_2127_;
v___y_1090_ = v___y_2132_;
v___y_1091_ = v___y_2133_;
v___y_1092_ = v_a_2140_;
v___y_1093_ = v___y_2137_;
v_a_1094_ = v_a_2178_;
goto v___jp_1086_;
}
}
}
v___jp_2179_:
{
if (v___y_2184_ == 0)
{
lean_object* v___x_2185_; 
lean_dec_ref(v___y_2182_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v___y_2181_);
v___x_2185_ = lean_apply_6(v___y_2180_, v___y_2181_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
if (lean_obj_tag(v_a_2186_) == 0)
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = lean_nat_add(v_n_1878_, v_one_1877_);
lean_dec(v_n_1878_);
v___x_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___y_2181_);
lean_ctor_set(v___x_2188_, 1, v_acc_968_);
v_n_966_ = v___x_2187_;
v_curr_967_ = v___y_2183_;
v_acc_968_ = v___x_2188_;
goto _start;
}
else
{
lean_object* v_val_2190_; lean_object* v___x_2191_; 
lean_dec(v___y_2181_);
v_val_2190_ = lean_ctor_get(v_a_2186_, 0);
lean_inc(v_val_2190_);
lean_dec_ref_known(v_a_2186_, 1);
v___x_2191_ = l_List_appendTR___redArg(v_val_2190_, v___y_2183_);
v_n_966_ = v_n_1878_;
v_curr_967_ = v___x_2191_;
goto _start;
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v___y_2183_);
lean_dec(v___y_2181_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
v_a_2193_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2185_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2185_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_dec(v___y_2183_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
return v___y_2182_;
}
}
v___jp_2201_:
{
if (lean_obj_tag(v_a_2202_) == 0)
{
if (lean_obj_tag(v_curr_967_) == 0)
{
lean_object* v_toCold_2203_; lean_object* v_options_2204_; lean_object* v_inheritedTraceOptions_2205_; uint8_t v_hasTrace_2206_; lean_object* v___x_2207_; 
lean_dec(v_n_1878_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec_ref(v_cfg_962_);
v_toCold_2203_ = lean_ctor_get(v_a_971_, 0);
v_options_2204_ = lean_ctor_get(v_toCold_2203_, 2);
v_inheritedTraceOptions_2205_ = lean_ctor_get(v_toCold_2203_, 11);
v_hasTrace_2206_ = lean_ctor_get_uint8(v_options_2204_, sizeof(void*)*1);
v___x_2207_ = l_List_reverse___redArg(v_acc_968_);
if (v_hasTrace_2206_ == 0)
{
lean_object* v___x_2208_; 
lean_dec(v_trace_963_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_2211_ = l_Lean_Name_append(v___x_2210_, v_trace_963_);
v___x_2212_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2205_, v_options_2204_, v___x_2211_);
lean_dec(v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = l_Lean_trace_profiler;
v___x_2214_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2204_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; 
lean_dec(v_trace_963_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2207_);
return v___x_2215_;
}
else
{
v___y_1167_ = v___x_2209_;
v___y_1168_ = v___x_2207_;
v___y_1169_ = v_hasTrace_2206_;
v___y_1170_ = v___x_2212_;
v___y_1171_ = v_options_2204_;
goto v___jp_1166_;
}
}
else
{
v___y_1167_ = v___x_2209_;
v___y_1168_ = v___x_2207_;
v___y_1169_ = v_hasTrace_2206_;
v___y_1170_ = v___x_2212_;
v___y_1171_ = v_options_2204_;
goto v___jp_1166_;
}
}
}
else
{
lean_object* v_head_2216_; lean_object* v_tail_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2291_; 
v_head_2216_ = lean_ctor_get(v_curr_967_, 0);
v_tail_2217_ = lean_ctor_get(v_curr_967_, 1);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_curr_967_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2219_ = v_curr_967_;
v_isShared_2220_ = v_isSharedCheck_2291_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_tail_2217_);
lean_inc(v_head_2216_);
lean_dec(v_curr_967_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2291_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___f_2221_; lean_object* v___f_2222_; lean_object* v___f_2223_; lean_object* v___x_2224_; lean_object* v_a_2225_; uint8_t v___x_2226_; uint8_t v___x_2227_; 
lean_inc(v_acc_968_);
lean_inc(v_n_1878_);
lean_inc(v_goals_965_);
lean_inc_ref(v_next_964_);
lean_inc(v_trace_963_);
lean_inc_ref(v_cfg_962_);
lean_inc(v_tail_2217_);
v___f_2221_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2221_, 0, v_tail_2217_);
lean_closure_set(v___f_2221_, 1, v_cfg_962_);
lean_closure_set(v___f_2221_, 2, v_trace_963_);
lean_closure_set(v___f_2221_, 3, v_next_964_);
lean_closure_set(v___f_2221_, 4, v_goals_965_);
lean_closure_set(v___f_2221_, 5, v_n_1878_);
lean_closure_set(v___f_2221_, 6, v_acc_968_);
lean_inc_n(v_head_2216_, 2);
v___f_2222_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___boxed), 7, 1);
lean_closure_set(v___f_2222_, 0, v_head_2216_);
v___f_2223_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(v___f_2223_, 0, v_head_2216_);
v___x_2224_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2216_, v_a_970_);
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = 1;
v___x_2227_ = lean_unbox(v_a_2225_);
lean_dec(v_a_2225_);
if (v___x_2227_ == 0)
{
lean_object* v_toCold_2228_; lean_object* v_options_2229_; uint8_t v_hasTrace_2230_; 
lean_dec_ref(v___f_2222_);
v_toCold_2228_ = lean_ctor_get(v_a_971_, 0);
v_options_2229_ = lean_ctor_get(v_toCold_2228_, 2);
v_hasTrace_2230_ = lean_ctor_get_uint8(v_options_2229_, sizeof(void*)*1);
if (v_hasTrace_2230_ == 0)
{
lean_object* v___x_2231_; 
lean_dec_ref(v___f_2223_);
lean_inc_ref(v_suspend_1163_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_head_2216_);
v___x_2231_ = lean_apply_6(v_suspend_1163_, v_head_2216_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; uint8_t v___x_2233_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
v___x_2233_ = lean_unbox(v_a_2232_);
lean_dec(v_a_2232_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; 
lean_del_object(v___x_2219_);
lean_inc_ref(v_next_964_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_head_2216_);
v___x_2234_ = lean_apply_7(v_next_964_, v_head_2216_, v___f_2221_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_dec(v_tail_2217_);
lean_dec(v_head_2216_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
return v___x_2234_;
}
else
{
lean_object* v_a_2235_; uint8_t v___x_2236_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
v___x_2236_ = l_Lean_Exception_isInterrupt(v_a_2235_);
if (v___x_2236_ == 0)
{
uint8_t v___x_2237_; 
v___x_2237_ = l_Lean_Exception_isRuntime(v_a_2235_);
lean_inc_ref(v_discharge_1164_);
v___y_2180_ = v_discharge_1164_;
v___y_2181_ = v_head_2216_;
v___y_2182_ = v___x_2234_;
v___y_2183_ = v_tail_2217_;
v___y_2184_ = v___x_2237_;
goto v___jp_2179_;
}
else
{
lean_dec(v_a_2235_);
lean_inc_ref(v_discharge_1164_);
v___y_2180_ = v_discharge_1164_;
v___y_2181_ = v_head_2216_;
v___y_2182_ = v___x_2234_;
v___y_2183_ = v_tail_2217_;
v___y_2184_ = v___x_2236_;
goto v___jp_2179_;
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2240_; 
lean_dec_ref(v___f_2221_);
v___x_2238_ = lean_nat_add(v_n_1878_, v_one_1877_);
lean_dec(v_n_1878_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v_acc_968_);
v___x_2240_ = v___x_2219_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_head_2216_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_acc_968_);
v___x_2240_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
v_n_966_ = v___x_2238_;
v_curr_967_ = v_tail_2217_;
v_acc_968_ = v___x_2240_;
goto _start;
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec_ref(v___f_2221_);
lean_del_object(v___x_2219_);
lean_dec(v_tail_2217_);
lean_dec(v_head_2216_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
v_a_2243_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2231_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2231_);
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
lean_object* v_inheritedTraceOptions_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v_inheritedTraceOptions_2251_ = lean_ctor_get(v_toCold_2228_, 11);
v___x_2252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_2254_ = l_Lean_Name_append(v___x_2253_, v_trace_963_);
v___x_2255_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2251_, v_options_2229_, v___x_2254_);
lean_dec(v___x_2254_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2256_ = l_Lean_trace_profiler;
v___x_2257_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2229_, v___x_2256_);
if (v___x_2257_ == 0)
{
lean_object* v___x_2258_; 
lean_dec_ref(v___f_2223_);
lean_inc_ref(v_suspend_1163_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_head_2216_);
v___x_2258_ = lean_apply_6(v_suspend_1163_, v_head_2216_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; uint8_t v___x_2260_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref_known(v___x_2258_, 1);
v___x_2260_ = lean_unbox(v_a_2259_);
lean_dec(v_a_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; 
lean_del_object(v___x_2219_);
lean_inc_ref(v_next_964_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_head_2216_);
v___x_2261_ = lean_apply_7(v_next_964_, v_head_2216_, v___f_2221_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, lean_box(0));
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_dec(v_tail_2217_);
lean_dec(v_head_2216_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
return v___x_2261_;
}
else
{
lean_object* v_a_2262_; uint8_t v___x_2263_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
v___x_2263_ = l_Lean_Exception_isInterrupt(v_a_2262_);
if (v___x_2263_ == 0)
{
uint8_t v___x_2264_; 
v___x_2264_ = l_Lean_Exception_isRuntime(v_a_2262_);
lean_inc_ref(v_discharge_1164_);
v___y_1926_ = v_options_2229_;
v___y_1927_ = v___x_2252_;
v___y_1928_ = v___x_2226_;
v___y_1929_ = v_inheritedTraceOptions_2251_;
v___y_1930_ = v___x_2257_;
v___y_1931_ = v_discharge_1164_;
v___y_1932_ = v___x_2261_;
v___y_1933_ = v_head_2216_;
v___y_1934_ = v_tail_2217_;
v___y_1935_ = v___x_2264_;
goto v___jp_1925_;
}
else
{
lean_dec(v_a_2262_);
lean_inc_ref(v_discharge_1164_);
v___y_1926_ = v_options_2229_;
v___y_1927_ = v___x_2252_;
v___y_1928_ = v___x_2226_;
v___y_1929_ = v_inheritedTraceOptions_2251_;
v___y_1930_ = v___x_2257_;
v___y_1931_ = v_discharge_1164_;
v___y_1932_ = v___x_2261_;
v___y_1933_ = v_head_2216_;
v___y_1934_ = v_tail_2217_;
v___y_1935_ = v___x_2263_;
goto v___jp_1925_;
}
}
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
lean_dec_ref(v___f_2221_);
v___x_2265_ = lean_nat_add(v_n_1878_, v_one_1877_);
lean_dec(v_n_1878_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 1, v_acc_968_);
v___x_2267_ = v___x_2219_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_head_2216_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_acc_968_);
v___x_2267_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
if (v___x_2255_ == 0)
{
if (v___x_2257_ == 0)
{
v_n_966_ = v___x_2265_;
v_curr_967_ = v_tail_2217_;
v_acc_968_ = v___x_2267_;
goto _start;
}
else
{
v___y_1830_ = v_options_2229_;
v___y_1831_ = v___x_2252_;
v___y_1832_ = v___x_2226_;
v___y_1833_ = v___x_2267_;
v___y_1834_ = v___x_2265_;
v___y_1835_ = v___x_2255_;
v___y_1836_ = v_tail_2217_;
goto v___jp_1829_;
}
}
else
{
v___y_1830_ = v_options_2229_;
v___y_1831_ = v___x_2252_;
v___y_1832_ = v___x_2226_;
v___y_1833_ = v___x_2267_;
v___y_1834_ = v___x_2265_;
v___y_1835_ = v___x_2255_;
v___y_1836_ = v_tail_2217_;
goto v___jp_1829_;
}
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v___f_2221_);
lean_del_object(v___x_2219_);
lean_dec(v_tail_2217_);
lean_dec(v_head_2216_);
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
v_a_2270_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2258_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2258_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_del_object(v___x_2219_);
lean_inc_ref(v_discharge_1164_);
lean_inc_ref(v_suspend_1163_);
lean_inc_ref(v___f_2221_);
v___y_2127_ = v___x_2252_;
v___y_2128_ = v___f_2221_;
v___y_2129_ = v_inheritedTraceOptions_2251_;
v___y_2130_ = v___f_2221_;
v___y_2131_ = v_options_2229_;
v___y_2132_ = v___x_2255_;
v___y_2133_ = v___x_2226_;
v___y_2134_ = v_suspend_1163_;
v___y_2135_ = v_discharge_1164_;
v___y_2136_ = v_head_2216_;
v___y_2137_ = v___f_2223_;
v___y_2138_ = v_tail_2217_;
goto v___jp_2126_;
}
}
else
{
lean_del_object(v___x_2219_);
lean_inc_ref(v_discharge_1164_);
lean_inc_ref(v_suspend_1163_);
lean_inc_ref(v___f_2221_);
v___y_2127_ = v___x_2252_;
v___y_2128_ = v___f_2221_;
v___y_2129_ = v_inheritedTraceOptions_2251_;
v___y_2130_ = v___f_2221_;
v___y_2131_ = v_options_2229_;
v___y_2132_ = v___x_2255_;
v___y_2133_ = v___x_2226_;
v___y_2134_ = v_suspend_1163_;
v___y_2135_ = v_discharge_1164_;
v___y_2136_ = v_head_2216_;
v___y_2137_ = v___f_2223_;
v___y_2138_ = v_tail_2217_;
goto v___jp_2126_;
}
}
}
else
{
lean_object* v_toCold_2278_; lean_object* v_options_2279_; lean_object* v_inheritedTraceOptions_2280_; uint8_t v_hasTrace_2281_; lean_object* v___x_2282_; 
lean_dec_ref(v___f_2223_);
lean_dec_ref(v___f_2221_);
lean_del_object(v___x_2219_);
lean_dec(v_head_2216_);
v_toCold_2278_ = lean_ctor_get(v_a_971_, 0);
v_options_2279_ = lean_ctor_get(v_toCold_2278_, 2);
v_inheritedTraceOptions_2280_ = lean_ctor_get(v_toCold_2278_, 11);
v_hasTrace_2281_ = lean_ctor_get_uint8(v_options_2279_, sizeof(void*)*1);
v___x_2282_ = lean_nat_add(v_n_1878_, v_one_1877_);
lean_dec(v_n_1878_);
if (v_hasTrace_2281_ == 0)
{
lean_dec_ref(v___f_2222_);
v_n_966_ = v___x_2282_;
v_curr_967_ = v_tail_2217_;
goto _start;
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_963_);
v___x_2286_ = l_Lean_Name_append(v___x_2285_, v_trace_963_);
v___x_2287_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2280_, v_options_2279_, v___x_2286_);
lean_dec(v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2288_ = l_Lean_trace_profiler;
v___x_2289_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2279_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_dec_ref(v___f_2222_);
v_n_966_ = v___x_2282_;
v_curr_967_ = v_tail_2217_;
goto _start;
}
else
{
v___y_1012_ = v_options_2279_;
v___y_1013_ = v___x_2226_;
v___y_1014_ = v___x_2284_;
v___y_1015_ = v___x_2282_;
v___y_1016_ = v___x_2287_;
v___y_1017_ = v___f_2222_;
v___y_1018_ = v_tail_2217_;
goto v___jp_1011_;
}
}
else
{
v___y_1012_ = v_options_2279_;
v___y_1013_ = v___x_2226_;
v___y_1014_ = v___x_2284_;
v___y_1015_ = v___x_2282_;
v___y_1016_ = v___x_2287_;
v___y_1017_ = v___f_2222_;
v___y_1018_ = v_tail_2217_;
goto v___jp_1011_;
}
}
}
}
}
}
else
{
lean_object* v_val_2292_; 
lean_dec(v_curr_967_);
v_val_2292_ = lean_ctor_get(v_a_2202_, 0);
lean_inc(v_val_2292_);
lean_dec_ref_known(v_a_2202_, 1);
v_n_966_ = v_n_1878_;
v_curr_967_ = v_val_2292_;
goto _start;
}
}
v___jp_2294_:
{
if (lean_obj_tag(v___y_2295_) == 0)
{
lean_object* v_a_2296_; 
v_a_2296_ = lean_ctor_get(v___y_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___y_2295_, 1);
v_a_2202_ = v_a_2296_;
goto v___jp_2201_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v_n_1878_);
lean_dec(v_acc_968_);
lean_dec(v_curr_967_);
lean_dec(v_goals_965_);
lean_dec_ref(v_next_964_);
lean_dec(v_trace_963_);
lean_dec_ref(v_cfg_962_);
v_a_2297_ = lean_ctor_get(v___y_2295_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___y_2295_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___y_2295_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___y_2295_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
v___jp_974_:
{
lean_object* v___x_983_; double v___x_984_; double v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_983_ = lean_io_get_num_heartbeats();
v___x_984_ = lean_float_of_nat(v___y_981_);
v___x_985_ = lean_float_of_nat(v___x_983_);
v___x_986_ = lean_box_float(v___x_984_);
v___x_987_ = lean_box_float(v___x_985_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v_a_982_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
lean_inc_ref(v___y_977_);
v___x_990_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_976_, v___y_977_, v___y_975_, v___y_978_, v___y_980_, v___y_979_, v___x_989_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_990_;
}
v___jp_991_:
{
lean_object* v___x_1000_; double v___x_1001_; double v___x_1002_; double v___x_1003_; double v___x_1004_; double v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1000_ = lean_io_mono_nanos_now();
v___x_1001_ = lean_float_of_nat(v___y_993_);
v___x_1002_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1003_ = lean_float_div(v___x_1001_, v___x_1002_);
v___x_1004_ = lean_float_of_nat(v___x_1000_);
v___x_1005_ = lean_float_div(v___x_1004_, v___x_1002_);
v___x_1006_ = lean_box_float(v___x_1003_);
v___x_1007_ = lean_box_float(v___x_1005_);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_a_999_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
lean_inc_ref(v___y_995_);
v___x_1010_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_994_, v___y_995_, v___y_992_, v___y_996_, v___y_998_, v___y_997_, v___x_1009_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1010_;
}
v___jp_1011_:
{
lean_object* v___x_1019_; lean_object* v_a_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1019_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_972_);
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref(v___x_1019_);
v___x_1021_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1022_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1012_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_io_mono_nanos_now();
lean_inc(v_trace_963_);
v___x_1024_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1015_, v___y_1018_, v_acc_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 1);
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
v___y_992_ = v___y_1012_;
v___y_993_ = v___x_1023_;
v___y_994_ = v___y_1013_;
v___y_995_ = v___y_1014_;
v___y_996_ = v___y_1016_;
v___y_997_ = v___y_1017_;
v___y_998_ = v_a_1020_;
v_a_999_ = v___x_1030_;
goto v___jp_991_;
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
v_a_1033_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1024_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1024_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set_tag(v___x_1035_, 0);
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
v___y_992_ = v___y_1012_;
v___y_993_ = v___x_1023_;
v___y_994_ = v___y_1013_;
v___y_995_ = v___y_1014_;
v___y_996_ = v___y_1016_;
v___y_997_ = v___y_1017_;
v___y_998_ = v_a_1020_;
v_a_999_ = v___x_1038_;
goto v___jp_991_;
}
}
}
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_963_);
v___x_1042_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_962_, v_trace_963_, v_next_964_, v_goals_965_, v___y_1015_, v___y_1018_, v_acc_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 1);
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
v___y_975_ = v___y_1012_;
v___y_976_ = v___y_1013_;
v___y_977_ = v___y_1014_;
v___y_978_ = v___y_1016_;
v___y_979_ = v___y_1017_;
v___y_980_ = v_a_1020_;
v___y_981_ = v___x_1041_;
v_a_982_ = v___x_1048_;
goto v___jp_974_;
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
v_a_1051_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1042_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1042_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 0);
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
v___y_975_ = v___y_1012_;
v___y_976_ = v___y_1013_;
v___y_977_ = v___y_1014_;
v___y_978_ = v___y_1016_;
v___y_979_ = v___y_1017_;
v___y_980_ = v_a_1020_;
v___y_981_ = v___x_1041_;
v_a_982_ = v___x_1056_;
goto v___jp_974_;
}
}
}
}
}
v___jp_1059_:
{
lean_object* v___x_1068_; double v___x_1069_; double v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1068_ = lean_io_get_num_heartbeats();
v___x_1069_ = lean_float_of_nat(v___y_1061_);
v___x_1070_ = lean_float_of_nat(v___x_1068_);
v___x_1071_ = lean_box_float(v___x_1069_);
v___x_1072_ = lean_box_float(v___x_1070_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_a_1067_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
lean_inc_ref(v___y_1062_);
v___x_1075_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1064_, v___y_1062_, v___y_1060_, v___y_1063_, v___y_1065_, v___y_1066_, v___x_1074_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1075_;
}
v___jp_1076_:
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_a_1084_);
v___y_1060_ = v___y_1078_;
v___y_1061_ = v___y_1077_;
v___y_1062_ = v___y_1079_;
v___y_1063_ = v___y_1080_;
v___y_1064_ = v___y_1081_;
v___y_1065_ = v___y_1082_;
v___y_1066_ = v___y_1083_;
v_a_1067_ = v___x_1085_;
goto v___jp_1059_;
}
v___jp_1086_:
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_a_1094_);
v___y_1060_ = v___y_1088_;
v___y_1061_ = v___y_1087_;
v___y_1062_ = v___y_1089_;
v___y_1063_ = v___y_1090_;
v___y_1064_ = v___y_1091_;
v___y_1065_ = v___y_1092_;
v___y_1066_ = v___y_1093_;
v_a_1067_ = v___x_1095_;
goto v___jp_1059_;
}
v___jp_1096_:
{
if (lean_obj_tag(v___y_1104_) == 0)
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v___y_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___y_1104_, 1);
v___y_1077_ = v___y_1098_;
v___y_1078_ = v___y_1097_;
v___y_1079_ = v___y_1099_;
v___y_1080_ = v___y_1100_;
v___y_1081_ = v___y_1101_;
v___y_1082_ = v___y_1102_;
v___y_1083_ = v___y_1103_;
v_a_1084_ = v_a_1105_;
goto v___jp_1076_;
}
else
{
lean_object* v_a_1106_; 
v_a_1106_ = lean_ctor_get(v___y_1104_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___y_1104_, 1);
v___y_1087_ = v___y_1098_;
v___y_1088_ = v___y_1097_;
v___y_1089_ = v___y_1099_;
v___y_1090_ = v___y_1100_;
v___y_1091_ = v___y_1101_;
v___y_1092_ = v___y_1102_;
v___y_1093_ = v___y_1103_;
v_a_1094_ = v_a_1106_;
goto v___jp_1086_;
}
}
v___jp_1107_:
{
lean_object* v___x_1116_; double v___x_1117_; double v___x_1118_; double v___x_1119_; double v___x_1120_; double v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1116_ = lean_io_mono_nanos_now();
v___x_1117_ = lean_float_of_nat(v___y_1112_);
v___x_1118_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1119_ = lean_float_div(v___x_1117_, v___x_1118_);
v___x_1120_ = lean_float_of_nat(v___x_1116_);
v___x_1121_ = lean_float_div(v___x_1120_, v___x_1118_);
v___x_1122_ = lean_box_float(v___x_1119_);
v___x_1123_ = lean_box_float(v___x_1121_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v_a_1115_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
lean_inc_ref(v___y_1109_);
v___x_1126_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_963_, v___y_1111_, v___y_1109_, v___y_1108_, v___y_1110_, v___y_1113_, v___y_1114_, v___x_1125_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1126_;
}
v___jp_1127_:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_a_1135_);
v___y_1108_ = v___y_1128_;
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___y_1130_;
v___y_1111_ = v___y_1131_;
v___y_1112_ = v___y_1132_;
v___y_1113_ = v___y_1133_;
v___y_1114_ = v___y_1134_;
v_a_1115_ = v___x_1136_;
goto v___jp_1107_;
}
v___jp_1137_:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_a_1145_);
v___y_1108_ = v___y_1138_;
v___y_1109_ = v___y_1139_;
v___y_1110_ = v___y_1140_;
v___y_1111_ = v___y_1141_;
v___y_1112_ = v___y_1142_;
v___y_1113_ = v___y_1143_;
v___y_1114_ = v___y_1144_;
v_a_1115_ = v___x_1146_;
goto v___jp_1107_;
}
v___jp_1147_:
{
if (lean_obj_tag(v___y_1155_) == 0)
{
lean_object* v_a_1156_; 
v_a_1156_ = lean_ctor_get(v___y_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___y_1155_, 1);
v___y_1128_ = v___y_1148_;
v___y_1129_ = v___y_1149_;
v___y_1130_ = v___y_1150_;
v___y_1131_ = v___y_1151_;
v___y_1132_ = v___y_1152_;
v___y_1133_ = v___y_1153_;
v___y_1134_ = v___y_1154_;
v_a_1135_ = v_a_1156_;
goto v___jp_1127_;
}
else
{
lean_object* v_a_1157_; 
v_a_1157_ = lean_ctor_get(v___y_1155_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___y_1155_, 1);
v___y_1138_ = v___y_1148_;
v___y_1139_ = v___y_1149_;
v___y_1140_ = v___y_1150_;
v___y_1141_ = v___y_1151_;
v___y_1142_ = v___y_1152_;
v___y_1143_ = v___y_1153_;
v___y_1144_ = v___y_1154_;
v_a_1145_ = v_a_1157_;
goto v___jp_1137_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2376_, lean_object* v_trace_2377_, lean_object* v_next_2378_, lean_object* v_goals_2379_, lean_object* v_n_2380_, lean_object* v_curr_2381_, lean_object* v_acc_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2376_, v_trace_2377_, v_next_2378_, v_goals_2379_, v_n_2380_, v_curr_2381_, v_acc_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object* v_tail_2389_, lean_object* v_cfg_2390_, lean_object* v_trace_2391_, lean_object* v_next_2392_, lean_object* v_goals_2393_, lean_object* v_n_2394_, lean_object* v_acc_2395_, lean_object* v_r_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = l_List_appendTR___redArg(v_r_2396_, v_tail_2389_);
v___x_2403_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2403_, 0, v_cfg_2390_);
lean_closure_set(v___x_2403_, 1, v_trace_2391_);
lean_closure_set(v___x_2403_, 2, v_next_2392_);
lean_closure_set(v___x_2403_, 3, v_goals_2393_);
lean_closure_set(v___x_2403_, 4, v_n_2394_);
lean_closure_set(v___x_2403_, 5, v___x_2402_);
lean_closure_set(v___x_2403_, 6, v_acc_2395_);
v___x_2404_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v___x_2403_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2405_, lean_object* v_msg_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2413_, lean_object* v_msg_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2413_, v_msg_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object* v_00_u03b1_2421_, lean_object* v_x_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_2422_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2429_, lean_object* v_x_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_00_u03b1_2429_, v_x_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* v_mvarId_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_2437_, v___y_2439_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* v_mvarId_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_mvarId_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v_mvarId_2444_);
return v_res_2450_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_object* v_00_u03b2_2451_, lean_object* v_x_2452_, lean_object* v_x_2453_){
_start:
{
uint8_t v___x_2454_; 
v___x_2454_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_2452_, v_x_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2455_, lean_object* v_x_2456_, lean_object* v_x_2457_){
_start:
{
uint8_t v_res_2458_; lean_object* v_r_2459_; 
v_res_2458_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(v_00_u03b2_2455_, v_x_2456_, v_x_2457_);
lean_dec(v_x_2457_);
lean_dec_ref(v_x_2456_);
v_r_2459_ = lean_box(v_res_2458_);
return v_r_2459_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_2460_, lean_object* v_x_2461_, size_t v_x_2462_, lean_object* v_x_2463_){
_start:
{
uint8_t v___x_2464_; 
v___x_2464_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_2461_, v_x_2462_, v_x_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___boxed(lean_object* v_00_u03b2_2465_, lean_object* v_x_2466_, lean_object* v_x_2467_, lean_object* v_x_2468_){
_start:
{
size_t v_x_77727__boxed_2469_; uint8_t v_res_2470_; lean_object* v_r_2471_; 
v_x_77727__boxed_2469_ = lean_unbox_usize(v_x_2467_);
lean_dec(v_x_2467_);
v_res_2470_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2465_, v_x_2466_, v_x_77727__boxed_2469_, v_x_2468_);
lean_dec(v_x_2468_);
lean_dec_ref(v_x_2466_);
v_r_2471_ = lean_box(v_res_2470_);
return v_r_2471_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_object* v_00_u03b2_2472_, lean_object* v_keys_2473_, lean_object* v_vals_2474_, lean_object* v_heq_2475_, lean_object* v_i_2476_, lean_object* v_k_2477_){
_start:
{
uint8_t v___x_2478_; 
v___x_2478_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_2473_, v_i_2476_, v_k_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2479_, lean_object* v_keys_2480_, lean_object* v_vals_2481_, lean_object* v_heq_2482_, lean_object* v_i_2483_, lean_object* v_k_2484_){
_start:
{
uint8_t v_res_2485_; lean_object* v_r_2486_; 
v_res_2485_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(v_00_u03b2_2479_, v_keys_2480_, v_vals_2481_, v_heq_2482_, v_i_2483_, v_k_2484_);
lean_dec(v_k_2484_);
lean_dec_ref(v_vals_2481_);
lean_dec_ref(v_keys_2480_);
v_r_2486_ = lean_box(v_res_2485_);
return v_r_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2487_, lean_object* v_h__1_2488_, lean_object* v_h__2_2489_){
_start:
{
lean_object* v_zero_2490_; uint8_t v_isZero_2491_; 
v_zero_2490_ = lean_unsigned_to_nat(0u);
v_isZero_2491_ = lean_nat_dec_eq(v_n_2487_, v_zero_2490_);
if (v_isZero_2491_ == 1)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
lean_dec(v_h__2_2489_);
v___x_2492_ = lean_box(0);
v___x_2493_ = lean_apply_1(v_h__1_2488_, v___x_2492_);
return v___x_2493_;
}
else
{
lean_object* v_one_2494_; lean_object* v_n_2495_; lean_object* v___x_2496_; 
lean_dec(v_h__1_2488_);
v_one_2494_ = lean_unsigned_to_nat(1u);
v_n_2495_ = lean_nat_sub(v_n_2487_, v_one_2494_);
v___x_2496_ = lean_apply_1(v_h__2_2489_, v_n_2495_);
return v___x_2496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2497_, lean_object* v_h__1_2498_, lean_object* v_h__2_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2497_, v_h__1_2498_, v_h__2_2499_);
lean_dec(v_n_2497_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2501_, lean_object* v_n_2502_, lean_object* v_h__1_2503_, lean_object* v_h__2_2504_){
_start:
{
lean_object* v_zero_2505_; uint8_t v_isZero_2506_; 
v_zero_2505_ = lean_unsigned_to_nat(0u);
v_isZero_2506_ = lean_nat_dec_eq(v_n_2502_, v_zero_2505_);
if (v_isZero_2506_ == 1)
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_dec(v_h__2_2504_);
v___x_2507_ = lean_box(0);
v___x_2508_ = lean_apply_1(v_h__1_2503_, v___x_2507_);
return v___x_2508_;
}
else
{
lean_object* v_one_2509_; lean_object* v_n_2510_; lean_object* v___x_2511_; 
lean_dec(v_h__1_2503_);
v_one_2509_ = lean_unsigned_to_nat(1u);
v_n_2510_ = lean_nat_sub(v_n_2502_, v_one_2509_);
v___x_2511_ = lean_apply_1(v_h__2_2504_, v_n_2510_);
return v___x_2511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* v_motive_2512_, lean_object* v_n_2513_, lean_object* v_h__1_2514_, lean_object* v_h__2_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(v_motive_2512_, v_n_2513_, v_h__1_2514_, v_h__2_2515_);
lean_dec(v_n_2513_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* v_procResult_x3f_2517_, lean_object* v_h__1_2518_, lean_object* v_h__2_2519_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2517_) == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec(v_h__1_2518_);
v___x_2520_ = lean_box(0);
v___x_2521_ = lean_apply_1(v_h__2_2519_, v___x_2520_);
return v___x_2521_;
}
else
{
lean_object* v_val_2522_; lean_object* v___x_2523_; 
lean_dec(v_h__2_2519_);
v_val_2522_ = lean_ctor_get(v_procResult_x3f_2517_, 0);
lean_inc(v_val_2522_);
lean_dec_ref_known(v_procResult_x3f_2517_, 1);
v___x_2523_ = lean_apply_1(v_h__1_2518_, v_val_2522_);
return v___x_2523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* v_motive_2524_, lean_object* v_procResult_x3f_2525_, lean_object* v_h__1_2526_, lean_object* v_h__2_2527_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2525_) == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec(v_h__1_2526_);
v___x_2528_ = lean_box(0);
v___x_2529_ = lean_apply_1(v_h__2_2527_, v___x_2528_);
return v___x_2529_;
}
else
{
lean_object* v_val_2530_; lean_object* v___x_2531_; 
lean_dec(v_h__2_2527_);
v_val_2530_ = lean_ctor_get(v_procResult_x3f_2525_, 0);
lean_inc(v_val_2530_);
lean_dec_ref_known(v_procResult_x3f_2525_, 1);
v___x_2531_ = lean_apply_1(v_h__1_2526_, v_val_2530_);
return v___x_2531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2532_, lean_object* v_h__1_2533_, lean_object* v_h__2_2534_){
_start:
{
if (lean_obj_tag(v_curr_2532_) == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec(v_h__2_2534_);
v___x_2535_ = lean_box(0);
v___x_2536_ = lean_apply_1(v_h__1_2533_, v___x_2535_);
return v___x_2536_;
}
else
{
lean_object* v_head_2537_; lean_object* v_tail_2538_; lean_object* v___x_2539_; 
lean_dec(v_h__1_2533_);
v_head_2537_ = lean_ctor_get(v_curr_2532_, 0);
lean_inc(v_head_2537_);
v_tail_2538_ = lean_ctor_get(v_curr_2532_, 1);
lean_inc(v_tail_2538_);
lean_dec_ref_known(v_curr_2532_, 2);
v___x_2539_ = lean_apply_2(v_h__2_2534_, v_head_2537_, v_tail_2538_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2540_, lean_object* v_curr_2541_, lean_object* v_h__1_2542_, lean_object* v_h__2_2543_){
_start:
{
if (lean_obj_tag(v_curr_2541_) == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_dec(v_h__2_2543_);
v___x_2544_ = lean_box(0);
v___x_2545_ = lean_apply_1(v_h__1_2542_, v___x_2544_);
return v___x_2545_;
}
else
{
lean_object* v_head_2546_; lean_object* v_tail_2547_; lean_object* v___x_2548_; 
lean_dec(v_h__1_2542_);
v_head_2546_ = lean_ctor_get(v_curr_2541_, 0);
lean_inc(v_head_2546_);
v_tail_2547_ = lean_ctor_get(v_curr_2541_, 1);
lean_inc(v_tail_2547_);
lean_dec_ref_known(v_curr_2541_, 2);
v___x_2548_ = lean_apply_2(v_h__2_2543_, v_head_2546_, v_tail_2547_);
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2549_, lean_object* v_h__1_2550_, lean_object* v_h__2_2551_){
_start:
{
if (lean_obj_tag(v_____do__lift_2549_) == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v_h__2_2551_);
v___x_2552_ = lean_box(0);
v___x_2553_ = lean_apply_1(v_h__1_2550_, v___x_2552_);
return v___x_2553_;
}
else
{
lean_object* v_val_2554_; lean_object* v___x_2555_; 
lean_dec(v_h__1_2550_);
v_val_2554_ = lean_ctor_get(v_____do__lift_2549_, 0);
lean_inc(v_val_2554_);
lean_dec_ref_known(v_____do__lift_2549_, 1);
v___x_2555_ = lean_apply_1(v_h__2_2551_, v_val_2554_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_2556_, lean_object* v_____do__lift_2557_, lean_object* v_h__1_2558_, lean_object* v_h__2_2559_){
_start:
{
if (lean_obj_tag(v_____do__lift_2557_) == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
lean_dec(v_h__2_2559_);
v___x_2560_ = lean_box(0);
v___x_2561_ = lean_apply_1(v_h__1_2558_, v___x_2560_);
return v___x_2561_;
}
else
{
lean_object* v_val_2562_; lean_object* v___x_2563_; 
lean_dec(v_h__1_2558_);
v_val_2562_ = lean_ctor_get(v_____do__lift_2557_, 0);
lean_inc(v_val_2562_);
lean_dec_ref_known(v_____do__lift_2557_, 1);
v___x_2563_ = lean_apply_1(v_h__2_2559_, v_val_2562_);
return v___x_2563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_2564_, lean_object* v_trace_2565_, lean_object* v_next_2566_, lean_object* v_orig_2567_, lean_object* v_g_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_maxDepth_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_maxDepth_2574_ = lean_ctor_get(v_cfg_2564_, 0);
lean_inc(v_maxDepth_2574_);
v___x_2575_ = lean_box(0);
v___x_2576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_g_2568_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2564_, v_trace_2565_, v_next_2566_, v_orig_2567_, v_maxDepth_2574_, v___x_2576_, v___x_2575_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_2578_, lean_object* v_trace_2579_, lean_object* v_next_2580_, lean_object* v_orig_2581_, lean_object* v_g_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2578_, v_trace_2579_, v_next_2580_, v_orig_2581_, v_g_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_2589_, lean_object* v_a_2590_){
_start:
{
if (lean_obj_tag(v_a_2589_) == 0)
{
lean_object* v___x_2591_; 
v___x_2591_ = l_List_reverse___redArg(v_a_2590_);
return v___x_2591_;
}
else
{
lean_object* v_head_2592_; lean_object* v_tail_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2602_; 
v_head_2592_ = lean_ctor_get(v_a_2589_, 0);
v_tail_2593_ = lean_ctor_get(v_a_2589_, 1);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_a_2589_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2595_ = v_a_2589_;
v_isShared_2596_ = v_isSharedCheck_2602_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_tail_2593_);
lean_inc(v_head_2592_);
lean_dec(v_a_2589_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2602_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2597_ = l_Lean_MessageData_ofFormat(v_head_2592_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 1, v_a_2590_);
lean_ctor_set(v___x_2595_, 0, v___x_2597_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_a_2590_);
v___x_2599_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
v_a_2589_ = v_tail_2593_;
v_a_2590_ = v___x_2599_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_2605_ = l_Lean_stringToMessageData(v___x_2604_);
return v___x_2605_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_2608_ = l_Lean_stringToMessageData(v___x_2607_);
return v___x_2608_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_2611_ = l_Lean_stringToMessageData(v___x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_2612_, lean_object* v_snd_2613_, lean_object* v_x_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2612_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2622_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2622_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_2613_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2642_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2642_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2642_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2627_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_2628_ = lean_box(0);
v___x_2629_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2621_, v___x_2628_);
v___x_2630_ = l_Lean_MessageData_ofList(v___x_2629_);
v___x_2631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2627_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set(v___x_2633_, 1, v___x_2632_);
v___x_2634_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_2635_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2623_, v___x_2628_);
v___x_2636_ = l_Lean_MessageData_ofList(v___x_2635_);
v___x_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2634_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2633_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2638_);
v___x_2640_ = v___x_2625_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_a_2621_);
v_a_2643_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2622_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2622_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v_snd_2613_);
v_a_2651_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2620_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2620_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_2659_, lean_object* v_snd_2660_, lean_object* v_x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2659_, v_snd_2660_, v_x_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec_ref(v_x_2661_);
return v_res_2667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_2670_ = l_Lean_stringToMessageData(v___x_2669_);
return v___x_2670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_2673_ = l_Lean_stringToMessageData(v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_2674_, lean_object* v___x_2675_, lean_object* v_x_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2674_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_2675_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2702_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2702_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2702_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v___x_2689_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_2690_ = lean_box(0);
v___x_2691_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2683_, v___x_2690_);
v___x_2692_ = l_Lean_MessageData_ofList(v___x_2691_);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2689_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2685_, v___x_2690_);
v___x_2697_ = l_Lean_MessageData_ofList(v___x_2696_);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2695_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2698_);
v___x_2700_ = v___x_2687_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_a_2683_);
v_a_2703_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2684_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2684_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v___x_2675_);
v_a_2711_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2682_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2682_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_2719_, lean_object* v___x_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2719_, v___x_2720_, v_x_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v_x_2721_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t v___x_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_, lean_object* v___y_2731_){
_start:
{
if (lean_obj_tag(v_x_2729_) == 0)
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v_x_2730_);
return v___x_2733_;
}
else
{
lean_object* v_head_2734_; lean_object* v_tail_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2750_; 
v_head_2734_ = lean_ctor_get(v_x_2729_, 0);
v_tail_2735_ = lean_ctor_get(v_x_2729_, 1);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_x_2729_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2737_ = v_x_2729_;
v_isShared_2738_ = v_isSharedCheck_2750_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_tail_2735_);
lean_inc(v_head_2734_);
lean_dec(v_x_2729_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2750_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
uint8_t v_a_2745_; lean_object* v___x_2747_; lean_object* v_a_2748_; uint8_t v___x_2749_; 
v___x_2747_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2734_, v___y_2731_);
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref(v___x_2747_);
v___x_2749_ = lean_unbox(v_a_2748_);
lean_dec(v_a_2748_);
if (v___x_2749_ == 0)
{
goto v___jp_2739_;
}
else
{
v_a_2745_ = v___x_2728_;
goto v___jp_2744_;
}
v___jp_2739_:
{
lean_object* v___x_2741_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 1, v_x_2730_);
v___x_2741_ = v___x_2737_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_head_2734_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_x_2730_);
v___x_2741_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
v_x_2729_ = v_tail_2735_;
v_x_2730_ = v___x_2741_;
goto _start;
}
}
v___jp_2744_:
{
if (v_a_2745_ == 0)
{
lean_del_object(v___x_2737_);
lean_dec(v_head_2734_);
v_x_2729_ = v_tail_2735_;
goto _start;
}
else
{
goto v___jp_2739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v___x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
uint8_t v___x_45712__boxed_2756_; lean_object* v_res_2757_; 
v___x_45712__boxed_2756_ = lean_unbox(v___x_2751_);
v_res_2757_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_45712__boxed_2756_, v_x_2752_, v_x_2753_, v___y_2754_);
lean_dec(v___y_2754_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_2758_, lean_object* v_a_2759_){
_start:
{
if (lean_obj_tag(v_a_2758_) == 0)
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_array_to_list(v_a_2759_);
return v___x_2760_;
}
else
{
lean_object* v_head_2761_; lean_object* v_tail_2762_; lean_object* v___x_2763_; 
v_head_2761_ = lean_ctor_get(v_a_2758_, 0);
lean_inc(v_head_2761_);
v_tail_2762_ = lean_ctor_get(v_a_2758_, 1);
lean_inc(v_tail_2762_);
lean_dec_ref_known(v_a_2758_, 2);
v___x_2763_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2759_, v_head_2761_);
v_a_2758_ = v_tail_2762_;
v_a_2759_ = v___x_2763_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
if (lean_obj_tag(v_a_2766_) == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
lean_dec(v_goals_2765_);
v___x_2774_ = lean_array_to_list(v_a_2767_);
v___x_2775_ = lean_array_to_list(v_a_2768_);
v___x_2776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
return v___x_2777_;
}
else
{
lean_object* v_head_2778_; lean_object* v_tail_2779_; lean_object* v___x_2780_; 
v_head_2778_ = lean_ctor_get(v_a_2766_, 0);
lean_inc_n(v_head_2778_, 2);
v_tail_2779_ = lean_ctor_get(v_a_2766_, 1);
lean_inc(v_tail_2779_);
lean_dec_ref_known(v_a_2766_, 2);
lean_inc(v_goals_2765_);
v___x_2780_ = l_Lean_MVarId_isIndependentOf(v_goals_2765_, v_head_2778_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; uint8_t v___x_2782_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = lean_unbox(v_a_2781_);
lean_dec(v_a_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_array_push(v_a_2768_, v_head_2778_);
v_a_2766_ = v_tail_2779_;
v_a_2768_ = v___x_2783_;
goto _start;
}
else
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_array_push(v_a_2767_, v_head_2778_);
v_a_2766_ = v_tail_2779_;
v_a_2767_ = v___x_2785_;
goto _start;
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v_tail_2779_);
lean_dec(v_head_2778_);
lean_dec_ref(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_goals_2765_);
v_a_2787_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2780_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2780_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_2805_, lean_object* v_a_2806_){
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
lean_object* v_head_2808_; 
v_head_2808_ = lean_ctor_get(v_a_2805_, 0);
if (lean_obj_tag(v_head_2808_) == 0)
{
lean_object* v_tail_2809_; lean_object* v_val_2810_; lean_object* v___x_2811_; 
lean_inc_ref(v_head_2808_);
v_tail_2809_ = lean_ctor_get(v_a_2805_, 1);
lean_inc(v_tail_2809_);
lean_dec_ref_known(v_a_2805_, 2);
v_val_2810_ = lean_ctor_get(v_head_2808_, 0);
lean_inc(v_val_2810_);
lean_dec_ref_known(v_head_2808_, 1);
v___x_2811_ = lean_array_push(v_a_2806_, v_val_2810_);
v_a_2805_ = v_tail_2809_;
v_a_2806_ = v___x_2811_;
goto _start;
}
else
{
lean_object* v_tail_2813_; 
v_tail_2813_ = lean_ctor_get(v_a_2805_, 1);
lean_inc(v_tail_2813_);
lean_dec_ref_known(v_a_2805_, 2);
v_a_2805_ = v_tail_2813_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_2815_, lean_object* v_x_2816_, lean_object* v_x_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
if (lean_obj_tag(v_x_2816_) == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec_ref(v_f_2815_);
v___x_2823_ = l_List_reverse___redArg(v_x_2817_);
v___x_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
return v___x_2824_;
}
else
{
lean_object* v_head_2825_; lean_object* v_tail_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2871_; 
v_head_2825_ = lean_ctor_get(v_x_2816_, 0);
v_tail_2826_ = lean_ctor_get(v_x_2816_, 1);
v_isSharedCheck_2871_ = !lean_is_exclusive(v_x_2816_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2828_ = v_x_2816_;
v_isShared_2829_ = v_isSharedCheck_2871_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_tail_2826_);
lean_inc(v_head_2825_);
lean_dec(v_x_2816_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2871_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v_a_2831_; lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_Meta_saveState___redArg(v___y_2819_, v___y_2821_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2838_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
lean_inc_ref(v_f_2815_);
lean_inc(v___y_2821_);
lean_inc_ref(v___y_2820_);
lean_inc(v___y_2819_);
lean_inc_ref(v___y_2818_);
lean_inc(v_head_2825_);
v___x_2838_ = lean_apply_6(v_f_2815_, v_head_2825_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, lean_box(0));
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; 
lean_dec(v_a_2837_);
lean_dec(v_head_2825_);
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2840_, 0, v_a_2839_);
v_a_2831_ = v___x_2840_;
goto v___jp_2830_;
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2862_; 
v_a_2841_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2843_ = v___x_2838_;
v_isShared_2844_ = v_isSharedCheck_2862_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2838_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2862_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
uint8_t v___y_2846_; uint8_t v___x_2860_; 
v___x_2860_ = l_Lean_Exception_isInterrupt(v_a_2841_);
if (v___x_2860_ == 0)
{
uint8_t v___x_2861_; 
lean_inc(v_a_2841_);
v___x_2861_ = l_Lean_Exception_isRuntime(v_a_2841_);
v___y_2846_ = v___x_2861_;
goto v___jp_2845_;
}
else
{
v___y_2846_ = v___x_2860_;
goto v___jp_2845_;
}
v___jp_2845_:
{
if (v___y_2846_ == 0)
{
lean_object* v___x_2847_; 
lean_del_object(v___x_2843_);
lean_dec(v_a_2841_);
v___x_2847_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2837_, v___y_2819_, v___y_2821_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v___x_2848_; 
lean_dec_ref_known(v___x_2847_, 1);
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_head_2825_);
v_a_2831_ = v___x_2848_;
goto v___jp_2830_;
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_del_object(v___x_2828_);
lean_dec(v_tail_2826_);
lean_dec(v_head_2825_);
lean_dec(v_x_2817_);
lean_dec_ref(v_f_2815_);
v_a_2849_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2847_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2847_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_object* v___x_2858_; 
lean_dec(v_a_2837_);
lean_del_object(v___x_2828_);
lean_dec(v_tail_2826_);
lean_dec(v_head_2825_);
lean_dec(v_x_2817_);
lean_dec_ref(v_f_2815_);
if (v_isShared_2844_ == 0)
{
v___x_2858_ = v___x_2843_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2841_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_del_object(v___x_2828_);
lean_dec(v_tail_2826_);
lean_dec(v_head_2825_);
lean_dec(v_x_2817_);
lean_dec_ref(v_f_2815_);
v_a_2863_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2836_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2836_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
v___jp_2830_:
{
lean_object* v___x_2833_; 
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 1, v_x_2817_);
lean_ctor_set(v___x_2828_, 0, v_a_2831_);
v___x_2833_ = v___x_2828_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2831_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_x_2817_);
v___x_2833_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
v_x_2816_ = v_tail_2826_;
v_x_2817_ = v___x_2833_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_2872_, lean_object* v_x_2873_, lean_object* v_x_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2872_, v_x_2873_, v_x_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
if (lean_obj_tag(v_a_2881_) == 0)
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_array_to_list(v_a_2882_);
return v___x_2883_;
}
else
{
lean_object* v_head_2884_; 
v_head_2884_ = lean_ctor_get(v_a_2881_, 0);
if (lean_obj_tag(v_head_2884_) == 1)
{
lean_object* v_tail_2885_; lean_object* v_val_2886_; lean_object* v___x_2887_; 
lean_inc_ref(v_head_2884_);
v_tail_2885_ = lean_ctor_get(v_a_2881_, 1);
lean_inc(v_tail_2885_);
lean_dec_ref_known(v_a_2881_, 2);
v_val_2886_ = lean_ctor_get(v_head_2884_, 0);
lean_inc(v_val_2886_);
lean_dec_ref_known(v_head_2884_, 1);
v___x_2887_ = lean_array_push(v_a_2882_, v_val_2886_);
v_a_2881_ = v_tail_2885_;
v_a_2882_ = v___x_2887_;
goto _start;
}
else
{
lean_object* v_tail_2889_; 
v_tail_2889_ = lean_ctor_get(v_a_2881_, 1);
lean_inc(v_tail_2889_);
lean_dec_ref_known(v_a_2881_, 2);
v_a_2881_ = v_tail_2889_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_2891_, lean_object* v_f_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_box(0);
v___x_2899_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2892_, v_L_2891_, v___x_2898_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2911_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_2911_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2911_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2904_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_2900_);
v___x_2905_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_2900_, v___x_2904_);
v___x_2906_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_2900_, v___x_2904_);
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_2907_);
v___x_2909_ = v___x_2902_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
v_a_2912_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2899_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2899_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* v_L_2920_, lean_object* v_f_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_2920_, v_f_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t v___x_2928_, uint8_t v___x_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_, lean_object* v___y_2932_){
_start:
{
if (lean_obj_tag(v_x_2930_) == 0)
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v_x_2931_);
return v___x_2934_;
}
else
{
lean_object* v_head_2935_; lean_object* v_tail_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2950_; 
v_head_2935_ = lean_ctor_get(v_x_2930_, 0);
v_tail_2936_ = lean_ctor_get(v_x_2930_, 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_x_2930_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2938_ = v_x_2930_;
v_isShared_2939_ = v_isSharedCheck_2950_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_tail_2936_);
lean_inc(v_head_2935_);
lean_dec(v_x_2930_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2950_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
uint8_t v_a_2941_; lean_object* v___x_2947_; lean_object* v_a_2948_; uint8_t v___x_2949_; 
v___x_2947_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2935_, v___y_2932_);
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref(v___x_2947_);
v___x_2949_ = lean_unbox(v_a_2948_);
lean_dec(v_a_2948_);
if (v___x_2949_ == 0)
{
v_a_2941_ = v___x_2928_;
goto v___jp_2940_;
}
else
{
v_a_2941_ = v___x_2929_;
goto v___jp_2940_;
}
v___jp_2940_:
{
if (v_a_2941_ == 0)
{
lean_del_object(v___x_2938_);
lean_dec(v_head_2935_);
v_x_2930_ = v_tail_2936_;
goto _start;
}
else
{
lean_object* v___x_2944_; 
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 1, v_x_2931_);
v___x_2944_ = v___x_2938_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_head_2935_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_x_2931_);
v___x_2944_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
v_x_2930_ = v_tail_2936_;
v_x_2931_ = v___x_2944_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* v___x_2951_, lean_object* v___x_2952_, lean_object* v_x_2953_, lean_object* v_x_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
uint8_t v___x_46066__boxed_2957_; uint8_t v___x_46067__boxed_2958_; lean_object* v_res_2959_; 
v___x_46066__boxed_2957_ = lean_unbox(v___x_2951_);
v___x_46067__boxed_2958_ = lean_unbox(v___x_2952_);
v_res_2959_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_46066__boxed_2957_, v___x_46067__boxed_2958_, v_x_2953_, v_x_2954_, v___y_2955_);
lean_dec(v___y_2955_);
return v_res_2959_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1));
v___x_2964_ = l_Lean_stringToMessageData(v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_2965_, lean_object* v_trace_2966_, lean_object* v_next_2967_, lean_object* v_orig_2968_, lean_object* v_goals_2969_, lean_object* v_remaining_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v___f_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_inc(v_orig_2968_);
lean_inc_ref(v_next_2967_);
lean_inc(v_trace_2966_);
lean_inc_ref(v_cfg_2965_);
v___f_2976_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2976_, 0, v_cfg_2965_);
lean_closure_set(v___f_2976_, 1, v_trace_2966_);
lean_closure_set(v___f_2976_, 2, v_next_2967_);
lean_closure_set(v___f_2976_, 3, v_orig_2968_);
v___x_2977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
lean_inc(v_remaining_2970_);
lean_inc(v_goals_2969_);
v___x_2978_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2969_, v_remaining_2970_, v___x_2977_, v___x_2977_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v_fst_2980_; lean_object* v_snd_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_4181_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v_fst_2980_ = lean_ctor_get(v_a_2979_, 0);
v_snd_2981_ = lean_ctor_get(v_a_2979_, 1);
v_isSharedCheck_4181_ = !lean_is_exclusive(v_a_2979_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_2983_ = v_a_2979_;
v_isShared_2984_ = v_isSharedCheck_4181_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_snd_2981_);
lean_inc(v_fst_2980_);
lean_dec(v_a_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_4181_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
uint8_t v___x_2985_; 
v___x_2985_ = l_List_isEmpty___redArg(v_fst_2980_);
if (v___x_2985_ == 0)
{
lean_object* v_toCold_2986_; lean_object* v_options_2987_; uint8_t v_hasTrace_2988_; 
lean_dec(v_remaining_2970_);
v_toCold_2986_ = lean_ctor_get(v_a_2973_, 0);
v_options_2987_ = lean_ctor_get(v_toCold_2986_, 2);
v_hasTrace_2988_ = lean_ctor_get_uint8(v_options_2987_, sizeof(void*)*1);
if (v_hasTrace_2988_ == 0)
{
lean_object* v___x_2989_; 
lean_del_object(v___x_2983_);
v___x_2989_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2980_, v___f_2976_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3062_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_3062_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3062_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v_fst_2994_; lean_object* v_snd_2995_; lean_object* v___x_2996_; lean_object* v_a_2998_; lean_object* v___y_3005_; lean_object* v___y_3008_; lean_object* v___y_3009_; uint8_t v___y_3010_; lean_object* v___y_3021_; lean_object* v___y_3037_; uint8_t v___y_3038_; lean_object* v_a_3053_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_fst_2994_ = lean_ctor_get(v_a_2990_, 0);
lean_inc(v_fst_2994_);
v_snd_2995_ = lean_ctor_get(v_a_2990_, 1);
lean_inc(v_snd_2995_);
lean_dec(v_a_2990_);
v___x_2996_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_2995_, v___x_2977_);
v___x_3057_ = lean_box(0);
v___x_3058_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_2985_, v_goals_2969_, v___x_3057_, v_a_2972_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v___x_3060_ = l_List_reverse___redArg(v_a_3059_);
v_a_3053_ = v___x_3060_;
goto v___jp_3052_;
}
else
{
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3061_; 
v_a_3061_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3058_, 1);
v_a_3053_ = v_a_3061_;
goto v___jp_3052_;
}
else
{
lean_dec(v___x_2996_);
lean_dec(v_fst_2994_);
lean_del_object(v___x_2992_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
return v___x_3058_;
}
}
v___jp_2997_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3002_; 
v___x_2999_ = l_List_appendTR___redArg(v___x_2996_, v_fst_2994_);
v___x_3000_ = l_List_appendTR___redArg(v___x_2999_, v_a_2998_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_3000_);
v___x_3002_ = v___x_2992_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
v___jp_3004_:
{
if (lean_obj_tag(v___y_3005_) == 0)
{
lean_object* v_a_3006_; 
v_a_3006_ = lean_ctor_get(v___y_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___y_3005_, 1);
v_a_2998_ = v_a_3006_;
goto v___jp_2997_;
}
else
{
lean_dec(v___x_2996_);
lean_dec(v_fst_2994_);
lean_del_object(v___x_2992_);
return v___y_3005_;
}
}
v___jp_3007_:
{
if (v___y_3010_ == 0)
{
lean_object* v___x_3011_; 
lean_dec_ref(v___y_3009_);
v___x_3011_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3008_, v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_dec_ref_known(v___x_3011_, 1);
v_a_2998_ = v_snd_2981_;
goto v___jp_2997_;
}
else
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_dec(v___x_2996_);
lean_dec(v_fst_2994_);
lean_del_object(v___x_2992_);
lean_dec(v_snd_2981_);
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_3011_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
else
{
lean_dec_ref(v___y_3008_);
lean_dec(v_snd_2981_);
v___y_3005_ = v___y_3009_;
goto v___jp_3004_;
}
}
v___jp_3020_:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3024_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
lean_inc(v_snd_2981_);
v___x_3024_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3021_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_dec(v_a_3023_);
lean_dec(v_snd_2981_);
v___y_3005_ = v___x_3024_;
goto v___jp_3004_;
}
else
{
lean_object* v_a_3025_; uint8_t v___x_3026_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v___x_3026_ = l_Lean_Exception_isInterrupt(v_a_3025_);
if (v___x_3026_ == 0)
{
uint8_t v___x_3027_; 
lean_inc(v_a_3025_);
v___x_3027_ = l_Lean_Exception_isRuntime(v_a_3025_);
v___y_3008_ = v_a_3023_;
v___y_3009_ = v___x_3024_;
v___y_3010_ = v___x_3027_;
goto v___jp_3007_;
}
else
{
v___y_3008_ = v_a_3023_;
v___y_3009_ = v___x_3024_;
v___y_3010_ = v___x_3026_;
goto v___jp_3007_;
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v___y_3021_);
lean_dec(v___x_2996_);
lean_dec(v_fst_2994_);
lean_del_object(v___x_2992_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_3028_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3022_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3022_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
v___jp_3036_:
{
if (v___y_3038_ == 0)
{
uint8_t v___x_3039_; 
lean_del_object(v___x_2992_);
v___x_3039_ = l_List_isEmpty___redArg(v_fst_2994_);
lean_dec(v_fst_2994_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_dec(v___y_3037_);
lean_dec(v___x_2996_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v___x_3040_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3041_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3040_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3041_;
}
else
{
lean_object* v___x_3042_; 
v___x_3042_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3037_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3051_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3051_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = l_List_appendTR___redArg(v___x_2996_, v_a_3043_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
else
{
lean_dec(v___x_2996_);
return v___x_3042_;
}
}
}
else
{
v___y_3021_ = v___y_3037_;
goto v___jp_3020_;
}
}
v___jp_3052_:
{
uint8_t v_commitIndependentGoals_3054_; lean_object* v___x_3055_; 
v_commitIndependentGoals_3054_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___x_2996_);
v___x_3055_ = l_List_appendTR___redArg(v_a_3053_, v___x_2996_);
if (v_commitIndependentGoals_3054_ == 0)
{
v___y_3037_ = v___x_3055_;
v___y_3038_ = v___x_2985_;
goto v___jp_3036_;
}
else
{
uint8_t v___x_3056_; 
v___x_3056_ = l_List_isEmpty___redArg(v___x_2996_);
if (v___x_3056_ == 0)
{
v___y_3021_ = v___x_3055_;
goto v___jp_3020_;
}
else
{
v___y_3037_ = v___x_3055_;
v___y_3038_ = v___x_2985_;
goto v___jp_3036_;
}
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v_snd_2981_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_3063_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_2989_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_2989_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3071_; lean_object* v___f_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v_a_3080_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v_a_3094_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v_a_3099_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v_a_3106_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; uint8_t v___y_3124_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; uint8_t v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v_a_3153_; lean_object* v___y_3166_; uint8_t v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v_a_3172_; lean_object* v___y_3175_; uint8_t v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v_a_3181_; lean_object* v___y_3184_; lean_object* v___y_3185_; uint8_t v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v_a_3192_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; uint8_t v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; uint8_t v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v___y_3218_; lean_object* v___y_3222_; lean_object* v___y_3223_; uint8_t v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; uint8_t v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; uint8_t v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; uint8_t v___y_3258_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; uint8_t v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v_a_3274_; uint8_t v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v_a_3285_; uint8_t v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v_a_3301_; uint8_t v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v_a_3310_; lean_object* v___y_3313_; lean_object* v___y_3314_; uint8_t v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v_a_3321_; lean_object* v___y_3325_; lean_object* v___y_3326_; uint8_t v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3337_; lean_object* v___y_3338_; uint8_t v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; uint8_t v___y_3347_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; uint8_t v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; uint8_t v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3378_; lean_object* v___y_3379_; uint8_t v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; uint8_t v___y_3393_; uint8_t v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; uint8_t v___y_3400_; lean_object* v___y_3405_; lean_object* v___y_3406_; uint8_t v___y_3407_; uint8_t v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v_a_3414_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; uint8_t v___y_3422_; uint8_t v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; uint8_t v___y_3449_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v_a_3461_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v_a_3468_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v_a_3483_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v_a_3488_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v_a_3495_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; uint8_t v___y_3513_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3536_; uint8_t v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v_a_3542_; lean_object* v___y_3552_; uint8_t v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v_a_3558_; lean_object* v___y_3561_; lean_object* v___y_3562_; uint8_t v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v_a_3569_; lean_object* v___y_3573_; uint8_t v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v_a_3579_; lean_object* v___y_3582_; uint8_t v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3592_; lean_object* v___y_3593_; uint8_t v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3604_; lean_object* v___y_3605_; uint8_t v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; uint8_t v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; uint8_t v___y_3626_; lean_object* v___y_3630_; lean_object* v___y_3631_; uint8_t v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3647_; lean_object* v___y_3648_; uint8_t v___y_3649_; uint8_t v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; uint8_t v___y_3657_; lean_object* v___y_3662_; lean_object* v___y_3663_; uint8_t v___y_3664_; uint8_t v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v_a_3671_; uint8_t v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v_a_3682_; lean_object* v___y_3695_; uint8_t v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v_a_3701_; lean_object* v___y_3704_; uint8_t v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v_a_3710_; lean_object* v___y_3713_; uint8_t v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v_a_3721_; lean_object* v___y_3725_; lean_object* v___y_3726_; uint8_t v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3737_; lean_object* v___y_3738_; uint8_t v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; uint8_t v___y_3747_; lean_object* v___y_3751_; uint8_t v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; uint8_t v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3778_; lean_object* v___y_3779_; uint8_t v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; uint8_t v___y_3787_; lean_object* v___y_3795_; lean_object* v___y_3796_; uint8_t v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v_a_3803_; lean_object* v___y_3808_; uint8_t v___y_3809_; uint8_t v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; uint8_t v___y_3838_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v_a_3850_; 
v_inheritedTraceOptions_3071_ = lean_ctor_get(v_toCold_2986_, 11);
lean_inc(v_snd_2981_);
lean_inc(v_fst_2980_);
v___f_3072_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3072_, 0, v_fst_2980_);
lean_closure_set(v___f_3072_, 1, v_snd_2981_);
v___x_3073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_3074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_2966_);
v___x_3075_ = l_Lean_Name_append(v___x_3074_, v_trace_2966_);
v___x_3076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3071_, v_options_2987_, v___x_3075_);
lean_dec(v___x_3075_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3899_ = l_Lean_trace_profiler;
v___x_3900_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2987_, v___x_3899_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; 
lean_dec_ref(v___f_3072_);
lean_del_object(v___x_2983_);
v___x_3901_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2980_, v___f_2976_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_4169_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_4169_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_4169_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v_fst_3906_; lean_object* v_snd_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_4168_; 
v_fst_3906_ = lean_ctor_get(v_a_3902_, 0);
v_snd_3907_ = lean_ctor_get(v_a_3902_, 1);
v_isSharedCheck_4168_ = !lean_is_exclusive(v_a_3902_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_3909_ = v_a_3902_;
v_isShared_3910_ = v_isSharedCheck_4168_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_snd_3907_);
lean_inc(v_fst_3906_);
lean_dec(v_a_3902_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_4168_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v_a_3913_; lean_object* v___y_3920_; lean_object* v___y_3923_; lean_object* v___y_3924_; uint8_t v___y_3925_; lean_object* v___y_3936_; lean_object* v___y_3952_; uint8_t v___y_3953_; lean_object* v_a_3968_; lean_object* v___f_3972_; lean_object* v___x_3973_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v_a_3977_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v_a_3994_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v_a_3999_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v_a_4005_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; uint8_t v___y_4024_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; uint8_t v___y_4042_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v_a_4052_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v_a_4059_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v_a_4071_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v_a_4076_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v_a_4081_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; uint8_t v___y_4095_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; uint8_t v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; uint8_t v___y_4127_; uint8_t v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v_a_4135_; 
v___x_3911_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3907_, v___x_2977_);
lean_inc(v___x_3911_);
lean_inc(v_fst_3906_);
v___f_3972_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3972_, 0, v_fst_3906_);
lean_closure_set(v___f_3972_, 1, v___x_3911_);
v___x_3973_ = lean_box(0);
if (v___x_3076_ == 0)
{
if (v___x_3900_ == 0)
{
lean_object* v___x_4164_; 
lean_dec_ref(v___f_3972_);
lean_del_object(v___x_3909_);
v___x_4164_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2988_, v___x_2985_, v_goals_2969_, v___x_3973_, v_a_2972_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4166_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
v___x_4166_ = l_List_reverse___redArg(v_a_4165_);
v_a_3968_ = v___x_4166_;
goto v___jp_3967_;
}
else
{
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4167_; 
v_a_4167_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4164_, 1);
v_a_3968_ = v_a_4167_;
goto v___jp_3967_;
}
else
{
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_del_object(v___x_3904_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
return v___x_4164_;
}
}
}
else
{
lean_del_object(v___x_3904_);
goto v___jp_4139_;
}
}
else
{
lean_del_object(v___x_3904_);
goto v___jp_4139_;
}
v___jp_3912_:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3917_; 
v___x_3914_ = l_List_appendTR___redArg(v___x_3911_, v_fst_3906_);
v___x_3915_ = l_List_appendTR___redArg(v___x_3914_, v_a_3913_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3915_);
v___x_3917_ = v___x_3904_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
v___jp_3919_:
{
if (lean_obj_tag(v___y_3920_) == 0)
{
lean_object* v_a_3921_; 
v_a_3921_ = lean_ctor_get(v___y_3920_, 0);
lean_inc(v_a_3921_);
lean_dec_ref_known(v___y_3920_, 1);
v_a_3913_ = v_a_3921_;
goto v___jp_3912_;
}
else
{
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_del_object(v___x_3904_);
return v___y_3920_;
}
}
v___jp_3922_:
{
if (v___y_3925_ == 0)
{
lean_object* v___x_3926_; 
lean_dec_ref(v___y_3923_);
v___x_3926_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3924_, v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_dec_ref_known(v___x_3926_, 1);
v_a_3913_ = v_snd_2981_;
goto v___jp_3912_;
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_del_object(v___x_3904_);
lean_dec(v_snd_2981_);
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3926_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3926_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
else
{
lean_dec_ref(v___y_3924_);
lean_dec(v_snd_2981_);
v___y_3920_ = v___y_3923_;
goto v___jp_3919_;
}
}
v___jp_3935_:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3939_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v___x_3937_, 1);
lean_inc(v_snd_2981_);
v___x_3939_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3936_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_dec(v_a_3938_);
lean_dec(v_snd_2981_);
v___y_3920_ = v___x_3939_;
goto v___jp_3919_;
}
else
{
lean_object* v_a_3940_; uint8_t v___x_3941_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
v___x_3941_ = l_Lean_Exception_isInterrupt(v_a_3940_);
if (v___x_3941_ == 0)
{
uint8_t v___x_3942_; 
lean_inc(v_a_3940_);
v___x_3942_ = l_Lean_Exception_isRuntime(v_a_3940_);
v___y_3923_ = v___x_3939_;
v___y_3924_ = v_a_3938_;
v___y_3925_ = v___x_3942_;
goto v___jp_3922_;
}
else
{
v___y_3923_ = v___x_3939_;
v___y_3924_ = v_a_3938_;
v___y_3925_ = v___x_3941_;
goto v___jp_3922_;
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec(v___y_3936_);
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_del_object(v___x_3904_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_3943_ = lean_ctor_get(v___x_3937_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3937_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3937_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3937_);
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
v___jp_3951_:
{
if (v___y_3953_ == 0)
{
uint8_t v___x_3954_; 
lean_del_object(v___x_3904_);
v___x_3954_ = l_List_isEmpty___redArg(v_fst_3906_);
lean_dec(v_fst_3906_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
lean_dec(v___y_3952_);
lean_dec(v___x_3911_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v___x_3955_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3956_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3955_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3956_;
}
else
{
lean_object* v___x_3957_; 
v___x_3957_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3952_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3966_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3960_ = v___x_3957_;
v_isShared_3961_ = v_isSharedCheck_3966_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3966_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3962_; lean_object* v___x_3964_; 
v___x_3962_ = l_List_appendTR___redArg(v___x_3911_, v_a_3958_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3962_);
v___x_3964_ = v___x_3960_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3962_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
else
{
lean_dec(v___x_3911_);
return v___x_3957_;
}
}
}
else
{
v___y_3936_ = v___y_3952_;
goto v___jp_3935_;
}
}
v___jp_3967_:
{
uint8_t v_commitIndependentGoals_3969_; lean_object* v___x_3970_; 
v_commitIndependentGoals_3969_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___x_3911_);
v___x_3970_ = l_List_appendTR___redArg(v_a_3968_, v___x_3911_);
if (v_commitIndependentGoals_3969_ == 0)
{
v___y_3952_ = v___x_3970_;
v___y_3953_ = v___x_2985_;
goto v___jp_3951_;
}
else
{
uint8_t v___x_3971_; 
v___x_3971_ = l_List_isEmpty___redArg(v___x_3911_);
if (v___x_3971_ == 0)
{
v___y_3936_ = v___x_3970_;
goto v___jp_3935_;
}
else
{
v___y_3952_ = v___x_3970_;
v___y_3953_ = v___x_2985_;
goto v___jp_3951_;
}
}
}
v___jp_3974_:
{
lean_object* v___x_3978_; double v___x_3979_; double v___x_3980_; double v___x_3981_; double v___x_3982_; double v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3987_; 
v___x_3978_ = lean_io_mono_nanos_now();
v___x_3979_ = lean_float_of_nat(v___y_3975_);
v___x_3980_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3981_ = lean_float_div(v___x_3979_, v___x_3980_);
v___x_3982_ = lean_float_of_nat(v___x_3978_);
v___x_3983_ = lean_float_div(v___x_3982_, v___x_3980_);
v___x_3984_ = lean_box_float(v___x_3981_);
v___x_3985_ = lean_box_float(v___x_3983_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 1, v___x_3985_);
lean_ctor_set(v___x_3909_, 0, v___x_3984_);
v___x_3987_ = v___x_3909_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3984_);
lean_ctor_set(v_reuseFailAlloc_3990_, 1, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3988_, 0, v_a_3977_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v___x_3989_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2988_, v___x_3073_, v_options_2987_, v___x_3076_, v___y_3976_, v___f_3972_, v___x_3988_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3989_;
}
}
v___jp_3991_:
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3995_, 0, v_a_3994_);
v___y_3975_ = v___y_3992_;
v___y_3976_ = v___y_3993_;
v_a_3977_ = v___x_3995_;
goto v___jp_3974_;
}
v___jp_3996_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = l_List_appendTR___redArg(v___x_3911_, v_fst_3906_);
v___x_4001_ = l_List_appendTR___redArg(v___x_4000_, v_a_3999_);
v___y_3992_ = v___y_3997_;
v___y_3993_ = v___y_3998_;
v_a_3994_ = v___x_4001_;
goto v___jp_3991_;
}
v___jp_4002_:
{
lean_object* v___x_4006_; 
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v_a_4005_);
v___y_3975_ = v___y_4003_;
v___y_3976_ = v___y_4004_;
v_a_3977_ = v___x_4006_;
goto v___jp_3974_;
}
v___jp_4007_:
{
if (lean_obj_tag(v___y_4010_) == 0)
{
lean_object* v_a_4011_; 
v_a_4011_ = lean_ctor_get(v___y_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___y_4010_, 1);
v___y_3992_ = v___y_4008_;
v___y_3993_ = v___y_4009_;
v_a_3994_ = v_a_4011_;
goto v___jp_3991_;
}
else
{
lean_object* v_a_4012_; 
v_a_4012_ = lean_ctor_get(v___y_4010_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v___y_4010_, 1);
v___y_4003_ = v___y_4008_;
v___y_4004_ = v___y_4009_;
v_a_4005_ = v_a_4012_;
goto v___jp_4002_;
}
}
v___jp_4013_:
{
if (lean_obj_tag(v___y_4016_) == 0)
{
lean_object* v_a_4017_; 
v_a_4017_ = lean_ctor_get(v___y_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___y_4016_, 1);
v___y_3997_ = v___y_4014_;
v___y_3998_ = v___y_4015_;
v_a_3999_ = v_a_4017_;
goto v___jp_3996_;
}
else
{
lean_object* v_a_4018_; 
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
v_a_4018_ = lean_ctor_get(v___y_4016_, 0);
lean_inc(v_a_4018_);
lean_dec_ref_known(v___y_4016_, 1);
v___y_4003_ = v___y_4014_;
v___y_4004_ = v___y_4015_;
v_a_4005_ = v_a_4018_;
goto v___jp_4002_;
}
}
v___jp_4019_:
{
if (v___y_4024_ == 0)
{
lean_object* v___x_4025_; 
lean_dec_ref(v___y_4020_);
v___x_4025_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4023_, v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_dec_ref_known(v___x_4025_, 1);
v___y_3997_ = v___y_4021_;
v___y_3998_ = v___y_4022_;
v_a_3999_ = v_snd_2981_;
goto v___jp_3996_;
}
else
{
lean_object* v_a_4026_; 
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2981_);
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4025_, 1);
v___y_4003_ = v___y_4021_;
v___y_4004_ = v___y_4022_;
v_a_4005_ = v_a_4026_;
goto v___jp_4002_;
}
}
else
{
lean_dec_ref(v___y_4023_);
lean_dec(v_snd_2981_);
v___y_4014_ = v___y_4021_;
v___y_4015_ = v___y_4022_;
v___y_4016_ = v___y_4020_;
goto v___jp_4013_;
}
}
v___jp_4027_:
{
lean_object* v___x_4031_; 
v___x_4031_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4033_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4031_, 1);
lean_inc(v_snd_2981_);
lean_inc(v_trace_2966_);
v___x_4033_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4030_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_dec(v_a_4032_);
lean_dec(v_snd_2981_);
v___y_4014_ = v___y_4028_;
v___y_4015_ = v___y_4029_;
v___y_4016_ = v___x_4033_;
goto v___jp_4013_;
}
else
{
lean_object* v_a_4034_; uint8_t v___x_4035_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
v___x_4035_ = l_Lean_Exception_isInterrupt(v_a_4034_);
if (v___x_4035_ == 0)
{
uint8_t v___x_4036_; 
lean_inc(v_a_4034_);
v___x_4036_ = l_Lean_Exception_isRuntime(v_a_4034_);
v___y_4020_ = v___x_4033_;
v___y_4021_ = v___y_4028_;
v___y_4022_ = v___y_4029_;
v___y_4023_ = v_a_4032_;
v___y_4024_ = v___x_4036_;
goto v___jp_4019_;
}
else
{
v___y_4020_ = v___x_4033_;
v___y_4021_ = v___y_4028_;
v___y_4022_ = v___y_4029_;
v___y_4023_ = v_a_4032_;
v___y_4024_ = v___x_4035_;
goto v___jp_4019_;
}
}
}
else
{
lean_object* v_a_4037_; 
lean_dec(v___y_4030_);
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_4037_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4031_, 1);
v___y_4003_ = v___y_4028_;
v___y_4004_ = v___y_4029_;
v_a_4005_ = v_a_4037_;
goto v___jp_4002_;
}
}
v___jp_4038_:
{
if (v___y_4042_ == 0)
{
uint8_t v___x_4043_; 
v___x_4043_ = l_List_isEmpty___redArg(v_fst_3906_);
lean_dec(v_fst_3906_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
lean_dec(v___y_4041_);
lean_dec(v___x_3911_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_4044_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4045_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4044_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_4008_ = v___y_4039_;
v___y_4009_ = v___y_4040_;
v___y_4010_ = v___x_4045_;
goto v___jp_4007_;
}
else
{
lean_object* v___x_4046_; 
lean_inc(v_trace_2966_);
v___x_4046_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4041_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4048_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_a_4047_);
lean_dec_ref_known(v___x_4046_, 1);
v___x_4048_ = l_List_appendTR___redArg(v___x_3911_, v_a_4047_);
v___y_3992_ = v___y_4039_;
v___y_3993_ = v___y_4040_;
v_a_3994_ = v___x_4048_;
goto v___jp_3991_;
}
else
{
lean_dec(v___x_3911_);
v___y_4008_ = v___y_4039_;
v___y_4009_ = v___y_4040_;
v___y_4010_ = v___x_4046_;
goto v___jp_4007_;
}
}
}
else
{
v___y_4028_ = v___y_4039_;
v___y_4029_ = v___y_4040_;
v___y_4030_ = v___y_4041_;
goto v___jp_4027_;
}
}
v___jp_4049_:
{
uint8_t v_commitIndependentGoals_4053_; lean_object* v___x_4054_; 
v_commitIndependentGoals_4053_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___x_3911_);
v___x_4054_ = l_List_appendTR___redArg(v_a_4052_, v___x_3911_);
if (v_commitIndependentGoals_4053_ == 0)
{
v___y_4039_ = v___y_4050_;
v___y_4040_ = v___y_4051_;
v___y_4041_ = v___x_4054_;
v___y_4042_ = v___x_2985_;
goto v___jp_4038_;
}
else
{
uint8_t v___x_4055_; 
v___x_4055_ = l_List_isEmpty___redArg(v___x_3911_);
if (v___x_4055_ == 0)
{
v___y_4028_ = v___y_4050_;
v___y_4029_ = v___y_4051_;
v___y_4030_ = v___x_4054_;
goto v___jp_4027_;
}
else
{
v___y_4039_ = v___y_4050_;
v___y_4040_ = v___y_4051_;
v___y_4041_ = v___x_4054_;
v___y_4042_ = v___x_2985_;
goto v___jp_4038_;
}
}
}
v___jp_4056_:
{
lean_object* v___x_4060_; double v___x_4061_; double v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4060_ = lean_io_get_num_heartbeats();
v___x_4061_ = lean_float_of_nat(v___y_4058_);
v___x_4062_ = lean_float_of_nat(v___x_4060_);
v___x_4063_ = lean_box_float(v___x_4061_);
v___x_4064_ = lean_box_float(v___x_4062_);
v___x_4065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4063_);
lean_ctor_set(v___x_4065_, 1, v___x_4064_);
v___x_4066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4066_, 0, v_a_4059_);
lean_ctor_set(v___x_4066_, 1, v___x_4065_);
v___x_4067_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2988_, v___x_3073_, v_options_2987_, v___x_3076_, v___y_4057_, v___f_3972_, v___x_4066_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_4067_;
}
v___jp_4068_:
{
lean_object* v___x_4072_; 
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v_a_4071_);
v___y_4057_ = v___y_4070_;
v___y_4058_ = v___y_4069_;
v_a_4059_ = v___x_4072_;
goto v___jp_4056_;
}
v___jp_4073_:
{
lean_object* v___x_4077_; 
v___x_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4077_, 0, v_a_4076_);
v___y_4057_ = v___y_4075_;
v___y_4058_ = v___y_4074_;
v_a_4059_ = v___x_4077_;
goto v___jp_4056_;
}
v___jp_4078_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = l_List_appendTR___redArg(v___x_3911_, v_fst_3906_);
v___x_4083_ = l_List_appendTR___redArg(v___x_4082_, v_a_4081_);
v___y_4074_ = v___y_4080_;
v___y_4075_ = v___y_4079_;
v_a_4076_ = v___x_4083_;
goto v___jp_4073_;
}
v___jp_4084_:
{
if (lean_obj_tag(v___y_4087_) == 0)
{
lean_object* v_a_4088_; 
v_a_4088_ = lean_ctor_get(v___y_4087_, 0);
lean_inc(v_a_4088_);
lean_dec_ref_known(v___y_4087_, 1);
v___y_4079_ = v___y_4086_;
v___y_4080_ = v___y_4085_;
v_a_4081_ = v_a_4088_;
goto v___jp_4078_;
}
else
{
lean_object* v_a_4089_; 
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
v_a_4089_ = lean_ctor_get(v___y_4087_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___y_4087_, 1);
v___y_4069_ = v___y_4085_;
v___y_4070_ = v___y_4086_;
v_a_4071_ = v_a_4089_;
goto v___jp_4068_;
}
}
v___jp_4090_:
{
if (v___y_4095_ == 0)
{
lean_object* v___x_4096_; 
lean_dec_ref(v___y_4092_);
v___x_4096_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4091_, v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_dec_ref_known(v___x_4096_, 1);
v___y_4079_ = v___y_4094_;
v___y_4080_ = v___y_4093_;
v_a_4081_ = v_snd_2981_;
goto v___jp_4078_;
}
else
{
lean_object* v_a_4097_; 
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2981_);
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4096_, 1);
v___y_4069_ = v___y_4093_;
v___y_4070_ = v___y_4094_;
v_a_4071_ = v_a_4097_;
goto v___jp_4068_;
}
}
else
{
lean_dec_ref(v___y_4091_);
lean_dec(v_snd_2981_);
v___y_4085_ = v___y_4093_;
v___y_4086_ = v___y_4094_;
v___y_4087_ = v___y_4092_;
goto v___jp_4084_;
}
}
v___jp_4098_:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4104_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v___x_4102_, 1);
lean_inc(v_snd_2981_);
lean_inc(v_trace_2966_);
v___x_4104_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4101_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_dec(v_a_4103_);
lean_dec(v_snd_2981_);
v___y_4085_ = v___y_4100_;
v___y_4086_ = v___y_4099_;
v___y_4087_ = v___x_4104_;
goto v___jp_4084_;
}
else
{
lean_object* v_a_4105_; uint8_t v___x_4106_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
v___x_4106_ = l_Lean_Exception_isInterrupt(v_a_4105_);
if (v___x_4106_ == 0)
{
uint8_t v___x_4107_; 
lean_inc(v_a_4105_);
v___x_4107_ = l_Lean_Exception_isRuntime(v_a_4105_);
v___y_4091_ = v_a_4103_;
v___y_4092_ = v___x_4104_;
v___y_4093_ = v___y_4100_;
v___y_4094_ = v___y_4099_;
v___y_4095_ = v___x_4107_;
goto v___jp_4090_;
}
else
{
v___y_4091_ = v_a_4103_;
v___y_4092_ = v___x_4104_;
v___y_4093_ = v___y_4100_;
v___y_4094_ = v___y_4099_;
v___y_4095_ = v___x_4106_;
goto v___jp_4090_;
}
}
}
else
{
lean_object* v_a_4108_; 
lean_dec(v___y_4101_);
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_4108_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4108_);
lean_dec_ref_known(v___x_4102_, 1);
v___y_4069_ = v___y_4100_;
v___y_4070_ = v___y_4099_;
v_a_4071_ = v_a_4108_;
goto v___jp_4068_;
}
}
v___jp_4109_:
{
if (lean_obj_tag(v___y_4112_) == 0)
{
lean_object* v_a_4113_; 
v_a_4113_ = lean_ctor_get(v___y_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v___y_4112_, 1);
v___y_4074_ = v___y_4111_;
v___y_4075_ = v___y_4110_;
v_a_4076_ = v_a_4113_;
goto v___jp_4073_;
}
else
{
lean_object* v_a_4114_; 
v_a_4114_ = lean_ctor_get(v___y_4112_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___y_4112_, 1);
v___y_4069_ = v___y_4111_;
v___y_4070_ = v___y_4110_;
v_a_4071_ = v_a_4114_;
goto v___jp_4068_;
}
}
v___jp_4115_:
{
lean_object* v___x_4119_; 
lean_inc(v_trace_2966_);
v___x_4119_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4118_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4121_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v___x_4121_ = l_List_appendTR___redArg(v___x_3911_, v_a_4120_);
v___y_4074_ = v___y_4117_;
v___y_4075_ = v___y_4116_;
v_a_4076_ = v___x_4121_;
goto v___jp_4073_;
}
else
{
lean_dec(v___x_3911_);
v___y_4110_ = v___y_4116_;
v___y_4111_ = v___y_4117_;
v___y_4112_ = v___x_4119_;
goto v___jp_4109_;
}
}
v___jp_4122_:
{
if (v___y_4127_ == 0)
{
uint8_t v___x_4128_; 
v___x_4128_ = l_List_isEmpty___redArg(v_fst_3906_);
lean_dec(v_fst_3906_);
if (v___x_4128_ == 0)
{
if (v___y_4123_ == 0)
{
v___y_4116_ = v___y_4125_;
v___y_4117_ = v___y_4124_;
v___y_4118_ = v___y_4126_;
goto v___jp_4115_;
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_dec(v___y_4126_);
lean_dec(v___x_3911_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_4129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4130_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4129_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_4110_ = v___y_4125_;
v___y_4111_ = v___y_4124_;
v___y_4112_ = v___x_4130_;
goto v___jp_4109_;
}
}
else
{
v___y_4116_ = v___y_4125_;
v___y_4117_ = v___y_4124_;
v___y_4118_ = v___y_4126_;
goto v___jp_4115_;
}
}
else
{
v___y_4099_ = v___y_4125_;
v___y_4100_ = v___y_4124_;
v___y_4101_ = v___y_4126_;
goto v___jp_4098_;
}
}
v___jp_4131_:
{
uint8_t v_commitIndependentGoals_4136_; lean_object* v___x_4137_; 
v_commitIndependentGoals_4136_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___x_3911_);
v___x_4137_ = l_List_appendTR___redArg(v_a_4135_, v___x_3911_);
if (v_commitIndependentGoals_4136_ == 0)
{
v___y_4123_ = v___y_4132_;
v___y_4124_ = v___y_4133_;
v___y_4125_ = v___y_4134_;
v___y_4126_ = v___x_4137_;
v___y_4127_ = v___x_2985_;
goto v___jp_4122_;
}
else
{
uint8_t v___x_4138_; 
v___x_4138_ = l_List_isEmpty___redArg(v___x_3911_);
if (v___x_4138_ == 0)
{
v___y_4099_ = v___y_4134_;
v___y_4100_ = v___y_4133_;
v___y_4101_ = v___x_4137_;
goto v___jp_4098_;
}
else
{
v___y_4123_ = v___y_4132_;
v___y_4124_ = v___y_4133_;
v___y_4125_ = v___y_4134_;
v___y_4126_ = v___x_4137_;
v___y_4127_ = v___x_2985_;
goto v___jp_4122_;
}
}
}
v___jp_4139_:
{
lean_object* v___x_4140_; 
v___x_4140_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2974_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v___x_4142_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4143_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2987_, v___x_4142_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4144_ = lean_io_mono_nanos_now();
v___x_4145_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2988_, v___x_2985_, v_goals_2969_, v___x_3973_, v_a_2972_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4147_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4145_, 1);
v___x_4147_ = l_List_reverse___redArg(v_a_4146_);
v___y_4050_ = v___x_4144_;
v___y_4051_ = v_a_4141_;
v_a_4052_ = v___x_4147_;
goto v___jp_4049_;
}
else
{
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4148_; 
v_a_4148_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4145_, 1);
v___y_4050_ = v___x_4144_;
v___y_4051_ = v_a_4141_;
v_a_4052_ = v_a_4148_;
goto v___jp_4049_;
}
else
{
lean_object* v_a_4149_; 
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_4149_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4145_, 1);
v___y_4003_ = v___x_4144_;
v___y_4004_ = v_a_4141_;
v_a_4005_ = v_a_4149_;
goto v___jp_4002_;
}
}
}
else
{
lean_object* v___x_4150_; lean_object* v___x_4151_; 
lean_del_object(v___x_3909_);
v___x_4150_ = lean_io_get_num_heartbeats();
v___x_4151_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2988_, v___x_2985_, v_goals_2969_, v___x_3973_, v_a_2972_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4153_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4153_ = l_List_reverse___redArg(v_a_4152_);
v___y_4132_ = v___x_4143_;
v___y_4133_ = v___x_4150_;
v___y_4134_ = v_a_4141_;
v_a_4135_ = v___x_4153_;
goto v___jp_4131_;
}
else
{
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4154_; 
v_a_4154_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4151_, 1);
v___y_4132_ = v___x_4143_;
v___y_4133_ = v___x_4150_;
v___y_4134_ = v_a_4141_;
v_a_4135_ = v_a_4154_;
goto v___jp_4131_;
}
else
{
lean_object* v_a_4155_; 
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_4155_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4151_, 1);
v___y_4069_ = v___x_4150_;
v___y_4070_ = v_a_4141_;
v_a_4071_ = v_a_4155_;
goto v___jp_4068_;
}
}
}
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec_ref(v___f_3972_);
lean_dec(v___x_3911_);
lean_del_object(v___x_3909_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2981_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_4156_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4140_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4140_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec(v_snd_2981_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_4170_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_3901_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_3901_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
else
{
goto v___jp_3854_;
}
}
else
{
goto v___jp_3854_;
}
v___jp_3077_:
{
lean_object* v___x_3081_; double v___x_3082_; double v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3081_ = lean_io_get_num_heartbeats();
v___x_3082_ = lean_float_of_nat(v___y_3079_);
v___x_3083_ = lean_float_of_nat(v___x_3081_);
v___x_3084_ = lean_box_float(v___x_3082_);
v___x_3085_ = lean_box_float(v___x_3083_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 1, v___x_3085_);
lean_ctor_set(v___x_2983_, 0, v___x_3084_);
v___x_3087_ = v___x_2983_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3084_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v_a_3080_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2988_, v___x_3073_, v_options_2987_, v___x_3076_, v___y_3078_, v___f_3072_, v___x_3088_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3089_;
}
}
v___jp_3091_:
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v_a_3094_);
v___y_3078_ = v___y_3092_;
v___y_3079_ = v___y_3093_;
v_a_3080_ = v___x_3095_;
goto v___jp_3077_;
}
v___jp_3096_:
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3100_, 0, v_a_3099_);
v___y_3078_ = v___y_3097_;
v___y_3079_ = v___y_3098_;
v_a_3080_ = v___x_3100_;
goto v___jp_3077_;
}
v___jp_3101_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = l_List_appendTR___redArg(v___y_3102_, v___y_3103_);
v___x_3108_ = l_List_appendTR___redArg(v___x_3107_, v_a_3106_);
v___y_3097_ = v___y_3104_;
v___y_3098_ = v___y_3105_;
v_a_3099_ = v___x_3108_;
goto v___jp_3096_;
}
v___jp_3109_:
{
if (lean_obj_tag(v___y_3114_) == 0)
{
lean_object* v_a_3115_; 
v_a_3115_ = lean_ctor_get(v___y_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___y_3114_, 1);
v___y_3102_ = v___y_3110_;
v___y_3103_ = v___y_3111_;
v___y_3104_ = v___y_3112_;
v___y_3105_ = v___y_3113_;
v_a_3106_ = v_a_3115_;
goto v___jp_3101_;
}
else
{
lean_object* v_a_3116_; 
lean_dec(v___y_3111_);
lean_dec(v___y_3110_);
v_a_3116_ = lean_ctor_get(v___y_3114_, 0);
lean_inc(v_a_3116_);
lean_dec_ref_known(v___y_3114_, 1);
v___y_3092_ = v___y_3112_;
v___y_3093_ = v___y_3113_;
v_a_3094_ = v_a_3116_;
goto v___jp_3091_;
}
}
v___jp_3117_:
{
if (v___y_3124_ == 0)
{
lean_object* v___x_3125_; 
lean_dec_ref(v___y_3121_);
v___x_3125_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3120_, v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_dec_ref_known(v___x_3125_, 1);
v___y_3102_ = v___y_3118_;
v___y_3103_ = v___y_3119_;
v___y_3104_ = v___y_3122_;
v___y_3105_ = v___y_3123_;
v_a_3106_ = v_snd_2981_;
goto v___jp_3101_;
}
else
{
lean_object* v_a_3126_; 
lean_dec(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec(v_snd_2981_);
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
lean_dec_ref_known(v___x_3125_, 1);
v___y_3092_ = v___y_3122_;
v___y_3093_ = v___y_3123_;
v_a_3094_ = v_a_3126_;
goto v___jp_3091_;
}
}
else
{
lean_dec_ref(v___y_3120_);
lean_dec(v_snd_2981_);
v___y_3110_ = v___y_3118_;
v___y_3111_ = v___y_3119_;
v___y_3112_ = v___y_3122_;
v___y_3113_ = v___y_3123_;
v___y_3114_ = v___y_3121_;
goto v___jp_3109_;
}
}
v___jp_3127_:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3135_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3134_);
lean_dec_ref_known(v___x_3133_, 1);
lean_inc(v_snd_2981_);
lean_inc(v_trace_2966_);
v___x_3135_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3130_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_dec(v_a_3134_);
lean_dec(v_snd_2981_);
v___y_3110_ = v___y_3128_;
v___y_3111_ = v___y_3129_;
v___y_3112_ = v___y_3131_;
v___y_3113_ = v___y_3132_;
v___y_3114_ = v___x_3135_;
goto v___jp_3109_;
}
else
{
lean_object* v_a_3136_; uint8_t v___x_3137_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v___x_3137_ = l_Lean_Exception_isInterrupt(v_a_3136_);
if (v___x_3137_ == 0)
{
uint8_t v___x_3138_; 
lean_inc(v_a_3136_);
v___x_3138_ = l_Lean_Exception_isRuntime(v_a_3136_);
v___y_3118_ = v___y_3128_;
v___y_3119_ = v___y_3129_;
v___y_3120_ = v_a_3134_;
v___y_3121_ = v___x_3135_;
v___y_3122_ = v___y_3131_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___x_3138_;
goto v___jp_3117_;
}
else
{
v___y_3118_ = v___y_3128_;
v___y_3119_ = v___y_3129_;
v___y_3120_ = v_a_3134_;
v___y_3121_ = v___x_3135_;
v___y_3122_ = v___y_3131_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___x_3137_;
goto v___jp_3117_;
}
}
}
else
{
lean_object* v_a_3139_; 
lean_dec(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3139_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___x_3133_, 1);
v___y_3092_ = v___y_3131_;
v___y_3093_ = v___y_3132_;
v_a_3094_ = v_a_3139_;
goto v___jp_3091_;
}
}
v___jp_3140_:
{
if (lean_obj_tag(v___y_3143_) == 0)
{
lean_object* v_a_3144_; 
v_a_3144_ = lean_ctor_get(v___y_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref_known(v___y_3143_, 1);
v___y_3097_ = v___y_3141_;
v___y_3098_ = v___y_3142_;
v_a_3099_ = v_a_3144_;
goto v___jp_3096_;
}
else
{
lean_object* v_a_3145_; 
v_a_3145_ = lean_ctor_get(v___y_3143_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___y_3143_, 1);
v___y_3092_ = v___y_3141_;
v___y_3093_ = v___y_3142_;
v_a_3094_ = v_a_3145_;
goto v___jp_3091_;
}
}
v___jp_3146_:
{
lean_object* v___x_3154_; double v___x_3155_; double v___x_3156_; double v___x_3157_; double v___x_3158_; double v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3154_ = lean_io_mono_nanos_now();
v___x_3155_ = lean_float_of_nat(v___y_3148_);
v___x_3156_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3157_ = lean_float_div(v___x_3155_, v___x_3156_);
v___x_3158_ = lean_float_of_nat(v___x_3154_);
v___x_3159_ = lean_float_div(v___x_3158_, v___x_3156_);
v___x_3160_ = lean_box_float(v___x_3157_);
v___x_3161_ = lean_box_float(v___x_3159_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3163_, 0, v_a_3153_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
lean_inc(v_trace_2966_);
v___x_3164_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2988_, v___x_3073_, v_options_2987_, v___y_3147_, v___y_3150_, v___y_3149_, v___x_3163_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3141_ = v___y_3151_;
v___y_3142_ = v___y_3152_;
v___y_3143_ = v___x_3164_;
goto v___jp_3140_;
}
v___jp_3165_:
{
lean_object* v___x_3173_; 
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v_a_3172_);
v___y_3147_ = v___y_3167_;
v___y_3148_ = v___y_3166_;
v___y_3149_ = v___y_3169_;
v___y_3150_ = v___y_3168_;
v___y_3151_ = v___y_3170_;
v___y_3152_ = v___y_3171_;
v_a_3153_ = v___x_3173_;
goto v___jp_3146_;
}
v___jp_3174_:
{
lean_object* v___x_3182_; 
v___x_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_a_3181_);
v___y_3147_ = v___y_3176_;
v___y_3148_ = v___y_3175_;
v___y_3149_ = v___y_3178_;
v___y_3150_ = v___y_3177_;
v___y_3151_ = v___y_3179_;
v___y_3152_ = v___y_3180_;
v_a_3153_ = v___x_3182_;
goto v___jp_3146_;
}
v___jp_3183_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = l_List_appendTR___redArg(v___y_3184_, v___y_3185_);
v___x_3194_ = l_List_appendTR___redArg(v___x_3193_, v_a_3192_);
v___y_3175_ = v___y_3187_;
v___y_3176_ = v___y_3186_;
v___y_3177_ = v___y_3189_;
v___y_3178_ = v___y_3188_;
v___y_3179_ = v___y_3190_;
v___y_3180_ = v___y_3191_;
v_a_3181_ = v___x_3194_;
goto v___jp_3174_;
}
v___jp_3195_:
{
if (lean_obj_tag(v___y_3204_) == 0)
{
lean_object* v_a_3205_; 
v_a_3205_ = lean_ctor_get(v___y_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___y_3204_, 1);
v___y_3184_ = v___y_3196_;
v___y_3185_ = v___y_3197_;
v___y_3186_ = v___y_3199_;
v___y_3187_ = v___y_3198_;
v___y_3188_ = v___y_3201_;
v___y_3189_ = v___y_3200_;
v___y_3190_ = v___y_3202_;
v___y_3191_ = v___y_3203_;
v_a_3192_ = v_a_3205_;
goto v___jp_3183_;
}
else
{
lean_object* v_a_3206_; 
lean_dec(v___y_3197_);
lean_dec(v___y_3196_);
v_a_3206_ = lean_ctor_get(v___y_3204_, 0);
lean_inc(v_a_3206_);
lean_dec_ref_known(v___y_3204_, 1);
v___y_3166_ = v___y_3198_;
v___y_3167_ = v___y_3199_;
v___y_3168_ = v___y_3200_;
v___y_3169_ = v___y_3201_;
v___y_3170_ = v___y_3202_;
v___y_3171_ = v___y_3203_;
v_a_3172_ = v_a_3206_;
goto v___jp_3165_;
}
}
v___jp_3207_:
{
if (v___y_3218_ == 0)
{
lean_object* v___x_3219_; 
lean_dec_ref(v___y_3212_);
v___x_3219_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3216_, v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_dec_ref_known(v___x_3219_, 1);
v___y_3184_ = v___y_3208_;
v___y_3185_ = v___y_3209_;
v___y_3186_ = v___y_3211_;
v___y_3187_ = v___y_3210_;
v___y_3188_ = v___y_3214_;
v___y_3189_ = v___y_3213_;
v___y_3190_ = v___y_3215_;
v___y_3191_ = v___y_3217_;
v_a_3192_ = v_snd_2981_;
goto v___jp_3183_;
}
else
{
lean_object* v_a_3220_; 
lean_dec(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec(v_snd_2981_);
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v___y_3166_ = v___y_3210_;
v___y_3167_ = v___y_3211_;
v___y_3168_ = v___y_3213_;
v___y_3169_ = v___y_3214_;
v___y_3170_ = v___y_3215_;
v___y_3171_ = v___y_3217_;
v_a_3172_ = v_a_3220_;
goto v___jp_3165_;
}
}
else
{
lean_dec_ref(v___y_3216_);
lean_dec(v_snd_2981_);
v___y_3196_ = v___y_3208_;
v___y_3197_ = v___y_3209_;
v___y_3198_ = v___y_3210_;
v___y_3199_ = v___y_3211_;
v___y_3200_ = v___y_3213_;
v___y_3201_ = v___y_3214_;
v___y_3202_ = v___y_3215_;
v___y_3203_ = v___y_3217_;
v___y_3204_ = v___y_3212_;
goto v___jp_3195_;
}
}
v___jp_3221_:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___x_3231_, 1);
lean_inc(v_snd_2981_);
lean_inc(v_trace_2966_);
v___x_3233_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3226_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_dec(v_a_3232_);
lean_dec(v_snd_2981_);
v___y_3196_ = v___y_3222_;
v___y_3197_ = v___y_3223_;
v___y_3198_ = v___y_3225_;
v___y_3199_ = v___y_3224_;
v___y_3200_ = v___y_3228_;
v___y_3201_ = v___y_3227_;
v___y_3202_ = v___y_3229_;
v___y_3203_ = v___y_3230_;
v___y_3204_ = v___x_3233_;
goto v___jp_3195_;
}
else
{
lean_object* v_a_3234_; uint8_t v___x_3235_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v___x_3235_ = l_Lean_Exception_isInterrupt(v_a_3234_);
if (v___x_3235_ == 0)
{
uint8_t v___x_3236_; 
lean_inc(v_a_3234_);
v___x_3236_ = l_Lean_Exception_isRuntime(v_a_3234_);
v___y_3208_ = v___y_3222_;
v___y_3209_ = v___y_3223_;
v___y_3210_ = v___y_3225_;
v___y_3211_ = v___y_3224_;
v___y_3212_ = v___x_3233_;
v___y_3213_ = v___y_3228_;
v___y_3214_ = v___y_3227_;
v___y_3215_ = v___y_3229_;
v___y_3216_ = v_a_3232_;
v___y_3217_ = v___y_3230_;
v___y_3218_ = v___x_3236_;
goto v___jp_3207_;
}
else
{
v___y_3208_ = v___y_3222_;
v___y_3209_ = v___y_3223_;
v___y_3210_ = v___y_3225_;
v___y_3211_ = v___y_3224_;
v___y_3212_ = v___x_3233_;
v___y_3213_ = v___y_3228_;
v___y_3214_ = v___y_3227_;
v___y_3215_ = v___y_3229_;
v___y_3216_ = v_a_3232_;
v___y_3217_ = v___y_3230_;
v___y_3218_ = v___x_3235_;
goto v___jp_3207_;
}
}
}
else
{
lean_object* v_a_3237_; 
lean_dec(v___y_3226_);
lean_dec(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3237_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3231_, 1);
v___y_3166_ = v___y_3225_;
v___y_3167_ = v___y_3224_;
v___y_3168_ = v___y_3228_;
v___y_3169_ = v___y_3227_;
v___y_3170_ = v___y_3229_;
v___y_3171_ = v___y_3230_;
v_a_3172_ = v_a_3237_;
goto v___jp_3165_;
}
}
v___jp_3238_:
{
if (lean_obj_tag(v___y_3245_) == 0)
{
lean_object* v_a_3246_; 
v_a_3246_ = lean_ctor_get(v___y_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v___y_3245_, 1);
v___y_3175_ = v___y_3240_;
v___y_3176_ = v___y_3239_;
v___y_3177_ = v___y_3242_;
v___y_3178_ = v___y_3241_;
v___y_3179_ = v___y_3243_;
v___y_3180_ = v___y_3244_;
v_a_3181_ = v_a_3246_;
goto v___jp_3174_;
}
else
{
lean_object* v_a_3247_; 
v_a_3247_ = lean_ctor_get(v___y_3245_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___y_3245_, 1);
v___y_3166_ = v___y_3240_;
v___y_3167_ = v___y_3239_;
v___y_3168_ = v___y_3242_;
v___y_3169_ = v___y_3241_;
v___y_3170_ = v___y_3243_;
v___y_3171_ = v___y_3244_;
v_a_3172_ = v_a_3247_;
goto v___jp_3165_;
}
}
v___jp_3248_:
{
if (v___y_3258_ == 0)
{
uint8_t v___x_3259_; 
v___x_3259_ = l_List_isEmpty___redArg(v___y_3250_);
lean_dec(v___y_3250_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec(v___y_3253_);
lean_dec(v___y_3249_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3261_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3260_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3239_ = v___y_3252_;
v___y_3240_ = v___y_3251_;
v___y_3241_ = v___y_3255_;
v___y_3242_ = v___y_3254_;
v___y_3243_ = v___y_3256_;
v___y_3244_ = v___y_3257_;
v___y_3245_ = v___x_3261_;
goto v___jp_3238_;
}
else
{
lean_object* v___x_3262_; 
lean_inc(v_trace_2966_);
v___x_3262_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3253_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3264_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3264_ = l_List_appendTR___redArg(v___y_3249_, v_a_3263_);
v___y_3175_ = v___y_3251_;
v___y_3176_ = v___y_3252_;
v___y_3177_ = v___y_3254_;
v___y_3178_ = v___y_3255_;
v___y_3179_ = v___y_3256_;
v___y_3180_ = v___y_3257_;
v_a_3181_ = v___x_3264_;
goto v___jp_3174_;
}
else
{
lean_dec(v___y_3249_);
v___y_3239_ = v___y_3252_;
v___y_3240_ = v___y_3251_;
v___y_3241_ = v___y_3255_;
v___y_3242_ = v___y_3254_;
v___y_3243_ = v___y_3256_;
v___y_3244_ = v___y_3257_;
v___y_3245_ = v___x_3262_;
goto v___jp_3238_;
}
}
}
else
{
v___y_3222_ = v___y_3249_;
v___y_3223_ = v___y_3250_;
v___y_3224_ = v___y_3252_;
v___y_3225_ = v___y_3251_;
v___y_3226_ = v___y_3253_;
v___y_3227_ = v___y_3255_;
v___y_3228_ = v___y_3254_;
v___y_3229_ = v___y_3256_;
v___y_3230_ = v___y_3257_;
goto v___jp_3221_;
}
}
v___jp_3265_:
{
uint8_t v_commitIndependentGoals_3275_; lean_object* v___x_3276_; 
v_commitIndependentGoals_3275_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3266_);
v___x_3276_ = l_List_appendTR___redArg(v_a_3274_, v___y_3266_);
if (v_commitIndependentGoals_3275_ == 0)
{
v___y_3249_ = v___y_3266_;
v___y_3250_ = v___y_3267_;
v___y_3251_ = v___y_3268_;
v___y_3252_ = v___y_3269_;
v___y_3253_ = v___x_3276_;
v___y_3254_ = v___y_3270_;
v___y_3255_ = v___y_3271_;
v___y_3256_ = v___y_3272_;
v___y_3257_ = v___y_3273_;
v___y_3258_ = v___x_2985_;
goto v___jp_3248_;
}
else
{
uint8_t v___x_3277_; 
v___x_3277_ = l_List_isEmpty___redArg(v___y_3266_);
if (v___x_3277_ == 0)
{
v___y_3222_ = v___y_3266_;
v___y_3223_ = v___y_3267_;
v___y_3224_ = v___y_3269_;
v___y_3225_ = v___y_3268_;
v___y_3226_ = v___x_3276_;
v___y_3227_ = v___y_3271_;
v___y_3228_ = v___y_3270_;
v___y_3229_ = v___y_3272_;
v___y_3230_ = v___y_3273_;
goto v___jp_3221_;
}
else
{
v___y_3249_ = v___y_3266_;
v___y_3250_ = v___y_3267_;
v___y_3251_ = v___y_3268_;
v___y_3252_ = v___y_3269_;
v___y_3253_ = v___x_3276_;
v___y_3254_ = v___y_3270_;
v___y_3255_ = v___y_3271_;
v___y_3256_ = v___y_3272_;
v___y_3257_ = v___y_3273_;
v___y_3258_ = v___x_2985_;
goto v___jp_3248_;
}
}
}
v___jp_3278_:
{
lean_object* v___x_3286_; double v___x_3287_; double v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3286_ = lean_io_get_num_heartbeats();
v___x_3287_ = lean_float_of_nat(v___y_3282_);
v___x_3288_ = lean_float_of_nat(v___x_3286_);
v___x_3289_ = lean_box_float(v___x_3287_);
v___x_3290_ = lean_box_float(v___x_3288_);
v___x_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3292_, 0, v_a_3285_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
lean_inc(v_trace_2966_);
v___x_3293_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2988_, v___x_3073_, v_options_2987_, v___y_3279_, v___y_3281_, v___y_3280_, v___x_3292_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3141_ = v___y_3283_;
v___y_3142_ = v___y_3284_;
v___y_3143_ = v___x_3293_;
goto v___jp_3140_;
}
v___jp_3294_:
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3302_, 0, v_a_3301_);
v___y_3279_ = v___y_3295_;
v___y_3280_ = v___y_3297_;
v___y_3281_ = v___y_3296_;
v___y_3282_ = v___y_3298_;
v___y_3283_ = v___y_3299_;
v___y_3284_ = v___y_3300_;
v_a_3285_ = v___x_3302_;
goto v___jp_3278_;
}
v___jp_3303_:
{
lean_object* v___x_3311_; 
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v_a_3310_);
v___y_3279_ = v___y_3304_;
v___y_3280_ = v___y_3306_;
v___y_3281_ = v___y_3305_;
v___y_3282_ = v___y_3307_;
v___y_3283_ = v___y_3308_;
v___y_3284_ = v___y_3309_;
v_a_3285_ = v___x_3311_;
goto v___jp_3278_;
}
v___jp_3312_:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = l_List_appendTR___redArg(v___y_3313_, v___y_3314_);
v___x_3323_ = l_List_appendTR___redArg(v___x_3322_, v_a_3321_);
v___y_3304_ = v___y_3315_;
v___y_3305_ = v___y_3317_;
v___y_3306_ = v___y_3316_;
v___y_3307_ = v___y_3318_;
v___y_3308_ = v___y_3319_;
v___y_3309_ = v___y_3320_;
v_a_3310_ = v___x_3323_;
goto v___jp_3303_;
}
v___jp_3324_:
{
if (lean_obj_tag(v___y_3333_) == 0)
{
lean_object* v_a_3334_; 
v_a_3334_ = lean_ctor_get(v___y_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___y_3333_, 1);
v___y_3313_ = v___y_3325_;
v___y_3314_ = v___y_3326_;
v___y_3315_ = v___y_3327_;
v___y_3316_ = v___y_3329_;
v___y_3317_ = v___y_3328_;
v___y_3318_ = v___y_3330_;
v___y_3319_ = v___y_3331_;
v___y_3320_ = v___y_3332_;
v_a_3321_ = v_a_3334_;
goto v___jp_3312_;
}
else
{
lean_object* v_a_3335_; 
lean_dec(v___y_3326_);
lean_dec(v___y_3325_);
v_a_3335_ = lean_ctor_get(v___y_3333_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___y_3333_, 1);
v___y_3295_ = v___y_3327_;
v___y_3296_ = v___y_3328_;
v___y_3297_ = v___y_3329_;
v___y_3298_ = v___y_3330_;
v___y_3299_ = v___y_3331_;
v___y_3300_ = v___y_3332_;
v_a_3301_ = v_a_3335_;
goto v___jp_3294_;
}
}
v___jp_3336_:
{
if (v___y_3347_ == 0)
{
lean_object* v___x_3348_; 
lean_dec_ref(v___y_3345_);
v___x_3348_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3343_, v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_dec_ref_known(v___x_3348_, 1);
v___y_3313_ = v___y_3337_;
v___y_3314_ = v___y_3338_;
v___y_3315_ = v___y_3339_;
v___y_3316_ = v___y_3341_;
v___y_3317_ = v___y_3340_;
v___y_3318_ = v___y_3342_;
v___y_3319_ = v___y_3344_;
v___y_3320_ = v___y_3346_;
v_a_3321_ = v_snd_2981_;
goto v___jp_3312_;
}
else
{
lean_object* v_a_3349_; 
lean_dec(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec(v_snd_2981_);
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3348_, 1);
v___y_3295_ = v___y_3339_;
v___y_3296_ = v___y_3340_;
v___y_3297_ = v___y_3341_;
v___y_3298_ = v___y_3342_;
v___y_3299_ = v___y_3344_;
v___y_3300_ = v___y_3346_;
v_a_3301_ = v_a_3349_;
goto v___jp_3294_;
}
}
else
{
lean_dec_ref(v___y_3343_);
lean_dec(v_snd_2981_);
v___y_3325_ = v___y_3337_;
v___y_3326_ = v___y_3338_;
v___y_3327_ = v___y_3339_;
v___y_3328_ = v___y_3340_;
v___y_3329_ = v___y_3341_;
v___y_3330_ = v___y_3342_;
v___y_3331_ = v___y_3344_;
v___y_3332_ = v___y_3346_;
v___y_3333_ = v___y_3345_;
goto v___jp_3324_;
}
}
v___jp_3350_:
{
lean_object* v___x_3360_; 
v___x_3360_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v___x_3360_, 1);
lean_inc(v_snd_2981_);
lean_inc(v_trace_2966_);
v___x_3362_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3352_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_dec(v_a_3361_);
lean_dec(v_snd_2981_);
v___y_3325_ = v___y_3351_;
v___y_3326_ = v___y_3353_;
v___y_3327_ = v___y_3354_;
v___y_3328_ = v___y_3356_;
v___y_3329_ = v___y_3355_;
v___y_3330_ = v___y_3357_;
v___y_3331_ = v___y_3358_;
v___y_3332_ = v___y_3359_;
v___y_3333_ = v___x_3362_;
goto v___jp_3324_;
}
else
{
lean_object* v_a_3363_; uint8_t v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
v___x_3364_ = l_Lean_Exception_isInterrupt(v_a_3363_);
if (v___x_3364_ == 0)
{
uint8_t v___x_3365_; 
lean_inc(v_a_3363_);
v___x_3365_ = l_Lean_Exception_isRuntime(v_a_3363_);
v___y_3337_ = v___y_3351_;
v___y_3338_ = v___y_3353_;
v___y_3339_ = v___y_3354_;
v___y_3340_ = v___y_3356_;
v___y_3341_ = v___y_3355_;
v___y_3342_ = v___y_3357_;
v___y_3343_ = v_a_3361_;
v___y_3344_ = v___y_3358_;
v___y_3345_ = v___x_3362_;
v___y_3346_ = v___y_3359_;
v___y_3347_ = v___x_3365_;
goto v___jp_3336_;
}
else
{
v___y_3337_ = v___y_3351_;
v___y_3338_ = v___y_3353_;
v___y_3339_ = v___y_3354_;
v___y_3340_ = v___y_3356_;
v___y_3341_ = v___y_3355_;
v___y_3342_ = v___y_3357_;
v___y_3343_ = v_a_3361_;
v___y_3344_ = v___y_3358_;
v___y_3345_ = v___x_3362_;
v___y_3346_ = v___y_3359_;
v___y_3347_ = v___x_3364_;
goto v___jp_3336_;
}
}
}
else
{
lean_object* v_a_3366_; 
lean_dec(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3366_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3366_);
lean_dec_ref_known(v___x_3360_, 1);
v___y_3295_ = v___y_3354_;
v___y_3296_ = v___y_3356_;
v___y_3297_ = v___y_3355_;
v___y_3298_ = v___y_3357_;
v___y_3299_ = v___y_3358_;
v___y_3300_ = v___y_3359_;
v_a_3301_ = v_a_3366_;
goto v___jp_3294_;
}
}
v___jp_3367_:
{
if (lean_obj_tag(v___y_3374_) == 0)
{
lean_object* v_a_3375_; 
v_a_3375_ = lean_ctor_get(v___y_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___y_3374_, 1);
v___y_3304_ = v___y_3368_;
v___y_3305_ = v___y_3370_;
v___y_3306_ = v___y_3369_;
v___y_3307_ = v___y_3371_;
v___y_3308_ = v___y_3372_;
v___y_3309_ = v___y_3373_;
v_a_3310_ = v_a_3375_;
goto v___jp_3303_;
}
else
{
lean_object* v_a_3376_; 
v_a_3376_ = lean_ctor_get(v___y_3374_, 0);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___y_3374_, 1);
v___y_3295_ = v___y_3368_;
v___y_3296_ = v___y_3370_;
v___y_3297_ = v___y_3369_;
v___y_3298_ = v___y_3371_;
v___y_3299_ = v___y_3372_;
v___y_3300_ = v___y_3373_;
v_a_3301_ = v_a_3376_;
goto v___jp_3294_;
}
}
v___jp_3377_:
{
lean_object* v___x_3386_; 
lean_inc(v_trace_2966_);
v___x_3386_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3379_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3388_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3388_ = l_List_appendTR___redArg(v___y_3378_, v_a_3387_);
v___y_3304_ = v___y_3380_;
v___y_3305_ = v___y_3382_;
v___y_3306_ = v___y_3381_;
v___y_3307_ = v___y_3383_;
v___y_3308_ = v___y_3384_;
v___y_3309_ = v___y_3385_;
v_a_3310_ = v___x_3388_;
goto v___jp_3303_;
}
else
{
lean_dec(v___y_3378_);
v___y_3368_ = v___y_3380_;
v___y_3369_ = v___y_3381_;
v___y_3370_ = v___y_3382_;
v___y_3371_ = v___y_3383_;
v___y_3372_ = v___y_3384_;
v___y_3373_ = v___y_3385_;
v___y_3374_ = v___x_3386_;
goto v___jp_3367_;
}
}
v___jp_3389_:
{
if (v___y_3400_ == 0)
{
uint8_t v___x_3401_; 
v___x_3401_ = l_List_isEmpty___redArg(v___y_3392_);
lean_dec(v___y_3392_);
if (v___x_3401_ == 0)
{
if (v___y_3394_ == 0)
{
v___y_3378_ = v___y_3390_;
v___y_3379_ = v___y_3391_;
v___y_3380_ = v___y_3393_;
v___y_3381_ = v___y_3396_;
v___y_3382_ = v___y_3395_;
v___y_3383_ = v___y_3397_;
v___y_3384_ = v___y_3398_;
v___y_3385_ = v___y_3399_;
goto v___jp_3377_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3403_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3402_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3368_ = v___y_3393_;
v___y_3369_ = v___y_3396_;
v___y_3370_ = v___y_3395_;
v___y_3371_ = v___y_3397_;
v___y_3372_ = v___y_3398_;
v___y_3373_ = v___y_3399_;
v___y_3374_ = v___x_3403_;
goto v___jp_3367_;
}
}
else
{
v___y_3378_ = v___y_3390_;
v___y_3379_ = v___y_3391_;
v___y_3380_ = v___y_3393_;
v___y_3381_ = v___y_3396_;
v___y_3382_ = v___y_3395_;
v___y_3383_ = v___y_3397_;
v___y_3384_ = v___y_3398_;
v___y_3385_ = v___y_3399_;
goto v___jp_3377_;
}
}
else
{
v___y_3351_ = v___y_3390_;
v___y_3352_ = v___y_3391_;
v___y_3353_ = v___y_3392_;
v___y_3354_ = v___y_3393_;
v___y_3355_ = v___y_3396_;
v___y_3356_ = v___y_3395_;
v___y_3357_ = v___y_3397_;
v___y_3358_ = v___y_3398_;
v___y_3359_ = v___y_3399_;
goto v___jp_3350_;
}
}
v___jp_3404_:
{
uint8_t v_commitIndependentGoals_3415_; lean_object* v___x_3416_; 
v_commitIndependentGoals_3415_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3405_);
v___x_3416_ = l_List_appendTR___redArg(v_a_3414_, v___y_3405_);
if (v_commitIndependentGoals_3415_ == 0)
{
v___y_3390_ = v___y_3405_;
v___y_3391_ = v___x_3416_;
v___y_3392_ = v___y_3406_;
v___y_3393_ = v___y_3407_;
v___y_3394_ = v___y_3408_;
v___y_3395_ = v___y_3409_;
v___y_3396_ = v___y_3410_;
v___y_3397_ = v___y_3411_;
v___y_3398_ = v___y_3412_;
v___y_3399_ = v___y_3413_;
v___y_3400_ = v___x_2985_;
goto v___jp_3389_;
}
else
{
uint8_t v___x_3417_; 
v___x_3417_ = l_List_isEmpty___redArg(v___y_3405_);
if (v___x_3417_ == 0)
{
v___y_3351_ = v___y_3405_;
v___y_3352_ = v___x_3416_;
v___y_3353_ = v___y_3406_;
v___y_3354_ = v___y_3407_;
v___y_3355_ = v___y_3410_;
v___y_3356_ = v___y_3409_;
v___y_3357_ = v___y_3411_;
v___y_3358_ = v___y_3412_;
v___y_3359_ = v___y_3413_;
goto v___jp_3350_;
}
else
{
v___y_3390_ = v___y_3405_;
v___y_3391_ = v___x_3416_;
v___y_3392_ = v___y_3406_;
v___y_3393_ = v___y_3407_;
v___y_3394_ = v___y_3408_;
v___y_3395_ = v___y_3409_;
v___y_3396_ = v___y_3410_;
v___y_3397_ = v___y_3411_;
v___y_3398_ = v___y_3412_;
v___y_3399_ = v___y_3413_;
v___y_3400_ = v___x_2985_;
goto v___jp_3389_;
}
}
}
v___jp_3418_:
{
lean_object* v___x_3427_; 
v___x_3427_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2974_);
if (lean_obj_tag(v___x_3427_) == 0)
{
if (v___y_3423_ == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v___x_3429_ = lean_io_mono_nanos_now();
v___x_3430_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3423_, v___x_2985_, v_goals_2969_, v___y_3421_, v_a_2972_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3432_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3432_ = l_List_reverse___redArg(v_a_3431_);
v___y_3266_ = v___y_3419_;
v___y_3267_ = v___y_3420_;
v___y_3268_ = v___x_3429_;
v___y_3269_ = v___y_3422_;
v___y_3270_ = v_a_3428_;
v___y_3271_ = v___y_3424_;
v___y_3272_ = v___y_3425_;
v___y_3273_ = v___y_3426_;
v_a_3274_ = v___x_3432_;
goto v___jp_3265_;
}
else
{
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3433_; 
v_a_3433_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3430_, 1);
v___y_3266_ = v___y_3419_;
v___y_3267_ = v___y_3420_;
v___y_3268_ = v___x_3429_;
v___y_3269_ = v___y_3422_;
v___y_3270_ = v_a_3428_;
v___y_3271_ = v___y_3424_;
v___y_3272_ = v___y_3425_;
v___y_3273_ = v___y_3426_;
v_a_3274_ = v_a_3433_;
goto v___jp_3265_;
}
else
{
lean_object* v_a_3434_; 
lean_dec(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3434_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3430_, 1);
v___y_3166_ = v___x_3429_;
v___y_3167_ = v___y_3422_;
v___y_3168_ = v_a_3428_;
v___y_3169_ = v___y_3424_;
v___y_3170_ = v___y_3425_;
v___y_3171_ = v___y_3426_;
v_a_3172_ = v_a_3434_;
goto v___jp_3165_;
}
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v_a_3435_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3427_, 1);
v___x_3436_ = lean_io_get_num_heartbeats();
v___x_3437_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3423_, v___x_2985_, v_goals_2969_, v___y_3421_, v_a_2972_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v___x_3439_ = l_List_reverse___redArg(v_a_3438_);
v___y_3405_ = v___y_3419_;
v___y_3406_ = v___y_3420_;
v___y_3407_ = v___y_3422_;
v___y_3408_ = v___y_3423_;
v___y_3409_ = v_a_3435_;
v___y_3410_ = v___y_3424_;
v___y_3411_ = v___x_3436_;
v___y_3412_ = v___y_3425_;
v___y_3413_ = v___y_3426_;
v_a_3414_ = v___x_3439_;
goto v___jp_3404_;
}
else
{
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3440_; 
v_a_3440_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3437_, 1);
v___y_3405_ = v___y_3419_;
v___y_3406_ = v___y_3420_;
v___y_3407_ = v___y_3422_;
v___y_3408_ = v___y_3423_;
v___y_3409_ = v_a_3435_;
v___y_3410_ = v___y_3424_;
v___y_3411_ = v___x_3436_;
v___y_3412_ = v___y_3425_;
v___y_3413_ = v___y_3426_;
v_a_3414_ = v_a_3440_;
goto v___jp_3404_;
}
else
{
lean_object* v_a_3441_; 
lean_dec(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3441_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3437_, 1);
v___y_3295_ = v___y_3422_;
v___y_3296_ = v_a_3435_;
v___y_3297_ = v___y_3424_;
v___y_3298_ = v___x_3436_;
v___y_3299_ = v___y_3425_;
v___y_3300_ = v___y_3426_;
v_a_3301_ = v_a_3441_;
goto v___jp_3294_;
}
}
}
}
else
{
lean_object* v_a_3442_; 
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec(v_snd_2981_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3442_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3442_);
lean_dec_ref_known(v___x_3427_, 1);
v___y_3092_ = v___y_3425_;
v___y_3093_ = v___y_3426_;
v_a_3094_ = v_a_3442_;
goto v___jp_3091_;
}
}
v___jp_3443_:
{
if (v___y_3449_ == 0)
{
uint8_t v___x_3450_; 
v___x_3450_ = l_List_isEmpty___redArg(v___y_3445_);
lean_dec(v___y_3445_);
if (v___x_3450_ == 0)
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
lean_dec(v___y_3446_);
lean_dec(v___y_3444_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3452_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3451_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3141_ = v___y_3447_;
v___y_3142_ = v___y_3448_;
v___y_3143_ = v___x_3452_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3453_; 
lean_inc(v_trace_2966_);
v___x_3453_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3446_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = l_List_appendTR___redArg(v___y_3444_, v_a_3454_);
v___y_3097_ = v___y_3447_;
v___y_3098_ = v___y_3448_;
v_a_3099_ = v___x_3455_;
goto v___jp_3096_;
}
else
{
lean_dec(v___y_3444_);
v___y_3141_ = v___y_3447_;
v___y_3142_ = v___y_3448_;
v___y_3143_ = v___x_3453_;
goto v___jp_3140_;
}
}
}
else
{
v___y_3128_ = v___y_3444_;
v___y_3129_ = v___y_3445_;
v___y_3130_ = v___y_3446_;
v___y_3131_ = v___y_3447_;
v___y_3132_ = v___y_3448_;
goto v___jp_3127_;
}
}
v___jp_3456_:
{
uint8_t v_commitIndependentGoals_3462_; lean_object* v___x_3463_; 
v_commitIndependentGoals_3462_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3457_);
v___x_3463_ = l_List_appendTR___redArg(v_a_3461_, v___y_3457_);
if (v_commitIndependentGoals_3462_ == 0)
{
v___y_3444_ = v___y_3457_;
v___y_3445_ = v___y_3458_;
v___y_3446_ = v___x_3463_;
v___y_3447_ = v___y_3459_;
v___y_3448_ = v___y_3460_;
v___y_3449_ = v___x_2985_;
goto v___jp_3443_;
}
else
{
uint8_t v___x_3464_; 
v___x_3464_ = l_List_isEmpty___redArg(v___y_3457_);
if (v___x_3464_ == 0)
{
v___y_3128_ = v___y_3457_;
v___y_3129_ = v___y_3458_;
v___y_3130_ = v___x_3463_;
v___y_3131_ = v___y_3459_;
v___y_3132_ = v___y_3460_;
goto v___jp_3127_;
}
else
{
v___y_3444_ = v___y_3457_;
v___y_3445_ = v___y_3458_;
v___y_3446_ = v___x_3463_;
v___y_3447_ = v___y_3459_;
v___y_3448_ = v___y_3460_;
v___y_3449_ = v___x_2985_;
goto v___jp_3443_;
}
}
}
v___jp_3465_:
{
lean_object* v___x_3469_; double v___x_3470_; double v___x_3471_; double v___x_3472_; double v___x_3473_; double v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3469_ = lean_io_mono_nanos_now();
v___x_3470_ = lean_float_of_nat(v___y_3466_);
v___x_3471_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3472_ = lean_float_div(v___x_3470_, v___x_3471_);
v___x_3473_ = lean_float_of_nat(v___x_3469_);
v___x_3474_ = lean_float_div(v___x_3473_, v___x_3471_);
v___x_3475_ = lean_box_float(v___x_3472_);
v___x_3476_ = lean_box_float(v___x_3474_);
v___x_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3475_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v_a_3468_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2988_, v___x_3073_, v_options_2987_, v___x_3076_, v___y_3467_, v___f_3072_, v___x_3478_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3479_;
}
v___jp_3480_:
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_a_3483_);
v___y_3466_ = v___y_3481_;
v___y_3467_ = v___y_3482_;
v_a_3468_ = v___x_3484_;
goto v___jp_3465_;
}
v___jp_3485_:
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3489_, 0, v_a_3488_);
v___y_3466_ = v___y_3486_;
v___y_3467_ = v___y_3487_;
v_a_3468_ = v___x_3489_;
goto v___jp_3465_;
}
v___jp_3490_:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = l_List_appendTR___redArg(v___y_3491_, v___y_3493_);
v___x_3497_ = l_List_appendTR___redArg(v___x_3496_, v_a_3495_);
v___y_3486_ = v___y_3492_;
v___y_3487_ = v___y_3494_;
v_a_3488_ = v___x_3497_;
goto v___jp_3485_;
}
v___jp_3498_:
{
if (lean_obj_tag(v___y_3503_) == 0)
{
lean_object* v_a_3504_; 
v_a_3504_ = lean_ctor_get(v___y_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___y_3503_, 1);
v___y_3491_ = v___y_3499_;
v___y_3492_ = v___y_3501_;
v___y_3493_ = v___y_3500_;
v___y_3494_ = v___y_3502_;
v_a_3495_ = v_a_3504_;
goto v___jp_3490_;
}
else
{
lean_object* v_a_3505_; 
lean_dec(v___y_3500_);
lean_dec(v___y_3499_);
v_a_3505_ = lean_ctor_get(v___y_3503_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___y_3503_, 1);
v___y_3481_ = v___y_3501_;
v___y_3482_ = v___y_3502_;
v_a_3483_ = v_a_3505_;
goto v___jp_3480_;
}
}
v___jp_3506_:
{
if (v___y_3513_ == 0)
{
lean_object* v___x_3514_; 
lean_dec_ref(v___y_3509_);
v___x_3514_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3508_, v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_dec_ref_known(v___x_3514_, 1);
v___y_3491_ = v___y_3507_;
v___y_3492_ = v___y_3511_;
v___y_3493_ = v___y_3510_;
v___y_3494_ = v___y_3512_;
v_a_3495_ = v_snd_2981_;
goto v___jp_3490_;
}
else
{
lean_object* v_a_3515_; 
lean_dec(v___y_3510_);
lean_dec(v___y_3507_);
lean_dec(v_snd_2981_);
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___y_3481_ = v___y_3511_;
v___y_3482_ = v___y_3512_;
v_a_3483_ = v_a_3515_;
goto v___jp_3480_;
}
}
else
{
lean_dec_ref(v___y_3508_);
lean_dec(v_snd_2981_);
v___y_3499_ = v___y_3507_;
v___y_3500_ = v___y_3510_;
v___y_3501_ = v___y_3511_;
v___y_3502_ = v___y_3512_;
v___y_3503_ = v___y_3509_;
goto v___jp_3498_;
}
}
v___jp_3516_:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3524_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___x_3522_, 1);
lean_inc(v_snd_2981_);
lean_inc(v_trace_2966_);
v___x_3524_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3518_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_dec(v_a_3523_);
lean_dec(v_snd_2981_);
v___y_3499_ = v___y_3517_;
v___y_3500_ = v___y_3520_;
v___y_3501_ = v___y_3519_;
v___y_3502_ = v___y_3521_;
v___y_3503_ = v___x_3524_;
goto v___jp_3498_;
}
else
{
lean_object* v_a_3525_; uint8_t v___x_3526_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v___x_3526_ = l_Lean_Exception_isInterrupt(v_a_3525_);
if (v___x_3526_ == 0)
{
uint8_t v___x_3527_; 
lean_inc(v_a_3525_);
v___x_3527_ = l_Lean_Exception_isRuntime(v_a_3525_);
v___y_3507_ = v___y_3517_;
v___y_3508_ = v_a_3523_;
v___y_3509_ = v___x_3524_;
v___y_3510_ = v___y_3520_;
v___y_3511_ = v___y_3519_;
v___y_3512_ = v___y_3521_;
v___y_3513_ = v___x_3527_;
goto v___jp_3506_;
}
else
{
v___y_3507_ = v___y_3517_;
v___y_3508_ = v_a_3523_;
v___y_3509_ = v___x_3524_;
v___y_3510_ = v___y_3520_;
v___y_3511_ = v___y_3519_;
v___y_3512_ = v___y_3521_;
v___y_3513_ = v___x_3526_;
goto v___jp_3506_;
}
}
}
else
{
lean_object* v_a_3528_; 
lean_dec(v___y_3520_);
lean_dec(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3528_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3528_);
lean_dec_ref_known(v___x_3522_, 1);
v___y_3481_ = v___y_3519_;
v___y_3482_ = v___y_3521_;
v_a_3483_ = v_a_3528_;
goto v___jp_3480_;
}
}
v___jp_3529_:
{
if (lean_obj_tag(v___y_3532_) == 0)
{
lean_object* v_a_3533_; 
v_a_3533_ = lean_ctor_get(v___y_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___y_3532_, 1);
v___y_3486_ = v___y_3530_;
v___y_3487_ = v___y_3531_;
v_a_3488_ = v_a_3533_;
goto v___jp_3485_;
}
else
{
lean_object* v_a_3534_; 
v_a_3534_ = lean_ctor_get(v___y_3532_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___y_3532_, 1);
v___y_3481_ = v___y_3530_;
v___y_3482_ = v___y_3531_;
v_a_3483_ = v_a_3534_;
goto v___jp_3480_;
}
}
v___jp_3535_:
{
lean_object* v___x_3543_; double v___x_3544_; double v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3543_ = lean_io_get_num_heartbeats();
v___x_3544_ = lean_float_of_nat(v___y_3536_);
v___x_3545_ = lean_float_of_nat(v___x_3543_);
v___x_3546_ = lean_box_float(v___x_3544_);
v___x_3547_ = lean_box_float(v___x_3545_);
v___x_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3546_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3549_, 0, v_a_3542_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
lean_inc(v_trace_2966_);
v___x_3550_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2988_, v___x_3073_, v_options_2987_, v___y_3537_, v___y_3540_, v___y_3541_, v___x_3549_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3530_ = v___y_3538_;
v___y_3531_ = v___y_3539_;
v___y_3532_ = v___x_3550_;
goto v___jp_3529_;
}
v___jp_3551_:
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3559_, 0, v_a_3558_);
v___y_3536_ = v___y_3552_;
v___y_3537_ = v___y_3553_;
v___y_3538_ = v___y_3554_;
v___y_3539_ = v___y_3555_;
v___y_3540_ = v___y_3556_;
v___y_3541_ = v___y_3557_;
v_a_3542_ = v___x_3559_;
goto v___jp_3535_;
}
v___jp_3560_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = l_List_appendTR___redArg(v___y_3561_, v___y_3565_);
v___x_3571_ = l_List_appendTR___redArg(v___x_3570_, v_a_3569_);
v___y_3552_ = v___y_3562_;
v___y_3553_ = v___y_3563_;
v___y_3554_ = v___y_3564_;
v___y_3555_ = v___y_3566_;
v___y_3556_ = v___y_3567_;
v___y_3557_ = v___y_3568_;
v_a_3558_ = v___x_3571_;
goto v___jp_3551_;
}
v___jp_3572_:
{
lean_object* v___x_3580_; 
v___x_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3580_, 0, v_a_3579_);
v___y_3536_ = v___y_3573_;
v___y_3537_ = v___y_3574_;
v___y_3538_ = v___y_3575_;
v___y_3539_ = v___y_3576_;
v___y_3540_ = v___y_3577_;
v___y_3541_ = v___y_3578_;
v_a_3542_ = v___x_3580_;
goto v___jp_3535_;
}
v___jp_3581_:
{
if (lean_obj_tag(v___y_3588_) == 0)
{
lean_object* v_a_3589_; 
v_a_3589_ = lean_ctor_get(v___y_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___y_3588_, 1);
v___y_3552_ = v___y_3582_;
v___y_3553_ = v___y_3583_;
v___y_3554_ = v___y_3584_;
v___y_3555_ = v___y_3585_;
v___y_3556_ = v___y_3586_;
v___y_3557_ = v___y_3587_;
v_a_3558_ = v_a_3589_;
goto v___jp_3551_;
}
else
{
lean_object* v_a_3590_; 
v_a_3590_ = lean_ctor_get(v___y_3588_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___y_3588_, 1);
v___y_3573_ = v___y_3582_;
v___y_3574_ = v___y_3583_;
v___y_3575_ = v___y_3584_;
v___y_3576_ = v___y_3585_;
v___y_3577_ = v___y_3586_;
v___y_3578_ = v___y_3587_;
v_a_3579_ = v_a_3590_;
goto v___jp_3572_;
}
}
v___jp_3591_:
{
lean_object* v___x_3600_; 
lean_inc(v_trace_2966_);
v___x_3600_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3595_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3602_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v___x_3602_ = l_List_appendTR___redArg(v___y_3592_, v_a_3601_);
v___y_3552_ = v___y_3593_;
v___y_3553_ = v___y_3594_;
v___y_3554_ = v___y_3596_;
v___y_3555_ = v___y_3597_;
v___y_3556_ = v___y_3598_;
v___y_3557_ = v___y_3599_;
v_a_3558_ = v___x_3602_;
goto v___jp_3551_;
}
else
{
lean_dec(v___y_3592_);
v___y_3582_ = v___y_3593_;
v___y_3583_ = v___y_3594_;
v___y_3584_ = v___y_3596_;
v___y_3585_ = v___y_3597_;
v___y_3586_ = v___y_3598_;
v___y_3587_ = v___y_3599_;
v___y_3588_ = v___x_3600_;
goto v___jp_3581_;
}
}
v___jp_3603_:
{
if (lean_obj_tag(v___y_3612_) == 0)
{
lean_object* v_a_3613_; 
v_a_3613_ = lean_ctor_get(v___y_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___y_3612_, 1);
v___y_3561_ = v___y_3604_;
v___y_3562_ = v___y_3605_;
v___y_3563_ = v___y_3606_;
v___y_3564_ = v___y_3608_;
v___y_3565_ = v___y_3607_;
v___y_3566_ = v___y_3609_;
v___y_3567_ = v___y_3610_;
v___y_3568_ = v___y_3611_;
v_a_3569_ = v_a_3613_;
goto v___jp_3560_;
}
else
{
lean_object* v_a_3614_; 
lean_dec(v___y_3607_);
lean_dec(v___y_3604_);
v_a_3614_ = lean_ctor_get(v___y_3612_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___y_3612_, 1);
v___y_3573_ = v___y_3605_;
v___y_3574_ = v___y_3606_;
v___y_3575_ = v___y_3608_;
v___y_3576_ = v___y_3609_;
v___y_3577_ = v___y_3610_;
v___y_3578_ = v___y_3611_;
v_a_3579_ = v_a_3614_;
goto v___jp_3572_;
}
}
v___jp_3615_:
{
if (v___y_3626_ == 0)
{
lean_object* v___x_3627_; 
lean_dec_ref(v___y_3617_);
v___x_3627_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3619_, v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_dec_ref_known(v___x_3627_, 1);
v___y_3561_ = v___y_3616_;
v___y_3562_ = v___y_3618_;
v___y_3563_ = v___y_3620_;
v___y_3564_ = v___y_3622_;
v___y_3565_ = v___y_3621_;
v___y_3566_ = v___y_3623_;
v___y_3567_ = v___y_3624_;
v___y_3568_ = v___y_3625_;
v_a_3569_ = v_snd_2981_;
goto v___jp_3560_;
}
else
{
lean_object* v_a_3628_; 
lean_dec(v___y_3621_);
lean_dec(v___y_3616_);
lean_dec(v_snd_2981_);
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3628_);
lean_dec_ref_known(v___x_3627_, 1);
v___y_3573_ = v___y_3618_;
v___y_3574_ = v___y_3620_;
v___y_3575_ = v___y_3622_;
v___y_3576_ = v___y_3623_;
v___y_3577_ = v___y_3624_;
v___y_3578_ = v___y_3625_;
v_a_3579_ = v_a_3628_;
goto v___jp_3572_;
}
}
else
{
lean_dec_ref(v___y_3619_);
lean_dec(v_snd_2981_);
v___y_3604_ = v___y_3616_;
v___y_3605_ = v___y_3618_;
v___y_3606_ = v___y_3620_;
v___y_3607_ = v___y_3621_;
v___y_3608_ = v___y_3622_;
v___y_3609_ = v___y_3623_;
v___y_3610_ = v___y_3624_;
v___y_3611_ = v___y_3625_;
v___y_3612_ = v___y_3617_;
goto v___jp_3603_;
}
}
v___jp_3629_:
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3641_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3639_, 1);
lean_inc(v_snd_2981_);
lean_inc(v_trace_2966_);
v___x_3641_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3633_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_dec(v_a_3640_);
lean_dec(v_snd_2981_);
v___y_3604_ = v___y_3630_;
v___y_3605_ = v___y_3631_;
v___y_3606_ = v___y_3632_;
v___y_3607_ = v___y_3635_;
v___y_3608_ = v___y_3634_;
v___y_3609_ = v___y_3636_;
v___y_3610_ = v___y_3637_;
v___y_3611_ = v___y_3638_;
v___y_3612_ = v___x_3641_;
goto v___jp_3603_;
}
else
{
lean_object* v_a_3642_; uint8_t v___x_3643_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v___x_3643_ = l_Lean_Exception_isInterrupt(v_a_3642_);
if (v___x_3643_ == 0)
{
uint8_t v___x_3644_; 
lean_inc(v_a_3642_);
v___x_3644_ = l_Lean_Exception_isRuntime(v_a_3642_);
v___y_3616_ = v___y_3630_;
v___y_3617_ = v___x_3641_;
v___y_3618_ = v___y_3631_;
v___y_3619_ = v_a_3640_;
v___y_3620_ = v___y_3632_;
v___y_3621_ = v___y_3635_;
v___y_3622_ = v___y_3634_;
v___y_3623_ = v___y_3636_;
v___y_3624_ = v___y_3637_;
v___y_3625_ = v___y_3638_;
v___y_3626_ = v___x_3644_;
goto v___jp_3615_;
}
else
{
v___y_3616_ = v___y_3630_;
v___y_3617_ = v___x_3641_;
v___y_3618_ = v___y_3631_;
v___y_3619_ = v_a_3640_;
v___y_3620_ = v___y_3632_;
v___y_3621_ = v___y_3635_;
v___y_3622_ = v___y_3634_;
v___y_3623_ = v___y_3636_;
v___y_3624_ = v___y_3637_;
v___y_3625_ = v___y_3638_;
v___y_3626_ = v___x_3643_;
goto v___jp_3615_;
}
}
}
else
{
lean_object* v_a_3645_; 
lean_dec(v___y_3635_);
lean_dec(v___y_3633_);
lean_dec(v___y_3630_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3645_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3639_, 1);
v___y_3573_ = v___y_3631_;
v___y_3574_ = v___y_3632_;
v___y_3575_ = v___y_3634_;
v___y_3576_ = v___y_3636_;
v___y_3577_ = v___y_3637_;
v___y_3578_ = v___y_3638_;
v_a_3579_ = v_a_3645_;
goto v___jp_3572_;
}
}
v___jp_3646_:
{
if (v___y_3657_ == 0)
{
uint8_t v___x_3658_; 
v___x_3658_ = l_List_isEmpty___redArg(v___y_3653_);
lean_dec(v___y_3653_);
if (v___x_3658_ == 0)
{
if (v___y_3650_ == 0)
{
v___y_3592_ = v___y_3647_;
v___y_3593_ = v___y_3648_;
v___y_3594_ = v___y_3649_;
v___y_3595_ = v___y_3651_;
v___y_3596_ = v___y_3652_;
v___y_3597_ = v___y_3654_;
v___y_3598_ = v___y_3655_;
v___y_3599_ = v___y_3656_;
goto v___jp_3591_;
}
else
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
lean_dec(v___y_3651_);
lean_dec(v___y_3647_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3659_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3660_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3659_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3582_ = v___y_3648_;
v___y_3583_ = v___y_3649_;
v___y_3584_ = v___y_3652_;
v___y_3585_ = v___y_3654_;
v___y_3586_ = v___y_3655_;
v___y_3587_ = v___y_3656_;
v___y_3588_ = v___x_3660_;
goto v___jp_3581_;
}
}
else
{
v___y_3592_ = v___y_3647_;
v___y_3593_ = v___y_3648_;
v___y_3594_ = v___y_3649_;
v___y_3595_ = v___y_3651_;
v___y_3596_ = v___y_3652_;
v___y_3597_ = v___y_3654_;
v___y_3598_ = v___y_3655_;
v___y_3599_ = v___y_3656_;
goto v___jp_3591_;
}
}
else
{
v___y_3630_ = v___y_3647_;
v___y_3631_ = v___y_3648_;
v___y_3632_ = v___y_3649_;
v___y_3633_ = v___y_3651_;
v___y_3634_ = v___y_3652_;
v___y_3635_ = v___y_3653_;
v___y_3636_ = v___y_3654_;
v___y_3637_ = v___y_3655_;
v___y_3638_ = v___y_3656_;
goto v___jp_3629_;
}
}
v___jp_3661_:
{
uint8_t v_commitIndependentGoals_3672_; lean_object* v___x_3673_; 
v_commitIndependentGoals_3672_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3662_);
v___x_3673_ = l_List_appendTR___redArg(v_a_3671_, v___y_3662_);
if (v_commitIndependentGoals_3672_ == 0)
{
v___y_3647_ = v___y_3662_;
v___y_3648_ = v___y_3663_;
v___y_3649_ = v___y_3665_;
v___y_3650_ = v___y_3664_;
v___y_3651_ = v___x_3673_;
v___y_3652_ = v___y_3667_;
v___y_3653_ = v___y_3666_;
v___y_3654_ = v___y_3668_;
v___y_3655_ = v___y_3669_;
v___y_3656_ = v___y_3670_;
v___y_3657_ = v___x_2985_;
goto v___jp_3646_;
}
else
{
uint8_t v___x_3674_; 
v___x_3674_ = l_List_isEmpty___redArg(v___y_3662_);
if (v___x_3674_ == 0)
{
v___y_3630_ = v___y_3662_;
v___y_3631_ = v___y_3663_;
v___y_3632_ = v___y_3665_;
v___y_3633_ = v___x_3673_;
v___y_3634_ = v___y_3667_;
v___y_3635_ = v___y_3666_;
v___y_3636_ = v___y_3668_;
v___y_3637_ = v___y_3669_;
v___y_3638_ = v___y_3670_;
goto v___jp_3629_;
}
else
{
v___y_3647_ = v___y_3662_;
v___y_3648_ = v___y_3663_;
v___y_3649_ = v___y_3665_;
v___y_3650_ = v___y_3664_;
v___y_3651_ = v___x_3673_;
v___y_3652_ = v___y_3667_;
v___y_3653_ = v___y_3666_;
v___y_3654_ = v___y_3668_;
v___y_3655_ = v___y_3669_;
v___y_3656_ = v___y_3670_;
v___y_3657_ = v___x_2985_;
goto v___jp_3646_;
}
}
}
v___jp_3675_:
{
lean_object* v___x_3683_; double v___x_3684_; double v___x_3685_; double v___x_3686_; double v___x_3687_; double v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3683_ = lean_io_mono_nanos_now();
v___x_3684_ = lean_float_of_nat(v___y_3677_);
v___x_3685_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3686_ = lean_float_div(v___x_3684_, v___x_3685_);
v___x_3687_ = lean_float_of_nat(v___x_3683_);
v___x_3688_ = lean_float_div(v___x_3687_, v___x_3685_);
v___x_3689_ = lean_box_float(v___x_3686_);
v___x_3690_ = lean_box_float(v___x_3688_);
v___x_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3689_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v_a_3682_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
lean_inc(v_trace_2966_);
v___x_3693_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2988_, v___x_3073_, v_options_2987_, v___y_3676_, v___y_3680_, v___y_3681_, v___x_3692_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3530_ = v___y_3678_;
v___y_3531_ = v___y_3679_;
v___y_3532_ = v___x_3693_;
goto v___jp_3529_;
}
v___jp_3694_:
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3702_, 0, v_a_3701_);
v___y_3676_ = v___y_3696_;
v___y_3677_ = v___y_3695_;
v___y_3678_ = v___y_3697_;
v___y_3679_ = v___y_3698_;
v___y_3680_ = v___y_3699_;
v___y_3681_ = v___y_3700_;
v_a_3682_ = v___x_3702_;
goto v___jp_3675_;
}
v___jp_3703_:
{
lean_object* v___x_3711_; 
v___x_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3711_, 0, v_a_3710_);
v___y_3676_ = v___y_3705_;
v___y_3677_ = v___y_3704_;
v___y_3678_ = v___y_3706_;
v___y_3679_ = v___y_3707_;
v___y_3680_ = v___y_3708_;
v___y_3681_ = v___y_3709_;
v_a_3682_ = v___x_3711_;
goto v___jp_3675_;
}
v___jp_3712_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = l_List_appendTR___redArg(v___y_3713_, v___y_3717_);
v___x_3723_ = l_List_appendTR___redArg(v___x_3722_, v_a_3721_);
v___y_3704_ = v___y_3715_;
v___y_3705_ = v___y_3714_;
v___y_3706_ = v___y_3716_;
v___y_3707_ = v___y_3718_;
v___y_3708_ = v___y_3719_;
v___y_3709_ = v___y_3720_;
v_a_3710_ = v___x_3723_;
goto v___jp_3703_;
}
v___jp_3724_:
{
if (lean_obj_tag(v___y_3733_) == 0)
{
lean_object* v_a_3734_; 
v_a_3734_ = lean_ctor_get(v___y_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___y_3733_, 1);
v___y_3713_ = v___y_3725_;
v___y_3714_ = v___y_3727_;
v___y_3715_ = v___y_3726_;
v___y_3716_ = v___y_3729_;
v___y_3717_ = v___y_3728_;
v___y_3718_ = v___y_3730_;
v___y_3719_ = v___y_3731_;
v___y_3720_ = v___y_3732_;
v_a_3721_ = v_a_3734_;
goto v___jp_3712_;
}
else
{
lean_object* v_a_3735_; 
lean_dec(v___y_3728_);
lean_dec(v___y_3725_);
v_a_3735_ = lean_ctor_get(v___y_3733_, 0);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___y_3733_, 1);
v___y_3695_ = v___y_3726_;
v___y_3696_ = v___y_3727_;
v___y_3697_ = v___y_3729_;
v___y_3698_ = v___y_3730_;
v___y_3699_ = v___y_3731_;
v___y_3700_ = v___y_3732_;
v_a_3701_ = v_a_3735_;
goto v___jp_3694_;
}
}
v___jp_3736_:
{
if (v___y_3747_ == 0)
{
lean_object* v___x_3748_; 
lean_dec_ref(v___y_3744_);
v___x_3748_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3740_, v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_dec_ref_known(v___x_3748_, 1);
v___y_3713_ = v___y_3737_;
v___y_3714_ = v___y_3739_;
v___y_3715_ = v___y_3738_;
v___y_3716_ = v___y_3742_;
v___y_3717_ = v___y_3741_;
v___y_3718_ = v___y_3743_;
v___y_3719_ = v___y_3745_;
v___y_3720_ = v___y_3746_;
v_a_3721_ = v_snd_2981_;
goto v___jp_3712_;
}
else
{
lean_object* v_a_3749_; 
lean_dec(v___y_3741_);
lean_dec(v___y_3737_);
lean_dec(v_snd_2981_);
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3748_, 1);
v___y_3695_ = v___y_3738_;
v___y_3696_ = v___y_3739_;
v___y_3697_ = v___y_3742_;
v___y_3698_ = v___y_3743_;
v___y_3699_ = v___y_3745_;
v___y_3700_ = v___y_3746_;
v_a_3701_ = v_a_3749_;
goto v___jp_3694_;
}
}
else
{
lean_dec_ref(v___y_3740_);
lean_dec(v_snd_2981_);
v___y_3725_ = v___y_3737_;
v___y_3726_ = v___y_3738_;
v___y_3727_ = v___y_3739_;
v___y_3728_ = v___y_3741_;
v___y_3729_ = v___y_3742_;
v___y_3730_ = v___y_3743_;
v___y_3731_ = v___y_3745_;
v___y_3732_ = v___y_3746_;
v___y_3733_ = v___y_3744_;
goto v___jp_3724_;
}
}
v___jp_3750_:
{
lean_object* v___x_3760_; 
v___x_3760_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3762_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___x_3760_, 1);
lean_inc(v_snd_2981_);
lean_inc(v_trace_2966_);
v___x_3762_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3758_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_dec(v_a_3761_);
lean_dec(v_snd_2981_);
v___y_3725_ = v___y_3751_;
v___y_3726_ = v___y_3753_;
v___y_3727_ = v___y_3752_;
v___y_3728_ = v___y_3755_;
v___y_3729_ = v___y_3754_;
v___y_3730_ = v___y_3756_;
v___y_3731_ = v___y_3757_;
v___y_3732_ = v___y_3759_;
v___y_3733_ = v___x_3762_;
goto v___jp_3724_;
}
else
{
lean_object* v_a_3763_; uint8_t v___x_3764_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
v___x_3764_ = l_Lean_Exception_isInterrupt(v_a_3763_);
if (v___x_3764_ == 0)
{
uint8_t v___x_3765_; 
lean_inc(v_a_3763_);
v___x_3765_ = l_Lean_Exception_isRuntime(v_a_3763_);
v___y_3737_ = v___y_3751_;
v___y_3738_ = v___y_3753_;
v___y_3739_ = v___y_3752_;
v___y_3740_ = v_a_3761_;
v___y_3741_ = v___y_3755_;
v___y_3742_ = v___y_3754_;
v___y_3743_ = v___y_3756_;
v___y_3744_ = v___x_3762_;
v___y_3745_ = v___y_3757_;
v___y_3746_ = v___y_3759_;
v___y_3747_ = v___x_3765_;
goto v___jp_3736_;
}
else
{
v___y_3737_ = v___y_3751_;
v___y_3738_ = v___y_3753_;
v___y_3739_ = v___y_3752_;
v___y_3740_ = v_a_3761_;
v___y_3741_ = v___y_3755_;
v___y_3742_ = v___y_3754_;
v___y_3743_ = v___y_3756_;
v___y_3744_ = v___x_3762_;
v___y_3745_ = v___y_3757_;
v___y_3746_ = v___y_3759_;
v___y_3747_ = v___x_3764_;
goto v___jp_3736_;
}
}
}
else
{
lean_object* v_a_3766_; 
lean_dec(v___y_3758_);
lean_dec(v___y_3755_);
lean_dec(v___y_3751_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3766_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3766_);
lean_dec_ref_known(v___x_3760_, 1);
v___y_3695_ = v___y_3753_;
v___y_3696_ = v___y_3752_;
v___y_3697_ = v___y_3754_;
v___y_3698_ = v___y_3756_;
v___y_3699_ = v___y_3757_;
v___y_3700_ = v___y_3759_;
v_a_3701_ = v_a_3766_;
goto v___jp_3694_;
}
}
v___jp_3767_:
{
if (lean_obj_tag(v___y_3774_) == 0)
{
lean_object* v_a_3775_; 
v_a_3775_ = lean_ctor_get(v___y_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref_known(v___y_3774_, 1);
v___y_3704_ = v___y_3769_;
v___y_3705_ = v___y_3768_;
v___y_3706_ = v___y_3770_;
v___y_3707_ = v___y_3771_;
v___y_3708_ = v___y_3772_;
v___y_3709_ = v___y_3773_;
v_a_3710_ = v_a_3775_;
goto v___jp_3703_;
}
else
{
lean_object* v_a_3776_; 
v_a_3776_ = lean_ctor_get(v___y_3774_, 0);
lean_inc(v_a_3776_);
lean_dec_ref_known(v___y_3774_, 1);
v___y_3695_ = v___y_3769_;
v___y_3696_ = v___y_3768_;
v___y_3697_ = v___y_3770_;
v___y_3698_ = v___y_3771_;
v___y_3699_ = v___y_3772_;
v___y_3700_ = v___y_3773_;
v_a_3701_ = v_a_3776_;
goto v___jp_3694_;
}
}
v___jp_3777_:
{
if (v___y_3787_ == 0)
{
uint8_t v___x_3788_; 
v___x_3788_ = l_List_isEmpty___redArg(v___y_3782_);
lean_dec(v___y_3782_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
lean_dec(v___y_3784_);
lean_dec(v___y_3778_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3789_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3790_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3789_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3768_ = v___y_3780_;
v___y_3769_ = v___y_3779_;
v___y_3770_ = v___y_3781_;
v___y_3771_ = v___y_3783_;
v___y_3772_ = v___y_3785_;
v___y_3773_ = v___y_3786_;
v___y_3774_ = v___x_3790_;
goto v___jp_3767_;
}
else
{
lean_object* v___x_3791_; 
lean_inc(v_trace_2966_);
v___x_3791_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3784_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3793_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v___x_3793_ = l_List_appendTR___redArg(v___y_3778_, v_a_3792_);
v___y_3704_ = v___y_3779_;
v___y_3705_ = v___y_3780_;
v___y_3706_ = v___y_3781_;
v___y_3707_ = v___y_3783_;
v___y_3708_ = v___y_3785_;
v___y_3709_ = v___y_3786_;
v_a_3710_ = v___x_3793_;
goto v___jp_3703_;
}
else
{
lean_dec(v___y_3778_);
v___y_3768_ = v___y_3780_;
v___y_3769_ = v___y_3779_;
v___y_3770_ = v___y_3781_;
v___y_3771_ = v___y_3783_;
v___y_3772_ = v___y_3785_;
v___y_3773_ = v___y_3786_;
v___y_3774_ = v___x_3791_;
goto v___jp_3767_;
}
}
}
else
{
v___y_3751_ = v___y_3778_;
v___y_3752_ = v___y_3780_;
v___y_3753_ = v___y_3779_;
v___y_3754_ = v___y_3781_;
v___y_3755_ = v___y_3782_;
v___y_3756_ = v___y_3783_;
v___y_3757_ = v___y_3785_;
v___y_3758_ = v___y_3784_;
v___y_3759_ = v___y_3786_;
goto v___jp_3750_;
}
}
v___jp_3794_:
{
uint8_t v_commitIndependentGoals_3804_; lean_object* v___x_3805_; 
v_commitIndependentGoals_3804_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3795_);
v___x_3805_ = l_List_appendTR___redArg(v_a_3803_, v___y_3795_);
if (v_commitIndependentGoals_3804_ == 0)
{
v___y_3778_ = v___y_3795_;
v___y_3779_ = v___y_3796_;
v___y_3780_ = v___y_3797_;
v___y_3781_ = v___y_3799_;
v___y_3782_ = v___y_3798_;
v___y_3783_ = v___y_3800_;
v___y_3784_ = v___x_3805_;
v___y_3785_ = v___y_3801_;
v___y_3786_ = v___y_3802_;
v___y_3787_ = v___x_2985_;
goto v___jp_3777_;
}
else
{
uint8_t v___x_3806_; 
v___x_3806_ = l_List_isEmpty___redArg(v___y_3795_);
if (v___x_3806_ == 0)
{
v___y_3751_ = v___y_3795_;
v___y_3752_ = v___y_3797_;
v___y_3753_ = v___y_3796_;
v___y_3754_ = v___y_3799_;
v___y_3755_ = v___y_3798_;
v___y_3756_ = v___y_3800_;
v___y_3757_ = v___y_3801_;
v___y_3758_ = v___x_3805_;
v___y_3759_ = v___y_3802_;
goto v___jp_3750_;
}
else
{
v___y_3778_ = v___y_3795_;
v___y_3779_ = v___y_3796_;
v___y_3780_ = v___y_3797_;
v___y_3781_ = v___y_3799_;
v___y_3782_ = v___y_3798_;
v___y_3783_ = v___y_3800_;
v___y_3784_ = v___x_3805_;
v___y_3785_ = v___y_3801_;
v___y_3786_ = v___y_3802_;
v___y_3787_ = v___x_2985_;
goto v___jp_3777_;
}
}
}
v___jp_3807_:
{
lean_object* v___x_3816_; 
v___x_3816_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2974_);
if (lean_obj_tag(v___x_3816_) == 0)
{
if (v___y_3810_ == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3816_, 1);
v___x_3818_ = lean_io_mono_nanos_now();
v___x_3819_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2988_, v___x_2985_, v_goals_2969_, v___y_3813_, v_a_2972_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3821_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3819_, 1);
v___x_3821_ = l_List_reverse___redArg(v_a_3820_);
v___y_3795_ = v___y_3808_;
v___y_3796_ = v___x_3818_;
v___y_3797_ = v___y_3809_;
v___y_3798_ = v___y_3811_;
v___y_3799_ = v___y_3812_;
v___y_3800_ = v___y_3814_;
v___y_3801_ = v_a_3817_;
v___y_3802_ = v___y_3815_;
v_a_3803_ = v___x_3821_;
goto v___jp_3794_;
}
else
{
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3822_; 
v_a_3822_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3819_, 1);
v___y_3795_ = v___y_3808_;
v___y_3796_ = v___x_3818_;
v___y_3797_ = v___y_3809_;
v___y_3798_ = v___y_3811_;
v___y_3799_ = v___y_3812_;
v___y_3800_ = v___y_3814_;
v___y_3801_ = v_a_3817_;
v___y_3802_ = v___y_3815_;
v_a_3803_ = v_a_3822_;
goto v___jp_3794_;
}
else
{
lean_object* v_a_3823_; 
lean_dec(v___y_3811_);
lean_dec(v___y_3808_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3823_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3823_);
lean_dec_ref_known(v___x_3819_, 1);
v___y_3695_ = v___x_3818_;
v___y_3696_ = v___y_3809_;
v___y_3697_ = v___y_3812_;
v___y_3698_ = v___y_3814_;
v___y_3699_ = v_a_3817_;
v___y_3700_ = v___y_3815_;
v_a_3701_ = v_a_3823_;
goto v___jp_3694_;
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v_a_3824_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3824_);
lean_dec_ref_known(v___x_3816_, 1);
v___x_3825_ = lean_io_get_num_heartbeats();
v___x_3826_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2988_, v___x_2985_, v_goals_2969_, v___y_3813_, v_a_2972_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3828_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3826_, 1);
v___x_3828_ = l_List_reverse___redArg(v_a_3827_);
v___y_3662_ = v___y_3808_;
v___y_3663_ = v___x_3825_;
v___y_3664_ = v___y_3810_;
v___y_3665_ = v___y_3809_;
v___y_3666_ = v___y_3811_;
v___y_3667_ = v___y_3812_;
v___y_3668_ = v___y_3814_;
v___y_3669_ = v_a_3824_;
v___y_3670_ = v___y_3815_;
v_a_3671_ = v___x_3828_;
goto v___jp_3661_;
}
else
{
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3829_; 
v_a_3829_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___x_3826_, 1);
v___y_3662_ = v___y_3808_;
v___y_3663_ = v___x_3825_;
v___y_3664_ = v___y_3810_;
v___y_3665_ = v___y_3809_;
v___y_3666_ = v___y_3811_;
v___y_3667_ = v___y_3812_;
v___y_3668_ = v___y_3814_;
v___y_3669_ = v_a_3824_;
v___y_3670_ = v___y_3815_;
v_a_3671_ = v_a_3829_;
goto v___jp_3661_;
}
else
{
lean_object* v_a_3830_; 
lean_dec(v___y_3811_);
lean_dec(v___y_3808_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3830_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3830_);
lean_dec_ref_known(v___x_3826_, 1);
v___y_3573_ = v___x_3825_;
v___y_3574_ = v___y_3809_;
v___y_3575_ = v___y_3812_;
v___y_3576_ = v___y_3814_;
v___y_3577_ = v_a_3824_;
v___y_3578_ = v___y_3815_;
v_a_3579_ = v_a_3830_;
goto v___jp_3572_;
}
}
}
}
else
{
lean_object* v_a_3831_; 
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3813_);
lean_dec(v___y_3811_);
lean_dec(v___y_3808_);
lean_dec(v_snd_2981_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3831_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3816_, 1);
v___y_3481_ = v___y_3812_;
v___y_3482_ = v___y_3814_;
v_a_3483_ = v_a_3831_;
goto v___jp_3480_;
}
}
v___jp_3832_:
{
if (v___y_3838_ == 0)
{
uint8_t v___x_3839_; 
v___x_3839_ = l_List_isEmpty___redArg(v___y_3836_);
lean_dec(v___y_3836_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_dec(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3841_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3840_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3530_ = v___y_3835_;
v___y_3531_ = v___y_3837_;
v___y_3532_ = v___x_3841_;
goto v___jp_3529_;
}
else
{
lean_object* v___x_3842_; 
lean_inc(v_trace_2966_);
v___x_3842_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3834_, v_snd_2981_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3844_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref_known(v___x_3842_, 1);
v___x_3844_ = l_List_appendTR___redArg(v___y_3833_, v_a_3843_);
v___y_3486_ = v___y_3835_;
v___y_3487_ = v___y_3837_;
v_a_3488_ = v___x_3844_;
goto v___jp_3485_;
}
else
{
lean_dec(v___y_3833_);
v___y_3530_ = v___y_3835_;
v___y_3531_ = v___y_3837_;
v___y_3532_ = v___x_3842_;
goto v___jp_3529_;
}
}
}
else
{
v___y_3517_ = v___y_3833_;
v___y_3518_ = v___y_3834_;
v___y_3519_ = v___y_3835_;
v___y_3520_ = v___y_3836_;
v___y_3521_ = v___y_3837_;
goto v___jp_3516_;
}
}
v___jp_3845_:
{
uint8_t v_commitIndependentGoals_3851_; lean_object* v___x_3852_; 
v_commitIndependentGoals_3851_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3846_);
v___x_3852_ = l_List_appendTR___redArg(v_a_3850_, v___y_3846_);
if (v_commitIndependentGoals_3851_ == 0)
{
v___y_3833_ = v___y_3846_;
v___y_3834_ = v___x_3852_;
v___y_3835_ = v___y_3848_;
v___y_3836_ = v___y_3847_;
v___y_3837_ = v___y_3849_;
v___y_3838_ = v___x_2985_;
goto v___jp_3832_;
}
else
{
uint8_t v___x_3853_; 
v___x_3853_ = l_List_isEmpty___redArg(v___y_3846_);
if (v___x_3853_ == 0)
{
v___y_3517_ = v___y_3846_;
v___y_3518_ = v___x_3852_;
v___y_3519_ = v___y_3848_;
v___y_3520_ = v___y_3847_;
v___y_3521_ = v___y_3849_;
goto v___jp_3516_;
}
else
{
v___y_3833_ = v___y_3846_;
v___y_3834_ = v___x_3852_;
v___y_3835_ = v___y_3848_;
v___y_3836_ = v___y_3847_;
v___y_3837_ = v___y_3849_;
v___y_3838_ = v___x_2985_;
goto v___jp_3832_;
}
}
}
v___jp_3854_:
{
lean_object* v___x_3855_; 
v___x_3855_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2974_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref_known(v___x_3855_, 1);
v___x_3857_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3858_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2987_, v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
lean_del_object(v___x_2983_);
v___x_3859_ = lean_io_mono_nanos_now();
v___x_3860_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2980_, v___f_2976_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v_fst_3862_; lean_object* v_snd_3863_; lean_object* v___x_3864_; lean_object* v___f_3865_; lean_object* v___x_3866_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v_fst_3862_ = lean_ctor_get(v_a_3861_, 0);
lean_inc_n(v_fst_3862_, 2);
v_snd_3863_ = lean_ctor_get(v_a_3861_, 1);
lean_inc(v_snd_3863_);
lean_dec(v_a_3861_);
v___x_3864_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3863_, v___x_2977_);
lean_inc(v___x_3864_);
v___f_3865_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3865_, 0, v_fst_3862_);
lean_closure_set(v___f_3865_, 1, v___x_3864_);
v___x_3866_ = lean_box(0);
if (v___x_3076_ == 0)
{
lean_object* v___x_3867_; uint8_t v___x_3868_; 
v___x_3867_ = l_Lean_trace_profiler;
v___x_3868_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2987_, v___x_3867_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3869_; 
lean_dec_ref(v___f_3865_);
v___x_3869_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2988_, v___x_2985_, v_goals_2969_, v___x_3866_, v_a_2972_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v___x_3871_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v___x_3871_ = l_List_reverse___redArg(v_a_3870_);
v___y_3846_ = v___x_3864_;
v___y_3847_ = v_fst_3862_;
v___y_3848_ = v___x_3859_;
v___y_3849_ = v_a_3856_;
v_a_3850_ = v___x_3871_;
goto v___jp_3845_;
}
else
{
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3872_; 
v_a_3872_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3869_, 1);
v___y_3846_ = v___x_3864_;
v___y_3847_ = v_fst_3862_;
v___y_3848_ = v___x_3859_;
v___y_3849_ = v_a_3856_;
v_a_3850_ = v_a_3872_;
goto v___jp_3845_;
}
else
{
lean_object* v_a_3873_; 
lean_dec(v___x_3864_);
lean_dec(v_fst_3862_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3873_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3869_, 1);
v___y_3481_ = v___x_3859_;
v___y_3482_ = v_a_3856_;
v_a_3483_ = v_a_3873_;
goto v___jp_3480_;
}
}
}
else
{
v___y_3808_ = v___x_3864_;
v___y_3809_ = v___x_3076_;
v___y_3810_ = v___x_3858_;
v___y_3811_ = v_fst_3862_;
v___y_3812_ = v___x_3859_;
v___y_3813_ = v___x_3866_;
v___y_3814_ = v_a_3856_;
v___y_3815_ = v___f_3865_;
goto v___jp_3807_;
}
}
else
{
v___y_3808_ = v___x_3864_;
v___y_3809_ = v___x_3076_;
v___y_3810_ = v___x_3858_;
v___y_3811_ = v_fst_3862_;
v___y_3812_ = v___x_3859_;
v___y_3813_ = v___x_3866_;
v___y_3814_ = v_a_3856_;
v___y_3815_ = v___f_3865_;
goto v___jp_3807_;
}
}
else
{
lean_object* v_a_3874_; 
lean_dec(v_snd_2981_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3874_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3860_, 1);
v___y_3481_ = v___x_3859_;
v___y_3482_ = v_a_3856_;
v_a_3483_ = v_a_3874_;
goto v___jp_3480_;
}
}
else
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_io_get_num_heartbeats();
v___x_3876_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2980_, v___f_2976_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v_fst_3878_; lean_object* v_snd_3879_; lean_object* v___x_3880_; lean_object* v___f_3881_; lean_object* v___x_3882_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v_fst_3878_ = lean_ctor_get(v_a_3877_, 0);
lean_inc_n(v_fst_3878_, 2);
v_snd_3879_ = lean_ctor_get(v_a_3877_, 1);
lean_inc(v_snd_3879_);
lean_dec(v_a_3877_);
v___x_3880_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3879_, v___x_2977_);
lean_inc(v___x_3880_);
v___f_3881_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3881_, 0, v_fst_3878_);
lean_closure_set(v___f_3881_, 1, v___x_3880_);
v___x_3882_ = lean_box(0);
if (v___x_3076_ == 0)
{
lean_object* v___x_3883_; uint8_t v___x_3884_; 
v___x_3883_ = l_Lean_trace_profiler;
v___x_3884_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2987_, v___x_3883_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; 
lean_dec_ref(v___f_3881_);
v___x_3885_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3858_, v___x_2985_, v_goals_2969_, v___x_3882_, v_a_2972_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3887_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
v___x_3887_ = l_List_reverse___redArg(v_a_3886_);
v___y_3457_ = v___x_3880_;
v___y_3458_ = v_fst_3878_;
v___y_3459_ = v_a_3856_;
v___y_3460_ = v___x_3875_;
v_a_3461_ = v___x_3887_;
goto v___jp_3456_;
}
else
{
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3888_; 
v_a_3888_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3885_, 1);
v___y_3457_ = v___x_3880_;
v___y_3458_ = v_fst_3878_;
v___y_3459_ = v_a_3856_;
v___y_3460_ = v___x_3875_;
v_a_3461_ = v_a_3888_;
goto v___jp_3456_;
}
else
{
lean_object* v_a_3889_; 
lean_dec(v___x_3880_);
lean_dec(v_fst_3878_);
lean_dec(v_snd_2981_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3889_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___x_3885_, 1);
v___y_3092_ = v_a_3856_;
v___y_3093_ = v___x_3875_;
v_a_3094_ = v_a_3889_;
goto v___jp_3091_;
}
}
}
else
{
v___y_3419_ = v___x_3880_;
v___y_3420_ = v_fst_3878_;
v___y_3421_ = v___x_3882_;
v___y_3422_ = v___x_3076_;
v___y_3423_ = v___x_3858_;
v___y_3424_ = v___f_3881_;
v___y_3425_ = v_a_3856_;
v___y_3426_ = v___x_3875_;
goto v___jp_3418_;
}
}
else
{
v___y_3419_ = v___x_3880_;
v___y_3420_ = v_fst_3878_;
v___y_3421_ = v___x_3882_;
v___y_3422_ = v___x_3076_;
v___y_3423_ = v___x_3858_;
v___y_3424_ = v___f_3881_;
v___y_3425_ = v_a_3856_;
v___y_3426_ = v___x_3875_;
goto v___jp_3418_;
}
}
else
{
lean_object* v_a_3890_; 
lean_dec(v_snd_2981_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3890_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3876_, 1);
v___y_3092_ = v_a_3856_;
v___y_3093_ = v___x_3875_;
v_a_3094_ = v_a_3890_;
goto v___jp_3091_;
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec_ref(v___f_3072_);
lean_del_object(v___x_2983_);
lean_dec(v_snd_2981_);
lean_dec(v_fst_2980_);
lean_dec_ref(v___f_2976_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_3891_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3855_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3855_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
}
}
else
{
lean_object* v_maxDepth_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
lean_del_object(v___x_2983_);
lean_dec(v_snd_2981_);
lean_dec(v_fst_2980_);
lean_dec_ref(v___f_2976_);
lean_dec(v_goals_2969_);
v_maxDepth_4178_ = lean_ctor_get(v_cfg_2965_, 0);
lean_inc(v_maxDepth_4178_);
v___x_4179_ = lean_box(0);
v___x_4180_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v_maxDepth_4178_, v_remaining_2970_, v___x_4179_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_4180_;
}
}
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
lean_dec_ref(v___f_2976_);
lean_dec(v_remaining_2970_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_4182_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_2978_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_2978_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_4190_, lean_object* v_trace_4191_, lean_object* v_next_4192_, lean_object* v_orig_4193_, lean_object* v_goals_4194_, lean_object* v_remaining_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4190_, v_trace_4191_, v_next_4192_, v_orig_4193_, v_goals_4194_, v_remaining_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
lean_dec(v_a_4199_);
lean_dec_ref(v_a_4198_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_4202_, lean_object* v_00_u03b2_4203_, lean_object* v_L_4204_, lean_object* v_f_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_4204_, v_f_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_4212_, lean_object* v_00_u03b2_4213_, lean_object* v_L_4214_, lean_object* v_f_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_4212_, v_00_u03b2_4213_, v_L_4214_, v_f_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_4222_, lean_object* v_x_4223_, lean_object* v_x_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v___x_4230_; 
v___x_4230_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_4222_, v_x_4223_, v_x_4224_, v___y_4226_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_4231_, lean_object* v_x_4232_, lean_object* v_x_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
uint8_t v___x_48625__boxed_4239_; lean_object* v_res_4240_; 
v___x_48625__boxed_4239_ = lean_unbox(v___x_4231_);
v_res_4240_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_48625__boxed_4239_, v_x_4232_, v_x_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_4241_, uint8_t v___x_4242_, lean_object* v_x_4243_, lean_object* v_x_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_4241_, v___x_4242_, v_x_4243_, v_x_4244_, v___y_4246_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_4251_, lean_object* v___x_4252_, lean_object* v_x_4253_, lean_object* v_x_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
uint8_t v___x_48651__boxed_4260_; uint8_t v___x_48652__boxed_4261_; lean_object* v_res_4262_; 
v___x_48651__boxed_4260_ = lean_unbox(v___x_4251_);
v___x_48652__boxed_4261_ = lean_unbox(v___x_4252_);
v_res_4262_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_48651__boxed_4260_, v___x_48652__boxed_4261_, v_x_4253_, v_x_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_4263_, lean_object* v_00_u03b2_4264_, lean_object* v_f_4265_, lean_object* v_x_4266_, lean_object* v_x_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_4265_, v_x_4266_, v_x_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4274_, lean_object* v_00_u03b2_4275_, lean_object* v_f_4276_, lean_object* v_x_4277_, lean_object* v_x_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_4274_, v_00_u03b2_4275_, v_f_4276_, v_x_4277_, v_x_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_4285_, lean_object* v_00_u03b2_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_4287_, v_a_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_4290_, lean_object* v_00_u03b2_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_4292_, v_a_4293_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_4295_, lean_object* v_g_4296_, lean_object* v_f_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v___x_4303_; 
lean_inc(v___y_4301_);
lean_inc_ref(v___y_4300_);
lean_inc(v___y_4299_);
lean_inc_ref(v___y_4298_);
v___x_4303_ = lean_apply_6(v_next_4295_, v_g_4296_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, lean_box(0));
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v___x_4305_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
lean_dec_ref_known(v___x_4303_, 1);
v___x_4305_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_4304_, v_f_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
return v___x_4305_;
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec_ref(v_f_4297_);
v_a_4306_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4303_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4303_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_4314_, lean_object* v_g_4315_, lean_object* v_f_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_4314_, v_g_4315_, v_f_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_4323_, lean_object* v_trace_4324_, lean_object* v_next_4325_, lean_object* v_goals_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_resolve_4332_; lean_object* v___x_4333_; 
v_resolve_4332_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_4332_, 0, v_next_4325_);
lean_inc_n(v_goals_4326_, 2);
v___x_4333_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4323_, v_trace_4324_, v_resolve_4332_, v_goals_4326_, v_goals_4326_, v_goals_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_4334_, lean_object* v_trace_4335_, lean_object* v_next_4336_, lean_object* v_goals_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_){
_start:
{
lean_object* v_res_4343_; 
v_res_4343_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_4334_, v_trace_4335_, v_next_4336_, v_goals_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
lean_dec(v_a_4341_);
lean_dec_ref(v_a_4340_);
lean_dec(v_a_4339_);
lean_dec_ref(v_a_4338_);
return v_res_4343_;
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

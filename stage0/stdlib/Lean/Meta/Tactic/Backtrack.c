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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
double lean_float_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "BacktrackConfig.proc failed: "};
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object*);
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
lean_dec_ref_known(v___x_217_, 1);
if (lean_obj_tag(v_val_219_) == 1)
{
uint8_t v_v_220_; 
v_v_220_ = lean_ctor_get_uint8(v_val_219_, 0);
lean_dec_ref_known(v_val_219_, 0);
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
lean_dec_ref_known(v___x_232_, 1);
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
lean_dec_ref_known(v___x_404_, 1);
if (lean_obj_tag(v_val_405_) == 3)
{
lean_object* v_v_406_; 
v_v_406_ = lean_ctor_get(v_val_405_, 0);
lean_inc(v_v_406_);
lean_dec_ref_known(v_val_405_, 1);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(lean_object* v_x_410_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_a_412_ = lean_ctor_get(v_x_410_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v_x_410_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v_x_410_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 1);
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
v_a_420_ = lean_ctor_get(v_x_410_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v_x_410_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v_x_410_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set_tag(v___x_422_, 0);
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg___boxed(lean_object* v_x_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(size_t v_sz_431_, size_t v_i_432_, lean_object* v_bs_433_){
_start:
{
uint8_t v___x_434_; 
v___x_434_ = lean_usize_dec_lt(v_i_432_, v_sz_431_);
if (v___x_434_ == 0)
{
return v_bs_433_;
}
else
{
lean_object* v_v_435_; lean_object* v_msg_436_; lean_object* v___x_437_; lean_object* v_bs_x27_438_; size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v_v_435_ = lean_array_uget_borrowed(v_bs_433_, v_i_432_);
v_msg_436_ = lean_ctor_get(v_v_435_, 1);
lean_inc_ref(v_msg_436_);
v___x_437_ = lean_unsigned_to_nat(0u);
v_bs_x27_438_ = lean_array_uset(v_bs_433_, v_i_432_, v___x_437_);
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_add(v_i_432_, v___x_439_);
v___x_441_ = lean_array_uset(v_bs_x27_438_, v_i_432_, v_msg_436_);
v_i_432_ = v___x_440_;
v_bs_433_ = v___x_441_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6___boxed(lean_object* v_sz_443_, lean_object* v_i_444_, lean_object* v_bs_445_){
_start:
{
size_t v_sz_boxed_446_; size_t v_i_boxed_447_; lean_object* v_res_448_; 
v_sz_boxed_446_ = lean_unbox_usize(v_sz_443_);
lean_dec(v_sz_443_);
v_i_boxed_447_ = lean_unbox_usize(v_i_444_);
lean_dec(v_i_444_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_boxed_446_, v_i_boxed_447_, v_bs_445_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object* v_oldTraces_449_, lean_object* v_data_450_, lean_object* v_ref_451_, lean_object* v_msg_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_fileName_458_; lean_object* v_fileMap_459_; lean_object* v_options_460_; lean_object* v_currRecDepth_461_; lean_object* v_maxRecDepth_462_; lean_object* v_ref_463_; lean_object* v_currNamespace_464_; lean_object* v_openDecls_465_; lean_object* v_initHeartbeats_466_; lean_object* v_maxHeartbeats_467_; lean_object* v_quotContext_468_; lean_object* v_currMacroScope_469_; uint8_t v_diag_470_; lean_object* v_cancelTk_x3f_471_; uint8_t v_suppressElabErrors_472_; lean_object* v_inheritedTraceOptions_473_; lean_object* v___x_474_; lean_object* v_traceState_475_; lean_object* v_traces_476_; lean_object* v_ref_477_; lean_object* v___x_478_; lean_object* v___x_479_; size_t v_sz_480_; size_t v___x_481_; lean_object* v___x_482_; lean_object* v_msg_483_; lean_object* v___x_484_; lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_522_; 
v_fileName_458_ = lean_ctor_get(v___y_455_, 0);
v_fileMap_459_ = lean_ctor_get(v___y_455_, 1);
v_options_460_ = lean_ctor_get(v___y_455_, 2);
v_currRecDepth_461_ = lean_ctor_get(v___y_455_, 3);
v_maxRecDepth_462_ = lean_ctor_get(v___y_455_, 4);
v_ref_463_ = lean_ctor_get(v___y_455_, 5);
v_currNamespace_464_ = lean_ctor_get(v___y_455_, 6);
v_openDecls_465_ = lean_ctor_get(v___y_455_, 7);
v_initHeartbeats_466_ = lean_ctor_get(v___y_455_, 8);
v_maxHeartbeats_467_ = lean_ctor_get(v___y_455_, 9);
v_quotContext_468_ = lean_ctor_get(v___y_455_, 10);
v_currMacroScope_469_ = lean_ctor_get(v___y_455_, 11);
v_diag_470_ = lean_ctor_get_uint8(v___y_455_, sizeof(void*)*14);
v_cancelTk_x3f_471_ = lean_ctor_get(v___y_455_, 12);
v_suppressElabErrors_472_ = lean_ctor_get_uint8(v___y_455_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_473_ = lean_ctor_get(v___y_455_, 13);
v___x_474_ = lean_st_ref_get(v___y_456_);
v_traceState_475_ = lean_ctor_get(v___x_474_, 4);
lean_inc_ref(v_traceState_475_);
lean_dec(v___x_474_);
v_traces_476_ = lean_ctor_get(v_traceState_475_, 0);
lean_inc_ref(v_traces_476_);
lean_dec_ref(v_traceState_475_);
v_ref_477_ = l_Lean_replaceRef(v_ref_451_, v_ref_463_);
lean_inc_ref(v_inheritedTraceOptions_473_);
lean_inc(v_cancelTk_x3f_471_);
lean_inc(v_currMacroScope_469_);
lean_inc(v_quotContext_468_);
lean_inc(v_maxHeartbeats_467_);
lean_inc(v_initHeartbeats_466_);
lean_inc(v_openDecls_465_);
lean_inc(v_currNamespace_464_);
lean_inc(v_maxRecDepth_462_);
lean_inc(v_currRecDepth_461_);
lean_inc_ref(v_options_460_);
lean_inc_ref(v_fileMap_459_);
lean_inc_ref(v_fileName_458_);
v___x_478_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_478_, 0, v_fileName_458_);
lean_ctor_set(v___x_478_, 1, v_fileMap_459_);
lean_ctor_set(v___x_478_, 2, v_options_460_);
lean_ctor_set(v___x_478_, 3, v_currRecDepth_461_);
lean_ctor_set(v___x_478_, 4, v_maxRecDepth_462_);
lean_ctor_set(v___x_478_, 5, v_ref_477_);
lean_ctor_set(v___x_478_, 6, v_currNamespace_464_);
lean_ctor_set(v___x_478_, 7, v_openDecls_465_);
lean_ctor_set(v___x_478_, 8, v_initHeartbeats_466_);
lean_ctor_set(v___x_478_, 9, v_maxHeartbeats_467_);
lean_ctor_set(v___x_478_, 10, v_quotContext_468_);
lean_ctor_set(v___x_478_, 11, v_currMacroScope_469_);
lean_ctor_set(v___x_478_, 12, v_cancelTk_x3f_471_);
lean_ctor_set(v___x_478_, 13, v_inheritedTraceOptions_473_);
lean_ctor_set_uint8(v___x_478_, sizeof(void*)*14, v_diag_470_);
lean_ctor_set_uint8(v___x_478_, sizeof(void*)*14 + 1, v_suppressElabErrors_472_);
v___x_479_ = l_Lean_PersistentArray_toArray___redArg(v_traces_476_);
lean_dec_ref(v_traces_476_);
v_sz_480_ = lean_array_size(v___x_479_);
v___x_481_ = ((size_t)0ULL);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_480_, v___x_481_, v___x_479_);
v_msg_483_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_483_, 0, v_data_450_);
lean_ctor_set(v_msg_483_, 1, v_msg_452_);
lean_ctor_set(v_msg_483_, 2, v___x_482_);
v___x_484_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_483_, v___y_453_, v___y_454_, v___x_478_, v___y_456_);
lean_dec_ref_known(v___x_478_, 14);
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_522_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_522_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_522_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v_traceState_490_; lean_object* v_env_491_; lean_object* v_nextMacroScope_492_; lean_object* v_ngen_493_; lean_object* v_auxDeclNGen_494_; lean_object* v_cache_495_; lean_object* v_messages_496_; lean_object* v_infoState_497_; lean_object* v_snapshotTasks_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_521_; 
v___x_489_ = lean_st_ref_take(v___y_456_);
v_traceState_490_ = lean_ctor_get(v___x_489_, 4);
v_env_491_ = lean_ctor_get(v___x_489_, 0);
v_nextMacroScope_492_ = lean_ctor_get(v___x_489_, 1);
v_ngen_493_ = lean_ctor_get(v___x_489_, 2);
v_auxDeclNGen_494_ = lean_ctor_get(v___x_489_, 3);
v_cache_495_ = lean_ctor_get(v___x_489_, 5);
v_messages_496_ = lean_ctor_get(v___x_489_, 6);
v_infoState_497_ = lean_ctor_get(v___x_489_, 7);
v_snapshotTasks_498_ = lean_ctor_get(v___x_489_, 8);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_521_ == 0)
{
v___x_500_ = v___x_489_;
v_isShared_501_ = v_isSharedCheck_521_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snapshotTasks_498_);
lean_inc(v_infoState_497_);
lean_inc(v_messages_496_);
lean_inc(v_cache_495_);
lean_inc(v_traceState_490_);
lean_inc(v_auxDeclNGen_494_);
lean_inc(v_ngen_493_);
lean_inc(v_nextMacroScope_492_);
lean_inc(v_env_491_);
lean_dec(v___x_489_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_521_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint64_t v_tid_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_519_; 
v_tid_502_ = lean_ctor_get_uint64(v_traceState_490_, sizeof(void*)*1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_traceState_490_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v_traceState_490_, 0);
lean_dec(v_unused_520_);
v___x_504_ = v_traceState_490_;
v_isShared_505_ = v_isSharedCheck_519_;
goto v_resetjp_503_;
}
else
{
lean_dec(v_traceState_490_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_519_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_ref_451_);
lean_ctor_set(v___x_506_, 1, v_a_485_);
v___x_507_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_449_, v___x_506_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_507_);
v___x_509_ = v___x_504_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_507_);
lean_ctor_set_uint64(v_reuseFailAlloc_518_, sizeof(void*)*1, v_tid_502_);
v___x_509_ = v_reuseFailAlloc_518_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_511_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 4, v___x_509_);
v___x_511_ = v___x_500_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_env_491_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_nextMacroScope_492_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_ngen_493_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_auxDeclNGen_494_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_517_, 5, v_cache_495_);
lean_ctor_set(v_reuseFailAlloc_517_, 6, v_messages_496_);
lean_ctor_set(v_reuseFailAlloc_517_, 7, v_infoState_497_);
lean_ctor_set(v_reuseFailAlloc_517_, 8, v_snapshotTasks_498_);
v___x_511_ = v_reuseFailAlloc_517_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_512_ = lean_st_ref_set(v___y_456_, v___x_511_);
v___x_513_ = lean_box(0);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_513_);
v___x_515_ = v___x_487_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object* v_oldTraces_523_, lean_object* v_data_524_, lean_object* v_ref_525_, lean_object* v_msg_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_523_, v_data_524_, v_ref_525_, v_msg_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
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
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0(void){
_start:
{
lean_object* v___x_541_; double v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_float_of_nat(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3(void){
_start:
{
lean_object* v___x_546_; double v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(1000u);
v___x_547_ = lean_float_of_nat(v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_cls_548_, uint8_t v_collapsed_549_, lean_object* v_tag_550_, lean_object* v_opts_551_, uint8_t v_clsEnabled_552_, lean_object* v_oldTraces_553_, lean_object* v_msg_554_, lean_object* v_resStartStop_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_fst_561_; lean_object* v_snd_562_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v_data_566_; lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___y_582_; lean_object* v_a_583_; uint8_t v___y_598_; double v___y_629_; 
v_fst_561_ = lean_ctor_get(v_resStartStop_555_, 0);
lean_inc(v_fst_561_);
v_snd_562_ = lean_ctor_get(v_resStartStop_555_, 1);
lean_inc(v_snd_562_);
lean_dec_ref(v_resStartStop_555_);
v_fst_577_ = lean_ctor_get(v_snd_562_, 0);
lean_inc(v_fst_577_);
v_snd_578_ = lean_ctor_get(v_snd_562_, 1);
lean_inc(v_snd_578_);
lean_dec(v_snd_562_);
v___x_579_ = l_Lean_trace_profiler;
v___x_580_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_551_, v___x_579_);
if (v___x_580_ == 0)
{
v___y_598_ = v___x_580_;
goto v___jp_597_;
}
else
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = l_Lean_trace_profiler_useHeartbeats;
v___x_635_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_551_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; double v___x_638_; double v___x_639_; double v___x_640_; 
v___x_636_ = l_Lean_trace_profiler_threshold;
v___x_637_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_551_, v___x_636_);
v___x_638_ = lean_float_of_nat(v___x_637_);
v___x_639_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_640_ = lean_float_div(v___x_638_, v___x_639_);
v___y_629_ = v___x_640_;
goto v___jp_628_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; double v___x_643_; 
v___x_641_ = l_Lean_trace_profiler_threshold;
v___x_642_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_551_, v___x_641_);
v___x_643_ = lean_float_of_nat(v___x_642_);
v___y_629_ = v___x_643_;
goto v___jp_628_;
}
}
v___jp_563_:
{
lean_object* v___x_567_; 
lean_inc(v___y_565_);
v___x_567_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_553_, v_data_566_, v___y_565_, v___y_564_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v___x_568_; 
lean_dec_ref_known(v___x_567_, 1);
v___x_568_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_561_);
return v___x_568_;
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v_fst_561_);
v_a_569_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_567_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
v___jp_581_:
{
uint8_t v_result_584_; lean_object* v___x_585_; lean_object* v___x_586_; double v___x_587_; lean_object* v_data_588_; 
v_result_584_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_fst_561_);
v___x_585_ = lean_box(v_result_584_);
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
v___x_587_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_550_);
lean_inc_ref(v___x_586_);
lean_inc(v_cls_548_);
v_data_588_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_588_, 0, v_cls_548_);
lean_ctor_set(v_data_588_, 1, v___x_586_);
lean_ctor_set(v_data_588_, 2, v_tag_550_);
lean_ctor_set_float(v_data_588_, sizeof(void*)*3, v___x_587_);
lean_ctor_set_float(v_data_588_, sizeof(void*)*3 + 8, v___x_587_);
lean_ctor_set_uint8(v_data_588_, sizeof(void*)*3 + 16, v_collapsed_549_);
if (v___x_580_ == 0)
{
lean_dec_ref_known(v___x_586_, 1);
lean_dec(v_snd_578_);
lean_dec(v_fst_577_);
lean_dec_ref(v_tag_550_);
lean_dec(v_cls_548_);
v___y_564_ = v_a_583_;
v___y_565_ = v___y_582_;
v_data_566_ = v_data_588_;
goto v___jp_563_;
}
else
{
lean_object* v_data_589_; double v___x_590_; double v___x_591_; 
lean_dec_ref_known(v_data_588_, 3);
v_data_589_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_589_, 0, v_cls_548_);
lean_ctor_set(v_data_589_, 1, v___x_586_);
lean_ctor_set(v_data_589_, 2, v_tag_550_);
v___x_590_ = lean_unbox_float(v_fst_577_);
lean_dec(v_fst_577_);
lean_ctor_set_float(v_data_589_, sizeof(void*)*3, v___x_590_);
v___x_591_ = lean_unbox_float(v_snd_578_);
lean_dec(v_snd_578_);
lean_ctor_set_float(v_data_589_, sizeof(void*)*3 + 8, v___x_591_);
lean_ctor_set_uint8(v_data_589_, sizeof(void*)*3 + 16, v_collapsed_549_);
v___y_564_ = v_a_583_;
v___y_565_ = v___y_582_;
v_data_566_ = v_data_589_;
goto v___jp_563_;
}
}
v___jp_592_:
{
lean_object* v_ref_593_; lean_object* v___x_594_; 
v_ref_593_ = lean_ctor_get(v___y_558_, 5);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___y_557_);
lean_inc_ref(v___y_556_);
lean_inc(v_fst_561_);
v___x_594_ = lean_apply_6(v_msg_554_, v_fst_561_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, lean_box(0));
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
v___y_582_ = v_ref_593_;
v_a_583_ = v_a_595_;
goto v___jp_581_;
}
else
{
lean_object* v___x_596_; 
lean_dec_ref_known(v___x_594_, 1);
v___x_596_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_582_ = v_ref_593_;
v_a_583_ = v___x_596_;
goto v___jp_581_;
}
}
v___jp_597_:
{
if (v_clsEnabled_552_ == 0)
{
if (v___y_598_ == 0)
{
lean_object* v___x_599_; lean_object* v_traceState_600_; lean_object* v_env_601_; lean_object* v_nextMacroScope_602_; lean_object* v_ngen_603_; lean_object* v_auxDeclNGen_604_; lean_object* v_cache_605_; lean_object* v_messages_606_; lean_object* v_infoState_607_; lean_object* v_snapshotTasks_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_snd_578_);
lean_dec(v_fst_577_);
lean_dec_ref(v_msg_554_);
lean_dec_ref(v_tag_550_);
lean_dec(v_cls_548_);
v___x_599_ = lean_st_ref_take(v___y_559_);
v_traceState_600_ = lean_ctor_get(v___x_599_, 4);
v_env_601_ = lean_ctor_get(v___x_599_, 0);
v_nextMacroScope_602_ = lean_ctor_get(v___x_599_, 1);
v_ngen_603_ = lean_ctor_get(v___x_599_, 2);
v_auxDeclNGen_604_ = lean_ctor_get(v___x_599_, 3);
v_cache_605_ = lean_ctor_get(v___x_599_, 5);
v_messages_606_ = lean_ctor_get(v___x_599_, 6);
v_infoState_607_ = lean_ctor_get(v___x_599_, 7);
v_snapshotTasks_608_ = lean_ctor_get(v___x_599_, 8);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_627_ == 0)
{
v___x_610_ = v___x_599_;
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_snapshotTasks_608_);
lean_inc(v_infoState_607_);
lean_inc(v_messages_606_);
lean_inc(v_cache_605_);
lean_inc(v_traceState_600_);
lean_inc(v_auxDeclNGen_604_);
lean_inc(v_ngen_603_);
lean_inc(v_nextMacroScope_602_);
lean_inc(v_env_601_);
lean_dec(v___x_599_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
uint64_t v_tid_612_; lean_object* v_traces_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_626_; 
v_tid_612_ = lean_ctor_get_uint64(v_traceState_600_, sizeof(void*)*1);
v_traces_613_ = lean_ctor_get(v_traceState_600_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_traceState_600_);
if (v_isSharedCheck_626_ == 0)
{
v___x_615_ = v_traceState_600_;
v_isShared_616_ = v_isSharedCheck_626_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_traces_613_);
lean_dec(v_traceState_600_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_626_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_617_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_553_, v_traces_613_);
lean_dec_ref(v_traces_613_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_617_);
v___x_619_ = v___x_615_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_617_);
lean_ctor_set_uint64(v_reuseFailAlloc_625_, sizeof(void*)*1, v_tid_612_);
v___x_619_ = v_reuseFailAlloc_625_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 4, v___x_619_);
v___x_621_ = v___x_610_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_env_601_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_nextMacroScope_602_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_ngen_603_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v_auxDeclNGen_604_);
lean_ctor_set(v_reuseFailAlloc_624_, 4, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_624_, 5, v_cache_605_);
lean_ctor_set(v_reuseFailAlloc_624_, 6, v_messages_606_);
lean_ctor_set(v_reuseFailAlloc_624_, 7, v_infoState_607_);
lean_ctor_set(v_reuseFailAlloc_624_, 8, v_snapshotTasks_608_);
v___x_621_ = v_reuseFailAlloc_624_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_st_ref_set(v___y_559_, v___x_621_);
v___x_623_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_561_);
return v___x_623_;
}
}
}
}
}
else
{
goto v___jp_592_;
}
}
else
{
goto v___jp_592_;
}
}
v___jp_628_:
{
double v___x_630_; double v___x_631_; double v___x_632_; uint8_t v___x_633_; 
v___x_630_ = lean_unbox_float(v_snd_578_);
v___x_631_ = lean_unbox_float(v_fst_577_);
v___x_632_ = lean_float_sub(v___x_630_, v___x_631_);
v___x_633_ = lean_float_decLt(v___y_629_, v___x_632_);
v___y_598_ = v___x_633_;
goto v___jp_597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_cls_644_, lean_object* v_collapsed_645_, lean_object* v_tag_646_, lean_object* v_opts_647_, lean_object* v_clsEnabled_648_, lean_object* v_oldTraces_649_, lean_object* v_msg_650_, lean_object* v_resStartStop_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v_collapsed_boxed_657_; uint8_t v_clsEnabled_boxed_658_; lean_object* v_res_659_; 
v_collapsed_boxed_657_ = lean_unbox(v_collapsed_645_);
v_clsEnabled_boxed_658_ = lean_unbox(v_clsEnabled_648_);
v_res_659_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_cls_644_, v_collapsed_boxed_657_, v_tag_646_, v_opts_647_, v_clsEnabled_boxed_658_, v_oldTraces_649_, v_msg_650_, v_resStartStop_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec_ref(v_opts_647_);
return v_res_659_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0));
v___x_662_ = l_Lean_stringToMessageData(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* v_a_663_, lean_object* v_x_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
v___x_671_ = l_Lean_Exception_toMessageData(v_a_663_);
v___x_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* v_a_674_, lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_a_674_, v_x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec_ref(v_x_675_);
return v_res_681_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object* v_keys_682_, lean_object* v_i_683_, lean_object* v_k_684_){
_start:
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_array_get_size(v_keys_682_);
v___x_686_ = lean_nat_dec_lt(v_i_683_, v___x_685_);
if (v___x_686_ == 0)
{
lean_dec(v_i_683_);
return v___x_686_;
}
else
{
lean_object* v_k_x27_687_; uint8_t v___x_688_; 
v_k_x27_687_ = lean_array_fget_borrowed(v_keys_682_, v_i_683_);
v___x_688_ = l_Lean_instBEqMVarId_beq(v_k_684_, v_k_x27_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_nat_add(v_i_683_, v___x_689_);
lean_dec(v_i_683_);
v_i_683_ = v___x_690_;
goto _start;
}
else
{
lean_dec(v_i_683_);
return v___x_688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object* v_keys_692_, lean_object* v_i_693_, lean_object* v_k_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_692_, v_i_693_, v_k_694_);
lean_dec(v_k_694_);
lean_dec_ref(v_keys_692_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_697_, size_t v_x_698_, lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_x_697_) == 0)
{
lean_object* v_es_700_; lean_object* v___x_701_; size_t v___x_702_; size_t v___x_703_; lean_object* v_j_704_; lean_object* v___x_705_; 
v_es_700_ = lean_ctor_get(v_x_697_, 0);
v___x_701_ = lean_box(2);
v___x_702_ = ((size_t)31ULL);
v___x_703_ = lean_usize_land(v_x_698_, v___x_702_);
v_j_704_ = lean_usize_to_nat(v___x_703_);
v___x_705_ = lean_array_get_borrowed(v___x_701_, v_es_700_, v_j_704_);
lean_dec(v_j_704_);
switch(lean_obj_tag(v___x_705_))
{
case 0:
{
lean_object* v_key_706_; uint8_t v___x_707_; 
v_key_706_ = lean_ctor_get(v___x_705_, 0);
v___x_707_ = l_Lean_instBEqMVarId_beq(v_x_699_, v_key_706_);
return v___x_707_;
}
case 1:
{
lean_object* v_node_708_; size_t v___x_709_; size_t v___x_710_; 
v_node_708_ = lean_ctor_get(v___x_705_, 0);
v___x_709_ = ((size_t)5ULL);
v___x_710_ = lean_usize_shift_right(v_x_698_, v___x_709_);
v_x_697_ = v_node_708_;
v_x_698_ = v___x_710_;
goto _start;
}
default: 
{
uint8_t v___x_712_; 
v___x_712_ = 0;
return v___x_712_;
}
}
}
else
{
lean_object* v_ks_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_ks_713_ = lean_ctor_get(v_x_697_, 0);
v___x_714_ = lean_unsigned_to_nat(0u);
v___x_715_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_ks_713_, v___x_714_, v_x_699_);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
size_t v_x_82046__boxed_719_; uint8_t v_res_720_; lean_object* v_r_721_; 
v_x_82046__boxed_719_ = lean_unbox_usize(v_x_717_);
lean_dec(v_x_717_);
v_res_720_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_716_, v_x_82046__boxed_719_, v_x_718_);
lean_dec(v_x_718_);
lean_dec_ref(v_x_716_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
uint64_t v___x_724_; size_t v___x_725_; uint8_t v___x_726_; 
v___x_724_ = l_Lean_instHashableMVarId_hash(v_x_723_);
v___x_725_ = lean_uint64_to_usize(v___x_724_);
v___x_726_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_722_, v___x_725_, v_x_723_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object* v_x_727_, lean_object* v_x_728_){
_start:
{
uint8_t v_res_729_; lean_object* v_r_730_; 
v_res_729_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_727_, v_x_728_);
lean_dec(v_x_728_);
lean_dec_ref(v_x_727_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object* v_mvarId_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; lean_object* v_mctx_735_; lean_object* v_eAssignment_736_; uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_734_ = lean_st_ref_get(v___y_732_);
v_mctx_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_mctx_735_);
lean_dec(v___x_734_);
v_eAssignment_736_ = lean_ctor_get(v_mctx_735_, 8);
lean_inc_ref(v_eAssignment_736_);
lean_dec_ref(v_mctx_735_);
v___x_737_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_eAssignment_736_, v_mvarId_731_);
lean_dec_ref(v_eAssignment_736_);
v___x_738_ = lean_box(v___x_737_);
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object* v_mvarId_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec(v_mvarId_740_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_ref_750_; lean_object* v___x_751_; lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_760_; 
v_ref_750_ = lean_ctor_get(v___y_747_, 5);
v___x_751_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_760_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_760_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
lean_inc(v_ref_750_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_ref_750_);
lean_ctor_set(v___x_756_, 1, v_a_752_);
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 1);
lean_ctor_set(v___x_754_, 0, v___x_756_);
v___x_758_ = v___x_754_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_767_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_e_768_){
_start:
{
if (lean_obj_tag(v_e_768_) == 0)
{
uint8_t v___x_769_; 
v___x_769_ = 2;
return v___x_769_;
}
else
{
uint8_t v___x_770_; 
v___x_770_ = 0;
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_e_771_){
_start:
{
uint8_t v_res_772_; lean_object* v_r_773_; 
v_res_772_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_e_771_);
lean_dec_ref(v_e_771_);
v_r_773_ = lean_box(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_774_, uint8_t v_collapsed_775_, lean_object* v_tag_776_, lean_object* v_opts_777_, uint8_t v_clsEnabled_778_, lean_object* v_oldTraces_779_, lean_object* v_msg_780_, lean_object* v_resStartStop_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_fst_787_; lean_object* v_snd_788_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v_data_792_; lean_object* v_fst_803_; lean_object* v_snd_804_; lean_object* v___x_805_; uint8_t v___x_806_; lean_object* v___y_808_; lean_object* v_a_809_; uint8_t v___y_824_; double v___y_855_; 
v_fst_787_ = lean_ctor_get(v_resStartStop_781_, 0);
lean_inc(v_fst_787_);
v_snd_788_ = lean_ctor_get(v_resStartStop_781_, 1);
lean_inc(v_snd_788_);
lean_dec_ref(v_resStartStop_781_);
v_fst_803_ = lean_ctor_get(v_snd_788_, 0);
lean_inc(v_fst_803_);
v_snd_804_ = lean_ctor_get(v_snd_788_, 1);
lean_inc(v_snd_804_);
lean_dec(v_snd_788_);
v___x_805_ = l_Lean_trace_profiler;
v___x_806_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_777_, v___x_805_);
if (v___x_806_ == 0)
{
v___y_824_ = v___x_806_;
goto v___jp_823_;
}
else
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = l_Lean_trace_profiler_useHeartbeats;
v___x_861_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_777_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; double v___x_864_; double v___x_865_; double v___x_866_; 
v___x_862_ = l_Lean_trace_profiler_threshold;
v___x_863_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_777_, v___x_862_);
v___x_864_ = lean_float_of_nat(v___x_863_);
v___x_865_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_866_ = lean_float_div(v___x_864_, v___x_865_);
v___y_855_ = v___x_866_;
goto v___jp_854_;
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; double v___x_869_; 
v___x_867_ = l_Lean_trace_profiler_threshold;
v___x_868_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_777_, v___x_867_);
v___x_869_ = lean_float_of_nat(v___x_868_);
v___y_855_ = v___x_869_;
goto v___jp_854_;
}
}
v___jp_789_:
{
lean_object* v___x_793_; 
lean_inc(v___y_790_);
v___x_793_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_779_, v_data_792_, v___y_790_, v___y_791_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v___x_794_; 
lean_dec_ref_known(v___x_793_, 1);
v___x_794_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_787_);
return v___x_794_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v_fst_787_);
v_a_795_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_793_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_793_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
v___jp_807_:
{
uint8_t v_result_810_; lean_object* v___x_811_; lean_object* v___x_812_; double v___x_813_; lean_object* v_data_814_; 
v_result_810_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_fst_787_);
v___x_811_ = lean_box(v_result_810_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_776_);
lean_inc_ref(v___x_812_);
lean_inc(v_cls_774_);
v_data_814_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_814_, 0, v_cls_774_);
lean_ctor_set(v_data_814_, 1, v___x_812_);
lean_ctor_set(v_data_814_, 2, v_tag_776_);
lean_ctor_set_float(v_data_814_, sizeof(void*)*3, v___x_813_);
lean_ctor_set_float(v_data_814_, sizeof(void*)*3 + 8, v___x_813_);
lean_ctor_set_uint8(v_data_814_, sizeof(void*)*3 + 16, v_collapsed_775_);
if (v___x_806_ == 0)
{
lean_dec_ref_known(v___x_812_, 1);
lean_dec(v_snd_804_);
lean_dec(v_fst_803_);
lean_dec_ref(v_tag_776_);
lean_dec(v_cls_774_);
v___y_790_ = v___y_808_;
v___y_791_ = v_a_809_;
v_data_792_ = v_data_814_;
goto v___jp_789_;
}
else
{
lean_object* v_data_815_; double v___x_816_; double v___x_817_; 
lean_dec_ref_known(v_data_814_, 3);
v_data_815_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_815_, 0, v_cls_774_);
lean_ctor_set(v_data_815_, 1, v___x_812_);
lean_ctor_set(v_data_815_, 2, v_tag_776_);
v___x_816_ = lean_unbox_float(v_fst_803_);
lean_dec(v_fst_803_);
lean_ctor_set_float(v_data_815_, sizeof(void*)*3, v___x_816_);
v___x_817_ = lean_unbox_float(v_snd_804_);
lean_dec(v_snd_804_);
lean_ctor_set_float(v_data_815_, sizeof(void*)*3 + 8, v___x_817_);
lean_ctor_set_uint8(v_data_815_, sizeof(void*)*3 + 16, v_collapsed_775_);
v___y_790_ = v___y_808_;
v___y_791_ = v_a_809_;
v_data_792_ = v_data_815_;
goto v___jp_789_;
}
}
v___jp_818_:
{
lean_object* v_ref_819_; lean_object* v___x_820_; 
v_ref_819_ = lean_ctor_get(v___y_784_, 5);
lean_inc(v___y_785_);
lean_inc_ref(v___y_784_);
lean_inc(v___y_783_);
lean_inc_ref(v___y_782_);
lean_inc(v_fst_787_);
v___x_820_ = lean_apply_6(v_msg_780_, v_fst_787_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, lean_box(0));
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
v___y_808_ = v_ref_819_;
v_a_809_ = v_a_821_;
goto v___jp_807_;
}
else
{
lean_object* v___x_822_; 
lean_dec_ref_known(v___x_820_, 1);
v___x_822_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_808_ = v_ref_819_;
v_a_809_ = v___x_822_;
goto v___jp_807_;
}
}
v___jp_823_:
{
if (v_clsEnabled_778_ == 0)
{
if (v___y_824_ == 0)
{
lean_object* v___x_825_; lean_object* v_traceState_826_; lean_object* v_env_827_; lean_object* v_nextMacroScope_828_; lean_object* v_ngen_829_; lean_object* v_auxDeclNGen_830_; lean_object* v_cache_831_; lean_object* v_messages_832_; lean_object* v_infoState_833_; lean_object* v_snapshotTasks_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_853_; 
lean_dec(v_snd_804_);
lean_dec(v_fst_803_);
lean_dec_ref(v_msg_780_);
lean_dec_ref(v_tag_776_);
lean_dec(v_cls_774_);
v___x_825_ = lean_st_ref_take(v___y_785_);
v_traceState_826_ = lean_ctor_get(v___x_825_, 4);
v_env_827_ = lean_ctor_get(v___x_825_, 0);
v_nextMacroScope_828_ = lean_ctor_get(v___x_825_, 1);
v_ngen_829_ = lean_ctor_get(v___x_825_, 2);
v_auxDeclNGen_830_ = lean_ctor_get(v___x_825_, 3);
v_cache_831_ = lean_ctor_get(v___x_825_, 5);
v_messages_832_ = lean_ctor_get(v___x_825_, 6);
v_infoState_833_ = lean_ctor_get(v___x_825_, 7);
v_snapshotTasks_834_ = lean_ctor_get(v___x_825_, 8);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_853_ == 0)
{
v___x_836_ = v___x_825_;
v_isShared_837_ = v_isSharedCheck_853_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_snapshotTasks_834_);
lean_inc(v_infoState_833_);
lean_inc(v_messages_832_);
lean_inc(v_cache_831_);
lean_inc(v_traceState_826_);
lean_inc(v_auxDeclNGen_830_);
lean_inc(v_ngen_829_);
lean_inc(v_nextMacroScope_828_);
lean_inc(v_env_827_);
lean_dec(v___x_825_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_853_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
uint64_t v_tid_838_; lean_object* v_traces_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_852_; 
v_tid_838_ = lean_ctor_get_uint64(v_traceState_826_, sizeof(void*)*1);
v_traces_839_ = lean_ctor_get(v_traceState_826_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v_traceState_826_);
if (v_isSharedCheck_852_ == 0)
{
v___x_841_ = v_traceState_826_;
v_isShared_842_ = v_isSharedCheck_852_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_traces_839_);
lean_dec(v_traceState_826_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_852_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_779_, v_traces_839_);
lean_dec_ref(v_traces_839_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_843_);
lean_ctor_set_uint64(v_reuseFailAlloc_851_, sizeof(void*)*1, v_tid_838_);
v___x_845_ = v_reuseFailAlloc_851_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 4, v___x_845_);
v___x_847_ = v___x_836_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_env_827_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_nextMacroScope_828_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_ngen_829_);
lean_ctor_set(v_reuseFailAlloc_850_, 3, v_auxDeclNGen_830_);
lean_ctor_set(v_reuseFailAlloc_850_, 4, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_850_, 5, v_cache_831_);
lean_ctor_set(v_reuseFailAlloc_850_, 6, v_messages_832_);
lean_ctor_set(v_reuseFailAlloc_850_, 7, v_infoState_833_);
lean_ctor_set(v_reuseFailAlloc_850_, 8, v_snapshotTasks_834_);
v___x_847_ = v_reuseFailAlloc_850_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_st_ref_set(v___y_785_, v___x_847_);
v___x_849_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_787_);
return v___x_849_;
}
}
}
}
}
else
{
goto v___jp_818_;
}
}
else
{
goto v___jp_818_;
}
}
v___jp_854_:
{
double v___x_856_; double v___x_857_; double v___x_858_; uint8_t v___x_859_; 
v___x_856_ = lean_unbox_float(v_snd_804_);
v___x_857_ = lean_unbox_float(v_fst_803_);
v___x_858_ = lean_float_sub(v___x_856_, v___x_857_);
v___x_859_ = lean_float_decLt(v___y_855_, v___x_858_);
v___y_824_ = v___x_859_;
goto v___jp_823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_870_, lean_object* v_collapsed_871_, lean_object* v_tag_872_, lean_object* v_opts_873_, lean_object* v_clsEnabled_874_, lean_object* v_oldTraces_875_, lean_object* v_msg_876_, lean_object* v_resStartStop_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v_collapsed_boxed_883_; uint8_t v_clsEnabled_boxed_884_; lean_object* v_res_885_; 
v_collapsed_boxed_883_ = lean_unbox(v_collapsed_871_);
v_clsEnabled_boxed_884_ = lean_unbox(v_clsEnabled_874_);
v_res_885_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_870_, v_collapsed_boxed_883_, v_tag_872_, v_opts_873_, v_clsEnabled_boxed_884_, v_oldTraces_875_, v_msg_876_, v_resStartStop_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec_ref(v_opts_873_);
return v_res_885_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_head_889_, lean_object* v_x_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_897_, 0, v_head_889_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_head_900_, lean_object* v_x_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_head_900_, v_x_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec_ref(v_x_901_);
return v_res_907_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object* v_head_911_, lean_object* v_x_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_929_; 
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v_head_911_);
v___x_919_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v___x_918_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_929_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_929_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_929_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1);
v___x_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v_a_920_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_925_);
v___x_927_ = v___x_922_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object* v_head_930_, lean_object* v_x_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(v_head_930_, v_x_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_x_931_);
return v_res_937_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_938_; double v___x_939_; 
v___x_938_ = lean_unsigned_to_nat(1000000000u);
v___x_939_ = lean_float_of_nat(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* v_tail_951_, lean_object* v_cfg_952_, lean_object* v_trace_953_, lean_object* v_next_954_, lean_object* v_goals_955_, lean_object* v_n_956_, lean_object* v_acc_957_, lean_object* v_r_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_951_, v_cfg_952_, v_trace_953_, v_next_954_, v_goals_955_, v_n_956_, v_acc_957_, v_r_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_965_, lean_object* v_trace_966_, lean_object* v_next_967_, lean_object* v_goals_968_, lean_object* v_n_969_, lean_object* v_curr_970_, lean_object* v_acc_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; uint8_t v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; uint8_t v___y_984_; lean_object* v_a_985_; lean_object* v___y_995_; lean_object* v___y_996_; uint8_t v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; uint8_t v___y_1001_; lean_object* v_a_1002_; lean_object* v___y_1015_; lean_object* v___y_1016_; uint8_t v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; uint8_t v___y_1021_; uint8_t v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___y_1069_; lean_object* v_a_1070_; uint8_t v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; uint8_t v___y_1086_; lean_object* v_a_1087_; uint8_t v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; uint8_t v___y_1096_; lean_object* v_a_1097_; uint8_t v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; uint8_t v___y_1106_; lean_object* v___y_1107_; uint8_t v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; uint8_t v___y_1116_; lean_object* v___y_1117_; lean_object* v_a_1118_; uint8_t v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; uint8_t v___y_1137_; lean_object* v_a_1138_; uint8_t v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; uint8_t v___y_1147_; lean_object* v_a_1148_; uint8_t v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; uint8_t v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v_zero_1161_; uint8_t v_isZero_1162_; 
v_zero_1161_ = lean_unsigned_to_nat(0u);
v_isZero_1162_ = lean_nat_dec_eq(v_n_969_, v_zero_1161_);
if (v_isZero_1162_ == 1)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec(v_acc_971_);
lean_dec(v_curr_970_);
lean_dec(v_n_969_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v___x_1163_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1164_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1163_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1164_;
}
else
{
lean_object* v_proc_1165_; lean_object* v_suspend_1166_; lean_object* v_discharge_1167_; lean_object* v___f_1168_; uint8_t v___y_1170_; lean_object* v___y_1171_; uint8_t v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___f_1210_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; uint8_t v___y_1215_; uint8_t v___y_1216_; lean_object* v___y_1217_; lean_object* v_a_1218_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; uint8_t v___y_1231_; lean_object* v___y_1232_; uint8_t v___y_1233_; lean_object* v_a_1234_; lean_object* v___y_1247_; lean_object* v___y_1248_; uint8_t v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; uint8_t v___y_1253_; lean_object* v___f_1294_; uint8_t v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; uint8_t v___y_1301_; lean_object* v_a_1302_; uint8_t v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; uint8_t v___y_1319_; lean_object* v___y_1320_; lean_object* v_a_1321_; lean_object* v___f_1330_; uint8_t v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; uint8_t v___y_1339_; lean_object* v___y_1340_; uint8_t v___y_1341_; lean_object* v_a_1342_; lean_object* v___y_1355_; uint8_t v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; uint8_t v___y_1364_; lean_object* v_a_1365_; lean_object* v___y_1375_; uint8_t v___y_1376_; uint8_t v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; uint8_t v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; uint8_t v___y_1385_; lean_object* v___y_1386_; uint8_t v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; uint8_t v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; uint8_t v___y_1436_; lean_object* v_a_1437_; uint8_t v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; uint8_t v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; uint8_t v___y_1459_; lean_object* v_a_1460_; lean_object* v___y_1470_; uint8_t v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; uint8_t v___y_1475_; lean_object* v___y_1476_; uint8_t v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; uint8_t v___y_1481_; uint8_t v___y_1522_; uint8_t v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; uint8_t v___y_1531_; lean_object* v_a_1532_; uint8_t v___y_1542_; lean_object* v___y_1543_; uint8_t v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; uint8_t v___y_1551_; lean_object* v_a_1552_; uint8_t v___y_1565_; lean_object* v___y_1566_; uint8_t v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; uint8_t v___y_1573_; lean_object* v___y_1574_; lean_object* v_a_1575_; uint8_t v___y_1585_; uint8_t v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; uint8_t v___y_1593_; lean_object* v___y_1594_; lean_object* v_a_1595_; uint8_t v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; uint8_t v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; uint8_t v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; uint8_t v___y_1619_; uint8_t v___y_1660_; uint8_t v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; uint8_t v___y_1669_; lean_object* v_a_1670_; uint8_t v___y_1683_; uint8_t v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; uint8_t v___y_1691_; lean_object* v___y_1692_; lean_object* v_a_1693_; lean_object* v___y_1703_; uint8_t v___y_1704_; uint8_t v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; uint8_t v___y_1711_; lean_object* v___y_1712_; lean_object* v_a_1713_; lean_object* v___y_1726_; uint8_t v___y_1727_; uint8_t v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; uint8_t v___y_1735_; lean_object* v_a_1736_; uint8_t v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; uint8_t v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; uint8_t v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; uint8_t v___y_1756_; lean_object* v___y_1757_; uint8_t v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; uint8_t v___y_1803_; lean_object* v_a_1804_; uint8_t v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; uint8_t v___y_1822_; lean_object* v_a_1823_; lean_object* v___y_1833_; uint8_t v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; uint8_t v___y_1839_; lean_object* v_one_1880_; lean_object* v_n_1881_; uint8_t v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; uint8_t v___y_1887_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; uint8_t v___y_1935_; uint8_t v___y_1936_; lean_object* v___y_1937_; uint8_t v___y_1938_; uint8_t v___y_1962_; uint8_t v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; uint8_t v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; uint8_t v___y_1971_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; uint8_t v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; uint8_t v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; uint8_t v___y_2025_; uint8_t v___y_2046_; uint8_t v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2052_; uint8_t v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; uint8_t v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; uint8_t v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; uint8_t v___y_2107_; lean_object* v___y_2108_; uint8_t v___y_2109_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; uint8_t v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; uint8_t v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; uint8_t v___y_2187_; lean_object* v_a_2205_; lean_object* v___y_2296_; lean_object* v___x_2306_; 
v_proc_1165_ = lean_ctor_get(v_cfg_965_, 1);
v_suspend_1166_ = lean_ctor_get(v_cfg_965_, 2);
v_discharge_1167_ = lean_ctor_get(v_cfg_965_, 3);
v___f_1168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1880_ = lean_unsigned_to_nat(1u);
v_n_1881_ = lean_nat_sub(v_n_969_, v_one_1880_);
lean_dec(v_n_969_);
lean_inc_ref(v_proc_1165_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_curr_970_);
lean_inc(v_goals_968_);
v___x_2306_ = lean_apply_7(v_proc_1165_, v_goals_968_, v_curr_970_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
v_a_2205_ = v_a_2307_;
goto v___jp_2204_;
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2375_; 
v_a_2308_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2310_ = v___x_2306_;
v_isShared_2311_ = v_isSharedCheck_2375_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2306_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2375_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___f_2312_; lean_object* v___y_2314_; uint8_t v___y_2315_; lean_object* v___y_2316_; uint8_t v___y_2317_; uint8_t v___y_2354_; uint8_t v___x_2373_; 
lean_inc(v_a_2308_);
v___f_2312_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(v___f_2312_, 0, v_a_2308_);
v___x_2373_ = l_Lean_Exception_isInterrupt(v_a_2308_);
if (v___x_2373_ == 0)
{
uint8_t v___x_2374_; 
lean_inc(v_a_2308_);
v___x_2374_ = l_Lean_Exception_isRuntime(v_a_2308_);
v___y_2354_ = v___x_2374_;
goto v___jp_2353_;
}
else
{
v___y_2354_ = v___x_2373_;
goto v___jp_2353_;
}
v___jp_2313_:
{
lean_object* v___x_2318_; lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2352_; 
v___x_2318_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2352_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2352_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2323_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2324_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2314_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2328_; 
v___x_2325_ = lean_io_mono_nanos_now();
v___x_2326_ = lean_io_mono_nanos_now();
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v_a_2308_);
v___x_2328_ = v___x_2321_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2308_);
v___x_2328_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
double v___x_2329_; double v___x_2330_; double v___x_2331_; double v___x_2332_; double v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2329_ = lean_float_of_nat(v___x_2325_);
v___x_2330_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2331_ = lean_float_div(v___x_2329_, v___x_2330_);
v___x_2332_ = lean_float_of_nat(v___x_2326_);
v___x_2333_ = lean_float_div(v___x_2332_, v___x_2330_);
v___x_2334_ = lean_box_float(v___x_2331_);
v___x_2335_ = lean_box_float(v___x_2333_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2328_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
lean_inc_ref(v___y_2316_);
lean_inc(v_trace_966_);
v___x_2338_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_966_, v___y_2315_, v___y_2316_, v___y_2314_, v___y_2317_, v_a_2319_, v___f_2312_, v___x_2337_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_2296_ = v___x_2338_;
goto v___jp_2295_;
}
}
else
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2340_ = lean_io_get_num_heartbeats();
v___x_2341_ = lean_io_get_num_heartbeats();
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v_a_2308_);
v___x_2343_ = v___x_2321_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2308_);
v___x_2343_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
double v___x_2344_; double v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2344_ = lean_float_of_nat(v___x_2340_);
v___x_2345_ = lean_float_of_nat(v___x_2341_);
v___x_2346_ = lean_box_float(v___x_2344_);
v___x_2347_ = lean_box_float(v___x_2345_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2343_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
lean_inc_ref(v___y_2316_);
lean_inc(v_trace_966_);
v___x_2350_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_966_, v___y_2315_, v___y_2316_, v___y_2314_, v___y_2317_, v_a_2319_, v___f_2312_, v___x_2349_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_2296_ = v___x_2350_;
goto v___jp_2295_;
}
}
}
}
v___jp_2353_:
{
if (v___y_2354_ == 0)
{
lean_object* v_options_2355_; uint8_t v_hasTrace_2356_; 
v_options_2355_ = lean_ctor_get(v_a_974_, 2);
v_hasTrace_2356_ = lean_ctor_get_uint8(v_options_2355_, sizeof(void*)*1);
if (v_hasTrace_2356_ == 0)
{
lean_object* v___x_2358_; 
lean_dec_ref(v___f_2312_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_curr_970_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
if (v_isShared_2311_ == 0)
{
v___x_2358_ = v___x_2310_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2308_);
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
v_inheritedTraceOptions_2360_ = lean_ctor_get(v_a_974_, 13);
v___x_2361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_966_);
v___x_2363_ = l_Lean_Name_append(v___x_2362_, v_trace_966_);
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
lean_dec_ref(v___f_2312_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_curr_970_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
if (v_isShared_2311_ == 0)
{
v___x_2368_ = v___x_2310_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2308_);
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
lean_del_object(v___x_2310_);
v___y_2314_ = v_options_2355_;
v___y_2315_ = v_hasTrace_2356_;
v___y_2316_ = v___x_2361_;
v___y_2317_ = v___x_2364_;
goto v___jp_2313_;
}
}
else
{
lean_del_object(v___x_2310_);
v___y_2314_ = v_options_2355_;
v___y_2315_ = v_hasTrace_2356_;
v___y_2316_ = v___x_2361_;
v___y_2317_ = v___x_2364_;
goto v___jp_2313_;
}
}
}
else
{
lean_object* v___x_2371_; 
lean_dec_ref(v___f_2312_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_curr_970_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
if (v_isShared_2311_ == 0)
{
v___x_2371_ = v___x_2310_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2308_);
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
v___jp_1169_:
{
lean_object* v___x_1175_; lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1209_; 
v___x_1175_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1209_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1209_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1181_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1171_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1182_ = lean_io_mono_nanos_now();
v___x_1183_ = lean_io_mono_nanos_now();
if (v_isShared_1179_ == 0)
{
lean_ctor_set_tag(v___x_1178_, 1);
lean_ctor_set(v___x_1178_, 0, v___y_1173_);
v___x_1185_ = v___x_1178_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___y_1173_);
v___x_1185_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
double v___x_1186_; double v___x_1187_; double v___x_1188_; double v___x_1189_; double v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1186_ = lean_float_of_nat(v___x_1182_);
v___x_1187_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1188_ = lean_float_div(v___x_1186_, v___x_1187_);
v___x_1189_ = lean_float_of_nat(v___x_1183_);
v___x_1190_ = lean_float_div(v___x_1189_, v___x_1187_);
v___x_1191_ = lean_box_float(v___x_1188_);
v___x_1192_ = lean_box_float(v___x_1190_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1185_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
lean_inc_ref(v___y_1174_);
v___x_1195_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1170_, v___y_1174_, v___y_1171_, v___y_1172_, v_a_1176_, v___f_1168_, v___x_1194_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1195_;
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1197_ = lean_io_get_num_heartbeats();
v___x_1198_ = lean_io_get_num_heartbeats();
if (v_isShared_1179_ == 0)
{
lean_ctor_set_tag(v___x_1178_, 1);
lean_ctor_set(v___x_1178_, 0, v___y_1173_);
v___x_1200_ = v___x_1178_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___y_1173_);
v___x_1200_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
double v___x_1201_; double v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1201_ = lean_float_of_nat(v___x_1197_);
v___x_1202_ = lean_float_of_nat(v___x_1198_);
v___x_1203_ = lean_box_float(v___x_1201_);
v___x_1204_ = lean_box_float(v___x_1202_);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1200_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
lean_inc_ref(v___y_1174_);
v___x_1207_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1170_, v___y_1174_, v___y_1171_, v___y_1172_, v_a_1176_, v___f_1168_, v___x_1206_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1207_;
}
}
}
}
v___jp_1211_:
{
lean_object* v___x_1219_; double v___x_1220_; double v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1219_ = lean_io_get_num_heartbeats();
v___x_1220_ = lean_float_of_nat(v___y_1217_);
v___x_1221_ = lean_float_of_nat(v___x_1219_);
v___x_1222_ = lean_box_float(v___x_1220_);
v___x_1223_ = lean_box_float(v___x_1221_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1222_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v_a_1218_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
lean_inc_ref(v___y_1214_);
v___x_1226_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1216_, v___y_1214_, v___y_1212_, v___y_1215_, v___y_1213_, v___f_1210_, v___x_1225_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1226_;
}
v___jp_1227_:
{
lean_object* v___x_1235_; double v___x_1236_; double v___x_1237_; double v___x_1238_; double v___x_1239_; double v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1235_ = lean_io_mono_nanos_now();
v___x_1236_ = lean_float_of_nat(v___y_1232_);
v___x_1237_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1238_ = lean_float_div(v___x_1236_, v___x_1237_);
v___x_1239_ = lean_float_of_nat(v___x_1235_);
v___x_1240_ = lean_float_div(v___x_1239_, v___x_1237_);
v___x_1241_ = lean_box_float(v___x_1238_);
v___x_1242_ = lean_box_float(v___x_1240_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_a_1234_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
lean_inc_ref(v___y_1230_);
v___x_1245_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1233_, v___y_1230_, v___y_1228_, v___y_1231_, v___y_1229_, v___f_1210_, v___x_1244_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1245_;
}
v___jp_1246_:
{
lean_object* v___x_1254_; lean_object* v_a_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1254_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref(v___x_1254_);
v___x_1256_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1257_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1247_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1259_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1252_, v___y_1250_, v___y_1251_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1259_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1259_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set_tag(v___x_1262_, 1);
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
v___y_1228_ = v___y_1247_;
v___y_1229_ = v_a_1255_;
v___y_1230_ = v___y_1248_;
v___y_1231_ = v___y_1249_;
v___y_1232_ = v___x_1258_;
v___y_1233_ = v___y_1253_;
v_a_1234_ = v___x_1265_;
goto v___jp_1227_;
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
v_a_1268_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1259_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1259_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 0);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
v___y_1228_ = v___y_1247_;
v___y_1229_ = v_a_1255_;
v___y_1230_ = v___y_1248_;
v___y_1231_ = v___y_1249_;
v___y_1232_ = v___x_1258_;
v___y_1233_ = v___y_1253_;
v_a_1234_ = v___x_1273_;
goto v___jp_1227_;
}
}
}
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1277_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1252_, v___y_1250_, v___y_1251_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set_tag(v___x_1280_, 1);
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
v___y_1212_ = v___y_1247_;
v___y_1213_ = v_a_1255_;
v___y_1214_ = v___y_1248_;
v___y_1215_ = v___y_1249_;
v___y_1216_ = v___y_1253_;
v___y_1217_ = v___x_1276_;
v_a_1218_ = v___x_1283_;
goto v___jp_1211_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1277_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1277_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set_tag(v___x_1288_, 0);
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
v___y_1212_ = v___y_1247_;
v___y_1213_ = v_a_1255_;
v___y_1214_ = v___y_1248_;
v___y_1215_ = v___y_1249_;
v___y_1216_ = v___y_1253_;
v___y_1217_ = v___x_1276_;
v_a_1218_ = v___x_1291_;
goto v___jp_1211_;
}
}
}
}
}
v___jp_1295_:
{
lean_object* v___x_1303_; double v___x_1304_; double v___x_1305_; double v___x_1306_; double v___x_1307_; double v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1303_ = lean_io_mono_nanos_now();
v___x_1304_ = lean_float_of_nat(v___y_1297_);
v___x_1305_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1306_ = lean_float_div(v___x_1304_, v___x_1305_);
v___x_1307_ = lean_float_of_nat(v___x_1303_);
v___x_1308_ = lean_float_div(v___x_1307_, v___x_1305_);
v___x_1309_ = lean_box_float(v___x_1306_);
v___x_1310_ = lean_box_float(v___x_1308_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1309_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v_a_1302_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
lean_inc_ref(v___y_1299_);
v___x_1313_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1301_, v___y_1299_, v___y_1298_, v___y_1296_, v___y_1300_, v___f_1294_, v___x_1312_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1313_;
}
v___jp_1314_:
{
lean_object* v___x_1322_; double v___x_1323_; double v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1322_ = lean_io_get_num_heartbeats();
v___x_1323_ = lean_float_of_nat(v___y_1320_);
v___x_1324_ = lean_float_of_nat(v___x_1322_);
v___x_1325_ = lean_box_float(v___x_1323_);
v___x_1326_ = lean_box_float(v___x_1324_);
v___x_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v_a_1321_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
lean_inc_ref(v___y_1317_);
v___x_1329_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1319_, v___y_1317_, v___y_1316_, v___y_1315_, v___y_1318_, v___f_1294_, v___x_1328_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1329_;
}
v___jp_1331_:
{
lean_object* v___x_1343_; double v___x_1344_; double v___x_1345_; double v___x_1346_; double v___x_1347_; double v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1343_ = lean_io_mono_nanos_now();
v___x_1344_ = lean_float_of_nat(v___y_1336_);
v___x_1345_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1346_ = lean_float_div(v___x_1344_, v___x_1345_);
v___x_1347_ = lean_float_of_nat(v___x_1343_);
v___x_1348_ = lean_float_div(v___x_1347_, v___x_1345_);
v___x_1349_ = lean_box_float(v___x_1346_);
v___x_1350_ = lean_box_float(v___x_1348_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1349_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_a_1342_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
lean_inc_ref(v___y_1337_);
lean_inc(v_trace_966_);
v___x_1353_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1341_, v___y_1337_, v___y_1334_, v___y_1339_, v___y_1333_, v___f_1330_, v___x_1352_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1100_ = v___y_1332_;
v___y_1101_ = v___y_1334_;
v___y_1102_ = v___y_1335_;
v___y_1103_ = v___y_1337_;
v___y_1104_ = v___y_1338_;
v___y_1105_ = v___y_1340_;
v___y_1106_ = v___y_1341_;
v___y_1107_ = v___x_1353_;
goto v___jp_1099_;
}
v___jp_1354_:
{
lean_object* v___x_1366_; double v___x_1367_; double v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1366_ = lean_io_get_num_heartbeats();
v___x_1367_ = lean_float_of_nat(v___y_1355_);
v___x_1368_ = lean_float_of_nat(v___x_1366_);
v___x_1369_ = lean_box_float(v___x_1367_);
v___x_1370_ = lean_box_float(v___x_1368_);
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v_a_1365_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
lean_inc_ref(v___y_1360_);
lean_inc(v_trace_966_);
v___x_1373_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1364_, v___y_1360_, v___y_1358_, v___y_1362_, v___y_1357_, v___f_1330_, v___x_1372_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1100_ = v___y_1356_;
v___y_1101_ = v___y_1358_;
v___y_1102_ = v___y_1359_;
v___y_1103_ = v___y_1360_;
v___y_1104_ = v___y_1361_;
v___y_1105_ = v___y_1363_;
v___y_1106_ = v___y_1364_;
v___y_1107_ = v___x_1373_;
goto v___jp_1099_;
}
v___jp_1374_:
{
lean_object* v___x_1387_; 
v___x_1387_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_1382_ == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref(v___x_1387_);
v___x_1389_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1390_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1386_, v___y_1383_, v___y_1379_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 1);
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
v___y_1332_ = v___y_1377_;
v___y_1333_ = v_a_1388_;
v___y_1334_ = v___y_1375_;
v___y_1335_ = v___y_1378_;
v___y_1336_ = v___x_1389_;
v___y_1337_ = v___y_1380_;
v___y_1338_ = v___y_1381_;
v___y_1339_ = v___y_1376_;
v___y_1340_ = v___y_1384_;
v___y_1341_ = v___y_1385_;
v_a_1342_ = v___x_1396_;
goto v___jp_1331_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
v_a_1399_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1390_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1390_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 0);
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
v___y_1332_ = v___y_1377_;
v___y_1333_ = v_a_1388_;
v___y_1334_ = v___y_1375_;
v___y_1335_ = v___y_1378_;
v___y_1336_ = v___x_1389_;
v___y_1337_ = v___y_1380_;
v___y_1338_ = v___y_1381_;
v___y_1339_ = v___y_1376_;
v___y_1340_ = v___y_1384_;
v___y_1341_ = v___y_1385_;
v_a_1342_ = v___x_1404_;
goto v___jp_1331_;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_a_1407_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1387_);
v___x_1408_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1409_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1386_, v___y_1383_, v___y_1379_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 1);
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
v___y_1355_ = v___x_1408_;
v___y_1356_ = v___y_1377_;
v___y_1357_ = v_a_1407_;
v___y_1358_ = v___y_1375_;
v___y_1359_ = v___y_1378_;
v___y_1360_ = v___y_1380_;
v___y_1361_ = v___y_1381_;
v___y_1362_ = v___y_1376_;
v___y_1363_ = v___y_1384_;
v___y_1364_ = v___y_1385_;
v_a_1365_ = v___x_1415_;
goto v___jp_1354_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
v_a_1418_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1409_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1409_);
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
v___y_1355_ = v___x_1408_;
v___y_1356_ = v___y_1377_;
v___y_1357_ = v_a_1407_;
v___y_1358_ = v___y_1375_;
v___y_1359_ = v___y_1378_;
v___y_1360_ = v___y_1380_;
v___y_1361_ = v___y_1381_;
v___y_1362_ = v___y_1376_;
v___y_1363_ = v___y_1384_;
v___y_1364_ = v___y_1385_;
v_a_1365_ = v___x_1423_;
goto v___jp_1354_;
}
}
}
}
}
v___jp_1426_:
{
lean_object* v___x_1438_; double v___x_1439_; double v___x_1440_; double v___x_1441_; double v___x_1442_; double v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1438_ = lean_io_mono_nanos_now();
v___x_1439_ = lean_float_of_nat(v___y_1431_);
v___x_1440_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1441_ = lean_float_div(v___x_1439_, v___x_1440_);
v___x_1442_ = lean_float_of_nat(v___x_1438_);
v___x_1443_ = lean_float_div(v___x_1442_, v___x_1440_);
v___x_1444_ = lean_box_float(v___x_1441_);
v___x_1445_ = lean_box_float(v___x_1443_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v_a_1437_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
lean_inc_ref(v___y_1430_);
lean_inc(v_trace_966_);
v___x_1448_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1436_, v___y_1430_, v___y_1429_, v___y_1433_, v___y_1428_, v___f_1210_, v___x_1447_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1151_ = v___y_1427_;
v___y_1152_ = v___y_1429_;
v___y_1153_ = v___y_1430_;
v___y_1154_ = v___y_1432_;
v___y_1155_ = v___y_1434_;
v___y_1156_ = v___y_1436_;
v___y_1157_ = v___y_1435_;
v___y_1158_ = v___x_1448_;
goto v___jp_1150_;
}
v___jp_1449_:
{
lean_object* v___x_1461_; double v___x_1462_; double v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1461_ = lean_io_get_num_heartbeats();
v___x_1462_ = lean_float_of_nat(v___y_1453_);
v___x_1463_ = lean_float_of_nat(v___x_1461_);
v___x_1464_ = lean_box_float(v___x_1462_);
v___x_1465_ = lean_box_float(v___x_1463_);
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1467_, 0, v_a_1460_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
lean_inc_ref(v___y_1454_);
lean_inc(v_trace_966_);
v___x_1468_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1459_, v___y_1454_, v___y_1452_, v___y_1456_, v___y_1451_, v___f_1210_, v___x_1467_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1151_ = v___y_1450_;
v___y_1152_ = v___y_1452_;
v___y_1153_ = v___y_1454_;
v___y_1154_ = v___y_1455_;
v___y_1155_ = v___y_1457_;
v___y_1156_ = v___y_1459_;
v___y_1157_ = v___y_1458_;
v___y_1158_ = v___x_1468_;
goto v___jp_1150_;
}
v___jp_1469_:
{
lean_object* v___x_1482_; 
v___x_1482_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_1477_ == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref(v___x_1482_);
v___x_1484_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1485_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1473_, v___y_1478_, v___y_1476_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set_tag(v___x_1488_, 1);
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
v___y_1427_ = v___y_1471_;
v___y_1428_ = v_a_1483_;
v___y_1429_ = v___y_1470_;
v___y_1430_ = v___y_1472_;
v___y_1431_ = v___x_1484_;
v___y_1432_ = v___y_1474_;
v___y_1433_ = v___y_1475_;
v___y_1434_ = v___y_1479_;
v___y_1435_ = v___y_1480_;
v___y_1436_ = v___y_1481_;
v_a_1437_ = v___x_1491_;
goto v___jp_1426_;
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
v_a_1494_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1485_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1485_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 0);
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
v___y_1427_ = v___y_1471_;
v___y_1428_ = v_a_1483_;
v___y_1429_ = v___y_1470_;
v___y_1430_ = v___y_1472_;
v___y_1431_ = v___x_1484_;
v___y_1432_ = v___y_1474_;
v___y_1433_ = v___y_1475_;
v___y_1434_ = v___y_1479_;
v___y_1435_ = v___y_1480_;
v___y_1436_ = v___y_1481_;
v_a_1437_ = v___x_1499_;
goto v___jp_1426_;
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_a_1502_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1502_);
lean_dec_ref(v___x_1482_);
v___x_1503_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1504_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1473_, v___y_1478_, v___y_1476_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set_tag(v___x_1507_, 1);
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
v___y_1450_ = v___y_1471_;
v___y_1451_ = v_a_1502_;
v___y_1452_ = v___y_1470_;
v___y_1453_ = v___x_1503_;
v___y_1454_ = v___y_1472_;
v___y_1455_ = v___y_1474_;
v___y_1456_ = v___y_1475_;
v___y_1457_ = v___y_1479_;
v___y_1458_ = v___y_1480_;
v___y_1459_ = v___y_1481_;
v_a_1460_ = v___x_1510_;
goto v___jp_1449_;
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
v_a_1513_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1504_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1504_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set_tag(v___x_1515_, 0);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
v___y_1450_ = v___y_1471_;
v___y_1451_ = v_a_1502_;
v___y_1452_ = v___y_1470_;
v___y_1453_ = v___x_1503_;
v___y_1454_ = v___y_1472_;
v___y_1455_ = v___y_1474_;
v___y_1456_ = v___y_1475_;
v___y_1457_ = v___y_1479_;
v___y_1458_ = v___y_1480_;
v___y_1459_ = v___y_1481_;
v_a_1460_ = v___x_1518_;
goto v___jp_1449_;
}
}
}
}
}
v___jp_1521_:
{
lean_object* v___x_1533_; double v___x_1534_; double v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1533_ = lean_io_get_num_heartbeats();
v___x_1534_ = lean_float_of_nat(v___y_1528_);
v___x_1535_ = lean_float_of_nat(v___x_1533_);
v___x_1536_ = lean_box_float(v___x_1534_);
v___x_1537_ = lean_box_float(v___x_1535_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_a_1532_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
lean_inc_ref(v___y_1525_);
lean_inc(v_trace_966_);
v___x_1540_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1531_, v___y_1525_, v___y_1524_, v___y_1522_, v___y_1527_, v___f_1294_, v___x_1539_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1151_ = v___y_1523_;
v___y_1152_ = v___y_1524_;
v___y_1153_ = v___y_1525_;
v___y_1154_ = v___y_1526_;
v___y_1155_ = v___y_1529_;
v___y_1156_ = v___y_1531_;
v___y_1157_ = v___y_1530_;
v___y_1158_ = v___x_1540_;
goto v___jp_1150_;
}
v___jp_1541_:
{
lean_object* v___x_1553_; double v___x_1554_; double v___x_1555_; double v___x_1556_; double v___x_1557_; double v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1553_ = lean_io_mono_nanos_now();
v___x_1554_ = lean_float_of_nat(v___y_1543_);
v___x_1555_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1556_ = lean_float_div(v___x_1554_, v___x_1555_);
v___x_1557_ = lean_float_of_nat(v___x_1553_);
v___x_1558_ = lean_float_div(v___x_1557_, v___x_1555_);
v___x_1559_ = lean_box_float(v___x_1556_);
v___x_1560_ = lean_box_float(v___x_1558_);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_a_1552_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
lean_inc_ref(v___y_1546_);
lean_inc(v_trace_966_);
v___x_1563_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1551_, v___y_1546_, v___y_1545_, v___y_1542_, v___y_1548_, v___f_1294_, v___x_1562_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1151_ = v___y_1544_;
v___y_1152_ = v___y_1545_;
v___y_1153_ = v___y_1546_;
v___y_1154_ = v___y_1547_;
v___y_1155_ = v___y_1549_;
v___y_1156_ = v___y_1551_;
v___y_1157_ = v___y_1550_;
v___y_1158_ = v___x_1563_;
goto v___jp_1150_;
}
v___jp_1564_:
{
lean_object* v___x_1576_; double v___x_1577_; double v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1576_ = lean_io_get_num_heartbeats();
v___x_1577_ = lean_float_of_nat(v___y_1566_);
v___x_1578_ = lean_float_of_nat(v___x_1576_);
v___x_1579_ = lean_box_float(v___x_1577_);
v___x_1580_ = lean_box_float(v___x_1578_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1582_, 0, v_a_1575_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
lean_inc_ref(v___y_1569_);
lean_inc(v_trace_966_);
v___x_1583_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1573_, v___y_1569_, v___y_1568_, v___y_1565_, v___y_1574_, v___f_1330_, v___x_1582_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1151_ = v___y_1567_;
v___y_1152_ = v___y_1568_;
v___y_1153_ = v___y_1569_;
v___y_1154_ = v___y_1570_;
v___y_1155_ = v___y_1571_;
v___y_1156_ = v___y_1573_;
v___y_1157_ = v___y_1572_;
v___y_1158_ = v___x_1583_;
goto v___jp_1150_;
}
v___jp_1584_:
{
lean_object* v___x_1596_; double v___x_1597_; double v___x_1598_; double v___x_1599_; double v___x_1600_; double v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1596_ = lean_io_mono_nanos_now();
v___x_1597_ = lean_float_of_nat(v___y_1588_);
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
lean_inc_ref(v___y_1589_);
lean_inc(v_trace_966_);
v___x_1606_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1593_, v___y_1589_, v___y_1587_, v___y_1585_, v___y_1594_, v___f_1330_, v___x_1605_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1151_ = v___y_1586_;
v___y_1152_ = v___y_1587_;
v___y_1153_ = v___y_1589_;
v___y_1154_ = v___y_1590_;
v___y_1155_ = v___y_1591_;
v___y_1156_ = v___y_1593_;
v___y_1157_ = v___y_1592_;
v___y_1158_ = v___x_1606_;
goto v___jp_1150_;
}
v___jp_1607_:
{
lean_object* v___x_1620_; 
v___x_1620_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_1615_ == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1623_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1610_, v___y_1616_, v___y_1613_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1623_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set_tag(v___x_1626_, 1);
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
v___y_1585_ = v___y_1608_;
v___y_1586_ = v___y_1611_;
v___y_1587_ = v___y_1609_;
v___y_1588_ = v___x_1622_;
v___y_1589_ = v___y_1612_;
v___y_1590_ = v___y_1614_;
v___y_1591_ = v___y_1617_;
v___y_1592_ = v___y_1618_;
v___y_1593_ = v___y_1619_;
v___y_1594_ = v_a_1621_;
v_a_1595_ = v___x_1629_;
goto v___jp_1584_;
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_a_1632_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1623_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1623_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set_tag(v___x_1634_, 0);
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
v___y_1585_ = v___y_1608_;
v___y_1586_ = v___y_1611_;
v___y_1587_ = v___y_1609_;
v___y_1588_ = v___x_1622_;
v___y_1589_ = v___y_1612_;
v___y_1590_ = v___y_1614_;
v___y_1591_ = v___y_1617_;
v___y_1592_ = v___y_1618_;
v___y_1593_ = v___y_1619_;
v___y_1594_ = v_a_1621_;
v_a_1595_ = v___x_1637_;
goto v___jp_1584_;
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_a_1640_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1620_);
v___x_1641_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1642_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1610_, v___y_1616_, v___y_1613_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 1);
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
v___y_1565_ = v___y_1608_;
v___y_1566_ = v___x_1641_;
v___y_1567_ = v___y_1611_;
v___y_1568_ = v___y_1609_;
v___y_1569_ = v___y_1612_;
v___y_1570_ = v___y_1614_;
v___y_1571_ = v___y_1617_;
v___y_1572_ = v___y_1618_;
v___y_1573_ = v___y_1619_;
v___y_1574_ = v_a_1640_;
v_a_1575_ = v___x_1648_;
goto v___jp_1564_;
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1642_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1642_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set_tag(v___x_1653_, 0);
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
v___y_1565_ = v___y_1608_;
v___y_1566_ = v___x_1641_;
v___y_1567_ = v___y_1611_;
v___y_1568_ = v___y_1609_;
v___y_1569_ = v___y_1612_;
v___y_1570_ = v___y_1614_;
v___y_1571_ = v___y_1617_;
v___y_1572_ = v___y_1618_;
v___y_1573_ = v___y_1619_;
v___y_1574_ = v_a_1640_;
v_a_1575_ = v___x_1656_;
goto v___jp_1564_;
}
}
}
}
}
v___jp_1659_:
{
lean_object* v___x_1671_; double v___x_1672_; double v___x_1673_; double v___x_1674_; double v___x_1675_; double v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1671_ = lean_io_mono_nanos_now();
v___x_1672_ = lean_float_of_nat(v___y_1664_);
v___x_1673_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1674_ = lean_float_div(v___x_1672_, v___x_1673_);
v___x_1675_ = lean_float_of_nat(v___x_1671_);
v___x_1676_ = lean_float_div(v___x_1675_, v___x_1673_);
v___x_1677_ = lean_box_float(v___x_1674_);
v___x_1678_ = lean_box_float(v___x_1676_);
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v_a_1670_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
lean_inc_ref(v___y_1665_);
lean_inc(v_trace_966_);
v___x_1681_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1669_, v___y_1665_, v___y_1662_, v___y_1661_, v___y_1667_, v___f_1294_, v___x_1680_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1100_ = v___y_1660_;
v___y_1101_ = v___y_1662_;
v___y_1102_ = v___y_1663_;
v___y_1103_ = v___y_1665_;
v___y_1104_ = v___y_1666_;
v___y_1105_ = v___y_1668_;
v___y_1106_ = v___y_1669_;
v___y_1107_ = v___x_1681_;
goto v___jp_1099_;
}
v___jp_1682_:
{
lean_object* v___x_1694_; double v___x_1695_; double v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1694_ = lean_io_get_num_heartbeats();
v___x_1695_ = lean_float_of_nat(v___y_1692_);
v___x_1696_ = lean_float_of_nat(v___x_1694_);
v___x_1697_ = lean_box_float(v___x_1695_);
v___x_1698_ = lean_box_float(v___x_1696_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_a_1693_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
lean_inc_ref(v___y_1687_);
lean_inc(v_trace_966_);
v___x_1701_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1691_, v___y_1687_, v___y_1685_, v___y_1684_, v___y_1689_, v___f_1294_, v___x_1700_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1100_ = v___y_1683_;
v___y_1101_ = v___y_1685_;
v___y_1102_ = v___y_1686_;
v___y_1103_ = v___y_1687_;
v___y_1104_ = v___y_1688_;
v___y_1105_ = v___y_1690_;
v___y_1106_ = v___y_1691_;
v___y_1107_ = v___x_1701_;
goto v___jp_1099_;
}
v___jp_1702_:
{
lean_object* v___x_1714_; double v___x_1715_; double v___x_1716_; double v___x_1717_; double v___x_1718_; double v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1714_ = lean_io_mono_nanos_now();
v___x_1715_ = lean_float_of_nat(v___y_1712_);
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
lean_inc_ref(v___y_1708_);
lean_inc(v_trace_966_);
v___x_1724_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1711_, v___y_1708_, v___y_1706_, v___y_1704_, v___y_1703_, v___f_1210_, v___x_1723_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1100_ = v___y_1705_;
v___y_1101_ = v___y_1706_;
v___y_1102_ = v___y_1707_;
v___y_1103_ = v___y_1708_;
v___y_1104_ = v___y_1709_;
v___y_1105_ = v___y_1710_;
v___y_1106_ = v___y_1711_;
v___y_1107_ = v___x_1724_;
goto v___jp_1099_;
}
v___jp_1725_:
{
lean_object* v___x_1737_; double v___x_1738_; double v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1737_ = lean_io_get_num_heartbeats();
v___x_1738_ = lean_float_of_nat(v___y_1732_);
v___x_1739_ = lean_float_of_nat(v___x_1737_);
v___x_1740_ = lean_box_float(v___x_1738_);
v___x_1741_ = lean_box_float(v___x_1739_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_a_1736_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
lean_inc_ref(v___y_1731_);
lean_inc(v_trace_966_);
v___x_1744_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1735_, v___y_1731_, v___y_1729_, v___y_1727_, v___y_1726_, v___f_1210_, v___x_1743_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1100_ = v___y_1728_;
v___y_1101_ = v___y_1729_;
v___y_1102_ = v___y_1730_;
v___y_1103_ = v___y_1731_;
v___y_1104_ = v___y_1733_;
v___y_1105_ = v___y_1734_;
v___y_1106_ = v___y_1735_;
v___y_1107_ = v___x_1744_;
goto v___jp_1099_;
}
v___jp_1745_:
{
lean_object* v___x_1758_; 
v___x_1758_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_1753_ == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref(v___x_1758_);
v___x_1760_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1761_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1748_, v___y_1754_, v___y_1757_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 1);
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
v___y_1703_ = v_a_1759_;
v___y_1704_ = v___y_1746_;
v___y_1705_ = v___y_1749_;
v___y_1706_ = v___y_1747_;
v___y_1707_ = v___y_1750_;
v___y_1708_ = v___y_1751_;
v___y_1709_ = v___y_1752_;
v___y_1710_ = v___y_1755_;
v___y_1711_ = v___y_1756_;
v___y_1712_ = v___x_1760_;
v_a_1713_ = v___x_1767_;
goto v___jp_1702_;
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1761_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1761_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 0);
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
v___y_1703_ = v_a_1759_;
v___y_1704_ = v___y_1746_;
v___y_1705_ = v___y_1749_;
v___y_1706_ = v___y_1747_;
v___y_1707_ = v___y_1750_;
v___y_1708_ = v___y_1751_;
v___y_1709_ = v___y_1752_;
v___y_1710_ = v___y_1755_;
v___y_1711_ = v___y_1756_;
v___y_1712_ = v___x_1760_;
v_a_1713_ = v___x_1775_;
goto v___jp_1702_;
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v_a_1778_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1778_);
lean_dec_ref(v___x_1758_);
v___x_1779_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1780_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1748_, v___y_1754_, v___y_1757_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set_tag(v___x_1783_, 1);
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
v___y_1726_ = v_a_1778_;
v___y_1727_ = v___y_1746_;
v___y_1728_ = v___y_1749_;
v___y_1729_ = v___y_1747_;
v___y_1730_ = v___y_1750_;
v___y_1731_ = v___y_1751_;
v___y_1732_ = v___x_1779_;
v___y_1733_ = v___y_1752_;
v___y_1734_ = v___y_1755_;
v___y_1735_ = v___y_1756_;
v_a_1736_ = v___x_1786_;
goto v___jp_1725_;
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
v_a_1789_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1780_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1780_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set_tag(v___x_1791_, 0);
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
v___y_1726_ = v_a_1778_;
v___y_1727_ = v___y_1746_;
v___y_1728_ = v___y_1749_;
v___y_1729_ = v___y_1747_;
v___y_1730_ = v___y_1750_;
v___y_1731_ = v___y_1751_;
v___y_1732_ = v___x_1779_;
v___y_1733_ = v___y_1752_;
v___y_1734_ = v___y_1755_;
v___y_1735_ = v___y_1756_;
v_a_1736_ = v___x_1794_;
goto v___jp_1725_;
}
}
}
}
}
v___jp_1797_:
{
lean_object* v___x_1805_; double v___x_1806_; double v___x_1807_; double v___x_1808_; double v___x_1809_; double v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1805_ = lean_io_mono_nanos_now();
v___x_1806_ = lean_float_of_nat(v___y_1800_);
v___x_1807_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1808_ = lean_float_div(v___x_1806_, v___x_1807_);
v___x_1809_ = lean_float_of_nat(v___x_1805_);
v___x_1810_ = lean_float_div(v___x_1809_, v___x_1807_);
v___x_1811_ = lean_box_float(v___x_1808_);
v___x_1812_ = lean_box_float(v___x_1810_);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_a_1804_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
lean_inc_ref(v___y_1801_);
v___x_1815_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1803_, v___y_1801_, v___y_1799_, v___y_1798_, v___y_1802_, v___f_1330_, v___x_1814_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1815_;
}
v___jp_1816_:
{
lean_object* v___x_1824_; double v___x_1825_; double v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1824_ = lean_io_get_num_heartbeats();
v___x_1825_ = lean_float_of_nat(v___y_1819_);
v___x_1826_ = lean_float_of_nat(v___x_1824_);
v___x_1827_ = lean_box_float(v___x_1825_);
v___x_1828_ = lean_box_float(v___x_1826_);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1827_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v_a_1823_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
lean_inc_ref(v___y_1820_);
v___x_1831_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1822_, v___y_1820_, v___y_1818_, v___y_1817_, v___y_1821_, v___f_1330_, v___x_1830_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1831_;
}
v___jp_1832_:
{
lean_object* v___x_1840_; lean_object* v_a_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1840_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1843_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1835_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1845_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1838_, v___y_1837_, v___y_1833_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 1);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
v___y_1798_ = v___y_1834_;
v___y_1799_ = v___y_1835_;
v___y_1800_ = v___x_1844_;
v___y_1801_ = v___y_1836_;
v___y_1802_ = v_a_1841_;
v___y_1803_ = v___y_1839_;
v_a_1804_ = v___x_1851_;
goto v___jp_1797_;
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_a_1854_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1845_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1845_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set_tag(v___x_1856_, 0);
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
v___y_1798_ = v___y_1834_;
v___y_1799_ = v___y_1835_;
v___y_1800_ = v___x_1844_;
v___y_1801_ = v___y_1836_;
v___y_1802_ = v_a_1841_;
v___y_1803_ = v___y_1839_;
v_a_1804_ = v___x_1859_;
goto v___jp_1797_;
}
}
}
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1863_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1838_, v___y_1837_, v___y_1833_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set_tag(v___x_1866_, 1);
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
v___y_1817_ = v___y_1834_;
v___y_1818_ = v___y_1835_;
v___y_1819_ = v___x_1862_;
v___y_1820_ = v___y_1836_;
v___y_1821_ = v_a_1841_;
v___y_1822_ = v___y_1839_;
v_a_1823_ = v___x_1869_;
goto v___jp_1816_;
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v_a_1872_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1863_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1863_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 0);
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
v___y_1817_ = v___y_1834_;
v___y_1818_ = v___y_1835_;
v___y_1819_ = v___x_1862_;
v___y_1820_ = v___y_1836_;
v___y_1821_ = v_a_1841_;
v___y_1822_ = v___y_1839_;
v_a_1823_ = v___x_1877_;
goto v___jp_1816_;
}
}
}
}
}
v___jp_1882_:
{
lean_object* v___x_1888_; lean_object* v_a_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1888_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1891_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1885_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1893_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_1881_, v___y_1884_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 1);
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
v___y_1296_ = v___y_1883_;
v___y_1297_ = v___x_1892_;
v___y_1298_ = v___y_1885_;
v___y_1299_ = v___y_1886_;
v___y_1300_ = v_a_1889_;
v___y_1301_ = v___y_1887_;
v_a_1302_ = v___x_1899_;
goto v___jp_1295_;
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
v_a_1902_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1893_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1893_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 0);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v___y_1296_ = v___y_1883_;
v___y_1297_ = v___x_1892_;
v___y_1298_ = v___y_1885_;
v___y_1299_ = v___y_1886_;
v___y_1300_ = v_a_1889_;
v___y_1301_ = v___y_1887_;
v_a_1302_ = v___x_1907_;
goto v___jp_1295_;
}
}
}
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1911_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_1881_, v___y_1884_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set_tag(v___x_1914_, 1);
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
v___y_1315_ = v___y_1883_;
v___y_1316_ = v___y_1885_;
v___y_1317_ = v___y_1886_;
v___y_1318_ = v_a_1889_;
v___y_1319_ = v___y_1887_;
v___y_1320_ = v___x_1910_;
v_a_1321_ = v___x_1917_;
goto v___jp_1314_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1911_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1911_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 0);
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
v___y_1315_ = v___y_1883_;
v___y_1316_ = v___y_1885_;
v___y_1317_ = v___y_1886_;
v___y_1318_ = v_a_1889_;
v___y_1319_ = v___y_1887_;
v___y_1320_ = v___x_1910_;
v_a_1321_ = v___x_1925_;
goto v___jp_1314_;
}
}
}
}
}
v___jp_1928_:
{
if (v___y_1938_ == 0)
{
lean_object* v___x_1939_; 
lean_dec_ref(v___y_1931_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_1937_);
v___x_1939_ = lean_apply_6(v___y_1933_, v___y_1937_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
if (lean_obj_tag(v_a_1940_) == 0)
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1941_ = lean_nat_add(v_n_1881_, v_one_1880_);
lean_dec(v_n_1881_);
v___x_1942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___y_1937_);
lean_ctor_set(v___x_1942_, 1, v_acc_971_);
v___x_1943_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_966_);
v___x_1944_ = l_Lean_Name_append(v___x_1943_, v_trace_966_);
v___x_1945_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1929_, v___y_1930_, v___x_1944_);
lean_dec(v___x_1944_);
if (v___x_1945_ == 0)
{
if (v___y_1935_ == 0)
{
v_n_969_ = v___x_1941_;
v_curr_970_ = v___y_1934_;
v_acc_971_ = v___x_1942_;
goto _start;
}
else
{
v___y_1247_ = v___y_1930_;
v___y_1248_ = v___y_1932_;
v___y_1249_ = v___x_1945_;
v___y_1250_ = v___y_1934_;
v___y_1251_ = v___x_1942_;
v___y_1252_ = v___x_1941_;
v___y_1253_ = v___y_1936_;
goto v___jp_1246_;
}
}
else
{
v___y_1247_ = v___y_1930_;
v___y_1248_ = v___y_1932_;
v___y_1249_ = v___x_1945_;
v___y_1250_ = v___y_1934_;
v___y_1251_ = v___x_1942_;
v___y_1252_ = v___x_1941_;
v___y_1253_ = v___y_1936_;
goto v___jp_1246_;
}
}
else
{
lean_object* v_val_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
lean_dec(v___y_1937_);
v_val_1947_ = lean_ctor_get(v_a_1940_, 0);
lean_inc(v_val_1947_);
lean_dec_ref_known(v_a_1940_, 1);
v___x_1948_ = l_List_appendTR___redArg(v_val_1947_, v___y_1934_);
v___x_1949_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_966_);
v___x_1950_ = l_Lean_Name_append(v___x_1949_, v_trace_966_);
v___x_1951_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1929_, v___y_1930_, v___x_1950_);
lean_dec(v___x_1950_);
if (v___x_1951_ == 0)
{
if (v___y_1935_ == 0)
{
v_n_969_ = v_n_1881_;
v_curr_970_ = v___x_1948_;
goto _start;
}
else
{
v___y_1883_ = v___x_1951_;
v___y_1884_ = v___x_1948_;
v___y_1885_ = v___y_1930_;
v___y_1886_ = v___y_1932_;
v___y_1887_ = v___y_1936_;
goto v___jp_1882_;
}
}
else
{
v___y_1883_ = v___x_1951_;
v___y_1884_ = v___x_1948_;
v___y_1885_ = v___y_1930_;
v___y_1886_ = v___y_1932_;
v___y_1887_ = v___y_1936_;
goto v___jp_1882_;
}
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v___y_1937_);
lean_dec(v___y_1934_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v_a_1953_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1939_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1939_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_dec(v___y_1937_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
return v___y_1931_;
}
}
v___jp_1961_:
{
lean_object* v___x_1972_; 
v___x_1972_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_1968_ == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref(v___x_1972_);
v___x_1974_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1975_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_1881_, v___y_1969_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set_tag(v___x_1978_, 1);
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
v___y_1660_ = v___y_1963_;
v___y_1661_ = v___y_1962_;
v___y_1662_ = v___y_1964_;
v___y_1663_ = v___y_1965_;
v___y_1664_ = v___x_1974_;
v___y_1665_ = v___y_1966_;
v___y_1666_ = v___y_1967_;
v___y_1667_ = v_a_1973_;
v___y_1668_ = v___y_1970_;
v___y_1669_ = v___y_1971_;
v_a_1670_ = v___x_1981_;
goto v___jp_1659_;
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
v_a_1984_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1975_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1975_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set_tag(v___x_1986_, 0);
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
v___y_1660_ = v___y_1963_;
v___y_1661_ = v___y_1962_;
v___y_1662_ = v___y_1964_;
v___y_1663_ = v___y_1965_;
v___y_1664_ = v___x_1974_;
v___y_1665_ = v___y_1966_;
v___y_1666_ = v___y_1967_;
v___y_1667_ = v_a_1973_;
v___y_1668_ = v___y_1970_;
v___y_1669_ = v___y_1971_;
v_a_1670_ = v___x_1989_;
goto v___jp_1659_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_a_1992_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1972_);
v___x_1993_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1994_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_1881_, v___y_1969_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 1);
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
v___y_1683_ = v___y_1963_;
v___y_1684_ = v___y_1962_;
v___y_1685_ = v___y_1964_;
v___y_1686_ = v___y_1965_;
v___y_1687_ = v___y_1966_;
v___y_1688_ = v___y_1967_;
v___y_1689_ = v_a_1992_;
v___y_1690_ = v___y_1970_;
v___y_1691_ = v___y_1971_;
v___y_1692_ = v___x_1993_;
v_a_1693_ = v___x_2000_;
goto v___jp_1682_;
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
v_a_2003_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1994_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1994_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set_tag(v___x_2005_, 0);
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
v___y_1683_ = v___y_1963_;
v___y_1684_ = v___y_1962_;
v___y_1685_ = v___y_1964_;
v___y_1686_ = v___y_1965_;
v___y_1687_ = v___y_1966_;
v___y_1688_ = v___y_1967_;
v___y_1689_ = v_a_1992_;
v___y_1690_ = v___y_1970_;
v___y_1691_ = v___y_1971_;
v___y_1692_ = v___x_1993_;
v_a_1693_ = v___x_2008_;
goto v___jp_1682_;
}
}
}
}
}
v___jp_2011_:
{
if (v___y_2025_ == 0)
{
lean_object* v___x_2026_; 
lean_dec_ref(v___y_2024_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2023_);
v___x_2026_ = lean_apply_6(v___y_2013_, v___y_2023_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
if (lean_obj_tag(v_a_2027_) == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2028_ = lean_nat_add(v_n_1881_, v_one_1880_);
lean_dec(v_n_1881_);
v___x_2029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___y_2023_);
lean_ctor_set(v___x_2029_, 1, v_acc_971_);
v___x_2030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_966_);
v___x_2031_ = l_Lean_Name_append(v___x_2030_, v_trace_966_);
v___x_2032_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2014_, v___y_2012_, v___x_2031_);
lean_dec(v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = l_Lean_trace_profiler;
v___x_2034_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2012_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; 
lean_inc(v_trace_966_);
v___x_2035_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___x_2028_, v___y_2020_, v___x_2029_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1100_ = v___y_2015_;
v___y_1101_ = v___y_2012_;
v___y_1102_ = v___y_2016_;
v___y_1103_ = v___y_2017_;
v___y_1104_ = v___y_2018_;
v___y_1105_ = v___y_2021_;
v___y_1106_ = v___y_2022_;
v___y_1107_ = v___x_2035_;
goto v___jp_1099_;
}
else
{
v___y_1746_ = v___x_2032_;
v___y_1747_ = v___y_2012_;
v___y_1748_ = v___x_2028_;
v___y_1749_ = v___y_2015_;
v___y_1750_ = v___y_2016_;
v___y_1751_ = v___y_2017_;
v___y_1752_ = v___y_2018_;
v___y_1753_ = v___y_2019_;
v___y_1754_ = v___y_2020_;
v___y_1755_ = v___y_2021_;
v___y_1756_ = v___y_2022_;
v___y_1757_ = v___x_2029_;
goto v___jp_1745_;
}
}
else
{
v___y_1746_ = v___x_2032_;
v___y_1747_ = v___y_2012_;
v___y_1748_ = v___x_2028_;
v___y_1749_ = v___y_2015_;
v___y_1750_ = v___y_2016_;
v___y_1751_ = v___y_2017_;
v___y_1752_ = v___y_2018_;
v___y_1753_ = v___y_2019_;
v___y_1754_ = v___y_2020_;
v___y_1755_ = v___y_2021_;
v___y_1756_ = v___y_2022_;
v___y_1757_ = v___x_2029_;
goto v___jp_1745_;
}
}
else
{
lean_object* v_val_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
lean_dec(v___y_2023_);
v_val_2036_ = lean_ctor_get(v_a_2027_, 0);
lean_inc(v_val_2036_);
lean_dec_ref_known(v_a_2027_, 1);
v___x_2037_ = l_List_appendTR___redArg(v_val_2036_, v___y_2020_);
v___x_2038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_966_);
v___x_2039_ = l_Lean_Name_append(v___x_2038_, v_trace_966_);
v___x_2040_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2014_, v___y_2012_, v___x_2039_);
lean_dec(v___x_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = l_Lean_trace_profiler;
v___x_2042_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2012_, v___x_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; 
lean_inc(v_trace_966_);
v___x_2043_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_1881_, v___x_2037_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1100_ = v___y_2015_;
v___y_1101_ = v___y_2012_;
v___y_1102_ = v___y_2016_;
v___y_1103_ = v___y_2017_;
v___y_1104_ = v___y_2018_;
v___y_1105_ = v___y_2021_;
v___y_1106_ = v___y_2022_;
v___y_1107_ = v___x_2043_;
goto v___jp_1099_;
}
else
{
v___y_1962_ = v___x_2040_;
v___y_1963_ = v___y_2015_;
v___y_1964_ = v___y_2012_;
v___y_1965_ = v___y_2016_;
v___y_1966_ = v___y_2017_;
v___y_1967_ = v___y_2018_;
v___y_1968_ = v___y_2019_;
v___y_1969_ = v___x_2037_;
v___y_1970_ = v___y_2021_;
v___y_1971_ = v___y_2022_;
goto v___jp_1961_;
}
}
else
{
v___y_1962_ = v___x_2040_;
v___y_1963_ = v___y_2015_;
v___y_1964_ = v___y_2012_;
v___y_1965_ = v___y_2016_;
v___y_1966_ = v___y_2017_;
v___y_1967_ = v___y_2018_;
v___y_1968_ = v___y_2019_;
v___y_1969_ = v___x_2037_;
v___y_1970_ = v___y_2021_;
v___y_1971_ = v___y_2022_;
goto v___jp_1961_;
}
}
}
else
{
lean_object* v_a_2044_; 
lean_dec(v___y_2023_);
lean_dec(v___y_2020_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2044_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2026_, 1);
v___y_1090_ = v___y_2015_;
v___y_1091_ = v___y_2012_;
v___y_1092_ = v___y_2016_;
v___y_1093_ = v___y_2017_;
v___y_1094_ = v___y_2018_;
v___y_1095_ = v___y_2021_;
v___y_1096_ = v___y_2022_;
v_a_1097_ = v_a_2044_;
goto v___jp_1089_;
}
}
else
{
lean_dec(v___y_2023_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2013_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v___y_1090_ = v___y_2015_;
v___y_1091_ = v___y_2012_;
v___y_1092_ = v___y_2016_;
v___y_1093_ = v___y_2017_;
v___y_1094_ = v___y_2018_;
v___y_1095_ = v___y_2021_;
v___y_1096_ = v___y_2022_;
v_a_1097_ = v___y_2024_;
goto v___jp_1089_;
}
}
v___jp_2045_:
{
lean_object* v___x_2056_; 
v___x_2056_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_2051_ == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref(v___x_2056_);
v___x_2058_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_2059_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_1881_, v___y_2055_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
lean_ctor_set_tag(v___x_2062_, 1);
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
v___y_1542_ = v___y_2046_;
v___y_1543_ = v___x_2058_;
v___y_1544_ = v___y_2047_;
v___y_1545_ = v___y_2048_;
v___y_1546_ = v___y_2049_;
v___y_1547_ = v___y_2050_;
v___y_1548_ = v_a_2057_;
v___y_1549_ = v___y_2052_;
v___y_1550_ = v___y_2054_;
v___y_1551_ = v___y_2053_;
v_a_1552_ = v___x_2065_;
goto v___jp_1541_;
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v_a_2068_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2059_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2059_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 0);
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
v___y_1542_ = v___y_2046_;
v___y_1543_ = v___x_2058_;
v___y_1544_ = v___y_2047_;
v___y_1545_ = v___y_2048_;
v___y_1546_ = v___y_2049_;
v___y_1547_ = v___y_2050_;
v___y_1548_ = v_a_2057_;
v___y_1549_ = v___y_2052_;
v___y_1550_ = v___y_2054_;
v___y_1551_ = v___y_2053_;
v_a_1552_ = v___x_2073_;
goto v___jp_1541_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v_a_2076_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2076_);
lean_dec_ref(v___x_2056_);
v___x_2077_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_2078_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_1881_, v___y_2055_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 1);
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
v___y_1522_ = v___y_2046_;
v___y_1523_ = v___y_2047_;
v___y_1524_ = v___y_2048_;
v___y_1525_ = v___y_2049_;
v___y_1526_ = v___y_2050_;
v___y_1527_ = v_a_2076_;
v___y_1528_ = v___x_2077_;
v___y_1529_ = v___y_2052_;
v___y_1530_ = v___y_2054_;
v___y_1531_ = v___y_2053_;
v_a_1532_ = v___x_2084_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
v_a_2087_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2078_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2078_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set_tag(v___x_2089_, 0);
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
v___y_1522_ = v___y_2046_;
v___y_1523_ = v___y_2047_;
v___y_1524_ = v___y_2048_;
v___y_1525_ = v___y_2049_;
v___y_1526_ = v___y_2050_;
v___y_1527_ = v_a_2076_;
v___y_1528_ = v___x_2077_;
v___y_1529_ = v___y_2052_;
v___y_1530_ = v___y_2054_;
v___y_1531_ = v___y_2053_;
v_a_1532_ = v___x_2092_;
goto v___jp_1521_;
}
}
}
}
}
v___jp_2095_:
{
if (v___y_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec_ref(v___y_2096_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2108_);
v___x_2110_ = lean_apply_6(v___y_2098_, v___y_2108_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
if (lean_obj_tag(v_a_2111_) == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2112_ = lean_nat_add(v_n_1881_, v_one_1880_);
lean_dec(v_n_1881_);
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___y_2108_);
lean_ctor_set(v___x_2113_, 1, v_acc_971_);
v___x_2114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_966_);
v___x_2115_ = l_Lean_Name_append(v___x_2114_, v_trace_966_);
v___x_2116_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2099_, v___y_2097_, v___x_2115_);
lean_dec(v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2117_ = l_Lean_trace_profiler;
v___x_2118_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2097_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
lean_inc(v_trace_966_);
v___x_2119_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___x_2112_, v___y_2104_, v___x_2113_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1151_ = v___y_2100_;
v___y_1152_ = v___y_2097_;
v___y_1153_ = v___y_2101_;
v___y_1154_ = v___y_2102_;
v___y_1155_ = v___y_2105_;
v___y_1156_ = v___y_2107_;
v___y_1157_ = v___y_2106_;
v___y_1158_ = v___x_2119_;
goto v___jp_1150_;
}
else
{
v___y_1470_ = v___y_2097_;
v___y_1471_ = v___y_2100_;
v___y_1472_ = v___y_2101_;
v___y_1473_ = v___x_2112_;
v___y_1474_ = v___y_2102_;
v___y_1475_ = v___x_2116_;
v___y_1476_ = v___x_2113_;
v___y_1477_ = v___y_2103_;
v___y_1478_ = v___y_2104_;
v___y_1479_ = v___y_2105_;
v___y_1480_ = v___y_2106_;
v___y_1481_ = v___y_2107_;
goto v___jp_1469_;
}
}
else
{
v___y_1470_ = v___y_2097_;
v___y_1471_ = v___y_2100_;
v___y_1472_ = v___y_2101_;
v___y_1473_ = v___x_2112_;
v___y_1474_ = v___y_2102_;
v___y_1475_ = v___x_2116_;
v___y_1476_ = v___x_2113_;
v___y_1477_ = v___y_2103_;
v___y_1478_ = v___y_2104_;
v___y_1479_ = v___y_2105_;
v___y_1480_ = v___y_2106_;
v___y_1481_ = v___y_2107_;
goto v___jp_1469_;
}
}
else
{
lean_object* v_val_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
lean_dec(v___y_2108_);
v_val_2120_ = lean_ctor_get(v_a_2111_, 0);
lean_inc(v_val_2120_);
lean_dec_ref_known(v_a_2111_, 1);
v___x_2121_ = l_List_appendTR___redArg(v_val_2120_, v___y_2104_);
v___x_2122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_966_);
v___x_2123_ = l_Lean_Name_append(v___x_2122_, v_trace_966_);
v___x_2124_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2099_, v___y_2097_, v___x_2123_);
lean_dec(v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = l_Lean_trace_profiler;
v___x_2126_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2097_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; 
lean_inc(v_trace_966_);
v___x_2127_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_1881_, v___x_2121_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1151_ = v___y_2100_;
v___y_1152_ = v___y_2097_;
v___y_1153_ = v___y_2101_;
v___y_1154_ = v___y_2102_;
v___y_1155_ = v___y_2105_;
v___y_1156_ = v___y_2107_;
v___y_1157_ = v___y_2106_;
v___y_1158_ = v___x_2127_;
goto v___jp_1150_;
}
else
{
v___y_2046_ = v___x_2124_;
v___y_2047_ = v___y_2100_;
v___y_2048_ = v___y_2097_;
v___y_2049_ = v___y_2101_;
v___y_2050_ = v___y_2102_;
v___y_2051_ = v___y_2103_;
v___y_2052_ = v___y_2105_;
v___y_2053_ = v___y_2107_;
v___y_2054_ = v___y_2106_;
v___y_2055_ = v___x_2121_;
goto v___jp_2045_;
}
}
else
{
v___y_2046_ = v___x_2124_;
v___y_2047_ = v___y_2100_;
v___y_2048_ = v___y_2097_;
v___y_2049_ = v___y_2101_;
v___y_2050_ = v___y_2102_;
v___y_2051_ = v___y_2103_;
v___y_2052_ = v___y_2105_;
v___y_2053_ = v___y_2107_;
v___y_2054_ = v___y_2106_;
v___y_2055_ = v___x_2121_;
goto v___jp_2045_;
}
}
}
else
{
lean_object* v_a_2128_; 
lean_dec(v___y_2108_);
lean_dec(v___y_2104_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2128_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2110_, 1);
v___y_1141_ = v___y_2100_;
v___y_1142_ = v___y_2097_;
v___y_1143_ = v___y_2101_;
v___y_1144_ = v___y_2102_;
v___y_1145_ = v___y_2105_;
v___y_1146_ = v___y_2106_;
v___y_1147_ = v___y_2107_;
v_a_1148_ = v_a_2128_;
goto v___jp_1140_;
}
}
else
{
lean_dec(v___y_2108_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2098_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v___y_1141_ = v___y_2100_;
v___y_1142_ = v___y_2097_;
v___y_1143_ = v___y_2101_;
v___y_1144_ = v___y_2102_;
v___y_1145_ = v___y_2105_;
v___y_1146_ = v___y_2106_;
v___y_1147_ = v___y_2107_;
v_a_1148_ = v___y_2096_;
goto v___jp_1140_;
}
}
v___jp_2129_:
{
lean_object* v___x_2142_; lean_object* v_a_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2142_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref(v___x_2142_);
v___x_2144_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2145_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2130_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
lean_dec_ref(v___y_2132_);
v___x_2146_ = lean_io_mono_nanos_now();
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2141_);
v___x_2147_ = lean_apply_6(v___y_2131_, v___y_2141_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; uint8_t v___x_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2147_, 1);
v___x_2149_ = lean_unbox(v_a_2148_);
lean_dec(v_a_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
lean_inc_ref(v_next_967_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2141_);
v___x_2150_ = lean_apply_7(v_next_967_, v___y_2141_, v___y_2137_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; 
lean_dec(v___y_2141_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2133_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___y_1131_ = v___y_2135_;
v___y_1132_ = v___y_2130_;
v___y_1133_ = v___y_2136_;
v___y_1134_ = v_a_2143_;
v___y_1135_ = v___y_2139_;
v___y_1136_ = v___x_2146_;
v___y_1137_ = v___y_2140_;
v_a_1138_ = v_a_2151_;
goto v___jp_1130_;
}
else
{
lean_object* v_a_2152_; uint8_t v___x_2153_; 
v_a_2152_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2153_ = l_Lean_Exception_isInterrupt(v_a_2152_);
if (v___x_2153_ == 0)
{
uint8_t v___x_2154_; 
lean_inc(v_a_2152_);
v___x_2154_ = l_Lean_Exception_isRuntime(v_a_2152_);
v___y_2096_ = v_a_2152_;
v___y_2097_ = v___y_2130_;
v___y_2098_ = v___y_2133_;
v___y_2099_ = v___y_2134_;
v___y_2100_ = v___y_2135_;
v___y_2101_ = v___y_2136_;
v___y_2102_ = v_a_2143_;
v___y_2103_ = v___x_2145_;
v___y_2104_ = v___y_2138_;
v___y_2105_ = v___y_2139_;
v___y_2106_ = v___x_2146_;
v___y_2107_ = v___y_2140_;
v___y_2108_ = v___y_2141_;
v___y_2109_ = v___x_2154_;
goto v___jp_2095_;
}
else
{
v___y_2096_ = v_a_2152_;
v___y_2097_ = v___y_2130_;
v___y_2098_ = v___y_2133_;
v___y_2099_ = v___y_2134_;
v___y_2100_ = v___y_2135_;
v___y_2101_ = v___y_2136_;
v___y_2102_ = v_a_2143_;
v___y_2103_ = v___x_2145_;
v___y_2104_ = v___y_2138_;
v___y_2105_ = v___y_2139_;
v___y_2106_ = v___x_2146_;
v___y_2107_ = v___y_2140_;
v___y_2108_ = v___y_2141_;
v___y_2109_ = v___x_2153_;
goto v___jp_2095_;
}
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
lean_dec_ref(v___y_2137_);
lean_dec_ref(v___y_2133_);
v___x_2155_ = lean_nat_add(v_n_1881_, v_one_1880_);
lean_dec(v_n_1881_);
v___x_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___y_2141_);
lean_ctor_set(v___x_2156_, 1, v_acc_971_);
v___x_2157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_966_);
v___x_2158_ = l_Lean_Name_append(v___x_2157_, v_trace_966_);
v___x_2159_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2134_, v___y_2130_, v___x_2158_);
lean_dec(v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = l_Lean_trace_profiler;
v___x_2161_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2130_, v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; 
lean_inc(v_trace_966_);
v___x_2162_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___x_2155_, v___y_2138_, v___x_2156_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1151_ = v___y_2135_;
v___y_1152_ = v___y_2130_;
v___y_1153_ = v___y_2136_;
v___y_1154_ = v_a_2143_;
v___y_1155_ = v___y_2139_;
v___y_1156_ = v___y_2140_;
v___y_1157_ = v___x_2146_;
v___y_1158_ = v___x_2162_;
goto v___jp_1150_;
}
else
{
v___y_1608_ = v___x_2159_;
v___y_1609_ = v___y_2130_;
v___y_1610_ = v___x_2155_;
v___y_1611_ = v___y_2135_;
v___y_1612_ = v___y_2136_;
v___y_1613_ = v___x_2156_;
v___y_1614_ = v_a_2143_;
v___y_1615_ = v___x_2145_;
v___y_1616_ = v___y_2138_;
v___y_1617_ = v___y_2139_;
v___y_1618_ = v___x_2146_;
v___y_1619_ = v___y_2140_;
goto v___jp_1607_;
}
}
else
{
v___y_1608_ = v___x_2159_;
v___y_1609_ = v___y_2130_;
v___y_1610_ = v___x_2155_;
v___y_1611_ = v___y_2135_;
v___y_1612_ = v___y_2136_;
v___y_1613_ = v___x_2156_;
v___y_1614_ = v_a_2143_;
v___y_1615_ = v___x_2145_;
v___y_1616_ = v___y_2138_;
v___y_1617_ = v___y_2139_;
v___y_1618_ = v___x_2146_;
v___y_1619_ = v___y_2140_;
goto v___jp_1607_;
}
}
}
else
{
lean_object* v_a_2163_; 
lean_dec(v___y_2141_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec_ref(v___y_2133_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2163_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2147_, 1);
v___y_1141_ = v___y_2135_;
v___y_1142_ = v___y_2130_;
v___y_1143_ = v___y_2136_;
v___y_1144_ = v_a_2143_;
v___y_1145_ = v___y_2139_;
v___y_1146_ = v___x_2146_;
v___y_1147_ = v___y_2140_;
v_a_1148_ = v_a_2163_;
goto v___jp_1140_;
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_dec_ref(v___y_2137_);
v___x_2164_ = lean_io_get_num_heartbeats();
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2141_);
v___x_2165_ = lean_apply_6(v___y_2131_, v___y_2141_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; uint8_t v___x_2167_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v___x_2167_ = lean_unbox(v_a_2166_);
lean_dec(v_a_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
lean_inc_ref(v_next_967_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2141_);
v___x_2168_ = lean_apply_7(v_next_967_, v___y_2141_, v___y_2132_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; 
lean_dec(v___y_2141_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2133_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v___y_1080_ = v___y_2135_;
v___y_1081_ = v___y_2130_;
v___y_1082_ = v___x_2164_;
v___y_1083_ = v___y_2136_;
v___y_1084_ = v_a_2143_;
v___y_1085_ = v___y_2139_;
v___y_1086_ = v___y_2140_;
v_a_1087_ = v_a_2169_;
goto v___jp_1079_;
}
else
{
lean_object* v_a_2170_; uint8_t v___x_2171_; 
v_a_2170_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2168_, 1);
v___x_2171_ = l_Lean_Exception_isInterrupt(v_a_2170_);
if (v___x_2171_ == 0)
{
uint8_t v___x_2172_; 
lean_inc(v_a_2170_);
v___x_2172_ = l_Lean_Exception_isRuntime(v_a_2170_);
v___y_2012_ = v___y_2130_;
v___y_2013_ = v___y_2133_;
v___y_2014_ = v___y_2134_;
v___y_2015_ = v___y_2135_;
v___y_2016_ = v___x_2164_;
v___y_2017_ = v___y_2136_;
v___y_2018_ = v_a_2143_;
v___y_2019_ = v___x_2145_;
v___y_2020_ = v___y_2138_;
v___y_2021_ = v___y_2139_;
v___y_2022_ = v___y_2140_;
v___y_2023_ = v___y_2141_;
v___y_2024_ = v_a_2170_;
v___y_2025_ = v___x_2172_;
goto v___jp_2011_;
}
else
{
v___y_2012_ = v___y_2130_;
v___y_2013_ = v___y_2133_;
v___y_2014_ = v___y_2134_;
v___y_2015_ = v___y_2135_;
v___y_2016_ = v___x_2164_;
v___y_2017_ = v___y_2136_;
v___y_2018_ = v_a_2143_;
v___y_2019_ = v___x_2145_;
v___y_2020_ = v___y_2138_;
v___y_2021_ = v___y_2139_;
v___y_2022_ = v___y_2140_;
v___y_2023_ = v___y_2141_;
v___y_2024_ = v_a_2170_;
v___y_2025_ = v___x_2171_;
goto v___jp_2011_;
}
}
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
lean_dec_ref(v___y_2133_);
lean_dec_ref(v___y_2132_);
v___x_2173_ = lean_nat_add(v_n_1881_, v_one_1880_);
lean_dec(v_n_1881_);
v___x_2174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___y_2141_);
lean_ctor_set(v___x_2174_, 1, v_acc_971_);
v___x_2175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_966_);
v___x_2176_ = l_Lean_Name_append(v___x_2175_, v_trace_966_);
v___x_2177_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2134_, v___y_2130_, v___x_2176_);
lean_dec(v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = l_Lean_trace_profiler;
v___x_2179_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2130_, v___x_2178_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; 
lean_inc(v_trace_966_);
v___x_2180_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___x_2173_, v___y_2138_, v___x_2174_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1100_ = v___y_2135_;
v___y_1101_ = v___y_2130_;
v___y_1102_ = v___x_2164_;
v___y_1103_ = v___y_2136_;
v___y_1104_ = v_a_2143_;
v___y_1105_ = v___y_2139_;
v___y_1106_ = v___y_2140_;
v___y_1107_ = v___x_2180_;
goto v___jp_1099_;
}
else
{
v___y_1375_ = v___y_2130_;
v___y_1376_ = v___x_2177_;
v___y_1377_ = v___y_2135_;
v___y_1378_ = v___x_2164_;
v___y_1379_ = v___x_2174_;
v___y_1380_ = v___y_2136_;
v___y_1381_ = v_a_2143_;
v___y_1382_ = v___x_2145_;
v___y_1383_ = v___y_2138_;
v___y_1384_ = v___y_2139_;
v___y_1385_ = v___y_2140_;
v___y_1386_ = v___x_2173_;
goto v___jp_1374_;
}
}
else
{
v___y_1375_ = v___y_2130_;
v___y_1376_ = v___x_2177_;
v___y_1377_ = v___y_2135_;
v___y_1378_ = v___x_2164_;
v___y_1379_ = v___x_2174_;
v___y_1380_ = v___y_2136_;
v___y_1381_ = v_a_2143_;
v___y_1382_ = v___x_2145_;
v___y_1383_ = v___y_2138_;
v___y_1384_ = v___y_2139_;
v___y_1385_ = v___y_2140_;
v___y_1386_ = v___x_2173_;
goto v___jp_1374_;
}
}
}
else
{
lean_object* v_a_2181_; 
lean_dec(v___y_2141_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2181_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2165_, 1);
v___y_1090_ = v___y_2135_;
v___y_1091_ = v___y_2130_;
v___y_1092_ = v___x_2164_;
v___y_1093_ = v___y_2136_;
v___y_1094_ = v_a_2143_;
v___y_1095_ = v___y_2139_;
v___y_1096_ = v___y_2140_;
v_a_1097_ = v_a_2181_;
goto v___jp_1089_;
}
}
}
v___jp_2182_:
{
if (v___y_2187_ == 0)
{
lean_object* v___x_2188_; 
lean_dec_ref(v___y_2185_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2186_);
v___x_2188_ = lean_apply_6(v___y_2183_, v___y_2186_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
if (lean_obj_tag(v_a_2189_) == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_nat_add(v_n_1881_, v_one_1880_);
lean_dec(v_n_1881_);
v___x_2191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___y_2186_);
lean_ctor_set(v___x_2191_, 1, v_acc_971_);
v_n_969_ = v___x_2190_;
v_curr_970_ = v___y_2184_;
v_acc_971_ = v___x_2191_;
goto _start;
}
else
{
lean_object* v_val_2193_; lean_object* v___x_2194_; 
lean_dec(v___y_2186_);
v_val_2193_ = lean_ctor_get(v_a_2189_, 0);
lean_inc(v_val_2193_);
lean_dec_ref_known(v_a_2189_, 1);
v___x_2194_ = l_List_appendTR___redArg(v_val_2193_, v___y_2184_);
v_n_969_ = v_n_1881_;
v_curr_970_ = v___x_2194_;
goto _start;
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec(v___y_2186_);
lean_dec(v___y_2184_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v_a_2196_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2188_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2188_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
else
{
lean_dec(v___y_2186_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
return v___y_2185_;
}
}
v___jp_2204_:
{
if (lean_obj_tag(v_a_2205_) == 0)
{
if (lean_obj_tag(v_curr_970_) == 0)
{
lean_object* v_options_2206_; lean_object* v_inheritedTraceOptions_2207_; uint8_t v_hasTrace_2208_; lean_object* v___x_2209_; 
lean_dec(v_n_1881_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_options_2206_ = lean_ctor_get(v_a_974_, 2);
v_inheritedTraceOptions_2207_ = lean_ctor_get(v_a_974_, 13);
v_hasTrace_2208_ = lean_ctor_get_uint8(v_options_2206_, sizeof(void*)*1);
v___x_2209_ = l_List_reverse___redArg(v_acc_971_);
if (v_hasTrace_2208_ == 0)
{
lean_object* v___x_2210_; 
lean_dec(v_trace_966_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_966_);
v___x_2213_ = l_Lean_Name_append(v___x_2212_, v_trace_966_);
v___x_2214_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2207_, v_options_2206_, v___x_2213_);
lean_dec(v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = l_Lean_trace_profiler;
v___x_2216_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2206_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; 
lean_dec(v_trace_966_);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2209_);
return v___x_2217_;
}
else
{
v___y_1170_ = v_hasTrace_2208_;
v___y_1171_ = v_options_2206_;
v___y_1172_ = v___x_2214_;
v___y_1173_ = v___x_2209_;
v___y_1174_ = v___x_2211_;
goto v___jp_1169_;
}
}
else
{
v___y_1170_ = v_hasTrace_2208_;
v___y_1171_ = v_options_2206_;
v___y_1172_ = v___x_2214_;
v___y_1173_ = v___x_2209_;
v___y_1174_ = v___x_2211_;
goto v___jp_1169_;
}
}
}
else
{
lean_object* v_head_2218_; lean_object* v_tail_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2292_; 
v_head_2218_ = lean_ctor_get(v_curr_970_, 0);
v_tail_2219_ = lean_ctor_get(v_curr_970_, 1);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_curr_970_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2221_ = v_curr_970_;
v_isShared_2222_ = v_isSharedCheck_2292_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_tail_2219_);
lean_inc(v_head_2218_);
lean_dec(v_curr_970_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2292_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v_a_2224_; uint8_t v___x_2225_; uint8_t v___x_2226_; 
v___x_2223_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2218_, v_a_973_);
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref(v___x_2223_);
v___x_2225_ = 1;
v___x_2226_ = lean_unbox(v_a_2224_);
lean_dec(v_a_2224_);
if (v___x_2226_ == 0)
{
lean_object* v_options_2227_; uint8_t v_hasTrace_2228_; 
v_options_2227_ = lean_ctor_get(v_a_974_, 2);
v_hasTrace_2228_ = lean_ctor_get_uint8(v_options_2227_, sizeof(void*)*1);
if (v_hasTrace_2228_ == 0)
{
lean_object* v___x_2229_; 
lean_inc_ref(v_suspend_1166_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_head_2218_);
v___x_2229_ = lean_apply_6(v_suspend_1166_, v_head_2218_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; uint8_t v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2229_, 1);
v___x_2231_ = lean_unbox(v_a_2230_);
lean_dec(v_a_2230_);
if (v___x_2231_ == 0)
{
lean_object* v___f_2232_; lean_object* v___x_2233_; 
lean_del_object(v___x_2221_);
lean_inc(v_acc_971_);
lean_inc(v_n_1881_);
lean_inc(v_goals_968_);
lean_inc_ref_n(v_next_967_, 2);
lean_inc(v_trace_966_);
lean_inc_ref(v_cfg_965_);
lean_inc(v_tail_2219_);
v___f_2232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2232_, 0, v_tail_2219_);
lean_closure_set(v___f_2232_, 1, v_cfg_965_);
lean_closure_set(v___f_2232_, 2, v_trace_966_);
lean_closure_set(v___f_2232_, 3, v_next_967_);
lean_closure_set(v___f_2232_, 4, v_goals_968_);
lean_closure_set(v___f_2232_, 5, v_n_1881_);
lean_closure_set(v___f_2232_, 6, v_acc_971_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_head_2218_);
v___x_2233_ = lean_apply_7(v_next_967_, v_head_2218_, v___f_2232_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_dec(v_tail_2219_);
lean_dec(v_head_2218_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
return v___x_2233_;
}
else
{
lean_object* v_a_2234_; uint8_t v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
v___x_2235_ = l_Lean_Exception_isInterrupt(v_a_2234_);
if (v___x_2235_ == 0)
{
uint8_t v___x_2236_; 
v___x_2236_ = l_Lean_Exception_isRuntime(v_a_2234_);
lean_inc_ref(v_discharge_1167_);
v___y_2183_ = v_discharge_1167_;
v___y_2184_ = v_tail_2219_;
v___y_2185_ = v___x_2233_;
v___y_2186_ = v_head_2218_;
v___y_2187_ = v___x_2236_;
goto v___jp_2182_;
}
else
{
lean_dec(v_a_2234_);
lean_inc_ref(v_discharge_1167_);
v___y_2183_ = v_discharge_1167_;
v___y_2184_ = v_tail_2219_;
v___y_2185_ = v___x_2233_;
v___y_2186_ = v_head_2218_;
v___y_2187_ = v___x_2235_;
goto v___jp_2182_;
}
}
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = lean_nat_add(v_n_1881_, v_one_1880_);
lean_dec(v_n_1881_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v_acc_971_);
v___x_2239_ = v___x_2221_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_head_2218_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_acc_971_);
v___x_2239_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
v_n_969_ = v___x_2237_;
v_curr_970_ = v_tail_2219_;
v_acc_971_ = v___x_2239_;
goto _start;
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_del_object(v___x_2221_);
lean_dec(v_tail_2219_);
lean_dec(v_head_2218_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v_a_2242_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2229_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2229_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2250_; lean_object* v___f_2251_; lean_object* v___f_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v_inheritedTraceOptions_2250_ = lean_ctor_get(v_a_974_, 13);
lean_inc(v_acc_971_);
lean_inc(v_n_1881_);
lean_inc(v_goals_968_);
lean_inc_ref(v_next_967_);
lean_inc_n(v_trace_966_, 2);
lean_inc_ref(v_cfg_965_);
lean_inc(v_tail_2219_);
v___f_2251_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2251_, 0, v_tail_2219_);
lean_closure_set(v___f_2251_, 1, v_cfg_965_);
lean_closure_set(v___f_2251_, 2, v_trace_966_);
lean_closure_set(v___f_2251_, 3, v_next_967_);
lean_closure_set(v___f_2251_, 4, v_goals_968_);
lean_closure_set(v___f_2251_, 5, v_n_1881_);
lean_closure_set(v___f_2251_, 6, v_acc_971_);
lean_inc(v_head_2218_);
v___f_2252_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(v___f_2252_, 0, v_head_2218_);
v___x_2253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2254_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
v___x_2255_ = l_Lean_Name_append(v___x_2254_, v_trace_966_);
v___x_2256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2250_, v_options_2227_, v___x_2255_);
lean_dec(v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; uint8_t v___x_2258_; 
v___x_2257_ = l_Lean_trace_profiler;
v___x_2258_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2227_, v___x_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; 
lean_dec_ref(v___f_2252_);
lean_inc_ref(v_suspend_1166_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_head_2218_);
v___x_2259_ = lean_apply_6(v_suspend_1166_, v_head_2218_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
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
lean_del_object(v___x_2221_);
lean_inc_ref(v_next_967_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_head_2218_);
v___x_2262_ = lean_apply_7(v_next_967_, v_head_2218_, v___f_2251_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_dec(v_tail_2219_);
lean_dec(v_head_2218_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
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
lean_inc_ref(v_discharge_1167_);
v___y_1929_ = v_inheritedTraceOptions_2250_;
v___y_1930_ = v_options_2227_;
v___y_1931_ = v___x_2262_;
v___y_1932_ = v___x_2253_;
v___y_1933_ = v_discharge_1167_;
v___y_1934_ = v_tail_2219_;
v___y_1935_ = v___x_2258_;
v___y_1936_ = v___x_2225_;
v___y_1937_ = v_head_2218_;
v___y_1938_ = v___x_2265_;
goto v___jp_1928_;
}
else
{
lean_dec(v_a_2263_);
lean_inc_ref(v_discharge_1167_);
v___y_1929_ = v_inheritedTraceOptions_2250_;
v___y_1930_ = v_options_2227_;
v___y_1931_ = v___x_2262_;
v___y_1932_ = v___x_2253_;
v___y_1933_ = v_discharge_1167_;
v___y_1934_ = v_tail_2219_;
v___y_1935_ = v___x_2258_;
v___y_1936_ = v___x_2225_;
v___y_1937_ = v_head_2218_;
v___y_1938_ = v___x_2264_;
goto v___jp_1928_;
}
}
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_dec_ref(v___f_2251_);
v___x_2266_ = lean_nat_add(v_n_1881_, v_one_1880_);
lean_dec(v_n_1881_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 1, v_acc_971_);
v___x_2268_ = v___x_2221_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_head_2218_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_acc_971_);
v___x_2268_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
if (v___x_2256_ == 0)
{
if (v___x_2258_ == 0)
{
v_n_969_ = v___x_2266_;
v_curr_970_ = v_tail_2219_;
v_acc_971_ = v___x_2268_;
goto _start;
}
else
{
v___y_1833_ = v___x_2268_;
v___y_1834_ = v___x_2256_;
v___y_1835_ = v_options_2227_;
v___y_1836_ = v___x_2253_;
v___y_1837_ = v_tail_2219_;
v___y_1838_ = v___x_2266_;
v___y_1839_ = v___x_2225_;
goto v___jp_1832_;
}
}
else
{
v___y_1833_ = v___x_2268_;
v___y_1834_ = v___x_2256_;
v___y_1835_ = v_options_2227_;
v___y_1836_ = v___x_2253_;
v___y_1837_ = v_tail_2219_;
v___y_1838_ = v___x_2266_;
v___y_1839_ = v___x_2225_;
goto v___jp_1832_;
}
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec_ref(v___f_2251_);
lean_del_object(v___x_2221_);
lean_dec(v_tail_2219_);
lean_dec(v_head_2218_);
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
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
lean_del_object(v___x_2221_);
lean_inc_ref(v_discharge_1167_);
lean_inc_ref(v___f_2251_);
lean_inc_ref(v_suspend_1166_);
v___y_2130_ = v_options_2227_;
v___y_2131_ = v_suspend_1166_;
v___y_2132_ = v___f_2251_;
v___y_2133_ = v_discharge_1167_;
v___y_2134_ = v_inheritedTraceOptions_2250_;
v___y_2135_ = v___x_2256_;
v___y_2136_ = v___x_2253_;
v___y_2137_ = v___f_2251_;
v___y_2138_ = v_tail_2219_;
v___y_2139_ = v___f_2252_;
v___y_2140_ = v___x_2225_;
v___y_2141_ = v_head_2218_;
goto v___jp_2129_;
}
}
else
{
lean_del_object(v___x_2221_);
lean_inc_ref(v_discharge_1167_);
lean_inc_ref(v___f_2251_);
lean_inc_ref(v_suspend_1166_);
v___y_2130_ = v_options_2227_;
v___y_2131_ = v_suspend_1166_;
v___y_2132_ = v___f_2251_;
v___y_2133_ = v_discharge_1167_;
v___y_2134_ = v_inheritedTraceOptions_2250_;
v___y_2135_ = v___x_2256_;
v___y_2136_ = v___x_2253_;
v___y_2137_ = v___f_2251_;
v___y_2138_ = v_tail_2219_;
v___y_2139_ = v___f_2252_;
v___y_2140_ = v___x_2225_;
v___y_2141_ = v_head_2218_;
goto v___jp_2129_;
}
}
}
else
{
lean_object* v_options_2279_; lean_object* v_inheritedTraceOptions_2280_; uint8_t v_hasTrace_2281_; lean_object* v___x_2282_; 
lean_del_object(v___x_2221_);
v_options_2279_ = lean_ctor_get(v_a_974_, 2);
v_inheritedTraceOptions_2280_ = lean_ctor_get(v_a_974_, 13);
v_hasTrace_2281_ = lean_ctor_get_uint8(v_options_2279_, sizeof(void*)*1);
v___x_2282_ = lean_nat_add(v_n_1881_, v_one_1880_);
lean_dec(v_n_1881_);
if (v_hasTrace_2281_ == 0)
{
lean_dec(v_head_2218_);
v_n_969_ = v___x_2282_;
v_curr_970_ = v_tail_2219_;
goto _start;
}
else
{
lean_object* v___f_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___f_2284_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2284_, 0, v_head_2218_);
v___x_2285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_966_);
v___x_2287_ = l_Lean_Name_append(v___x_2286_, v_trace_966_);
v___x_2288_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2280_, v_options_2279_, v___x_2287_);
lean_dec(v___x_2287_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; uint8_t v___x_2290_; 
v___x_2289_ = l_Lean_trace_profiler;
v___x_2290_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2279_, v___x_2289_);
if (v___x_2290_ == 0)
{
lean_dec_ref(v___f_2284_);
v_n_969_ = v___x_2282_;
v_curr_970_ = v_tail_2219_;
goto _start;
}
else
{
v___y_1015_ = v_options_2279_;
v___y_1016_ = v___x_2282_;
v___y_1017_ = v___x_2288_;
v___y_1018_ = v_tail_2219_;
v___y_1019_ = v___f_2284_;
v___y_1020_ = v___x_2285_;
v___y_1021_ = v___x_2225_;
goto v___jp_1014_;
}
}
else
{
v___y_1015_ = v_options_2279_;
v___y_1016_ = v___x_2282_;
v___y_1017_ = v___x_2288_;
v___y_1018_ = v_tail_2219_;
v___y_1019_ = v___f_2284_;
v___y_1020_ = v___x_2285_;
v___y_1021_ = v___x_2225_;
goto v___jp_1014_;
}
}
}
}
}
}
else
{
lean_object* v_val_2293_; 
lean_dec(v_curr_970_);
v_val_2293_ = lean_ctor_get(v_a_2205_, 0);
lean_inc(v_val_2293_);
lean_dec_ref_known(v_a_2205_, 1);
v_n_969_ = v_n_1881_;
v_curr_970_ = v_val_2293_;
goto _start;
}
}
v___jp_2295_:
{
if (lean_obj_tag(v___y_2296_) == 0)
{
lean_object* v_a_2297_; 
v_a_2297_ = lean_ctor_get(v___y_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___y_2296_, 1);
v_a_2205_ = v_a_2297_;
goto v___jp_2204_;
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_n_1881_);
lean_dec(v_acc_971_);
lean_dec(v_curr_970_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v_a_2298_ = lean_ctor_get(v___y_2296_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___y_2296_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___y_2296_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___y_2296_);
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
}
v___jp_977_:
{
lean_object* v___x_986_; double v___x_987_; double v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_986_ = lean_io_get_num_heartbeats();
v___x_987_ = lean_float_of_nat(v___y_978_);
v___x_988_ = lean_float_of_nat(v___x_986_);
v___x_989_ = lean_box_float(v___x_987_);
v___x_990_ = lean_box_float(v___x_988_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_a_985_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
lean_inc_ref(v___y_983_);
v___x_993_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_984_, v___y_983_, v___y_979_, v___y_981_, v___y_980_, v___y_982_, v___x_992_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_993_;
}
v___jp_994_:
{
lean_object* v___x_1003_; double v___x_1004_; double v___x_1005_; double v___x_1006_; double v___x_1007_; double v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1003_ = lean_io_mono_nanos_now();
v___x_1004_ = lean_float_of_nat(v___y_999_);
v___x_1005_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1006_ = lean_float_div(v___x_1004_, v___x_1005_);
v___x_1007_ = lean_float_of_nat(v___x_1003_);
v___x_1008_ = lean_float_div(v___x_1007_, v___x_1005_);
v___x_1009_ = lean_box_float(v___x_1006_);
v___x_1010_ = lean_box_float(v___x_1008_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v_a_1002_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
lean_inc_ref(v___y_1000_);
v___x_1013_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1001_, v___y_1000_, v___y_995_, v___y_997_, v___y_996_, v___y_998_, v___x_1012_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1013_;
}
v___jp_1014_:
{
lean_object* v___x_1022_; lean_object* v_a_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1022_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref(v___x_1022_);
v___x_1024_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1025_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1015_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1027_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1016_, v___y_1018_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 1);
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
v___y_995_ = v___y_1015_;
v___y_996_ = v_a_1023_;
v___y_997_ = v___y_1017_;
v___y_998_ = v___y_1019_;
v___y_999_ = v___x_1026_;
v___y_1000_ = v___y_1020_;
v___y_1001_ = v___y_1021_;
v_a_1002_ = v___x_1033_;
goto v___jp_994_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_a_1036_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1027_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1027_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 0);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
v___y_995_ = v___y_1015_;
v___y_996_ = v_a_1023_;
v___y_997_ = v___y_1017_;
v___y_998_ = v___y_1019_;
v___y_999_ = v___x_1026_;
v___y_1000_ = v___y_1020_;
v___y_1001_ = v___y_1021_;
v_a_1002_ = v___x_1041_;
goto v___jp_994_;
}
}
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1045_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1016_, v___y_1018_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 1);
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
v___y_978_ = v___x_1044_;
v___y_979_ = v___y_1015_;
v___y_980_ = v_a_1023_;
v___y_981_ = v___y_1017_;
v___y_982_ = v___y_1019_;
v___y_983_ = v___y_1020_;
v___y_984_ = v___y_1021_;
v_a_985_ = v___x_1051_;
goto v___jp_977_;
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
v_a_1054_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1045_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1045_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set_tag(v___x_1056_, 0);
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
v___y_978_ = v___x_1044_;
v___y_979_ = v___y_1015_;
v___y_980_ = v_a_1023_;
v___y_981_ = v___y_1017_;
v___y_982_ = v___y_1019_;
v___y_983_ = v___y_1020_;
v___y_984_ = v___y_1021_;
v_a_985_ = v___x_1059_;
goto v___jp_977_;
}
}
}
}
}
v___jp_1062_:
{
lean_object* v___x_1071_; double v___x_1072_; double v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1071_ = lean_io_get_num_heartbeats();
v___x_1072_ = lean_float_of_nat(v___y_1065_);
v___x_1073_ = lean_float_of_nat(v___x_1071_);
v___x_1074_ = lean_box_float(v___x_1072_);
v___x_1075_ = lean_box_float(v___x_1073_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v_a_1070_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
lean_inc_ref(v___y_1066_);
v___x_1078_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1069_, v___y_1066_, v___y_1064_, v___y_1063_, v___y_1067_, v___y_1068_, v___x_1077_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1078_;
}
v___jp_1079_:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_a_1087_);
v___y_1063_ = v___y_1080_;
v___y_1064_ = v___y_1081_;
v___y_1065_ = v___y_1082_;
v___y_1066_ = v___y_1083_;
v___y_1067_ = v___y_1084_;
v___y_1068_ = v___y_1085_;
v___y_1069_ = v___y_1086_;
v_a_1070_ = v___x_1088_;
goto v___jp_1062_;
}
v___jp_1089_:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_a_1097_);
v___y_1063_ = v___y_1090_;
v___y_1064_ = v___y_1091_;
v___y_1065_ = v___y_1092_;
v___y_1066_ = v___y_1093_;
v___y_1067_ = v___y_1094_;
v___y_1068_ = v___y_1095_;
v___y_1069_ = v___y_1096_;
v_a_1070_ = v___x_1098_;
goto v___jp_1062_;
}
v___jp_1099_:
{
if (lean_obj_tag(v___y_1107_) == 0)
{
lean_object* v_a_1108_; 
v_a_1108_ = lean_ctor_get(v___y_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___y_1107_, 1);
v___y_1080_ = v___y_1100_;
v___y_1081_ = v___y_1101_;
v___y_1082_ = v___y_1102_;
v___y_1083_ = v___y_1103_;
v___y_1084_ = v___y_1104_;
v___y_1085_ = v___y_1105_;
v___y_1086_ = v___y_1106_;
v_a_1087_ = v_a_1108_;
goto v___jp_1079_;
}
else
{
lean_object* v_a_1109_; 
v_a_1109_ = lean_ctor_get(v___y_1107_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___y_1107_, 1);
v___y_1090_ = v___y_1100_;
v___y_1091_ = v___y_1101_;
v___y_1092_ = v___y_1102_;
v___y_1093_ = v___y_1103_;
v___y_1094_ = v___y_1104_;
v___y_1095_ = v___y_1105_;
v___y_1096_ = v___y_1106_;
v_a_1097_ = v_a_1109_;
goto v___jp_1089_;
}
}
v___jp_1110_:
{
lean_object* v___x_1119_; double v___x_1120_; double v___x_1121_; double v___x_1122_; double v___x_1123_; double v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1119_ = lean_io_mono_nanos_now();
v___x_1120_ = lean_float_of_nat(v___y_1117_);
v___x_1121_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1122_ = lean_float_div(v___x_1120_, v___x_1121_);
v___x_1123_ = lean_float_of_nat(v___x_1119_);
v___x_1124_ = lean_float_div(v___x_1123_, v___x_1121_);
v___x_1125_ = lean_box_float(v___x_1122_);
v___x_1126_ = lean_box_float(v___x_1124_);
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_a_1118_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
lean_inc_ref(v___y_1113_);
v___x_1129_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1116_, v___y_1113_, v___y_1112_, v___y_1111_, v___y_1114_, v___y_1115_, v___x_1128_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1129_;
}
v___jp_1130_:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_a_1138_);
v___y_1111_ = v___y_1131_;
v___y_1112_ = v___y_1132_;
v___y_1113_ = v___y_1133_;
v___y_1114_ = v___y_1134_;
v___y_1115_ = v___y_1135_;
v___y_1116_ = v___y_1137_;
v___y_1117_ = v___y_1136_;
v_a_1118_ = v___x_1139_;
goto v___jp_1110_;
}
v___jp_1140_:
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v_a_1148_);
v___y_1111_ = v___y_1141_;
v___y_1112_ = v___y_1142_;
v___y_1113_ = v___y_1143_;
v___y_1114_ = v___y_1144_;
v___y_1115_ = v___y_1145_;
v___y_1116_ = v___y_1147_;
v___y_1117_ = v___y_1146_;
v_a_1118_ = v___x_1149_;
goto v___jp_1110_;
}
v___jp_1150_:
{
if (lean_obj_tag(v___y_1158_) == 0)
{
lean_object* v_a_1159_; 
v_a_1159_ = lean_ctor_get(v___y_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___y_1158_, 1);
v___y_1131_ = v___y_1151_;
v___y_1132_ = v___y_1152_;
v___y_1133_ = v___y_1153_;
v___y_1134_ = v___y_1154_;
v___y_1135_ = v___y_1155_;
v___y_1136_ = v___y_1157_;
v___y_1137_ = v___y_1156_;
v_a_1138_ = v_a_1159_;
goto v___jp_1130_;
}
else
{
lean_object* v_a_1160_; 
v_a_1160_ = lean_ctor_get(v___y_1158_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___y_1158_, 1);
v___y_1141_ = v___y_1151_;
v___y_1142_ = v___y_1152_;
v___y_1143_ = v___y_1153_;
v___y_1144_ = v___y_1154_;
v___y_1145_ = v___y_1155_;
v___y_1146_ = v___y_1157_;
v___y_1147_ = v___y_1156_;
v_a_1148_ = v_a_1160_;
goto v___jp_1140_;
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
size_t v_x_85378__boxed_2469_; uint8_t v_res_2470_; lean_object* v_r_2471_; 
v_x_85378__boxed_2469_ = lean_unbox_usize(v_x_2467_);
lean_dec(v_x_2467_);
v_res_2470_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2465_, v_x_2466_, v_x_85378__boxed_2469_, v_x_2468_);
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
uint8_t v___x_57591__boxed_2756_; lean_object* v_res_2757_; 
v___x_57591__boxed_2756_ = lean_unbox(v___x_2751_);
v_res_2757_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_57591__boxed_2756_, v_x_2752_, v_x_2753_, v___y_2754_);
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
lean_dec(v_a_2837_);
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
uint8_t v___x_57945__boxed_2957_; uint8_t v___x_57946__boxed_2958_; lean_object* v_res_2959_; 
v___x_57945__boxed_2957_ = lean_unbox(v___x_2951_);
v___x_57946__boxed_2958_ = lean_unbox(v___x_2952_);
v_res_2959_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_57945__boxed_2957_, v___x_57946__boxed_2958_, v_x_2953_, v_x_2954_, v___y_2955_);
lean_dec(v___y_2955_);
return v_res_2959_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
v___x_2962_ = l_Lean_stringToMessageData(v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_2965_, lean_object* v_trace_2966_, lean_object* v_next_2967_, lean_object* v_orig_2968_, lean_object* v_goals_2969_, lean_object* v_remaining_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2));
lean_inc(v_remaining_2970_);
lean_inc(v_goals_2969_);
v___x_2980_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2969_, v_remaining_2970_, v___x_2979_, v___x_2979_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v_fst_2982_; lean_object* v_snd_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_4191_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v_fst_2982_ = lean_ctor_get(v_a_2981_, 0);
v_snd_2983_ = lean_ctor_get(v_a_2981_, 1);
v_isSharedCheck_4191_ = !lean_is_exclusive(v_a_2981_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_2985_ = v_a_2981_;
v_isShared_2986_ = v_isSharedCheck_4191_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_snd_2983_);
lean_inc(v_fst_2982_);
lean_dec(v_a_2981_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_4191_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
uint8_t v___x_2987_; 
v___x_2987_ = l_List_isEmpty___redArg(v_fst_2982_);
if (v___x_2987_ == 0)
{
lean_object* v_options_2988_; lean_object* v_inheritedTraceOptions_2989_; uint8_t v_hasTrace_2990_; lean_object* v___f_2991_; 
lean_dec(v_remaining_2970_);
v_options_2988_ = lean_ctor_get(v_a_2973_, 2);
v_inheritedTraceOptions_2989_ = lean_ctor_get(v_a_2973_, 13);
v_hasTrace_2990_ = lean_ctor_get_uint8(v_options_2988_, sizeof(void*)*1);
lean_inc(v_orig_2968_);
lean_inc_ref(v_next_2967_);
lean_inc(v_trace_2966_);
lean_inc_ref(v_cfg_2965_);
v___f_2991_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2991_, 0, v_cfg_2965_);
lean_closure_set(v___f_2991_, 1, v_trace_2966_);
lean_closure_set(v___f_2991_, 2, v_next_2967_);
lean_closure_set(v___f_2991_, 3, v_orig_2968_);
if (v_hasTrace_2990_ == 0)
{
lean_object* v___x_2992_; 
lean_del_object(v___x_2985_);
v___x_2992_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2982_, v___f_2991_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3062_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3062_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3062_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v_fst_2997_; lean_object* v_snd_2998_; lean_object* v___x_2999_; lean_object* v_a_3001_; lean_object* v___y_3008_; lean_object* v___y_3011_; lean_object* v___y_3012_; uint8_t v___y_3013_; lean_object* v___y_3024_; lean_object* v_a_3039_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_fst_2997_ = lean_ctor_get(v_a_2993_, 0);
lean_inc(v_fst_2997_);
v_snd_2998_ = lean_ctor_get(v_a_2993_, 1);
lean_inc(v_snd_2998_);
lean_dec(v_a_2993_);
v___x_2999_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_2998_, v___x_2979_);
v___x_3057_ = lean_box(0);
v___x_3058_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_hasTrace_2990_, v_goals_2969_, v___x_3057_, v_a_2972_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v___x_3060_ = l_List_reverse___redArg(v_a_3059_);
v_a_3039_ = v___x_3060_;
goto v___jp_3038_;
}
else
{
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3061_; 
v_a_3061_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3058_, 1);
v_a_3039_ = v_a_3061_;
goto v___jp_3038_;
}
else
{
lean_dec(v___x_2999_);
lean_dec(v_fst_2997_);
lean_del_object(v___x_2995_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
return v___x_3058_;
}
}
v___jp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3002_ = l_List_appendTR___redArg(v___x_2999_, v_fst_2997_);
v___x_3003_ = l_List_appendTR___redArg(v___x_3002_, v_a_3001_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v___x_3003_);
v___x_3005_ = v___x_2995_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
v___jp_3007_:
{
if (lean_obj_tag(v___y_3008_) == 0)
{
lean_object* v_a_3009_; 
v_a_3009_ = lean_ctor_get(v___y_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___y_3008_, 1);
v_a_3001_ = v_a_3009_;
goto v___jp_3000_;
}
else
{
lean_dec(v___x_2999_);
lean_dec(v_fst_2997_);
lean_del_object(v___x_2995_);
return v___y_3008_;
}
}
v___jp_3010_:
{
if (v___y_3013_ == 0)
{
lean_object* v___x_3014_; 
lean_dec_ref(v___y_3012_);
v___x_3014_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3011_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3011_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_dec_ref_known(v___x_3014_, 1);
v_a_3001_ = v_snd_2983_;
goto v___jp_3000_;
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v___x_2999_);
lean_dec(v_fst_2997_);
lean_del_object(v___x_2995_);
lean_dec(v_snd_2983_);
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3014_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
lean_dec_ref(v___y_3011_);
lean_dec(v_snd_2983_);
v___y_3008_ = v___y_3012_;
goto v___jp_3007_;
}
}
v___jp_3023_:
{
uint8_t v___x_3025_; 
v___x_3025_ = l_List_isEmpty___redArg(v_fst_2997_);
lean_dec(v_fst_2997_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
lean_dec(v___y_3024_);
lean_dec(v___x_2999_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v___x_3026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3027_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3026_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3027_;
}
else
{
lean_object* v___x_3028_; 
v___x_3028_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3024_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3037_; 
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3031_ = v___x_3028_;
v_isShared_3032_ = v_isSharedCheck_3037_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3028_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3037_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___x_3033_ = l_List_appendTR___redArg(v___x_2999_, v_a_3029_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3033_);
v___x_3035_ = v___x_3031_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
else
{
lean_dec(v___x_2999_);
return v___x_3028_;
}
}
}
v___jp_3038_:
{
uint8_t v_commitIndependentGoals_3040_; lean_object* v___x_3041_; 
v_commitIndependentGoals_3040_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___x_2999_);
v___x_3041_ = l_List_appendTR___redArg(v_a_3039_, v___x_2999_);
if (v_commitIndependentGoals_3040_ == 0)
{
lean_del_object(v___x_2995_);
v___y_3024_ = v___x_3041_;
goto v___jp_3023_;
}
else
{
uint8_t v___x_3042_; 
v___x_3042_ = l_List_isEmpty___redArg(v___x_2999_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; 
v___x_3043_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3045_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
lean_inc(v_snd_2983_);
v___x_3045_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___x_3041_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_dec(v_a_3044_);
lean_dec(v_snd_2983_);
v___y_3008_ = v___x_3045_;
goto v___jp_3007_;
}
else
{
lean_object* v_a_3046_; uint8_t v___x_3047_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
v___x_3047_ = l_Lean_Exception_isInterrupt(v_a_3046_);
if (v___x_3047_ == 0)
{
uint8_t v___x_3048_; 
v___x_3048_ = l_Lean_Exception_isRuntime(v_a_3046_);
v___y_3011_ = v_a_3044_;
v___y_3012_ = v___x_3045_;
v___y_3013_ = v___x_3048_;
goto v___jp_3010_;
}
else
{
lean_dec(v_a_3046_);
v___y_3011_ = v_a_3044_;
v___y_3012_ = v___x_3045_;
v___y_3013_ = v___x_3047_;
goto v___jp_3010_;
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec(v___x_3041_);
lean_dec(v___x_2999_);
lean_dec(v_fst_2997_);
lean_del_object(v___x_2995_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_3049_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3043_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3043_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
else
{
lean_del_object(v___x_2995_);
v___y_3024_ = v___x_3041_;
goto v___jp_3023_;
}
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v_snd_2983_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_3063_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_2992_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_2992_);
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
lean_object* v___f_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v_a_3079_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v_a_3096_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v_a_3103_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v_a_3109_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; uint8_t v___y_3126_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; uint8_t v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v_a_3155_; uint8_t v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v_a_3174_; uint8_t v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3182_; lean_object* v_a_3183_; uint8_t v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v_a_3194_; uint8_t v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3210_; uint8_t v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; uint8_t v___y_3220_; uint8_t v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; uint8_t v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; uint8_t v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; uint8_t v___y_3269_; uint8_t v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; uint8_t v___y_3283_; lean_object* v_a_3284_; lean_object* v___y_3289_; uint8_t v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v_a_3295_; lean_object* v___y_3305_; uint8_t v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v_a_3311_; lean_object* v___y_3314_; uint8_t v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v_a_3322_; lean_object* v___y_3326_; uint8_t v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v_a_3332_; lean_object* v___y_3335_; uint8_t v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3345_; lean_object* v___y_3346_; uint8_t v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3357_; uint8_t v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3369_; uint8_t v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; uint8_t v___y_3379_; lean_object* v___y_3383_; lean_object* v___y_3384_; uint8_t v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3400_; uint8_t v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; uint8_t v___y_3408_; lean_object* v_a_3409_; uint8_t v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; uint8_t v___y_3423_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; uint8_t v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; uint8_t v___y_3460_; lean_object* v___y_3461_; lean_object* v_a_3462_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v_a_3469_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v_a_3481_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v_a_3486_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; uint8_t v___y_3499_; lean_object* v___y_3500_; lean_object* v_a_3501_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; uint8_t v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v_a_3520_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; uint8_t v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v_a_3529_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; uint8_t v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v_a_3540_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; uint8_t v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; uint8_t v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; uint8_t v___y_3566_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; uint8_t v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; uint8_t v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; uint8_t v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; uint8_t v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; uint8_t v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; uint8_t v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; uint8_t v___y_3628_; lean_object* v___y_3629_; lean_object* v_a_3630_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; uint8_t v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v_a_3641_; lean_object* v___y_3651_; lean_object* v___y_3652_; uint8_t v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v_a_3657_; lean_object* v___y_3660_; lean_object* v___y_3661_; uint8_t v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v_a_3666_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; uint8_t v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v_a_3677_; lean_object* v___y_3681_; lean_object* v___y_3682_; uint8_t v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; uint8_t v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; uint8_t v___y_3703_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; uint8_t v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; uint8_t v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; uint8_t v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; uint8_t v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; uint8_t v___y_3755_; lean_object* v___y_3760_; lean_object* v___y_3761_; uint8_t v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v___y_3766_; uint8_t v___y_3767_; lean_object* v___y_3768_; lean_object* v_a_3769_; lean_object* v___y_3774_; lean_object* v___y_3775_; uint8_t v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; uint8_t v___y_3781_; lean_object* v___y_3799_; lean_object* v___y_3800_; uint8_t v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v_a_3819_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; uint8_t v___y_3837_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; uint8_t v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v_a_3859_; 
lean_inc(v_snd_2983_);
lean_inc(v_fst_2982_);
v___f_3071_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3071_, 0, v_fst_2982_);
lean_closure_set(v___f_3071_, 1, v_snd_2983_);
v___x_3072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_3073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_2966_);
v___x_3074_ = l_Lean_Name_append(v___x_3073_, v_trace_2966_);
v___x_3075_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2989_, v_options_2988_, v___x_3074_);
lean_dec(v___x_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3908_; uint8_t v___x_3909_; 
v___x_3908_ = l_Lean_trace_profiler;
v___x_3909_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2988_, v___x_3908_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; 
lean_dec_ref(v___f_3071_);
lean_del_object(v___x_2985_);
v___x_3910_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2982_, v___f_2991_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_4179_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_4179_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_4179_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v_fst_3915_; lean_object* v_snd_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_4178_; 
v_fst_3915_ = lean_ctor_get(v_a_3911_, 0);
v_snd_3916_ = lean_ctor_get(v_a_3911_, 1);
v_isSharedCheck_4178_ = !lean_is_exclusive(v_a_3911_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_3918_ = v_a_3911_;
v_isShared_3919_ = v_isSharedCheck_4178_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_snd_3916_);
lean_inc(v_fst_3915_);
lean_dec(v_a_3911_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_4178_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3920_; lean_object* v___y_3922_; lean_object* v_a_3935_; lean_object* v___y_3942_; lean_object* v___y_3945_; lean_object* v___y_3946_; uint8_t v___y_3947_; lean_object* v___y_3958_; lean_object* v_a_3974_; lean_object* v___f_3978_; lean_object* v___x_3979_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v_a_3983_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v_a_4000_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v_a_4005_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v_a_4010_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; uint8_t v___y_4024_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4045_; lean_object* v___y_4046_; uint8_t v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; uint8_t v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v_a_4062_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v_a_4069_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v_a_4081_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v_a_4086_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v_a_4092_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; uint8_t v___y_4104_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; uint8_t v___y_4114_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; uint8_t v___y_4127_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; uint8_t v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v_a_4145_; 
v___x_3920_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3916_, v___x_2979_);
lean_inc(v___x_3920_);
lean_inc(v_fst_3915_);
v___f_3978_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3978_, 0, v_fst_3915_);
lean_closure_set(v___f_3978_, 1, v___x_3920_);
v___x_3979_ = lean_box(0);
if (v___x_3075_ == 0)
{
if (v___x_3909_ == 0)
{
lean_object* v___x_4174_; 
lean_dec_ref(v___f_3978_);
lean_del_object(v___x_3918_);
v___x_4174_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2990_, v___x_3909_, v_goals_2969_, v___x_3979_, v_a_2972_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4176_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4175_);
lean_dec_ref_known(v___x_4174_, 1);
v___x_4176_ = l_List_reverse___redArg(v_a_4175_);
v_a_3974_ = v___x_4176_;
goto v___jp_3973_;
}
else
{
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4177_; 
v_a_4177_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4177_);
lean_dec_ref_known(v___x_4174_, 1);
v_a_3974_ = v_a_4177_;
goto v___jp_3973_;
}
else
{
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
lean_del_object(v___x_3913_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
return v___x_4174_;
}
}
}
else
{
lean_del_object(v___x_3913_);
goto v___jp_4149_;
}
}
else
{
lean_del_object(v___x_3913_);
goto v___jp_4149_;
}
v___jp_3921_:
{
uint8_t v___x_3923_; 
v___x_3923_ = l_List_isEmpty___redArg(v_fst_3915_);
lean_dec(v_fst_3915_);
if (v___x_3923_ == 0)
{
lean_dec(v___y_3922_);
lean_dec(v___x_3920_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
goto v___jp_2976_;
}
else
{
if (v___x_3909_ == 0)
{
lean_object* v___x_3924_; 
v___x_3924_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3922_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3933_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3927_ = v___x_3924_;
v_isShared_3928_ = v_isSharedCheck_3933_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3924_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3933_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3929_ = l_List_appendTR___redArg(v___x_3920_, v_a_3925_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v___x_3929_);
v___x_3931_ = v___x_3927_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3929_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
else
{
lean_dec(v___x_3920_);
return v___x_3924_;
}
}
else
{
lean_dec(v___y_3922_);
lean_dec(v___x_3920_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
goto v___jp_2976_;
}
}
}
v___jp_3934_:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3936_ = l_List_appendTR___redArg(v___x_3920_, v_fst_3915_);
v___x_3937_ = l_List_appendTR___redArg(v___x_3936_, v_a_3935_);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3937_);
v___x_3939_ = v___x_3913_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
v___jp_3941_:
{
if (lean_obj_tag(v___y_3942_) == 0)
{
lean_object* v_a_3943_; 
v_a_3943_ = lean_ctor_get(v___y_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___y_3942_, 1);
v_a_3935_ = v_a_3943_;
goto v___jp_3934_;
}
else
{
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
lean_del_object(v___x_3913_);
return v___y_3942_;
}
}
v___jp_3944_:
{
if (v___y_3947_ == 0)
{
lean_object* v___x_3948_; 
lean_dec_ref(v___y_3946_);
v___x_3948_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3945_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3945_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_dec_ref_known(v___x_3948_, 1);
v_a_3935_ = v_snd_2983_;
goto v___jp_3934_;
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
lean_del_object(v___x_3913_);
lean_dec(v_snd_2983_);
v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3948_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3948_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
else
{
lean_dec_ref(v___y_3945_);
lean_dec(v_snd_2983_);
v___y_3942_ = v___y_3946_;
goto v___jp_3941_;
}
}
v___jp_3957_:
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v___x_3961_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v___x_3959_, 1);
lean_inc(v_snd_2983_);
v___x_3961_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3958_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_dec(v_a_3960_);
lean_dec(v_snd_2983_);
v___y_3942_ = v___x_3961_;
goto v___jp_3941_;
}
else
{
lean_object* v_a_3962_; uint8_t v___x_3963_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
v___x_3963_ = l_Lean_Exception_isInterrupt(v_a_3962_);
if (v___x_3963_ == 0)
{
uint8_t v___x_3964_; 
v___x_3964_ = l_Lean_Exception_isRuntime(v_a_3962_);
v___y_3945_ = v_a_3960_;
v___y_3946_ = v___x_3961_;
v___y_3947_ = v___x_3964_;
goto v___jp_3944_;
}
else
{
lean_dec(v_a_3962_);
v___y_3945_ = v_a_3960_;
v___y_3946_ = v___x_3961_;
v___y_3947_ = v___x_3963_;
goto v___jp_3944_;
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec(v___y_3958_);
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
lean_del_object(v___x_3913_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_3965_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3959_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3959_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
v___jp_3973_:
{
uint8_t v_commitIndependentGoals_3975_; lean_object* v___x_3976_; 
v_commitIndependentGoals_3975_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___x_3920_);
v___x_3976_ = l_List_appendTR___redArg(v_a_3974_, v___x_3920_);
if (v_commitIndependentGoals_3975_ == 0)
{
lean_del_object(v___x_3913_);
v___y_3922_ = v___x_3976_;
goto v___jp_3921_;
}
else
{
uint8_t v___x_3977_; 
v___x_3977_ = l_List_isEmpty___redArg(v___x_3920_);
if (v___x_3977_ == 0)
{
v___y_3958_ = v___x_3976_;
goto v___jp_3957_;
}
else
{
if (v___x_3909_ == 0)
{
lean_del_object(v___x_3913_);
v___y_3922_ = v___x_3976_;
goto v___jp_3921_;
}
else
{
v___y_3958_ = v___x_3976_;
goto v___jp_3957_;
}
}
}
}
v___jp_3980_:
{
lean_object* v___x_3984_; double v___x_3985_; double v___x_3986_; double v___x_3987_; double v___x_3988_; double v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3993_; 
v___x_3984_ = lean_io_mono_nanos_now();
v___x_3985_ = lean_float_of_nat(v___y_3982_);
v___x_3986_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3987_ = lean_float_div(v___x_3985_, v___x_3986_);
v___x_3988_ = lean_float_of_nat(v___x_3984_);
v___x_3989_ = lean_float_div(v___x_3988_, v___x_3986_);
v___x_3990_ = lean_box_float(v___x_3987_);
v___x_3991_ = lean_box_float(v___x_3989_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 1, v___x_3991_);
lean_ctor_set(v___x_3918_, 0, v___x_3990_);
v___x_3993_ = v___x_3918_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3990_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v___x_3991_);
v___x_3993_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3994_, 0, v_a_3983_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
v___x_3995_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2990_, v___x_3072_, v_options_2988_, v___x_3075_, v___y_3981_, v___f_3978_, v___x_3994_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3995_;
}
}
v___jp_3997_:
{
lean_object* v___x_4001_; 
v___x_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4001_, 0, v_a_4000_);
v___y_3981_ = v___y_3998_;
v___y_3982_ = v___y_3999_;
v_a_3983_ = v___x_4001_;
goto v___jp_3980_;
}
v___jp_4002_:
{
lean_object* v___x_4006_; 
v___x_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4006_, 0, v_a_4005_);
v___y_3981_ = v___y_4003_;
v___y_3982_ = v___y_4004_;
v_a_3983_ = v___x_4006_;
goto v___jp_3980_;
}
v___jp_4007_:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4011_ = l_List_appendTR___redArg(v___x_3920_, v_fst_3915_);
v___x_4012_ = l_List_appendTR___redArg(v___x_4011_, v_a_4010_);
v___y_4003_ = v___y_4008_;
v___y_4004_ = v___y_4009_;
v_a_4005_ = v___x_4012_;
goto v___jp_4002_;
}
v___jp_4013_:
{
if (lean_obj_tag(v___y_4016_) == 0)
{
lean_object* v_a_4017_; 
v_a_4017_ = lean_ctor_get(v___y_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___y_4016_, 1);
v___y_4008_ = v___y_4014_;
v___y_4009_ = v___y_4015_;
v_a_4010_ = v_a_4017_;
goto v___jp_4007_;
}
else
{
lean_object* v_a_4018_; 
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
v_a_4018_ = lean_ctor_get(v___y_4016_, 0);
lean_inc(v_a_4018_);
lean_dec_ref_known(v___y_4016_, 1);
v___y_3998_ = v___y_4014_;
v___y_3999_ = v___y_4015_;
v_a_4000_ = v_a_4018_;
goto v___jp_3997_;
}
}
v___jp_4019_:
{
if (v___y_4024_ == 0)
{
lean_object* v___x_4025_; 
lean_dec_ref(v___y_4020_);
v___x_4025_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4021_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_4021_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_dec_ref_known(v___x_4025_, 1);
v___y_4008_ = v___y_4022_;
v___y_4009_ = v___y_4023_;
v_a_4010_ = v_snd_2983_;
goto v___jp_4007_;
}
else
{
lean_object* v_a_4026_; 
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
lean_dec(v_snd_2983_);
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4025_, 1);
v___y_3998_ = v___y_4022_;
v___y_3999_ = v___y_4023_;
v_a_4000_ = v_a_4026_;
goto v___jp_3997_;
}
}
else
{
lean_dec_ref(v___y_4021_);
lean_dec(v_snd_2983_);
v___y_4014_ = v___y_4022_;
v___y_4015_ = v___y_4023_;
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
lean_inc(v_snd_2983_);
lean_inc(v_trace_2966_);
v___x_4033_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4030_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_dec(v_a_4032_);
lean_dec(v_snd_2983_);
v___y_4014_ = v___y_4028_;
v___y_4015_ = v___y_4029_;
v___y_4016_ = v___x_4033_;
goto v___jp_4013_;
}
else
{
lean_object* v_a_4034_; uint8_t v___x_4035_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
v___x_4035_ = l_Lean_Exception_isInterrupt(v_a_4034_);
if (v___x_4035_ == 0)
{
uint8_t v___x_4036_; 
v___x_4036_ = l_Lean_Exception_isRuntime(v_a_4034_);
v___y_4020_ = v___x_4033_;
v___y_4021_ = v_a_4032_;
v___y_4022_ = v___y_4028_;
v___y_4023_ = v___y_4029_;
v___y_4024_ = v___x_4036_;
goto v___jp_4019_;
}
else
{
lean_dec(v_a_4034_);
v___y_4020_ = v___x_4033_;
v___y_4021_ = v_a_4032_;
v___y_4022_ = v___y_4028_;
v___y_4023_ = v___y_4029_;
v___y_4024_ = v___x_4035_;
goto v___jp_4019_;
}
}
}
else
{
lean_object* v_a_4037_; 
lean_dec(v___y_4030_);
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_4037_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4031_, 1);
v___y_3998_ = v___y_4028_;
v___y_3999_ = v___y_4029_;
v_a_4000_ = v_a_4037_;
goto v___jp_3997_;
}
}
v___jp_4038_:
{
if (lean_obj_tag(v___y_4041_) == 0)
{
lean_object* v_a_4042_; 
v_a_4042_ = lean_ctor_get(v___y_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v___y_4041_, 1);
v___y_4003_ = v___y_4039_;
v___y_4004_ = v___y_4040_;
v_a_4005_ = v_a_4042_;
goto v___jp_4002_;
}
else
{
lean_object* v_a_4043_; 
v_a_4043_ = lean_ctor_get(v___y_4041_, 0);
lean_inc(v_a_4043_);
lean_dec_ref_known(v___y_4041_, 1);
v___y_3998_ = v___y_4039_;
v___y_3999_ = v___y_4040_;
v_a_4000_ = v_a_4043_;
goto v___jp_3997_;
}
}
v___jp_4044_:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4048_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4047_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_4039_ = v___y_4045_;
v___y_4040_ = v___y_4046_;
v___y_4041_ = v___x_4048_;
goto v___jp_4038_;
}
v___jp_4049_:
{
uint8_t v___x_4054_; 
v___x_4054_ = l_List_isEmpty___redArg(v_fst_3915_);
lean_dec(v_fst_3915_);
if (v___x_4054_ == 0)
{
lean_dec(v___y_4052_);
lean_dec(v___x_3920_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___y_4045_ = v___y_4051_;
v___y_4046_ = v___y_4053_;
goto v___jp_4044_;
}
else
{
if (v___y_4050_ == 0)
{
lean_object* v___x_4055_; 
lean_inc(v_trace_2966_);
v___x_4055_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4052_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4057_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___x_4055_, 1);
v___x_4057_ = l_List_appendTR___redArg(v___x_3920_, v_a_4056_);
v___y_4003_ = v___y_4051_;
v___y_4004_ = v___y_4053_;
v_a_4005_ = v___x_4057_;
goto v___jp_4002_;
}
else
{
lean_dec(v___x_3920_);
v___y_4039_ = v___y_4051_;
v___y_4040_ = v___y_4053_;
v___y_4041_ = v___x_4055_;
goto v___jp_4038_;
}
}
else
{
lean_dec(v___y_4052_);
lean_dec(v___x_3920_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___y_4045_ = v___y_4051_;
v___y_4046_ = v___y_4053_;
goto v___jp_4044_;
}
}
}
v___jp_4058_:
{
uint8_t v_commitIndependentGoals_4063_; lean_object* v___x_4064_; 
v_commitIndependentGoals_4063_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___x_3920_);
v___x_4064_ = l_List_appendTR___redArg(v_a_4062_, v___x_3920_);
if (v_commitIndependentGoals_4063_ == 0)
{
v___y_4050_ = v___y_4059_;
v___y_4051_ = v___y_4060_;
v___y_4052_ = v___x_4064_;
v___y_4053_ = v___y_4061_;
goto v___jp_4049_;
}
else
{
uint8_t v___x_4065_; 
v___x_4065_ = l_List_isEmpty___redArg(v___x_3920_);
if (v___x_4065_ == 0)
{
v___y_4028_ = v___y_4060_;
v___y_4029_ = v___y_4061_;
v___y_4030_ = v___x_4064_;
goto v___jp_4027_;
}
else
{
if (v___y_4059_ == 0)
{
v___y_4050_ = v___y_4059_;
v___y_4051_ = v___y_4060_;
v___y_4052_ = v___x_4064_;
v___y_4053_ = v___y_4061_;
goto v___jp_4049_;
}
else
{
v___y_4028_ = v___y_4060_;
v___y_4029_ = v___y_4061_;
v___y_4030_ = v___x_4064_;
goto v___jp_4027_;
}
}
}
}
v___jp_4066_:
{
lean_object* v___x_4070_; double v___x_4071_; double v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4070_ = lean_io_get_num_heartbeats();
v___x_4071_ = lean_float_of_nat(v___y_4068_);
v___x_4072_ = lean_float_of_nat(v___x_4070_);
v___x_4073_ = lean_box_float(v___x_4071_);
v___x_4074_ = lean_box_float(v___x_4072_);
v___x_4075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4073_);
lean_ctor_set(v___x_4075_, 1, v___x_4074_);
v___x_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4076_, 0, v_a_4069_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
v___x_4077_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2990_, v___x_3072_, v_options_2988_, v___x_3075_, v___y_4067_, v___f_3978_, v___x_4076_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_4077_;
}
v___jp_4078_:
{
lean_object* v___x_4082_; 
v___x_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4082_, 0, v_a_4081_);
v___y_4067_ = v___y_4080_;
v___y_4068_ = v___y_4079_;
v_a_4069_ = v___x_4082_;
goto v___jp_4066_;
}
v___jp_4083_:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = l_List_appendTR___redArg(v___x_3920_, v_fst_3915_);
v___x_4088_ = l_List_appendTR___redArg(v___x_4087_, v_a_4086_);
v___y_4079_ = v___y_4085_;
v___y_4080_ = v___y_4084_;
v_a_4081_ = v___x_4088_;
goto v___jp_4078_;
}
v___jp_4089_:
{
lean_object* v___x_4093_; 
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v_a_4092_);
v___y_4067_ = v___y_4091_;
v___y_4068_ = v___y_4090_;
v_a_4069_ = v___x_4093_;
goto v___jp_4066_;
}
v___jp_4094_:
{
if (lean_obj_tag(v___y_4097_) == 0)
{
lean_object* v_a_4098_; 
v_a_4098_ = lean_ctor_get(v___y_4097_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___y_4097_, 1);
v___y_4079_ = v___y_4096_;
v___y_4080_ = v___y_4095_;
v_a_4081_ = v_a_4098_;
goto v___jp_4078_;
}
else
{
lean_object* v_a_4099_; 
v_a_4099_ = lean_ctor_get(v___y_4097_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___y_4097_, 1);
v___y_4090_ = v___y_4096_;
v___y_4091_ = v___y_4095_;
v_a_4092_ = v_a_4099_;
goto v___jp_4089_;
}
}
v___jp_4100_:
{
if (v___y_4104_ == 0)
{
lean_object* v___x_4105_; 
lean_inc(v_trace_2966_);
v___x_4105_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4101_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; lean_object* v___x_4107_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
lean_inc(v_a_4106_);
lean_dec_ref_known(v___x_4105_, 1);
v___x_4107_ = l_List_appendTR___redArg(v___x_3920_, v_a_4106_);
v___y_4079_ = v___y_4103_;
v___y_4080_ = v___y_4102_;
v_a_4081_ = v___x_4107_;
goto v___jp_4078_;
}
else
{
lean_dec(v___x_3920_);
v___y_4095_ = v___y_4102_;
v___y_4096_ = v___y_4103_;
v___y_4097_ = v___x_4105_;
goto v___jp_4094_;
}
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
lean_dec(v___y_4101_);
lean_dec(v___x_3920_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_4108_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4109_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4108_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_4095_ = v___y_4102_;
v___y_4096_ = v___y_4103_;
v___y_4097_ = v___x_4109_;
goto v___jp_4094_;
}
}
v___jp_4110_:
{
uint8_t v___x_4115_; 
v___x_4115_ = l_List_isEmpty___redArg(v_fst_3915_);
lean_dec(v_fst_3915_);
if (v___x_4115_ == 0)
{
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4113_;
v___y_4103_ = v___y_4112_;
v___y_4104_ = v___y_4114_;
goto v___jp_4100_;
}
else
{
v___y_4101_ = v___y_4111_;
v___y_4102_ = v___y_4113_;
v___y_4103_ = v___y_4112_;
v___y_4104_ = v___x_3909_;
goto v___jp_4100_;
}
}
v___jp_4116_:
{
if (lean_obj_tag(v___y_4119_) == 0)
{
lean_object* v_a_4120_; 
v_a_4120_ = lean_ctor_get(v___y_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___y_4119_, 1);
v___y_4084_ = v___y_4118_;
v___y_4085_ = v___y_4117_;
v_a_4086_ = v_a_4120_;
goto v___jp_4083_;
}
else
{
lean_object* v_a_4121_; 
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
v_a_4121_ = lean_ctor_get(v___y_4119_, 0);
lean_inc(v_a_4121_);
lean_dec_ref_known(v___y_4119_, 1);
v___y_4090_ = v___y_4117_;
v___y_4091_ = v___y_4118_;
v_a_4092_ = v_a_4121_;
goto v___jp_4089_;
}
}
v___jp_4122_:
{
if (v___y_4127_ == 0)
{
lean_object* v___x_4128_; 
lean_dec_ref(v___y_4126_);
v___x_4128_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4123_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_4123_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_dec_ref_known(v___x_4128_, 1);
v___y_4084_ = v___y_4125_;
v___y_4085_ = v___y_4124_;
v_a_4086_ = v_snd_2983_;
goto v___jp_4083_;
}
else
{
lean_object* v_a_4129_; 
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
lean_dec(v_snd_2983_);
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v___x_4128_, 1);
v___y_4090_ = v___y_4124_;
v___y_4091_ = v___y_4125_;
v_a_4092_ = v_a_4129_;
goto v___jp_4089_;
}
}
else
{
lean_dec_ref(v___y_4123_);
lean_dec(v_snd_2983_);
v___y_4117_ = v___y_4124_;
v___y_4118_ = v___y_4125_;
v___y_4119_ = v___y_4126_;
goto v___jp_4116_;
}
}
v___jp_4130_:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4136_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4134_, 1);
lean_inc(v_snd_2983_);
lean_inc(v_trace_2966_);
v___x_4136_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4131_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_dec(v_a_4135_);
lean_dec(v_snd_2983_);
v___y_4117_ = v___y_4133_;
v___y_4118_ = v___y_4132_;
v___y_4119_ = v___x_4136_;
goto v___jp_4116_;
}
else
{
lean_object* v_a_4137_; uint8_t v___x_4138_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
v___x_4138_ = l_Lean_Exception_isInterrupt(v_a_4137_);
if (v___x_4138_ == 0)
{
uint8_t v___x_4139_; 
v___x_4139_ = l_Lean_Exception_isRuntime(v_a_4137_);
v___y_4123_ = v_a_4135_;
v___y_4124_ = v___y_4133_;
v___y_4125_ = v___y_4132_;
v___y_4126_ = v___x_4136_;
v___y_4127_ = v___x_4139_;
goto v___jp_4122_;
}
else
{
lean_dec(v_a_4137_);
v___y_4123_ = v_a_4135_;
v___y_4124_ = v___y_4133_;
v___y_4125_ = v___y_4132_;
v___y_4126_ = v___x_4136_;
v___y_4127_ = v___x_4138_;
goto v___jp_4122_;
}
}
}
else
{
lean_object* v_a_4140_; 
lean_dec(v___y_4131_);
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_4140_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4134_, 1);
v___y_4090_ = v___y_4133_;
v___y_4091_ = v___y_4132_;
v_a_4092_ = v_a_4140_;
goto v___jp_4089_;
}
}
v___jp_4141_:
{
uint8_t v_commitIndependentGoals_4146_; lean_object* v___x_4147_; 
v_commitIndependentGoals_4146_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___x_3920_);
v___x_4147_ = l_List_appendTR___redArg(v_a_4145_, v___x_3920_);
if (v_commitIndependentGoals_4146_ == 0)
{
v___y_4111_ = v___x_4147_;
v___y_4112_ = v___y_4143_;
v___y_4113_ = v___y_4144_;
v___y_4114_ = v___y_4142_;
goto v___jp_4110_;
}
else
{
uint8_t v___x_4148_; 
v___x_4148_ = l_List_isEmpty___redArg(v___x_3920_);
if (v___x_4148_ == 0)
{
v___y_4131_ = v___x_4147_;
v___y_4132_ = v___y_4144_;
v___y_4133_ = v___y_4143_;
goto v___jp_4130_;
}
else
{
if (v___x_3909_ == 0)
{
v___y_4111_ = v___x_4147_;
v___y_4112_ = v___y_4143_;
v___y_4113_ = v___y_4144_;
v___y_4114_ = v___y_4142_;
goto v___jp_4110_;
}
else
{
v___y_4131_ = v___x_4147_;
v___y_4132_ = v___y_4144_;
v___y_4133_ = v___y_4143_;
goto v___jp_4130_;
}
}
}
}
v___jp_4149_:
{
lean_object* v___x_4150_; 
v___x_4150_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2974_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4151_);
lean_dec_ref_known(v___x_4150_, 1);
v___x_4152_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4153_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2988_, v___x_4152_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = lean_io_mono_nanos_now();
v___x_4155_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2990_, v___x_3909_, v_goals_2969_, v___x_3979_, v_a_2972_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4157_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
v___x_4157_ = l_List_reverse___redArg(v_a_4156_);
v___y_4059_ = v___x_4153_;
v___y_4060_ = v_a_4151_;
v___y_4061_ = v___x_4154_;
v_a_4062_ = v___x_4157_;
goto v___jp_4058_;
}
else
{
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4158_; 
v_a_4158_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4155_, 1);
v___y_4059_ = v___x_4153_;
v___y_4060_ = v_a_4151_;
v___y_4061_ = v___x_4154_;
v_a_4062_ = v_a_4158_;
goto v___jp_4058_;
}
else
{
lean_object* v_a_4159_; 
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_4159_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4159_);
lean_dec_ref_known(v___x_4155_, 1);
v___y_3998_ = v_a_4151_;
v___y_3999_ = v___x_4154_;
v_a_4000_ = v_a_4159_;
goto v___jp_3997_;
}
}
}
else
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
lean_del_object(v___x_3918_);
v___x_4160_ = lean_io_get_num_heartbeats();
v___x_4161_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2990_, v___x_3909_, v_goals_2969_, v___x_3979_, v_a_2972_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4163_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v___x_4161_, 1);
v___x_4163_ = l_List_reverse___redArg(v_a_4162_);
v___y_4142_ = v___x_4153_;
v___y_4143_ = v___x_4160_;
v___y_4144_ = v_a_4151_;
v_a_4145_ = v___x_4163_;
goto v___jp_4141_;
}
else
{
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4164_; 
v_a_4164_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4161_, 1);
v___y_4142_ = v___x_4153_;
v___y_4143_ = v___x_4160_;
v___y_4144_ = v_a_4151_;
v_a_4145_ = v_a_4164_;
goto v___jp_4141_;
}
else
{
lean_object* v_a_4165_; 
lean_dec(v___x_3920_);
lean_dec(v_fst_3915_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_4165_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4161_, 1);
v___y_4090_ = v___x_4160_;
v___y_4091_ = v_a_4151_;
v_a_4092_ = v_a_4165_;
goto v___jp_4089_;
}
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec_ref(v___f_3978_);
lean_dec(v___x_3920_);
lean_del_object(v___x_3918_);
lean_dec(v_fst_3915_);
lean_dec(v_snd_2983_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_4166_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4150_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4150_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec(v_snd_2983_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_4180_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_3910_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_3910_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
else
{
goto v___jp_3863_;
}
}
else
{
goto v___jp_3863_;
}
v___jp_3076_:
{
lean_object* v___x_3080_; double v___x_3081_; double v___x_3082_; double v___x_3083_; double v___x_3084_; double v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3080_ = lean_io_mono_nanos_now();
v___x_3081_ = lean_float_of_nat(v___y_3078_);
v___x_3082_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3083_ = lean_float_div(v___x_3081_, v___x_3082_);
v___x_3084_ = lean_float_of_nat(v___x_3080_);
v___x_3085_ = lean_float_div(v___x_3084_, v___x_3082_);
v___x_3086_ = lean_box_float(v___x_3083_);
v___x_3087_ = lean_box_float(v___x_3085_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 1, v___x_3087_);
lean_ctor_set(v___x_2985_, 0, v___x_3086_);
v___x_3089_ = v___x_2985_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v_a_3079_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
v___x_3091_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2990_, v___x_3072_, v_options_2988_, v___x_3075_, v___y_3077_, v___f_3071_, v___x_3090_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3091_;
}
}
v___jp_3093_:
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3097_, 0, v_a_3096_);
v___y_3077_ = v___y_3094_;
v___y_3078_ = v___y_3095_;
v_a_3079_ = v___x_3097_;
goto v___jp_3076_;
}
v___jp_3098_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = l_List_appendTR___redArg(v___y_3100_, v___y_3102_);
v___x_3105_ = l_List_appendTR___redArg(v___x_3104_, v_a_3103_);
v___y_3094_ = v___y_3099_;
v___y_3095_ = v___y_3101_;
v_a_3096_ = v___x_3105_;
goto v___jp_3093_;
}
v___jp_3106_:
{
lean_object* v___x_3110_; 
v___x_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3110_, 0, v_a_3109_);
v___y_3077_ = v___y_3107_;
v___y_3078_ = v___y_3108_;
v_a_3079_ = v___x_3110_;
goto v___jp_3076_;
}
v___jp_3111_:
{
if (lean_obj_tag(v___y_3116_) == 0)
{
lean_object* v_a_3117_; 
v_a_3117_ = lean_ctor_get(v___y_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___y_3116_, 1);
v___y_3099_ = v___y_3112_;
v___y_3100_ = v___y_3113_;
v___y_3101_ = v___y_3114_;
v___y_3102_ = v___y_3115_;
v_a_3103_ = v_a_3117_;
goto v___jp_3098_;
}
else
{
lean_object* v_a_3118_; 
lean_dec(v___y_3115_);
lean_dec(v___y_3113_);
v_a_3118_ = lean_ctor_get(v___y_3116_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___y_3116_, 1);
v___y_3107_ = v___y_3112_;
v___y_3108_ = v___y_3114_;
v_a_3109_ = v_a_3118_;
goto v___jp_3106_;
}
}
v___jp_3119_:
{
if (v___y_3126_ == 0)
{
lean_object* v___x_3127_; 
lean_dec_ref(v___y_3120_);
v___x_3127_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3122_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3122_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_dec_ref_known(v___x_3127_, 1);
v___y_3099_ = v___y_3121_;
v___y_3100_ = v___y_3123_;
v___y_3101_ = v___y_3124_;
v___y_3102_ = v___y_3125_;
v_a_3103_ = v_snd_2983_;
goto v___jp_3098_;
}
else
{
lean_object* v_a_3128_; 
lean_dec(v___y_3125_);
lean_dec(v___y_3123_);
lean_dec(v_snd_2983_);
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3127_, 1);
v___y_3107_ = v___y_3121_;
v___y_3108_ = v___y_3124_;
v_a_3109_ = v_a_3128_;
goto v___jp_3106_;
}
}
else
{
lean_dec_ref(v___y_3122_);
lean_dec(v_snd_2983_);
v___y_3112_ = v___y_3121_;
v___y_3113_ = v___y_3123_;
v___y_3114_ = v___y_3124_;
v___y_3115_ = v___y_3125_;
v___y_3116_ = v___y_3120_;
goto v___jp_3111_;
}
}
v___jp_3129_:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3137_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___x_3135_, 1);
lean_inc(v_snd_2983_);
lean_inc(v_trace_2966_);
v___x_3137_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3131_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_dec(v_a_3136_);
lean_dec(v_snd_2983_);
v___y_3112_ = v___y_3130_;
v___y_3113_ = v___y_3132_;
v___y_3114_ = v___y_3133_;
v___y_3115_ = v___y_3134_;
v___y_3116_ = v___x_3137_;
goto v___jp_3111_;
}
else
{
lean_object* v_a_3138_; uint8_t v___x_3139_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
v___x_3139_ = l_Lean_Exception_isInterrupt(v_a_3138_);
if (v___x_3139_ == 0)
{
uint8_t v___x_3140_; 
v___x_3140_ = l_Lean_Exception_isRuntime(v_a_3138_);
v___y_3120_ = v___x_3137_;
v___y_3121_ = v___y_3130_;
v___y_3122_ = v_a_3136_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___y_3133_;
v___y_3125_ = v___y_3134_;
v___y_3126_ = v___x_3140_;
goto v___jp_3119_;
}
else
{
lean_dec(v_a_3138_);
v___y_3120_ = v___x_3137_;
v___y_3121_ = v___y_3130_;
v___y_3122_ = v_a_3136_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___y_3133_;
v___y_3125_ = v___y_3134_;
v___y_3126_ = v___x_3139_;
goto v___jp_3119_;
}
}
}
else
{
lean_object* v_a_3141_; 
lean_dec(v___y_3134_);
lean_dec(v___y_3132_);
lean_dec(v___y_3131_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3141_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3135_, 1);
v___y_3107_ = v___y_3130_;
v___y_3108_ = v___y_3133_;
v_a_3109_ = v_a_3141_;
goto v___jp_3106_;
}
}
v___jp_3142_:
{
if (lean_obj_tag(v___y_3145_) == 0)
{
lean_object* v_a_3146_; 
v_a_3146_ = lean_ctor_get(v___y_3145_, 0);
lean_inc(v_a_3146_);
lean_dec_ref_known(v___y_3145_, 1);
v___y_3094_ = v___y_3143_;
v___y_3095_ = v___y_3144_;
v_a_3096_ = v_a_3146_;
goto v___jp_3093_;
}
else
{
lean_object* v_a_3147_; 
v_a_3147_ = lean_ctor_get(v___y_3145_, 0);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___y_3145_, 1);
v___y_3107_ = v___y_3143_;
v___y_3108_ = v___y_3144_;
v_a_3109_ = v_a_3147_;
goto v___jp_3106_;
}
}
v___jp_3148_:
{
lean_object* v___x_3156_; double v___x_3157_; double v___x_3158_; double v___x_3159_; double v___x_3160_; double v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3156_ = lean_io_mono_nanos_now();
v___x_3157_ = lean_float_of_nat(v___y_3152_);
v___x_3158_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3159_ = lean_float_div(v___x_3157_, v___x_3158_);
v___x_3160_ = lean_float_of_nat(v___x_3156_);
v___x_3161_ = lean_float_div(v___x_3160_, v___x_3158_);
v___x_3162_ = lean_box_float(v___x_3159_);
v___x_3163_ = lean_box_float(v___x_3161_);
v___x_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v_a_3155_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
lean_inc(v_trace_2966_);
v___x_3166_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2990_, v___x_3072_, v_options_2988_, v___y_3149_, v___y_3154_, v___y_3153_, v___x_3165_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3143_ = v___y_3150_;
v___y_3144_ = v___y_3151_;
v___y_3145_ = v___x_3166_;
goto v___jp_3142_;
}
v___jp_3167_:
{
lean_object* v___x_3175_; 
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v_a_3174_);
v___y_3149_ = v___y_3168_;
v___y_3150_ = v___y_3169_;
v___y_3151_ = v___y_3171_;
v___y_3152_ = v___y_3170_;
v___y_3153_ = v___y_3172_;
v___y_3154_ = v___y_3173_;
v_a_3155_ = v___x_3175_;
goto v___jp_3148_;
}
v___jp_3176_:
{
lean_object* v___x_3184_; 
v___x_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3184_, 0, v_a_3183_);
v___y_3149_ = v___y_3177_;
v___y_3150_ = v___y_3178_;
v___y_3151_ = v___y_3180_;
v___y_3152_ = v___y_3179_;
v___y_3153_ = v___y_3181_;
v___y_3154_ = v___y_3182_;
v_a_3155_ = v___x_3184_;
goto v___jp_3148_;
}
v___jp_3185_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = l_List_appendTR___redArg(v___y_3188_, v___y_3192_);
v___x_3196_ = l_List_appendTR___redArg(v___x_3195_, v_a_3194_);
v___y_3177_ = v___y_3186_;
v___y_3178_ = v___y_3187_;
v___y_3179_ = v___y_3190_;
v___y_3180_ = v___y_3189_;
v___y_3181_ = v___y_3191_;
v___y_3182_ = v___y_3193_;
v_a_3183_ = v___x_3196_;
goto v___jp_3176_;
}
v___jp_3197_:
{
if (lean_obj_tag(v___y_3206_) == 0)
{
lean_object* v_a_3207_; 
v_a_3207_ = lean_ctor_get(v___y_3206_, 0);
lean_inc(v_a_3207_);
lean_dec_ref_known(v___y_3206_, 1);
v___y_3186_ = v___y_3198_;
v___y_3187_ = v___y_3199_;
v___y_3188_ = v___y_3200_;
v___y_3189_ = v___y_3202_;
v___y_3190_ = v___y_3201_;
v___y_3191_ = v___y_3203_;
v___y_3192_ = v___y_3204_;
v___y_3193_ = v___y_3205_;
v_a_3194_ = v_a_3207_;
goto v___jp_3185_;
}
else
{
lean_object* v_a_3208_; 
lean_dec(v___y_3204_);
lean_dec(v___y_3200_);
v_a_3208_ = lean_ctor_get(v___y_3206_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___y_3206_, 1);
v___y_3168_ = v___y_3198_;
v___y_3169_ = v___y_3199_;
v___y_3170_ = v___y_3201_;
v___y_3171_ = v___y_3202_;
v___y_3172_ = v___y_3203_;
v___y_3173_ = v___y_3205_;
v_a_3174_ = v_a_3208_;
goto v___jp_3167_;
}
}
v___jp_3209_:
{
if (v___y_3220_ == 0)
{
lean_object* v___x_3221_; 
lean_dec_ref(v___y_3210_);
v___x_3221_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3219_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3219_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_dec_ref_known(v___x_3221_, 1);
v___y_3186_ = v___y_3211_;
v___y_3187_ = v___y_3212_;
v___y_3188_ = v___y_3213_;
v___y_3189_ = v___y_3215_;
v___y_3190_ = v___y_3214_;
v___y_3191_ = v___y_3216_;
v___y_3192_ = v___y_3217_;
v___y_3193_ = v___y_3218_;
v_a_3194_ = v_snd_2983_;
goto v___jp_3185_;
}
else
{
lean_object* v_a_3222_; 
lean_dec(v___y_3217_);
lean_dec(v___y_3213_);
lean_dec(v_snd_2983_);
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3221_, 1);
v___y_3168_ = v___y_3211_;
v___y_3169_ = v___y_3212_;
v___y_3170_ = v___y_3214_;
v___y_3171_ = v___y_3215_;
v___y_3172_ = v___y_3216_;
v___y_3173_ = v___y_3218_;
v_a_3174_ = v_a_3222_;
goto v___jp_3167_;
}
}
else
{
lean_dec_ref(v___y_3219_);
lean_dec(v_snd_2983_);
v___y_3198_ = v___y_3211_;
v___y_3199_ = v___y_3212_;
v___y_3200_ = v___y_3213_;
v___y_3201_ = v___y_3214_;
v___y_3202_ = v___y_3215_;
v___y_3203_ = v___y_3216_;
v___y_3204_ = v___y_3217_;
v___y_3205_ = v___y_3218_;
v___y_3206_ = v___y_3210_;
goto v___jp_3197_;
}
}
v___jp_3223_:
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3235_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3234_);
lean_dec_ref_known(v___x_3233_, 1);
lean_inc(v_snd_2983_);
lean_inc(v_trace_2966_);
v___x_3235_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3230_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_dec(v_a_3234_);
lean_dec(v_snd_2983_);
v___y_3198_ = v___y_3224_;
v___y_3199_ = v___y_3225_;
v___y_3200_ = v___y_3226_;
v___y_3201_ = v___y_3228_;
v___y_3202_ = v___y_3227_;
v___y_3203_ = v___y_3229_;
v___y_3204_ = v___y_3231_;
v___y_3205_ = v___y_3232_;
v___y_3206_ = v___x_3235_;
goto v___jp_3197_;
}
else
{
lean_object* v_a_3236_; uint8_t v___x_3237_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
v___x_3237_ = l_Lean_Exception_isInterrupt(v_a_3236_);
if (v___x_3237_ == 0)
{
uint8_t v___x_3238_; 
v___x_3238_ = l_Lean_Exception_isRuntime(v_a_3236_);
v___y_3210_ = v___x_3235_;
v___y_3211_ = v___y_3224_;
v___y_3212_ = v___y_3225_;
v___y_3213_ = v___y_3226_;
v___y_3214_ = v___y_3228_;
v___y_3215_ = v___y_3227_;
v___y_3216_ = v___y_3229_;
v___y_3217_ = v___y_3231_;
v___y_3218_ = v___y_3232_;
v___y_3219_ = v_a_3234_;
v___y_3220_ = v___x_3238_;
goto v___jp_3209_;
}
else
{
lean_dec(v_a_3236_);
v___y_3210_ = v___x_3235_;
v___y_3211_ = v___y_3224_;
v___y_3212_ = v___y_3225_;
v___y_3213_ = v___y_3226_;
v___y_3214_ = v___y_3228_;
v___y_3215_ = v___y_3227_;
v___y_3216_ = v___y_3229_;
v___y_3217_ = v___y_3231_;
v___y_3218_ = v___y_3232_;
v___y_3219_ = v_a_3234_;
v___y_3220_ = v___x_3237_;
goto v___jp_3209_;
}
}
}
else
{
lean_object* v_a_3239_; 
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec(v___y_3226_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3239_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3233_, 1);
v___y_3168_ = v___y_3224_;
v___y_3169_ = v___y_3225_;
v___y_3170_ = v___y_3228_;
v___y_3171_ = v___y_3227_;
v___y_3172_ = v___y_3229_;
v___y_3173_ = v___y_3232_;
v_a_3174_ = v_a_3239_;
goto v___jp_3167_;
}
}
v___jp_3240_:
{
if (lean_obj_tag(v___y_3247_) == 0)
{
lean_object* v_a_3248_; 
v_a_3248_ = lean_ctor_get(v___y_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___y_3247_, 1);
v___y_3177_ = v___y_3241_;
v___y_3178_ = v___y_3242_;
v___y_3179_ = v___y_3244_;
v___y_3180_ = v___y_3243_;
v___y_3181_ = v___y_3245_;
v___y_3182_ = v___y_3246_;
v_a_3183_ = v_a_3248_;
goto v___jp_3176_;
}
else
{
lean_object* v_a_3249_; 
v_a_3249_ = lean_ctor_get(v___y_3247_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___y_3247_, 1);
v___y_3168_ = v___y_3241_;
v___y_3169_ = v___y_3242_;
v___y_3170_ = v___y_3244_;
v___y_3171_ = v___y_3243_;
v___y_3172_ = v___y_3245_;
v___y_3173_ = v___y_3246_;
v_a_3174_ = v_a_3249_;
goto v___jp_3167_;
}
}
v___jp_3250_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3258_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3257_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3241_ = v___y_3251_;
v___y_3242_ = v___y_3252_;
v___y_3243_ = v___y_3254_;
v___y_3244_ = v___y_3253_;
v___y_3245_ = v___y_3255_;
v___y_3246_ = v___y_3256_;
v___y_3247_ = v___x_3258_;
goto v___jp_3240_;
}
v___jp_3259_:
{
uint8_t v___x_3270_; 
v___x_3270_ = l_List_isEmpty___redArg(v___y_3267_);
lean_dec(v___y_3267_);
if (v___x_3270_ == 0)
{
lean_dec(v___y_3266_);
lean_dec(v___y_3262_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___y_3251_ = v___y_3260_;
v___y_3252_ = v___y_3261_;
v___y_3253_ = v___y_3264_;
v___y_3254_ = v___y_3263_;
v___y_3255_ = v___y_3265_;
v___y_3256_ = v___y_3268_;
goto v___jp_3250_;
}
else
{
if (v___y_3269_ == 0)
{
lean_object* v___x_3271_; 
lean_inc(v_trace_2966_);
v___x_3271_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3266_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3273_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v___x_3273_ = l_List_appendTR___redArg(v___y_3262_, v_a_3272_);
v___y_3177_ = v___y_3260_;
v___y_3178_ = v___y_3261_;
v___y_3179_ = v___y_3264_;
v___y_3180_ = v___y_3263_;
v___y_3181_ = v___y_3265_;
v___y_3182_ = v___y_3268_;
v_a_3183_ = v___x_3273_;
goto v___jp_3176_;
}
else
{
lean_dec(v___y_3262_);
v___y_3241_ = v___y_3260_;
v___y_3242_ = v___y_3261_;
v___y_3243_ = v___y_3263_;
v___y_3244_ = v___y_3264_;
v___y_3245_ = v___y_3265_;
v___y_3246_ = v___y_3268_;
v___y_3247_ = v___x_3271_;
goto v___jp_3240_;
}
}
else
{
lean_dec(v___y_3266_);
lean_dec(v___y_3262_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___y_3251_ = v___y_3260_;
v___y_3252_ = v___y_3261_;
v___y_3253_ = v___y_3264_;
v___y_3254_ = v___y_3263_;
v___y_3255_ = v___y_3265_;
v___y_3256_ = v___y_3268_;
goto v___jp_3250_;
}
}
}
v___jp_3274_:
{
uint8_t v_commitIndependentGoals_3285_; lean_object* v___x_3286_; 
v_commitIndependentGoals_3285_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3277_);
v___x_3286_ = l_List_appendTR___redArg(v_a_3284_, v___y_3277_);
if (v_commitIndependentGoals_3285_ == 0)
{
v___y_3260_ = v___y_3275_;
v___y_3261_ = v___y_3276_;
v___y_3262_ = v___y_3277_;
v___y_3263_ = v___y_3278_;
v___y_3264_ = v___y_3279_;
v___y_3265_ = v___y_3280_;
v___y_3266_ = v___x_3286_;
v___y_3267_ = v___y_3281_;
v___y_3268_ = v___y_3282_;
v___y_3269_ = v___y_3283_;
goto v___jp_3259_;
}
else
{
uint8_t v___x_3287_; 
v___x_3287_ = l_List_isEmpty___redArg(v___y_3277_);
if (v___x_3287_ == 0)
{
v___y_3224_ = v___y_3275_;
v___y_3225_ = v___y_3276_;
v___y_3226_ = v___y_3277_;
v___y_3227_ = v___y_3278_;
v___y_3228_ = v___y_3279_;
v___y_3229_ = v___y_3280_;
v___y_3230_ = v___x_3286_;
v___y_3231_ = v___y_3281_;
v___y_3232_ = v___y_3282_;
goto v___jp_3223_;
}
else
{
if (v___y_3283_ == 0)
{
v___y_3260_ = v___y_3275_;
v___y_3261_ = v___y_3276_;
v___y_3262_ = v___y_3277_;
v___y_3263_ = v___y_3278_;
v___y_3264_ = v___y_3279_;
v___y_3265_ = v___y_3280_;
v___y_3266_ = v___x_3286_;
v___y_3267_ = v___y_3281_;
v___y_3268_ = v___y_3282_;
v___y_3269_ = v___y_3283_;
goto v___jp_3259_;
}
else
{
v___y_3224_ = v___y_3275_;
v___y_3225_ = v___y_3276_;
v___y_3226_ = v___y_3277_;
v___y_3227_ = v___y_3278_;
v___y_3228_ = v___y_3279_;
v___y_3229_ = v___y_3280_;
v___y_3230_ = v___x_3286_;
v___y_3231_ = v___y_3281_;
v___y_3232_ = v___y_3282_;
goto v___jp_3223_;
}
}
}
}
v___jp_3288_:
{
lean_object* v___x_3296_; double v___x_3297_; double v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3296_ = lean_io_get_num_heartbeats();
v___x_3297_ = lean_float_of_nat(v___y_3289_);
v___x_3298_ = lean_float_of_nat(v___x_3296_);
v___x_3299_ = lean_box_float(v___x_3297_);
v___x_3300_ = lean_box_float(v___x_3298_);
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3299_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3302_, 0, v_a_3295_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
lean_inc(v_trace_2966_);
v___x_3303_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2990_, v___x_3072_, v_options_2988_, v___y_3290_, v___y_3294_, v___y_3293_, v___x_3302_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3143_ = v___y_3291_;
v___y_3144_ = v___y_3292_;
v___y_3145_ = v___x_3303_;
goto v___jp_3142_;
}
v___jp_3304_:
{
lean_object* v___x_3312_; 
v___x_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3312_, 0, v_a_3311_);
v___y_3289_ = v___y_3305_;
v___y_3290_ = v___y_3306_;
v___y_3291_ = v___y_3307_;
v___y_3292_ = v___y_3308_;
v___y_3293_ = v___y_3309_;
v___y_3294_ = v___y_3310_;
v_a_3295_ = v___x_3312_;
goto v___jp_3288_;
}
v___jp_3313_:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = l_List_appendTR___redArg(v___y_3317_, v___y_3320_);
v___x_3324_ = l_List_appendTR___redArg(v___x_3323_, v_a_3322_);
v___y_3305_ = v___y_3314_;
v___y_3306_ = v___y_3315_;
v___y_3307_ = v___y_3316_;
v___y_3308_ = v___y_3318_;
v___y_3309_ = v___y_3319_;
v___y_3310_ = v___y_3321_;
v_a_3311_ = v___x_3324_;
goto v___jp_3304_;
}
v___jp_3325_:
{
lean_object* v___x_3333_; 
v___x_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3333_, 0, v_a_3332_);
v___y_3289_ = v___y_3326_;
v___y_3290_ = v___y_3327_;
v___y_3291_ = v___y_3328_;
v___y_3292_ = v___y_3329_;
v___y_3293_ = v___y_3330_;
v___y_3294_ = v___y_3331_;
v_a_3295_ = v___x_3333_;
goto v___jp_3288_;
}
v___jp_3334_:
{
if (lean_obj_tag(v___y_3341_) == 0)
{
lean_object* v_a_3342_; 
v_a_3342_ = lean_ctor_get(v___y_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___y_3341_, 1);
v___y_3305_ = v___y_3335_;
v___y_3306_ = v___y_3336_;
v___y_3307_ = v___y_3337_;
v___y_3308_ = v___y_3338_;
v___y_3309_ = v___y_3339_;
v___y_3310_ = v___y_3340_;
v_a_3311_ = v_a_3342_;
goto v___jp_3304_;
}
else
{
lean_object* v_a_3343_; 
v_a_3343_ = lean_ctor_get(v___y_3341_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___y_3341_, 1);
v___y_3326_ = v___y_3335_;
v___y_3327_ = v___y_3336_;
v___y_3328_ = v___y_3337_;
v___y_3329_ = v___y_3338_;
v___y_3330_ = v___y_3339_;
v___y_3331_ = v___y_3340_;
v_a_3332_ = v_a_3343_;
goto v___jp_3325_;
}
}
v___jp_3344_:
{
lean_object* v___x_3353_; 
lean_inc(v_trace_2966_);
v___x_3353_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3346_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3355_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3353_, 1);
v___x_3355_ = l_List_appendTR___redArg(v___y_3349_, v_a_3354_);
v___y_3305_ = v___y_3345_;
v___y_3306_ = v___y_3347_;
v___y_3307_ = v___y_3348_;
v___y_3308_ = v___y_3350_;
v___y_3309_ = v___y_3351_;
v___y_3310_ = v___y_3352_;
v_a_3311_ = v___x_3355_;
goto v___jp_3304_;
}
else
{
lean_dec(v___y_3349_);
v___y_3335_ = v___y_3345_;
v___y_3336_ = v___y_3347_;
v___y_3337_ = v___y_3348_;
v___y_3338_ = v___y_3350_;
v___y_3339_ = v___y_3351_;
v___y_3340_ = v___y_3352_;
v___y_3341_ = v___x_3353_;
goto v___jp_3334_;
}
}
v___jp_3356_:
{
if (lean_obj_tag(v___y_3365_) == 0)
{
lean_object* v_a_3366_; 
v_a_3366_ = lean_ctor_get(v___y_3365_, 0);
lean_inc(v_a_3366_);
lean_dec_ref_known(v___y_3365_, 1);
v___y_3314_ = v___y_3357_;
v___y_3315_ = v___y_3358_;
v___y_3316_ = v___y_3359_;
v___y_3317_ = v___y_3360_;
v___y_3318_ = v___y_3361_;
v___y_3319_ = v___y_3362_;
v___y_3320_ = v___y_3363_;
v___y_3321_ = v___y_3364_;
v_a_3322_ = v_a_3366_;
goto v___jp_3313_;
}
else
{
lean_object* v_a_3367_; 
lean_dec(v___y_3363_);
lean_dec(v___y_3360_);
v_a_3367_ = lean_ctor_get(v___y_3365_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___y_3365_, 1);
v___y_3326_ = v___y_3357_;
v___y_3327_ = v___y_3358_;
v___y_3328_ = v___y_3359_;
v___y_3329_ = v___y_3361_;
v___y_3330_ = v___y_3362_;
v___y_3331_ = v___y_3364_;
v_a_3332_ = v_a_3367_;
goto v___jp_3325_;
}
}
v___jp_3368_:
{
if (v___y_3379_ == 0)
{
lean_object* v___x_3380_; 
lean_dec_ref(v___y_3374_);
v___x_3380_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3377_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3377_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_dec_ref_known(v___x_3380_, 1);
v___y_3314_ = v___y_3369_;
v___y_3315_ = v___y_3370_;
v___y_3316_ = v___y_3371_;
v___y_3317_ = v___y_3372_;
v___y_3318_ = v___y_3373_;
v___y_3319_ = v___y_3375_;
v___y_3320_ = v___y_3376_;
v___y_3321_ = v___y_3378_;
v_a_3322_ = v_snd_2983_;
goto v___jp_3313_;
}
else
{
lean_object* v_a_3381_; 
lean_dec(v___y_3376_);
lean_dec(v___y_3372_);
lean_dec(v_snd_2983_);
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref_known(v___x_3380_, 1);
v___y_3326_ = v___y_3369_;
v___y_3327_ = v___y_3370_;
v___y_3328_ = v___y_3371_;
v___y_3329_ = v___y_3373_;
v___y_3330_ = v___y_3375_;
v___y_3331_ = v___y_3378_;
v_a_3332_ = v_a_3381_;
goto v___jp_3325_;
}
}
else
{
lean_dec_ref(v___y_3377_);
lean_dec(v_snd_2983_);
v___y_3357_ = v___y_3369_;
v___y_3358_ = v___y_3370_;
v___y_3359_ = v___y_3371_;
v___y_3360_ = v___y_3372_;
v___y_3361_ = v___y_3373_;
v___y_3362_ = v___y_3375_;
v___y_3363_ = v___y_3376_;
v___y_3364_ = v___y_3378_;
v___y_3365_ = v___y_3374_;
goto v___jp_3356_;
}
}
v___jp_3382_:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3394_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
lean_inc(v_snd_2983_);
lean_inc(v_trace_2966_);
v___x_3394_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3384_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_dec(v_a_3393_);
lean_dec(v_snd_2983_);
v___y_3357_ = v___y_3383_;
v___y_3358_ = v___y_3385_;
v___y_3359_ = v___y_3386_;
v___y_3360_ = v___y_3387_;
v___y_3361_ = v___y_3388_;
v___y_3362_ = v___y_3389_;
v___y_3363_ = v___y_3390_;
v___y_3364_ = v___y_3391_;
v___y_3365_ = v___x_3394_;
goto v___jp_3356_;
}
else
{
lean_object* v_a_3395_; uint8_t v___x_3396_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
v___x_3396_ = l_Lean_Exception_isInterrupt(v_a_3395_);
if (v___x_3396_ == 0)
{
uint8_t v___x_3397_; 
v___x_3397_ = l_Lean_Exception_isRuntime(v_a_3395_);
v___y_3369_ = v___y_3383_;
v___y_3370_ = v___y_3385_;
v___y_3371_ = v___y_3386_;
v___y_3372_ = v___y_3387_;
v___y_3373_ = v___y_3388_;
v___y_3374_ = v___x_3394_;
v___y_3375_ = v___y_3389_;
v___y_3376_ = v___y_3390_;
v___y_3377_ = v_a_3393_;
v___y_3378_ = v___y_3391_;
v___y_3379_ = v___x_3397_;
goto v___jp_3368_;
}
else
{
lean_dec(v_a_3395_);
v___y_3369_ = v___y_3383_;
v___y_3370_ = v___y_3385_;
v___y_3371_ = v___y_3386_;
v___y_3372_ = v___y_3387_;
v___y_3373_ = v___y_3388_;
v___y_3374_ = v___x_3394_;
v___y_3375_ = v___y_3389_;
v___y_3376_ = v___y_3390_;
v___y_3377_ = v_a_3393_;
v___y_3378_ = v___y_3391_;
v___y_3379_ = v___x_3396_;
goto v___jp_3368_;
}
}
}
else
{
lean_object* v_a_3398_; 
lean_dec(v___y_3390_);
lean_dec(v___y_3387_);
lean_dec(v___y_3384_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3398_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3392_, 1);
v___y_3326_ = v___y_3383_;
v___y_3327_ = v___y_3385_;
v___y_3328_ = v___y_3386_;
v___y_3329_ = v___y_3388_;
v___y_3330_ = v___y_3389_;
v___y_3331_ = v___y_3391_;
v_a_3332_ = v_a_3398_;
goto v___jp_3325_;
}
}
v___jp_3399_:
{
uint8_t v_commitIndependentGoals_3410_; lean_object* v___x_3411_; 
v_commitIndependentGoals_3410_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3403_);
v___x_3411_ = l_List_appendTR___redArg(v_a_3409_, v___y_3403_);
if (v_commitIndependentGoals_3410_ == 0)
{
lean_dec(v___y_3406_);
if (v___y_3408_ == 0)
{
v___y_3345_ = v___y_3400_;
v___y_3346_ = v___x_3411_;
v___y_3347_ = v___y_3401_;
v___y_3348_ = v___y_3402_;
v___y_3349_ = v___y_3403_;
v___y_3350_ = v___y_3404_;
v___y_3351_ = v___y_3405_;
v___y_3352_ = v___y_3407_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_dec(v___x_3411_);
lean_dec(v___y_3403_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3413_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3412_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3335_ = v___y_3400_;
v___y_3336_ = v___y_3401_;
v___y_3337_ = v___y_3402_;
v___y_3338_ = v___y_3404_;
v___y_3339_ = v___y_3405_;
v___y_3340_ = v___y_3407_;
v___y_3341_ = v___x_3413_;
goto v___jp_3334_;
}
}
else
{
uint8_t v___x_3414_; 
v___x_3414_ = l_List_isEmpty___redArg(v___y_3403_);
if (v___x_3414_ == 0)
{
v___y_3383_ = v___y_3400_;
v___y_3384_ = v___x_3411_;
v___y_3385_ = v___y_3401_;
v___y_3386_ = v___y_3402_;
v___y_3387_ = v___y_3403_;
v___y_3388_ = v___y_3404_;
v___y_3389_ = v___y_3405_;
v___y_3390_ = v___y_3406_;
v___y_3391_ = v___y_3407_;
goto v___jp_3382_;
}
else
{
if (v___y_3408_ == 0)
{
lean_dec(v___y_3406_);
v___y_3345_ = v___y_3400_;
v___y_3346_ = v___x_3411_;
v___y_3347_ = v___y_3401_;
v___y_3348_ = v___y_3402_;
v___y_3349_ = v___y_3403_;
v___y_3350_ = v___y_3404_;
v___y_3351_ = v___y_3405_;
v___y_3352_ = v___y_3407_;
goto v___jp_3344_;
}
else
{
v___y_3383_ = v___y_3400_;
v___y_3384_ = v___x_3411_;
v___y_3385_ = v___y_3401_;
v___y_3386_ = v___y_3402_;
v___y_3387_ = v___y_3403_;
v___y_3388_ = v___y_3404_;
v___y_3389_ = v___y_3405_;
v___y_3390_ = v___y_3406_;
v___y_3391_ = v___y_3407_;
goto v___jp_3382_;
}
}
}
}
v___jp_3415_:
{
lean_object* v___x_3424_; 
v___x_3424_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2974_);
if (lean_obj_tag(v___x_3424_) == 0)
{
if (v___y_3423_ == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
v___x_3426_ = lean_io_mono_nanos_now();
v___x_3427_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2990_, v___y_3423_, v_goals_2969_, v___y_3420_, v_a_2972_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v___x_3429_ = l_List_reverse___redArg(v_a_3428_);
v___y_3275_ = v___y_3416_;
v___y_3276_ = v___y_3417_;
v___y_3277_ = v___y_3418_;
v___y_3278_ = v___y_3419_;
v___y_3279_ = v___x_3426_;
v___y_3280_ = v___y_3421_;
v___y_3281_ = v___y_3422_;
v___y_3282_ = v_a_3425_;
v___y_3283_ = v___y_3423_;
v_a_3284_ = v___x_3429_;
goto v___jp_3274_;
}
else
{
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3430_; 
v_a_3430_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3427_, 1);
v___y_3275_ = v___y_3416_;
v___y_3276_ = v___y_3417_;
v___y_3277_ = v___y_3418_;
v___y_3278_ = v___y_3419_;
v___y_3279_ = v___x_3426_;
v___y_3280_ = v___y_3421_;
v___y_3281_ = v___y_3422_;
v___y_3282_ = v_a_3425_;
v___y_3283_ = v___y_3423_;
v_a_3284_ = v_a_3430_;
goto v___jp_3274_;
}
else
{
lean_object* v_a_3431_; 
lean_dec(v___y_3422_);
lean_dec(v___y_3418_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3431_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3427_, 1);
v___y_3168_ = v___y_3416_;
v___y_3169_ = v___y_3417_;
v___y_3170_ = v___x_3426_;
v___y_3171_ = v___y_3419_;
v___y_3172_ = v___y_3421_;
v___y_3173_ = v_a_3425_;
v_a_3174_ = v_a_3431_;
goto v___jp_3167_;
}
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v_a_3432_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3424_, 1);
v___x_3433_ = lean_io_get_num_heartbeats();
v___x_3434_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2990_, v___y_3423_, v_goals_2969_, v___y_3420_, v_a_2972_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3436_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3436_ = l_List_reverse___redArg(v_a_3435_);
v___y_3400_ = v___x_3433_;
v___y_3401_ = v___y_3416_;
v___y_3402_ = v___y_3417_;
v___y_3403_ = v___y_3418_;
v___y_3404_ = v___y_3419_;
v___y_3405_ = v___y_3421_;
v___y_3406_ = v___y_3422_;
v___y_3407_ = v_a_3432_;
v___y_3408_ = v___y_3423_;
v_a_3409_ = v___x_3436_;
goto v___jp_3399_;
}
else
{
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3437_; 
v_a_3437_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3434_, 1);
v___y_3400_ = v___x_3433_;
v___y_3401_ = v___y_3416_;
v___y_3402_ = v___y_3417_;
v___y_3403_ = v___y_3418_;
v___y_3404_ = v___y_3419_;
v___y_3405_ = v___y_3421_;
v___y_3406_ = v___y_3422_;
v___y_3407_ = v_a_3432_;
v___y_3408_ = v___y_3423_;
v_a_3409_ = v_a_3437_;
goto v___jp_3399_;
}
else
{
lean_object* v_a_3438_; 
lean_dec(v___y_3422_);
lean_dec(v___y_3418_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3438_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3434_, 1);
v___y_3326_ = v___x_3433_;
v___y_3327_ = v___y_3416_;
v___y_3328_ = v___y_3417_;
v___y_3329_ = v___y_3419_;
v___y_3330_ = v___y_3421_;
v___y_3331_ = v_a_3432_;
v_a_3332_ = v_a_3438_;
goto v___jp_3325_;
}
}
}
}
else
{
lean_object* v_a_3439_; 
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec(v___y_3418_);
lean_dec(v_snd_2983_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3439_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3424_, 1);
v___y_3107_ = v___y_3417_;
v___y_3108_ = v___y_3419_;
v_a_3109_ = v_a_3439_;
goto v___jp_3106_;
}
}
v___jp_3440_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3444_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3443_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3143_ = v___y_3441_;
v___y_3144_ = v___y_3442_;
v___y_3145_ = v___x_3444_;
goto v___jp_3142_;
}
v___jp_3445_:
{
uint8_t v___x_3452_; 
v___x_3452_ = l_List_isEmpty___redArg(v___y_3451_);
lean_dec(v___y_3451_);
if (v___x_3452_ == 0)
{
lean_dec(v___y_3448_);
lean_dec(v___y_3446_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___y_3441_ = v___y_3447_;
v___y_3442_ = v___y_3449_;
goto v___jp_3440_;
}
else
{
if (v___y_3450_ == 0)
{
lean_object* v___x_3453_; 
lean_inc(v_trace_2966_);
v___x_3453_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3446_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = l_List_appendTR___redArg(v___y_3448_, v_a_3454_);
v___y_3094_ = v___y_3447_;
v___y_3095_ = v___y_3449_;
v_a_3096_ = v___x_3455_;
goto v___jp_3093_;
}
else
{
lean_dec(v___y_3448_);
v___y_3143_ = v___y_3447_;
v___y_3144_ = v___y_3449_;
v___y_3145_ = v___x_3453_;
goto v___jp_3142_;
}
}
else
{
lean_dec(v___y_3448_);
lean_dec(v___y_3446_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___y_3441_ = v___y_3447_;
v___y_3442_ = v___y_3449_;
goto v___jp_3440_;
}
}
}
v___jp_3456_:
{
uint8_t v_commitIndependentGoals_3463_; lean_object* v___x_3464_; 
v_commitIndependentGoals_3463_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3458_);
v___x_3464_ = l_List_appendTR___redArg(v_a_3462_, v___y_3458_);
if (v_commitIndependentGoals_3463_ == 0)
{
v___y_3446_ = v___x_3464_;
v___y_3447_ = v___y_3457_;
v___y_3448_ = v___y_3458_;
v___y_3449_ = v___y_3459_;
v___y_3450_ = v___y_3460_;
v___y_3451_ = v___y_3461_;
goto v___jp_3445_;
}
else
{
uint8_t v___x_3465_; 
v___x_3465_ = l_List_isEmpty___redArg(v___y_3458_);
if (v___x_3465_ == 0)
{
v___y_3130_ = v___y_3457_;
v___y_3131_ = v___x_3464_;
v___y_3132_ = v___y_3458_;
v___y_3133_ = v___y_3459_;
v___y_3134_ = v___y_3461_;
goto v___jp_3129_;
}
else
{
if (v___y_3460_ == 0)
{
v___y_3446_ = v___x_3464_;
v___y_3447_ = v___y_3457_;
v___y_3448_ = v___y_3458_;
v___y_3449_ = v___y_3459_;
v___y_3450_ = v___y_3460_;
v___y_3451_ = v___y_3461_;
goto v___jp_3445_;
}
else
{
v___y_3130_ = v___y_3457_;
v___y_3131_ = v___x_3464_;
v___y_3132_ = v___y_3458_;
v___y_3133_ = v___y_3459_;
v___y_3134_ = v___y_3461_;
goto v___jp_3129_;
}
}
}
}
v___jp_3466_:
{
lean_object* v___x_3470_; double v___x_3471_; double v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3470_ = lean_io_get_num_heartbeats();
v___x_3471_ = lean_float_of_nat(v___y_3468_);
v___x_3472_ = lean_float_of_nat(v___x_3470_);
v___x_3473_ = lean_box_float(v___x_3471_);
v___x_3474_ = lean_box_float(v___x_3472_);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3473_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3476_, 0, v_a_3469_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2990_, v___x_3072_, v_options_2988_, v___x_3075_, v___y_3467_, v___f_3071_, v___x_3476_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_3477_;
}
v___jp_3478_:
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3482_, 0, v_a_3481_);
v___y_3467_ = v___y_3479_;
v___y_3468_ = v___y_3480_;
v_a_3469_ = v___x_3482_;
goto v___jp_3466_;
}
v___jp_3483_:
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3487_, 0, v_a_3486_);
v___y_3467_ = v___y_3484_;
v___y_3468_ = v___y_3485_;
v_a_3469_ = v___x_3487_;
goto v___jp_3466_;
}
v___jp_3488_:
{
if (lean_obj_tag(v___y_3491_) == 0)
{
lean_object* v_a_3492_; 
v_a_3492_ = lean_ctor_get(v___y_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___y_3491_, 1);
v___y_3484_ = v___y_3489_;
v___y_3485_ = v___y_3490_;
v_a_3486_ = v_a_3492_;
goto v___jp_3483_;
}
else
{
lean_object* v_a_3493_; 
v_a_3493_ = lean_ctor_get(v___y_3491_, 0);
lean_inc(v_a_3493_);
lean_dec_ref_known(v___y_3491_, 1);
v___y_3479_ = v___y_3489_;
v___y_3480_ = v___y_3490_;
v_a_3481_ = v_a_3493_;
goto v___jp_3478_;
}
}
v___jp_3494_:
{
lean_object* v___x_3502_; double v___x_3503_; double v___x_3504_; double v___x_3505_; double v___x_3506_; double v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3502_ = lean_io_mono_nanos_now();
v___x_3503_ = lean_float_of_nat(v___y_3497_);
v___x_3504_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3505_ = lean_float_div(v___x_3503_, v___x_3504_);
v___x_3506_ = lean_float_of_nat(v___x_3502_);
v___x_3507_ = lean_float_div(v___x_3506_, v___x_3504_);
v___x_3508_ = lean_box_float(v___x_3505_);
v___x_3509_ = lean_box_float(v___x_3507_);
v___x_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3508_);
lean_ctor_set(v___x_3510_, 1, v___x_3509_);
v___x_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3511_, 0, v_a_3501_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
lean_inc(v_trace_2966_);
v___x_3512_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2990_, v___x_3072_, v_options_2988_, v___y_3499_, v___y_3500_, v___y_3495_, v___x_3511_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3489_ = v___y_3496_;
v___y_3490_ = v___y_3498_;
v___y_3491_ = v___x_3512_;
goto v___jp_3488_;
}
v___jp_3513_:
{
lean_object* v___x_3521_; 
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v_a_3520_);
v___y_3495_ = v___y_3514_;
v___y_3496_ = v___y_3515_;
v___y_3497_ = v___y_3516_;
v___y_3498_ = v___y_3518_;
v___y_3499_ = v___y_3517_;
v___y_3500_ = v___y_3519_;
v_a_3501_ = v___x_3521_;
goto v___jp_3494_;
}
v___jp_3522_:
{
lean_object* v___x_3530_; 
v___x_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3530_, 0, v_a_3529_);
v___y_3495_ = v___y_3523_;
v___y_3496_ = v___y_3524_;
v___y_3497_ = v___y_3525_;
v___y_3498_ = v___y_3527_;
v___y_3499_ = v___y_3526_;
v___y_3500_ = v___y_3528_;
v_a_3501_ = v___x_3530_;
goto v___jp_3494_;
}
v___jp_3531_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = l_List_appendTR___redArg(v___y_3538_, v___y_3537_);
v___x_3542_ = l_List_appendTR___redArg(v___x_3541_, v_a_3540_);
v___y_3523_ = v___y_3532_;
v___y_3524_ = v___y_3533_;
v___y_3525_ = v___y_3534_;
v___y_3526_ = v___y_3536_;
v___y_3527_ = v___y_3535_;
v___y_3528_ = v___y_3539_;
v_a_3529_ = v___x_3542_;
goto v___jp_3522_;
}
v___jp_3543_:
{
if (lean_obj_tag(v___y_3552_) == 0)
{
lean_object* v_a_3553_; 
v_a_3553_ = lean_ctor_get(v___y_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___y_3552_, 1);
v___y_3532_ = v___y_3544_;
v___y_3533_ = v___y_3545_;
v___y_3534_ = v___y_3546_;
v___y_3535_ = v___y_3548_;
v___y_3536_ = v___y_3547_;
v___y_3537_ = v___y_3549_;
v___y_3538_ = v___y_3550_;
v___y_3539_ = v___y_3551_;
v_a_3540_ = v_a_3553_;
goto v___jp_3531_;
}
else
{
lean_object* v_a_3554_; 
lean_dec(v___y_3550_);
lean_dec(v___y_3549_);
v_a_3554_ = lean_ctor_get(v___y_3552_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___y_3552_, 1);
v___y_3514_ = v___y_3544_;
v___y_3515_ = v___y_3545_;
v___y_3516_ = v___y_3546_;
v___y_3517_ = v___y_3547_;
v___y_3518_ = v___y_3548_;
v___y_3519_ = v___y_3551_;
v_a_3520_ = v_a_3554_;
goto v___jp_3513_;
}
}
v___jp_3555_:
{
if (v___y_3566_ == 0)
{
lean_object* v___x_3567_; 
lean_dec_ref(v___y_3556_);
v___x_3567_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3559_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3559_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_dec_ref_known(v___x_3567_, 1);
v___y_3532_ = v___y_3557_;
v___y_3533_ = v___y_3558_;
v___y_3534_ = v___y_3560_;
v___y_3535_ = v___y_3562_;
v___y_3536_ = v___y_3561_;
v___y_3537_ = v___y_3563_;
v___y_3538_ = v___y_3564_;
v___y_3539_ = v___y_3565_;
v_a_3540_ = v_snd_2983_;
goto v___jp_3531_;
}
else
{
lean_object* v_a_3568_; 
lean_dec(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec(v_snd_2983_);
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v___y_3514_ = v___y_3557_;
v___y_3515_ = v___y_3558_;
v___y_3516_ = v___y_3560_;
v___y_3517_ = v___y_3561_;
v___y_3518_ = v___y_3562_;
v___y_3519_ = v___y_3565_;
v_a_3520_ = v_a_3568_;
goto v___jp_3513_;
}
}
else
{
lean_dec_ref(v___y_3559_);
lean_dec(v_snd_2983_);
v___y_3544_ = v___y_3557_;
v___y_3545_ = v___y_3558_;
v___y_3546_ = v___y_3560_;
v___y_3547_ = v___y_3561_;
v___y_3548_ = v___y_3562_;
v___y_3549_ = v___y_3563_;
v___y_3550_ = v___y_3564_;
v___y_3551_ = v___y_3565_;
v___y_3552_ = v___y_3556_;
goto v___jp_3543_;
}
}
v___jp_3569_:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3581_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3579_, 1);
lean_inc(v_snd_2983_);
lean_inc(v_trace_2966_);
v___x_3581_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3575_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_dec(v_a_3580_);
lean_dec(v_snd_2983_);
v___y_3544_ = v___y_3570_;
v___y_3545_ = v___y_3571_;
v___y_3546_ = v___y_3572_;
v___y_3547_ = v___y_3574_;
v___y_3548_ = v___y_3573_;
v___y_3549_ = v___y_3576_;
v___y_3550_ = v___y_3577_;
v___y_3551_ = v___y_3578_;
v___y_3552_ = v___x_3581_;
goto v___jp_3543_;
}
else
{
lean_object* v_a_3582_; uint8_t v___x_3583_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
v___x_3583_ = l_Lean_Exception_isInterrupt(v_a_3582_);
if (v___x_3583_ == 0)
{
uint8_t v___x_3584_; 
v___x_3584_ = l_Lean_Exception_isRuntime(v_a_3582_);
v___y_3556_ = v___x_3581_;
v___y_3557_ = v___y_3570_;
v___y_3558_ = v___y_3571_;
v___y_3559_ = v_a_3580_;
v___y_3560_ = v___y_3572_;
v___y_3561_ = v___y_3574_;
v___y_3562_ = v___y_3573_;
v___y_3563_ = v___y_3576_;
v___y_3564_ = v___y_3577_;
v___y_3565_ = v___y_3578_;
v___y_3566_ = v___x_3584_;
goto v___jp_3555_;
}
else
{
lean_dec(v_a_3582_);
v___y_3556_ = v___x_3581_;
v___y_3557_ = v___y_3570_;
v___y_3558_ = v___y_3571_;
v___y_3559_ = v_a_3580_;
v___y_3560_ = v___y_3572_;
v___y_3561_ = v___y_3574_;
v___y_3562_ = v___y_3573_;
v___y_3563_ = v___y_3576_;
v___y_3564_ = v___y_3577_;
v___y_3565_ = v___y_3578_;
v___y_3566_ = v___x_3583_;
goto v___jp_3555_;
}
}
}
else
{
lean_object* v_a_3585_; 
lean_dec(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3585_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3585_);
lean_dec_ref_known(v___x_3579_, 1);
v___y_3514_ = v___y_3570_;
v___y_3515_ = v___y_3571_;
v___y_3516_ = v___y_3572_;
v___y_3517_ = v___y_3574_;
v___y_3518_ = v___y_3573_;
v___y_3519_ = v___y_3578_;
v_a_3520_ = v_a_3585_;
goto v___jp_3513_;
}
}
v___jp_3586_:
{
if (lean_obj_tag(v___y_3593_) == 0)
{
lean_object* v_a_3594_; 
v_a_3594_ = lean_ctor_get(v___y_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref_known(v___y_3593_, 1);
v___y_3523_ = v___y_3587_;
v___y_3524_ = v___y_3588_;
v___y_3525_ = v___y_3589_;
v___y_3526_ = v___y_3591_;
v___y_3527_ = v___y_3590_;
v___y_3528_ = v___y_3592_;
v_a_3529_ = v_a_3594_;
goto v___jp_3522_;
}
else
{
lean_object* v_a_3595_; 
v_a_3595_ = lean_ctor_get(v___y_3593_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___y_3593_, 1);
v___y_3514_ = v___y_3587_;
v___y_3515_ = v___y_3588_;
v___y_3516_ = v___y_3589_;
v___y_3517_ = v___y_3591_;
v___y_3518_ = v___y_3590_;
v___y_3519_ = v___y_3592_;
v_a_3520_ = v_a_3595_;
goto v___jp_3513_;
}
}
v___jp_3596_:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3604_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3603_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3587_ = v___y_3597_;
v___y_3588_ = v___y_3598_;
v___y_3589_ = v___y_3599_;
v___y_3590_ = v___y_3601_;
v___y_3591_ = v___y_3600_;
v___y_3592_ = v___y_3602_;
v___y_3593_ = v___x_3604_;
goto v___jp_3586_;
}
v___jp_3605_:
{
uint8_t v___x_3616_; 
v___x_3616_ = l_List_isEmpty___redArg(v___y_3612_);
lean_dec(v___y_3612_);
if (v___x_3616_ == 0)
{
lean_dec(v___y_3613_);
lean_dec(v___y_3611_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___y_3597_ = v___y_3606_;
v___y_3598_ = v___y_3607_;
v___y_3599_ = v___y_3608_;
v___y_3600_ = v___y_3610_;
v___y_3601_ = v___y_3609_;
v___y_3602_ = v___y_3615_;
goto v___jp_3596_;
}
else
{
if (v___y_3614_ == 0)
{
lean_object* v___x_3617_; 
lean_inc(v_trace_2966_);
v___x_3617_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3611_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
v___x_3619_ = l_List_appendTR___redArg(v___y_3613_, v_a_3618_);
v___y_3523_ = v___y_3606_;
v___y_3524_ = v___y_3607_;
v___y_3525_ = v___y_3608_;
v___y_3526_ = v___y_3610_;
v___y_3527_ = v___y_3609_;
v___y_3528_ = v___y_3615_;
v_a_3529_ = v___x_3619_;
goto v___jp_3522_;
}
else
{
lean_dec(v___y_3613_);
v___y_3587_ = v___y_3606_;
v___y_3588_ = v___y_3607_;
v___y_3589_ = v___y_3608_;
v___y_3590_ = v___y_3609_;
v___y_3591_ = v___y_3610_;
v___y_3592_ = v___y_3615_;
v___y_3593_ = v___x_3617_;
goto v___jp_3586_;
}
}
else
{
lean_dec(v___y_3613_);
lean_dec(v___y_3611_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___y_3597_ = v___y_3606_;
v___y_3598_ = v___y_3607_;
v___y_3599_ = v___y_3608_;
v___y_3600_ = v___y_3610_;
v___y_3601_ = v___y_3609_;
v___y_3602_ = v___y_3615_;
goto v___jp_3596_;
}
}
}
v___jp_3620_:
{
uint8_t v_commitIndependentGoals_3631_; lean_object* v___x_3632_; 
v_commitIndependentGoals_3631_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3627_);
v___x_3632_ = l_List_appendTR___redArg(v_a_3630_, v___y_3627_);
if (v_commitIndependentGoals_3631_ == 0)
{
v___y_3606_ = v___y_3621_;
v___y_3607_ = v___y_3622_;
v___y_3608_ = v___y_3623_;
v___y_3609_ = v___y_3624_;
v___y_3610_ = v___y_3625_;
v___y_3611_ = v___x_3632_;
v___y_3612_ = v___y_3626_;
v___y_3613_ = v___y_3627_;
v___y_3614_ = v___y_3628_;
v___y_3615_ = v___y_3629_;
goto v___jp_3605_;
}
else
{
uint8_t v___x_3633_; 
v___x_3633_ = l_List_isEmpty___redArg(v___y_3627_);
if (v___x_3633_ == 0)
{
v___y_3570_ = v___y_3621_;
v___y_3571_ = v___y_3622_;
v___y_3572_ = v___y_3623_;
v___y_3573_ = v___y_3624_;
v___y_3574_ = v___y_3625_;
v___y_3575_ = v___x_3632_;
v___y_3576_ = v___y_3626_;
v___y_3577_ = v___y_3627_;
v___y_3578_ = v___y_3629_;
goto v___jp_3569_;
}
else
{
if (v___y_3628_ == 0)
{
v___y_3606_ = v___y_3621_;
v___y_3607_ = v___y_3622_;
v___y_3608_ = v___y_3623_;
v___y_3609_ = v___y_3624_;
v___y_3610_ = v___y_3625_;
v___y_3611_ = v___x_3632_;
v___y_3612_ = v___y_3626_;
v___y_3613_ = v___y_3627_;
v___y_3614_ = v___y_3628_;
v___y_3615_ = v___y_3629_;
goto v___jp_3605_;
}
else
{
v___y_3570_ = v___y_3621_;
v___y_3571_ = v___y_3622_;
v___y_3572_ = v___y_3623_;
v___y_3573_ = v___y_3624_;
v___y_3574_ = v___y_3625_;
v___y_3575_ = v___x_3632_;
v___y_3576_ = v___y_3626_;
v___y_3577_ = v___y_3627_;
v___y_3578_ = v___y_3629_;
goto v___jp_3569_;
}
}
}
}
v___jp_3634_:
{
lean_object* v___x_3642_; double v___x_3643_; double v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3642_ = lean_io_get_num_heartbeats();
v___x_3643_ = lean_float_of_nat(v___y_3639_);
v___x_3644_ = lean_float_of_nat(v___x_3642_);
v___x_3645_ = lean_box_float(v___x_3643_);
v___x_3646_ = lean_box_float(v___x_3644_);
v___x_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3645_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v_a_3641_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
lean_inc(v_trace_2966_);
v___x_3649_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2990_, v___x_3072_, v_options_2988_, v___y_3638_, v___y_3640_, v___y_3635_, v___x_3648_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3489_ = v___y_3636_;
v___y_3490_ = v___y_3637_;
v___y_3491_ = v___x_3649_;
goto v___jp_3488_;
}
v___jp_3650_:
{
lean_object* v___x_3658_; 
v___x_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3658_, 0, v_a_3657_);
v___y_3635_ = v___y_3651_;
v___y_3636_ = v___y_3652_;
v___y_3637_ = v___y_3654_;
v___y_3638_ = v___y_3653_;
v___y_3639_ = v___y_3655_;
v___y_3640_ = v___y_3656_;
v_a_3641_ = v___x_3658_;
goto v___jp_3634_;
}
v___jp_3659_:
{
lean_object* v___x_3667_; 
v___x_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3667_, 0, v_a_3666_);
v___y_3635_ = v___y_3660_;
v___y_3636_ = v___y_3661_;
v___y_3637_ = v___y_3663_;
v___y_3638_ = v___y_3662_;
v___y_3639_ = v___y_3664_;
v___y_3640_ = v___y_3665_;
v_a_3641_ = v___x_3667_;
goto v___jp_3634_;
}
v___jp_3668_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = l_List_appendTR___redArg(v___y_3675_, v___y_3673_);
v___x_3679_ = l_List_appendTR___redArg(v___x_3678_, v_a_3677_);
v___y_3660_ = v___y_3669_;
v___y_3661_ = v___y_3670_;
v___y_3662_ = v___y_3672_;
v___y_3663_ = v___y_3671_;
v___y_3664_ = v___y_3674_;
v___y_3665_ = v___y_3676_;
v_a_3666_ = v___x_3679_;
goto v___jp_3659_;
}
v___jp_3680_:
{
if (lean_obj_tag(v___y_3689_) == 0)
{
lean_object* v_a_3690_; 
v_a_3690_ = lean_ctor_get(v___y_3689_, 0);
lean_inc(v_a_3690_);
lean_dec_ref_known(v___y_3689_, 1);
v___y_3669_ = v___y_3681_;
v___y_3670_ = v___y_3682_;
v___y_3671_ = v___y_3684_;
v___y_3672_ = v___y_3683_;
v___y_3673_ = v___y_3685_;
v___y_3674_ = v___y_3686_;
v___y_3675_ = v___y_3687_;
v___y_3676_ = v___y_3688_;
v_a_3677_ = v_a_3690_;
goto v___jp_3668_;
}
else
{
lean_object* v_a_3691_; 
lean_dec(v___y_3687_);
lean_dec(v___y_3685_);
v_a_3691_ = lean_ctor_get(v___y_3689_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___y_3689_, 1);
v___y_3651_ = v___y_3681_;
v___y_3652_ = v___y_3682_;
v___y_3653_ = v___y_3683_;
v___y_3654_ = v___y_3684_;
v___y_3655_ = v___y_3686_;
v___y_3656_ = v___y_3688_;
v_a_3657_ = v_a_3691_;
goto v___jp_3650_;
}
}
v___jp_3692_:
{
if (v___y_3703_ == 0)
{
lean_object* v___x_3704_; 
lean_dec_ref(v___y_3699_);
v___x_3704_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3695_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3695_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_dec_ref_known(v___x_3704_, 1);
v___y_3669_ = v___y_3693_;
v___y_3670_ = v___y_3694_;
v___y_3671_ = v___y_3697_;
v___y_3672_ = v___y_3696_;
v___y_3673_ = v___y_3698_;
v___y_3674_ = v___y_3700_;
v___y_3675_ = v___y_3701_;
v___y_3676_ = v___y_3702_;
v_a_3677_ = v_snd_2983_;
goto v___jp_3668_;
}
else
{
lean_object* v_a_3705_; 
lean_dec(v___y_3701_);
lean_dec(v___y_3698_);
lean_dec(v_snd_2983_);
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
v___y_3651_ = v___y_3693_;
v___y_3652_ = v___y_3694_;
v___y_3653_ = v___y_3696_;
v___y_3654_ = v___y_3697_;
v___y_3655_ = v___y_3700_;
v___y_3656_ = v___y_3702_;
v_a_3657_ = v_a_3705_;
goto v___jp_3650_;
}
}
else
{
lean_dec_ref(v___y_3695_);
lean_dec(v_snd_2983_);
v___y_3681_ = v___y_3693_;
v___y_3682_ = v___y_3694_;
v___y_3683_ = v___y_3696_;
v___y_3684_ = v___y_3697_;
v___y_3685_ = v___y_3698_;
v___y_3686_ = v___y_3700_;
v___y_3687_ = v___y_3701_;
v___y_3688_ = v___y_3702_;
v___y_3689_ = v___y_3699_;
goto v___jp_3680_;
}
}
v___jp_3706_:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3718_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3717_);
lean_dec_ref_known(v___x_3716_, 1);
lean_inc(v_snd_2983_);
lean_inc(v_trace_2966_);
v___x_3718_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3709_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_dec(v_a_3717_);
lean_dec(v_snd_2983_);
v___y_3681_ = v___y_3707_;
v___y_3682_ = v___y_3708_;
v___y_3683_ = v___y_3711_;
v___y_3684_ = v___y_3710_;
v___y_3685_ = v___y_3712_;
v___y_3686_ = v___y_3713_;
v___y_3687_ = v___y_3714_;
v___y_3688_ = v___y_3715_;
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
v___y_3693_ = v___y_3707_;
v___y_3694_ = v___y_3708_;
v___y_3695_ = v_a_3717_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3710_;
v___y_3698_ = v___y_3712_;
v___y_3699_ = v___x_3718_;
v___y_3700_ = v___y_3713_;
v___y_3701_ = v___y_3714_;
v___y_3702_ = v___y_3715_;
v___y_3703_ = v___x_3721_;
goto v___jp_3692_;
}
else
{
lean_dec(v_a_3719_);
v___y_3693_ = v___y_3707_;
v___y_3694_ = v___y_3708_;
v___y_3695_ = v_a_3717_;
v___y_3696_ = v___y_3711_;
v___y_3697_ = v___y_3710_;
v___y_3698_ = v___y_3712_;
v___y_3699_ = v___x_3718_;
v___y_3700_ = v___y_3713_;
v___y_3701_ = v___y_3714_;
v___y_3702_ = v___y_3715_;
v___y_3703_ = v___x_3720_;
goto v___jp_3692_;
}
}
}
else
{
lean_object* v_a_3722_; 
lean_dec(v___y_3714_);
lean_dec(v___y_3712_);
lean_dec(v___y_3709_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3722_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3716_, 1);
v___y_3651_ = v___y_3707_;
v___y_3652_ = v___y_3708_;
v___y_3653_ = v___y_3711_;
v___y_3654_ = v___y_3710_;
v___y_3655_ = v___y_3713_;
v___y_3656_ = v___y_3715_;
v_a_3657_ = v_a_3722_;
goto v___jp_3650_;
}
}
v___jp_3723_:
{
if (lean_obj_tag(v___y_3730_) == 0)
{
lean_object* v_a_3731_; 
v_a_3731_ = lean_ctor_get(v___y_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref_known(v___y_3730_, 1);
v___y_3660_ = v___y_3724_;
v___y_3661_ = v___y_3725_;
v___y_3662_ = v___y_3727_;
v___y_3663_ = v___y_3726_;
v___y_3664_ = v___y_3728_;
v___y_3665_ = v___y_3729_;
v_a_3666_ = v_a_3731_;
goto v___jp_3659_;
}
else
{
lean_object* v_a_3732_; 
v_a_3732_ = lean_ctor_get(v___y_3730_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___y_3730_, 1);
v___y_3651_ = v___y_3724_;
v___y_3652_ = v___y_3725_;
v___y_3653_ = v___y_3727_;
v___y_3654_ = v___y_3726_;
v___y_3655_ = v___y_3728_;
v___y_3656_ = v___y_3729_;
v_a_3657_ = v_a_3732_;
goto v___jp_3650_;
}
}
v___jp_3733_:
{
lean_object* v___x_3742_; 
lean_inc(v_trace_2966_);
v___x_3742_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3736_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___x_3744_ = l_List_appendTR___redArg(v___y_3740_, v_a_3743_);
v___y_3660_ = v___y_3734_;
v___y_3661_ = v___y_3735_;
v___y_3662_ = v___y_3738_;
v___y_3663_ = v___y_3737_;
v___y_3664_ = v___y_3739_;
v___y_3665_ = v___y_3741_;
v_a_3666_ = v___x_3744_;
goto v___jp_3659_;
}
else
{
lean_dec(v___y_3740_);
v___y_3724_ = v___y_3734_;
v___y_3725_ = v___y_3735_;
v___y_3726_ = v___y_3737_;
v___y_3727_ = v___y_3738_;
v___y_3728_ = v___y_3739_;
v___y_3729_ = v___y_3741_;
v___y_3730_ = v___x_3742_;
goto v___jp_3723_;
}
}
v___jp_3745_:
{
uint8_t v___x_3756_; 
v___x_3756_ = l_List_isEmpty___redArg(v___y_3751_);
lean_dec(v___y_3751_);
if (v___x_3756_ == 0)
{
if (v___y_3755_ == 0)
{
v___y_3734_ = v___y_3746_;
v___y_3735_ = v___y_3747_;
v___y_3736_ = v___y_3748_;
v___y_3737_ = v___y_3750_;
v___y_3738_ = v___y_3749_;
v___y_3739_ = v___y_3752_;
v___y_3740_ = v___y_3753_;
v___y_3741_ = v___y_3754_;
goto v___jp_3733_;
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
lean_dec(v___y_3753_);
lean_dec(v___y_3748_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3757_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3758_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3757_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3724_ = v___y_3746_;
v___y_3725_ = v___y_3747_;
v___y_3726_ = v___y_3750_;
v___y_3727_ = v___y_3749_;
v___y_3728_ = v___y_3752_;
v___y_3729_ = v___y_3754_;
v___y_3730_ = v___x_3758_;
goto v___jp_3723_;
}
}
else
{
v___y_3734_ = v___y_3746_;
v___y_3735_ = v___y_3747_;
v___y_3736_ = v___y_3748_;
v___y_3737_ = v___y_3750_;
v___y_3738_ = v___y_3749_;
v___y_3739_ = v___y_3752_;
v___y_3740_ = v___y_3753_;
v___y_3741_ = v___y_3754_;
goto v___jp_3733_;
}
}
v___jp_3759_:
{
uint8_t v_commitIndependentGoals_3770_; lean_object* v___x_3771_; 
v_commitIndependentGoals_3770_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3766_);
v___x_3771_ = l_List_appendTR___redArg(v_a_3769_, v___y_3766_);
if (v_commitIndependentGoals_3770_ == 0)
{
v___y_3746_ = v___y_3760_;
v___y_3747_ = v___y_3761_;
v___y_3748_ = v___x_3771_;
v___y_3749_ = v___y_3762_;
v___y_3750_ = v___y_3763_;
v___y_3751_ = v___y_3764_;
v___y_3752_ = v___y_3765_;
v___y_3753_ = v___y_3766_;
v___y_3754_ = v___y_3768_;
v___y_3755_ = v___y_3767_;
goto v___jp_3745_;
}
else
{
uint8_t v___x_3772_; 
v___x_3772_ = l_List_isEmpty___redArg(v___y_3766_);
if (v___x_3772_ == 0)
{
v___y_3707_ = v___y_3760_;
v___y_3708_ = v___y_3761_;
v___y_3709_ = v___x_3771_;
v___y_3710_ = v___y_3763_;
v___y_3711_ = v___y_3762_;
v___y_3712_ = v___y_3764_;
v___y_3713_ = v___y_3765_;
v___y_3714_ = v___y_3766_;
v___y_3715_ = v___y_3768_;
goto v___jp_3706_;
}
else
{
if (v___x_2987_ == 0)
{
v___y_3746_ = v___y_3760_;
v___y_3747_ = v___y_3761_;
v___y_3748_ = v___x_3771_;
v___y_3749_ = v___y_3762_;
v___y_3750_ = v___y_3763_;
v___y_3751_ = v___y_3764_;
v___y_3752_ = v___y_3765_;
v___y_3753_ = v___y_3766_;
v___y_3754_ = v___y_3768_;
v___y_3755_ = v___y_3767_;
goto v___jp_3745_;
}
else
{
v___y_3707_ = v___y_3760_;
v___y_3708_ = v___y_3761_;
v___y_3709_ = v___x_3771_;
v___y_3710_ = v___y_3763_;
v___y_3711_ = v___y_3762_;
v___y_3712_ = v___y_3764_;
v___y_3713_ = v___y_3765_;
v___y_3714_ = v___y_3766_;
v___y_3715_ = v___y_3768_;
goto v___jp_3706_;
}
}
}
}
v___jp_3773_:
{
lean_object* v___x_3782_; 
v___x_3782_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2974_);
if (lean_obj_tag(v___x_3782_) == 0)
{
if (v___y_3781_ == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
v___x_3784_ = lean_io_mono_nanos_now();
v___x_3785_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3781_, v___x_2987_, v_goals_2969_, v___y_3778_, v_a_2972_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3787_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v___x_3787_ = l_List_reverse___redArg(v_a_3786_);
v___y_3621_ = v___y_3774_;
v___y_3622_ = v___y_3775_;
v___y_3623_ = v___x_3784_;
v___y_3624_ = v___y_3777_;
v___y_3625_ = v___y_3776_;
v___y_3626_ = v___y_3779_;
v___y_3627_ = v___y_3780_;
v___y_3628_ = v___y_3781_;
v___y_3629_ = v_a_3783_;
v_a_3630_ = v___x_3787_;
goto v___jp_3620_;
}
else
{
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3788_; 
v_a_3788_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3788_);
lean_dec_ref_known(v___x_3785_, 1);
v___y_3621_ = v___y_3774_;
v___y_3622_ = v___y_3775_;
v___y_3623_ = v___x_3784_;
v___y_3624_ = v___y_3777_;
v___y_3625_ = v___y_3776_;
v___y_3626_ = v___y_3779_;
v___y_3627_ = v___y_3780_;
v___y_3628_ = v___y_3781_;
v___y_3629_ = v_a_3783_;
v_a_3630_ = v_a_3788_;
goto v___jp_3620_;
}
else
{
lean_object* v_a_3789_; 
lean_dec(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3789_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3785_, 1);
v___y_3514_ = v___y_3774_;
v___y_3515_ = v___y_3775_;
v___y_3516_ = v___x_3784_;
v___y_3517_ = v___y_3776_;
v___y_3518_ = v___y_3777_;
v___y_3519_ = v_a_3783_;
v_a_3520_ = v_a_3789_;
goto v___jp_3513_;
}
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v_a_3790_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3782_, 1);
v___x_3791_ = lean_io_get_num_heartbeats();
v___x_3792_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3781_, v___x_2987_, v_goals_2969_, v___y_3778_, v_a_2972_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3794_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v___x_3794_ = l_List_reverse___redArg(v_a_3793_);
v___y_3760_ = v___y_3774_;
v___y_3761_ = v___y_3775_;
v___y_3762_ = v___y_3776_;
v___y_3763_ = v___y_3777_;
v___y_3764_ = v___y_3779_;
v___y_3765_ = v___x_3791_;
v___y_3766_ = v___y_3780_;
v___y_3767_ = v___y_3781_;
v___y_3768_ = v_a_3790_;
v_a_3769_ = v___x_3794_;
goto v___jp_3759_;
}
else
{
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3795_; 
v_a_3795_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3792_, 1);
v___y_3760_ = v___y_3774_;
v___y_3761_ = v___y_3775_;
v___y_3762_ = v___y_3776_;
v___y_3763_ = v___y_3777_;
v___y_3764_ = v___y_3779_;
v___y_3765_ = v___x_3791_;
v___y_3766_ = v___y_3780_;
v___y_3767_ = v___y_3781_;
v___y_3768_ = v_a_3790_;
v_a_3769_ = v_a_3795_;
goto v___jp_3759_;
}
else
{
lean_object* v_a_3796_; 
lean_dec(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3796_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3792_, 1);
v___y_3651_ = v___y_3774_;
v___y_3652_ = v___y_3775_;
v___y_3653_ = v___y_3776_;
v___y_3654_ = v___y_3777_;
v___y_3655_ = v___x_3791_;
v___y_3656_ = v_a_3790_;
v_a_3657_ = v_a_3796_;
goto v___jp_3650_;
}
}
}
}
else
{
lean_object* v_a_3797_; 
lean_dec(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3774_);
lean_dec(v_snd_2983_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3797_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3782_, 1);
v___y_3479_ = v___y_3775_;
v___y_3480_ = v___y_3777_;
v_a_3481_ = v_a_3797_;
goto v___jp_3478_;
}
}
v___jp_3798_:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3802_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3801_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3489_ = v___y_3799_;
v___y_3490_ = v___y_3800_;
v___y_3491_ = v___x_3802_;
goto v___jp_3488_;
}
v___jp_3803_:
{
uint8_t v___x_3810_; 
v___x_3810_ = l_List_isEmpty___redArg(v___y_3808_);
lean_dec(v___y_3808_);
if (v___x_3810_ == 0)
{
lean_dec(v___y_3809_);
lean_dec(v___y_3807_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___y_3799_ = v___y_3805_;
v___y_3800_ = v___y_3806_;
goto v___jp_3798_;
}
else
{
if (v___y_3804_ == 0)
{
lean_object* v___x_3811_; 
lean_inc(v_trace_2966_);
v___x_3811_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3807_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3813_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_a_3812_);
lean_dec_ref_known(v___x_3811_, 1);
v___x_3813_ = l_List_appendTR___redArg(v___y_3809_, v_a_3812_);
v___y_3484_ = v___y_3805_;
v___y_3485_ = v___y_3806_;
v_a_3486_ = v___x_3813_;
goto v___jp_3483_;
}
else
{
lean_dec(v___y_3809_);
v___y_3489_ = v___y_3805_;
v___y_3490_ = v___y_3806_;
v___y_3491_ = v___x_3811_;
goto v___jp_3488_;
}
}
else
{
lean_dec(v___y_3809_);
lean_dec(v___y_3807_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___y_3799_ = v___y_3805_;
v___y_3800_ = v___y_3806_;
goto v___jp_3798_;
}
}
}
v___jp_3814_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = l_List_appendTR___redArg(v___y_3818_, v___y_3817_);
v___x_3821_ = l_List_appendTR___redArg(v___x_3820_, v_a_3819_);
v___y_3484_ = v___y_3815_;
v___y_3485_ = v___y_3816_;
v_a_3486_ = v___x_3821_;
goto v___jp_3483_;
}
v___jp_3822_:
{
if (lean_obj_tag(v___y_3827_) == 0)
{
lean_object* v_a_3828_; 
v_a_3828_ = lean_ctor_get(v___y_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref_known(v___y_3827_, 1);
v___y_3815_ = v___y_3823_;
v___y_3816_ = v___y_3824_;
v___y_3817_ = v___y_3825_;
v___y_3818_ = v___y_3826_;
v_a_3819_ = v_a_3828_;
goto v___jp_3814_;
}
else
{
lean_object* v_a_3829_; 
lean_dec(v___y_3826_);
lean_dec(v___y_3825_);
v_a_3829_ = lean_ctor_get(v___y_3827_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___y_3827_, 1);
v___y_3479_ = v___y_3823_;
v___y_3480_ = v___y_3824_;
v_a_3481_ = v_a_3829_;
goto v___jp_3478_;
}
}
v___jp_3830_:
{
if (v___y_3837_ == 0)
{
lean_object* v___x_3838_; 
lean_dec_ref(v___y_3831_);
v___x_3838_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3833_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3833_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_dec_ref_known(v___x_3838_, 1);
v___y_3815_ = v___y_3832_;
v___y_3816_ = v___y_3834_;
v___y_3817_ = v___y_3835_;
v___y_3818_ = v___y_3836_;
v_a_3819_ = v_snd_2983_;
goto v___jp_3814_;
}
else
{
lean_object* v_a_3839_; 
lean_dec(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec(v_snd_2983_);
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref_known(v___x_3838_, 1);
v___y_3479_ = v___y_3832_;
v___y_3480_ = v___y_3834_;
v_a_3481_ = v_a_3839_;
goto v___jp_3478_;
}
}
else
{
lean_dec_ref(v___y_3833_);
lean_dec(v_snd_2983_);
v___y_3823_ = v___y_3832_;
v___y_3824_ = v___y_3834_;
v___y_3825_ = v___y_3835_;
v___y_3826_ = v___y_3836_;
v___y_3827_ = v___y_3831_;
goto v___jp_3822_;
}
}
v___jp_3840_:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_Meta_saveState___redArg(v_a_2972_, v_a_2974_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3848_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v___x_3846_, 1);
lean_inc(v_snd_2983_);
lean_inc(v_trace_2966_);
v___x_3848_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3844_, v_snd_2983_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_dec(v_a_3847_);
lean_dec(v_snd_2983_);
v___y_3823_ = v___y_3841_;
v___y_3824_ = v___y_3842_;
v___y_3825_ = v___y_3843_;
v___y_3826_ = v___y_3845_;
v___y_3827_ = v___x_3848_;
goto v___jp_3822_;
}
else
{
lean_object* v_a_3849_; uint8_t v___x_3850_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
v___x_3850_ = l_Lean_Exception_isInterrupt(v_a_3849_);
if (v___x_3850_ == 0)
{
uint8_t v___x_3851_; 
v___x_3851_ = l_Lean_Exception_isRuntime(v_a_3849_);
v___y_3831_ = v___x_3848_;
v___y_3832_ = v___y_3841_;
v___y_3833_ = v_a_3847_;
v___y_3834_ = v___y_3842_;
v___y_3835_ = v___y_3843_;
v___y_3836_ = v___y_3845_;
v___y_3837_ = v___x_3851_;
goto v___jp_3830_;
}
else
{
lean_dec(v_a_3849_);
v___y_3831_ = v___x_3848_;
v___y_3832_ = v___y_3841_;
v___y_3833_ = v_a_3847_;
v___y_3834_ = v___y_3842_;
v___y_3835_ = v___y_3843_;
v___y_3836_ = v___y_3845_;
v___y_3837_ = v___x_3850_;
goto v___jp_3830_;
}
}
}
else
{
lean_object* v_a_3852_; 
lean_dec(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3852_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3852_);
lean_dec_ref_known(v___x_3846_, 1);
v___y_3479_ = v___y_3841_;
v___y_3480_ = v___y_3842_;
v_a_3481_ = v_a_3852_;
goto v___jp_3478_;
}
}
v___jp_3853_:
{
uint8_t v_commitIndependentGoals_3860_; lean_object* v___x_3861_; 
v_commitIndependentGoals_3860_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3858_);
v___x_3861_ = l_List_appendTR___redArg(v_a_3859_, v___y_3858_);
if (v_commitIndependentGoals_3860_ == 0)
{
v___y_3804_ = v___y_3854_;
v___y_3805_ = v___y_3855_;
v___y_3806_ = v___y_3856_;
v___y_3807_ = v___x_3861_;
v___y_3808_ = v___y_3857_;
v___y_3809_ = v___y_3858_;
goto v___jp_3803_;
}
else
{
uint8_t v___x_3862_; 
v___x_3862_ = l_List_isEmpty___redArg(v___y_3858_);
if (v___x_3862_ == 0)
{
v___y_3841_ = v___y_3855_;
v___y_3842_ = v___y_3856_;
v___y_3843_ = v___y_3857_;
v___y_3844_ = v___x_3861_;
v___y_3845_ = v___y_3858_;
goto v___jp_3840_;
}
else
{
if (v___y_3854_ == 0)
{
v___y_3804_ = v___y_3854_;
v___y_3805_ = v___y_3855_;
v___y_3806_ = v___y_3856_;
v___y_3807_ = v___x_3861_;
v___y_3808_ = v___y_3857_;
v___y_3809_ = v___y_3858_;
goto v___jp_3803_;
}
else
{
v___y_3841_ = v___y_3855_;
v___y_3842_ = v___y_3856_;
v___y_3843_ = v___y_3857_;
v___y_3844_ = v___x_3861_;
v___y_3845_ = v___y_3858_;
goto v___jp_3840_;
}
}
}
}
v___jp_3863_:
{
lean_object* v___x_3864_; 
v___x_3864_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2974_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
v___x_3866_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3867_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2988_, v___x_3866_);
if (v___x_3867_ == 0)
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = lean_io_mono_nanos_now();
v___x_3869_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2982_, v___f_2991_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v_fst_3871_; lean_object* v_snd_3872_; lean_object* v___x_3873_; lean_object* v___f_3874_; lean_object* v___x_3875_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v_fst_3871_ = lean_ctor_get(v_a_3870_, 0);
lean_inc_n(v_fst_3871_, 2);
v_snd_3872_ = lean_ctor_get(v_a_3870_, 1);
lean_inc(v_snd_3872_);
lean_dec(v_a_3870_);
v___x_3873_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3872_, v___x_2979_);
lean_inc(v___x_3873_);
v___f_3874_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3874_, 0, v_fst_3871_);
lean_closure_set(v___f_3874_, 1, v___x_3873_);
v___x_3875_ = lean_box(0);
if (v___x_3075_ == 0)
{
lean_object* v___x_3876_; uint8_t v___x_3877_; 
v___x_3876_ = l_Lean_trace_profiler;
v___x_3877_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2988_, v___x_3876_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; 
lean_dec_ref(v___f_3874_);
v___x_3878_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2990_, v___x_3867_, v_goals_2969_, v___x_3875_, v_a_2972_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3880_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
v___x_3880_ = l_List_reverse___redArg(v_a_3879_);
v___y_3457_ = v_a_3865_;
v___y_3458_ = v___x_3873_;
v___y_3459_ = v___x_3868_;
v___y_3460_ = v___x_3877_;
v___y_3461_ = v_fst_3871_;
v_a_3462_ = v___x_3880_;
goto v___jp_3456_;
}
else
{
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3881_; 
v_a_3881_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3878_, 1);
v___y_3457_ = v_a_3865_;
v___y_3458_ = v___x_3873_;
v___y_3459_ = v___x_3868_;
v___y_3460_ = v___x_3877_;
v___y_3461_ = v_fst_3871_;
v_a_3462_ = v_a_3881_;
goto v___jp_3456_;
}
else
{
lean_object* v_a_3882_; 
lean_dec(v___x_3873_);
lean_dec(v_fst_3871_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3882_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3878_, 1);
v___y_3107_ = v_a_3865_;
v___y_3108_ = v___x_3868_;
v_a_3109_ = v_a_3882_;
goto v___jp_3106_;
}
}
}
else
{
v___y_3416_ = v___x_3075_;
v___y_3417_ = v_a_3865_;
v___y_3418_ = v___x_3873_;
v___y_3419_ = v___x_3868_;
v___y_3420_ = v___x_3875_;
v___y_3421_ = v___f_3874_;
v___y_3422_ = v_fst_3871_;
v___y_3423_ = v___x_3867_;
goto v___jp_3415_;
}
}
else
{
v___y_3416_ = v___x_3075_;
v___y_3417_ = v_a_3865_;
v___y_3418_ = v___x_3873_;
v___y_3419_ = v___x_3868_;
v___y_3420_ = v___x_3875_;
v___y_3421_ = v___f_3874_;
v___y_3422_ = v_fst_3871_;
v___y_3423_ = v___x_3867_;
goto v___jp_3415_;
}
}
else
{
lean_object* v_a_3883_; 
lean_dec(v_snd_2983_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3883_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3869_, 1);
v___y_3107_ = v_a_3865_;
v___y_3108_ = v___x_3868_;
v_a_3109_ = v_a_3883_;
goto v___jp_3106_;
}
}
else
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
lean_del_object(v___x_2985_);
v___x_3884_ = lean_io_get_num_heartbeats();
v___x_3885_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2982_, v___f_2991_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v_fst_3887_; lean_object* v_snd_3888_; lean_object* v___x_3889_; lean_object* v___f_3890_; lean_object* v___x_3891_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
v_fst_3887_ = lean_ctor_get(v_a_3886_, 0);
lean_inc_n(v_fst_3887_, 2);
v_snd_3888_ = lean_ctor_get(v_a_3886_, 1);
lean_inc(v_snd_3888_);
lean_dec(v_a_3886_);
v___x_3889_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3888_, v___x_2979_);
lean_inc(v___x_3889_);
v___f_3890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3890_, 0, v_fst_3887_);
lean_closure_set(v___f_3890_, 1, v___x_3889_);
v___x_3891_ = lean_box(0);
if (v___x_3075_ == 0)
{
lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3892_ = l_Lean_trace_profiler;
v___x_3893_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2988_, v___x_3892_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; 
lean_dec_ref(v___f_3890_);
v___x_3894_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3867_, v___x_2987_, v_goals_2969_, v___x_3891_, v_a_2972_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3896_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref_known(v___x_3894_, 1);
v___x_3896_ = l_List_reverse___redArg(v_a_3895_);
v___y_3854_ = v___x_3893_;
v___y_3855_ = v_a_3865_;
v___y_3856_ = v___x_3884_;
v___y_3857_ = v_fst_3887_;
v___y_3858_ = v___x_3889_;
v_a_3859_ = v___x_3896_;
goto v___jp_3853_;
}
else
{
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3897_; 
v_a_3897_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3894_, 1);
v___y_3854_ = v___x_3893_;
v___y_3855_ = v_a_3865_;
v___y_3856_ = v___x_3884_;
v___y_3857_ = v_fst_3887_;
v___y_3858_ = v___x_3889_;
v_a_3859_ = v_a_3897_;
goto v___jp_3853_;
}
else
{
lean_object* v_a_3898_; 
lean_dec(v___x_3889_);
lean_dec(v_fst_3887_);
lean_dec(v_snd_2983_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3898_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3894_, 1);
v___y_3479_ = v_a_3865_;
v___y_3480_ = v___x_3884_;
v_a_3481_ = v_a_3898_;
goto v___jp_3478_;
}
}
}
else
{
v___y_3774_ = v___f_3890_;
v___y_3775_ = v_a_3865_;
v___y_3776_ = v___x_3075_;
v___y_3777_ = v___x_3884_;
v___y_3778_ = v___x_3891_;
v___y_3779_ = v_fst_3887_;
v___y_3780_ = v___x_3889_;
v___y_3781_ = v___x_3867_;
goto v___jp_3773_;
}
}
else
{
v___y_3774_ = v___f_3890_;
v___y_3775_ = v_a_3865_;
v___y_3776_ = v___x_3075_;
v___y_3777_ = v___x_3884_;
v___y_3778_ = v___x_3891_;
v___y_3779_ = v_fst_3887_;
v___y_3780_ = v___x_3889_;
v___y_3781_ = v___x_3867_;
goto v___jp_3773_;
}
}
else
{
lean_object* v_a_3899_; 
lean_dec(v_snd_2983_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3899_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3899_);
lean_dec_ref_known(v___x_3885_, 1);
v___y_3479_ = v_a_3865_;
v___y_3480_ = v___x_3884_;
v_a_3481_ = v_a_3899_;
goto v___jp_3478_;
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec_ref(v___f_3071_);
lean_dec_ref(v___f_2991_);
lean_del_object(v___x_2985_);
lean_dec(v_snd_2983_);
lean_dec(v_fst_2982_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_3900_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3864_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3864_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
}
}
else
{
lean_object* v_maxDepth_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
lean_del_object(v___x_2985_);
lean_dec(v_snd_2983_);
lean_dec(v_fst_2982_);
lean_dec(v_goals_2969_);
v_maxDepth_4188_ = lean_ctor_get(v_cfg_2965_, 0);
lean_inc(v_maxDepth_4188_);
v___x_4189_ = lean_box(0);
v___x_4190_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v_maxDepth_4188_, v_remaining_2970_, v___x_4189_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_4190_;
}
}
}
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec(v_remaining_2970_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_4192_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_2980_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_2980_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
v___jp_2976_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_2978_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_2977_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_2978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_4200_, lean_object* v_trace_4201_, lean_object* v_next_4202_, lean_object* v_orig_4203_, lean_object* v_goals_4204_, lean_object* v_remaining_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4200_, v_trace_4201_, v_next_4202_, v_orig_4203_, v_goals_4204_, v_remaining_4205_, v_a_4206_, v_a_4207_, v_a_4208_, v_a_4209_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
lean_dec(v_a_4207_);
lean_dec_ref(v_a_4206_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_4212_, lean_object* v_00_u03b2_4213_, lean_object* v_L_4214_, lean_object* v_f_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_4214_, v_f_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_4222_, lean_object* v_00_u03b2_4223_, lean_object* v_L_4224_, lean_object* v_f_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_4222_, v_00_u03b2_4223_, v_L_4224_, v_f_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_4232_, lean_object* v_x_4233_, lean_object* v_x_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_4232_, v_x_4233_, v_x_4234_, v___y_4236_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_4241_, lean_object* v_x_4242_, lean_object* v_x_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
uint8_t v___x_60526__boxed_4249_; lean_object* v_res_4250_; 
v___x_60526__boxed_4249_ = lean_unbox(v___x_4241_);
v_res_4250_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_60526__boxed_4249_, v_x_4242_, v_x_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_4251_, uint8_t v___x_4252_, lean_object* v_x_4253_, lean_object* v_x_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_4251_, v___x_4252_, v_x_4253_, v_x_4254_, v___y_4256_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_4261_, lean_object* v___x_4262_, lean_object* v_x_4263_, lean_object* v_x_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
uint8_t v___x_60552__boxed_4270_; uint8_t v___x_60553__boxed_4271_; lean_object* v_res_4272_; 
v___x_60552__boxed_4270_ = lean_unbox(v___x_4261_);
v___x_60553__boxed_4271_ = lean_unbox(v___x_4262_);
v_res_4272_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_60552__boxed_4270_, v___x_60553__boxed_4271_, v_x_4263_, v_x_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_4273_, lean_object* v_00_u03b2_4274_, lean_object* v_f_4275_, lean_object* v_x_4276_, lean_object* v_x_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_4275_, v_x_4276_, v_x_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4284_, lean_object* v_00_u03b2_4285_, lean_object* v_f_4286_, lean_object* v_x_4287_, lean_object* v_x_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_4284_, v_00_u03b2_4285_, v_f_4286_, v_x_4287_, v_x_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_4295_, lean_object* v_00_u03b2_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_4297_, v_a_4298_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_4300_, lean_object* v_00_u03b2_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_4302_, v_a_4303_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_4305_, lean_object* v_g_4306_, lean_object* v_f_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; 
lean_inc(v___y_4311_);
lean_inc_ref(v___y_4310_);
lean_inc(v___y_4309_);
lean_inc_ref(v___y_4308_);
v___x_4313_ = lean_apply_6(v_next_4305_, v_g_4306_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, lean_box(0));
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4315_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4313_, 1);
v___x_4315_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_4314_, v_f_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
return v___x_4315_;
}
else
{
lean_object* v_a_4316_; lean_object* v___x_4318_; uint8_t v_isShared_4319_; uint8_t v_isSharedCheck_4323_; 
lean_dec_ref(v_f_4307_);
v_a_4316_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4318_ = v___x_4313_;
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
else
{
lean_inc(v_a_4316_);
lean_dec(v___x_4313_);
v___x_4318_ = lean_box(0);
v_isShared_4319_ = v_isSharedCheck_4323_;
goto v_resetjp_4317_;
}
v_resetjp_4317_:
{
lean_object* v___x_4321_; 
if (v_isShared_4319_ == 0)
{
v___x_4321_ = v___x_4318_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_4324_, lean_object* v_g_4325_, lean_object* v_f_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_4324_, v_g_4325_, v_f_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_4333_, lean_object* v_trace_4334_, lean_object* v_next_4335_, lean_object* v_goals_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v_resolve_4342_; lean_object* v___x_4343_; 
v_resolve_4342_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_4342_, 0, v_next_4335_);
lean_inc_n(v_goals_4336_, 2);
v___x_4343_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4333_, v_trace_4334_, v_resolve_4342_, v_goals_4336_, v_goals_4336_, v_goals_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_4344_, lean_object* v_trace_4345_, lean_object* v_next_4346_, lean_object* v_goals_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_4344_, v_trace_4345_, v_next_4346_, v_goals_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
return v_res_4353_;
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

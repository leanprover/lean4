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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0(void){
_start:
{
size_t v___x_697_; size_t v___x_698_; size_t v___x_699_; 
v___x_697_ = ((size_t)5ULL);
v___x_698_ = ((size_t)1ULL);
v___x_699_ = lean_usize_shift_left(v___x_698_, v___x_697_);
return v___x_699_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1(void){
_start:
{
size_t v___x_700_; size_t v___x_701_; size_t v___x_702_; 
v___x_700_ = ((size_t)1ULL);
v___x_701_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__0);
v___x_702_ = lean_usize_sub(v___x_701_, v___x_700_);
return v___x_702_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_703_, size_t v_x_704_, lean_object* v_x_705_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_object* v_es_706_; lean_object* v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; lean_object* v_j_711_; lean_object* v___x_712_; 
v_es_706_ = lean_ctor_get(v_x_703_, 0);
v___x_707_ = lean_box(2);
v___x_708_ = ((size_t)5ULL);
v___x_709_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___closed__1);
v___x_710_ = lean_usize_land(v_x_704_, v___x_709_);
v_j_711_ = lean_usize_to_nat(v___x_710_);
v___x_712_ = lean_array_get_borrowed(v___x_707_, v_es_706_, v_j_711_);
lean_dec(v_j_711_);
switch(lean_obj_tag(v___x_712_))
{
case 0:
{
lean_object* v_key_713_; uint8_t v___x_714_; 
v_key_713_ = lean_ctor_get(v___x_712_, 0);
v___x_714_ = l_Lean_instBEqMVarId_beq(v_x_705_, v_key_713_);
return v___x_714_;
}
case 1:
{
lean_object* v_node_715_; size_t v___x_716_; 
v_node_715_ = lean_ctor_get(v___x_712_, 0);
v___x_716_ = lean_usize_shift_right(v_x_704_, v___x_708_);
v_x_703_ = v_node_715_;
v_x_704_ = v___x_716_;
goto _start;
}
default: 
{
uint8_t v___x_718_; 
v___x_718_ = 0;
return v___x_718_;
}
}
}
else
{
lean_object* v_ks_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_ks_719_ = lean_ctor_get(v_x_703_, 0);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_ks_719_, v___x_720_, v_x_705_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
size_t v_x_82064__boxed_725_; uint8_t v_res_726_; lean_object* v_r_727_; 
v_x_82064__boxed_725_ = lean_unbox_usize(v_x_723_);
lean_dec(v_x_723_);
v_res_726_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_722_, v_x_82064__boxed_725_, v_x_724_);
lean_dec(v_x_724_);
lean_dec_ref(v_x_722_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
uint64_t v___x_730_; size_t v___x_731_; uint8_t v___x_732_; 
v___x_730_ = l_Lean_instHashableMVarId_hash(v_x_729_);
v___x_731_ = lean_uint64_to_usize(v___x_730_);
v___x_732_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_728_, v___x_731_, v_x_729_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
uint8_t v_res_735_; lean_object* v_r_736_; 
v_res_735_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_733_, v_x_734_);
lean_dec(v_x_734_);
lean_dec_ref(v_x_733_);
v_r_736_ = lean_box(v_res_735_);
return v_r_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object* v_mvarId_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; lean_object* v_mctx_741_; lean_object* v_eAssignment_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_740_ = lean_st_ref_get(v___y_738_);
v_mctx_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc_ref(v_mctx_741_);
lean_dec(v___x_740_);
v_eAssignment_742_ = lean_ctor_get(v_mctx_741_, 8);
lean_inc_ref(v_eAssignment_742_);
lean_dec_ref(v_mctx_741_);
v___x_743_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_eAssignment_742_, v_mvarId_737_);
lean_dec_ref(v_eAssignment_742_);
v___x_744_ = lean_box(v___x_743_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object* v_mvarId_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec(v_mvarId_746_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_ref_756_; lean_object* v___x_757_; lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_766_; 
v_ref_756_ = lean_ctor_get(v___y_753_, 5);
v___x_757_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_766_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
lean_inc(v_ref_756_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v_ref_756_);
lean_ctor_set(v___x_762_, 1, v_a_758_);
if (v_isShared_761_ == 0)
{
lean_ctor_set_tag(v___x_760_, 1);
lean_ctor_set(v___x_760_, 0, v___x_762_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_773_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_e_774_){
_start:
{
if (lean_obj_tag(v_e_774_) == 0)
{
uint8_t v___x_775_; 
v___x_775_ = 2;
return v___x_775_;
}
else
{
uint8_t v___x_776_; 
v___x_776_ = 0;
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_e_777_){
_start:
{
uint8_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_e_777_);
lean_dec_ref(v_e_777_);
v_r_779_ = lean_box(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_780_, uint8_t v_collapsed_781_, lean_object* v_tag_782_, lean_object* v_opts_783_, uint8_t v_clsEnabled_784_, lean_object* v_oldTraces_785_, lean_object* v_msg_786_, lean_object* v_resStartStop_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_fst_793_; lean_object* v_snd_794_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v_data_798_; lean_object* v_fst_809_; lean_object* v_snd_810_; lean_object* v___x_811_; uint8_t v___x_812_; lean_object* v___y_814_; lean_object* v_a_815_; uint8_t v___y_830_; double v___y_861_; 
v_fst_793_ = lean_ctor_get(v_resStartStop_787_, 0);
lean_inc(v_fst_793_);
v_snd_794_ = lean_ctor_get(v_resStartStop_787_, 1);
lean_inc(v_snd_794_);
lean_dec_ref(v_resStartStop_787_);
v_fst_809_ = lean_ctor_get(v_snd_794_, 0);
lean_inc(v_fst_809_);
v_snd_810_ = lean_ctor_get(v_snd_794_, 1);
lean_inc(v_snd_810_);
lean_dec(v_snd_794_);
v___x_811_ = l_Lean_trace_profiler;
v___x_812_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_783_, v___x_811_);
if (v___x_812_ == 0)
{
v___y_830_ = v___x_812_;
goto v___jp_829_;
}
else
{
lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_866_ = l_Lean_trace_profiler_useHeartbeats;
v___x_867_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_783_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; double v___x_870_; double v___x_871_; double v___x_872_; 
v___x_868_ = l_Lean_trace_profiler_threshold;
v___x_869_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_783_, v___x_868_);
v___x_870_ = lean_float_of_nat(v___x_869_);
v___x_871_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_872_ = lean_float_div(v___x_870_, v___x_871_);
v___y_861_ = v___x_872_;
goto v___jp_860_;
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; double v___x_875_; 
v___x_873_ = l_Lean_trace_profiler_threshold;
v___x_874_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_783_, v___x_873_);
v___x_875_ = lean_float_of_nat(v___x_874_);
v___y_861_ = v___x_875_;
goto v___jp_860_;
}
}
v___jp_795_:
{
lean_object* v___x_799_; 
lean_inc(v___y_797_);
v___x_799_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_785_, v_data_798_, v___y_797_, v___y_796_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; 
lean_dec_ref_known(v___x_799_, 1);
v___x_800_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_793_);
return v___x_800_;
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec(v_fst_793_);
v_a_801_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_799_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
v___jp_813_:
{
uint8_t v_result_816_; lean_object* v___x_817_; lean_object* v___x_818_; double v___x_819_; lean_object* v_data_820_; 
v_result_816_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_fst_793_);
v___x_817_ = lean_box(v_result_816_);
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
v___x_819_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_782_);
lean_inc_ref(v___x_818_);
lean_inc(v_cls_780_);
v_data_820_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_820_, 0, v_cls_780_);
lean_ctor_set(v_data_820_, 1, v___x_818_);
lean_ctor_set(v_data_820_, 2, v_tag_782_);
lean_ctor_set_float(v_data_820_, sizeof(void*)*3, v___x_819_);
lean_ctor_set_float(v_data_820_, sizeof(void*)*3 + 8, v___x_819_);
lean_ctor_set_uint8(v_data_820_, sizeof(void*)*3 + 16, v_collapsed_781_);
if (v___x_812_ == 0)
{
lean_dec_ref_known(v___x_818_, 1);
lean_dec(v_snd_810_);
lean_dec(v_fst_809_);
lean_dec_ref(v_tag_782_);
lean_dec(v_cls_780_);
v___y_796_ = v_a_815_;
v___y_797_ = v___y_814_;
v_data_798_ = v_data_820_;
goto v___jp_795_;
}
else
{
lean_object* v_data_821_; double v___x_822_; double v___x_823_; 
lean_dec_ref_known(v_data_820_, 3);
v_data_821_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_821_, 0, v_cls_780_);
lean_ctor_set(v_data_821_, 1, v___x_818_);
lean_ctor_set(v_data_821_, 2, v_tag_782_);
v___x_822_ = lean_unbox_float(v_fst_809_);
lean_dec(v_fst_809_);
lean_ctor_set_float(v_data_821_, sizeof(void*)*3, v___x_822_);
v___x_823_ = lean_unbox_float(v_snd_810_);
lean_dec(v_snd_810_);
lean_ctor_set_float(v_data_821_, sizeof(void*)*3 + 8, v___x_823_);
lean_ctor_set_uint8(v_data_821_, sizeof(void*)*3 + 16, v_collapsed_781_);
v___y_796_ = v_a_815_;
v___y_797_ = v___y_814_;
v_data_798_ = v_data_821_;
goto v___jp_795_;
}
}
v___jp_824_:
{
lean_object* v_ref_825_; lean_object* v___x_826_; 
v_ref_825_ = lean_ctor_get(v___y_790_, 5);
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
lean_inc(v_fst_793_);
v___x_826_ = lean_apply_6(v_msg_786_, v_fst_793_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, lean_box(0));
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
v___y_814_ = v_ref_825_;
v_a_815_ = v_a_827_;
goto v___jp_813_;
}
else
{
lean_object* v___x_828_; 
lean_dec_ref_known(v___x_826_, 1);
v___x_828_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_814_ = v_ref_825_;
v_a_815_ = v___x_828_;
goto v___jp_813_;
}
}
v___jp_829_:
{
if (v_clsEnabled_784_ == 0)
{
if (v___y_830_ == 0)
{
lean_object* v___x_831_; lean_object* v_traceState_832_; lean_object* v_env_833_; lean_object* v_nextMacroScope_834_; lean_object* v_ngen_835_; lean_object* v_auxDeclNGen_836_; lean_object* v_cache_837_; lean_object* v_messages_838_; lean_object* v_infoState_839_; lean_object* v_snapshotTasks_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_859_; 
lean_dec(v_snd_810_);
lean_dec(v_fst_809_);
lean_dec_ref(v_msg_786_);
lean_dec_ref(v_tag_782_);
lean_dec(v_cls_780_);
v___x_831_ = lean_st_ref_take(v___y_791_);
v_traceState_832_ = lean_ctor_get(v___x_831_, 4);
v_env_833_ = lean_ctor_get(v___x_831_, 0);
v_nextMacroScope_834_ = lean_ctor_get(v___x_831_, 1);
v_ngen_835_ = lean_ctor_get(v___x_831_, 2);
v_auxDeclNGen_836_ = lean_ctor_get(v___x_831_, 3);
v_cache_837_ = lean_ctor_get(v___x_831_, 5);
v_messages_838_ = lean_ctor_get(v___x_831_, 6);
v_infoState_839_ = lean_ctor_get(v___x_831_, 7);
v_snapshotTasks_840_ = lean_ctor_get(v___x_831_, 8);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_859_ == 0)
{
v___x_842_ = v___x_831_;
v_isShared_843_ = v_isSharedCheck_859_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_snapshotTasks_840_);
lean_inc(v_infoState_839_);
lean_inc(v_messages_838_);
lean_inc(v_cache_837_);
lean_inc(v_traceState_832_);
lean_inc(v_auxDeclNGen_836_);
lean_inc(v_ngen_835_);
lean_inc(v_nextMacroScope_834_);
lean_inc(v_env_833_);
lean_dec(v___x_831_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_859_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
uint64_t v_tid_844_; lean_object* v_traces_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_858_; 
v_tid_844_ = lean_ctor_get_uint64(v_traceState_832_, sizeof(void*)*1);
v_traces_845_ = lean_ctor_get(v_traceState_832_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_traceState_832_);
if (v_isSharedCheck_858_ == 0)
{
v___x_847_ = v_traceState_832_;
v_isShared_848_ = v_isSharedCheck_858_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_traces_845_);
lean_dec(v_traceState_832_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_858_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_785_, v_traces_845_);
lean_dec_ref(v_traces_845_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_849_);
lean_ctor_set_uint64(v_reuseFailAlloc_857_, sizeof(void*)*1, v_tid_844_);
v___x_851_ = v_reuseFailAlloc_857_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_853_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 4, v___x_851_);
v___x_853_ = v___x_842_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_env_833_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_nextMacroScope_834_);
lean_ctor_set(v_reuseFailAlloc_856_, 2, v_ngen_835_);
lean_ctor_set(v_reuseFailAlloc_856_, 3, v_auxDeclNGen_836_);
lean_ctor_set(v_reuseFailAlloc_856_, 4, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_856_, 5, v_cache_837_);
lean_ctor_set(v_reuseFailAlloc_856_, 6, v_messages_838_);
lean_ctor_set(v_reuseFailAlloc_856_, 7, v_infoState_839_);
lean_ctor_set(v_reuseFailAlloc_856_, 8, v_snapshotTasks_840_);
v___x_853_ = v_reuseFailAlloc_856_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_st_ref_set(v___y_791_, v___x_853_);
v___x_855_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_793_);
return v___x_855_;
}
}
}
}
}
else
{
goto v___jp_824_;
}
}
else
{
goto v___jp_824_;
}
}
v___jp_860_:
{
double v___x_862_; double v___x_863_; double v___x_864_; uint8_t v___x_865_; 
v___x_862_ = lean_unbox_float(v_snd_810_);
v___x_863_ = lean_unbox_float(v_fst_809_);
v___x_864_ = lean_float_sub(v___x_862_, v___x_863_);
v___x_865_ = lean_float_decLt(v___y_861_, v___x_864_);
v___y_830_ = v___x_865_;
goto v___jp_829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_876_, lean_object* v_collapsed_877_, lean_object* v_tag_878_, lean_object* v_opts_879_, lean_object* v_clsEnabled_880_, lean_object* v_oldTraces_881_, lean_object* v_msg_882_, lean_object* v_resStartStop_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v_collapsed_boxed_889_; uint8_t v_clsEnabled_boxed_890_; lean_object* v_res_891_; 
v_collapsed_boxed_889_ = lean_unbox(v_collapsed_877_);
v_clsEnabled_boxed_890_ = lean_unbox(v_clsEnabled_880_);
v_res_891_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_876_, v_collapsed_boxed_889_, v_tag_878_, v_opts_879_, v_clsEnabled_boxed_890_, v_oldTraces_881_, v_msg_882_, v_resStartStop_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_opts_879_);
return v_res_891_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_head_895_, lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_903_, 0, v_head_895_);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_head_906_, lean_object* v_x_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_head_906_, v_x_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec_ref(v_x_907_);
return v_res_913_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0));
v___x_916_ = l_Lean_stringToMessageData(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object* v_head_917_, lean_object* v_x_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_935_; 
v___x_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_924_, 0, v_head_917_);
v___x_925_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v___x_924_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_935_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_935_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_930_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v_a_926_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_931_);
v___x_933_ = v___x_928_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object* v_head_936_, lean_object* v_x_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(v_head_936_, v_x_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec_ref(v_x_937_);
return v_res_943_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_944_; double v___x_945_; 
v___x_944_ = lean_unsigned_to_nat(1000000000u);
v___x_945_ = lean_float_of_nat(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* v_tail_957_, lean_object* v_cfg_958_, lean_object* v_trace_959_, lean_object* v_next_960_, lean_object* v_goals_961_, lean_object* v_n_962_, lean_object* v_acc_963_, lean_object* v_r_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_957_, v_cfg_958_, v_trace_959_, v_next_960_, v_goals_961_, v_n_962_, v_acc_963_, v_r_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_971_, lean_object* v_trace_972_, lean_object* v_next_973_, lean_object* v_goals_974_, lean_object* v_n_975_, lean_object* v_curr_976_, lean_object* v_acc_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v___y_984_; uint8_t v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; uint8_t v___y_989_; lean_object* v___y_990_; lean_object* v_a_991_; lean_object* v___y_1001_; uint8_t v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; uint8_t v___y_1006_; lean_object* v___y_1007_; lean_object* v_a_1008_; lean_object* v___y_1021_; uint8_t v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; uint8_t v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1069_; uint8_t v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; uint8_t v___y_1075_; lean_object* v_a_1076_; lean_object* v___y_1086_; uint8_t v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; uint8_t v___y_1092_; lean_object* v_a_1093_; lean_object* v___y_1096_; uint8_t v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; uint8_t v___y_1102_; lean_object* v_a_1103_; lean_object* v___y_1106_; uint8_t v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; uint8_t v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1117_; uint8_t v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; uint8_t v___y_1123_; lean_object* v_a_1124_; lean_object* v___y_1137_; uint8_t v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; uint8_t v___y_1143_; lean_object* v_a_1144_; lean_object* v___y_1147_; uint8_t v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; uint8_t v___y_1153_; lean_object* v_a_1154_; lean_object* v___y_1157_; uint8_t v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; uint8_t v___y_1163_; lean_object* v___y_1164_; lean_object* v_zero_1167_; uint8_t v_isZero_1168_; 
v_zero_1167_ = lean_unsigned_to_nat(0u);
v_isZero_1168_ = lean_nat_dec_eq(v_n_975_, v_zero_1167_);
if (v_isZero_1168_ == 1)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec(v_acc_977_);
lean_dec(v_curr_976_);
lean_dec(v_n_975_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
v___x_1169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1170_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1169_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1170_;
}
else
{
lean_object* v_proc_1171_; lean_object* v_suspend_1172_; lean_object* v_discharge_1173_; lean_object* v___f_1174_; uint8_t v___y_1176_; uint8_t v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___f_1216_; uint8_t v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; uint8_t v___y_1223_; lean_object* v_a_1224_; uint8_t v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; uint8_t v___y_1238_; lean_object* v___y_1239_; lean_object* v_a_1240_; lean_object* v___y_1253_; uint8_t v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; uint8_t v___y_1259_; lean_object* v___f_1300_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; uint8_t v___y_1306_; uint8_t v___y_1307_; lean_object* v_a_1308_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; uint8_t v___y_1325_; uint8_t v___y_1326_; lean_object* v_a_1327_; lean_object* v___f_1336_; lean_object* v___y_1338_; uint8_t v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; uint8_t v___y_1346_; uint8_t v___y_1347_; lean_object* v_a_1348_; lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; uint8_t v___y_1369_; uint8_t v___y_1370_; lean_object* v_a_1371_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; uint8_t v___y_1384_; lean_object* v___y_1385_; uint8_t v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; uint8_t v___y_1391_; uint8_t v___y_1392_; lean_object* v___y_1433_; lean_object* v___y_1434_; uint8_t v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; uint8_t v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; uint8_t v___y_1442_; lean_object* v_a_1443_; lean_object* v___y_1456_; uint8_t v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; uint8_t v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; uint8_t v___y_1465_; lean_object* v_a_1466_; uint8_t v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; uint8_t v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; uint8_t v___y_1486_; uint8_t v___y_1487_; lean_object* v___y_1528_; uint8_t v___y_1529_; uint8_t v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; uint8_t v___y_1536_; lean_object* v___y_1537_; lean_object* v_a_1538_; lean_object* v___y_1548_; uint8_t v___y_1549_; uint8_t v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; uint8_t v___y_1557_; lean_object* v_a_1558_; lean_object* v___y_1571_; lean_object* v___y_1572_; uint8_t v___y_1573_; lean_object* v___y_1574_; uint8_t v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; uint8_t v___y_1579_; lean_object* v___y_1580_; lean_object* v_a_1581_; lean_object* v___y_1591_; uint8_t v___y_1592_; lean_object* v___y_1593_; uint8_t v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; uint8_t v___y_1599_; lean_object* v___y_1600_; lean_object* v_a_1601_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; uint8_t v___y_1618_; lean_object* v___y_1619_; uint8_t v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___y_1623_; uint8_t v___y_1624_; uint8_t v___y_1625_; lean_object* v___y_1666_; lean_object* v___y_1667_; uint8_t v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; uint8_t v___y_1674_; uint8_t v___y_1675_; lean_object* v_a_1676_; lean_object* v___y_1689_; lean_object* v___y_1690_; uint8_t v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___y_1696_; uint8_t v___y_1697_; uint8_t v___y_1698_; lean_object* v_a_1699_; lean_object* v___y_1709_; uint8_t v___y_1710_; lean_object* v___y_1711_; uint8_t v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; uint8_t v___y_1718_; lean_object* v_a_1719_; lean_object* v___y_1732_; uint8_t v___y_1733_; lean_object* v___y_1734_; uint8_t v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; uint8_t v___y_1741_; lean_object* v_a_1742_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; uint8_t v___y_1757_; uint8_t v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; uint8_t v___y_1762_; uint8_t v___y_1763_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; uint8_t v___y_1807_; lean_object* v___y_1808_; uint8_t v___y_1809_; lean_object* v_a_1810_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; uint8_t v___y_1826_; lean_object* v___y_1827_; uint8_t v___y_1828_; lean_object* v_a_1829_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; uint8_t v___y_1844_; uint8_t v___y_1845_; lean_object* v_one_1886_; lean_object* v_n_1887_; lean_object* v___y_1889_; lean_object* v___y_1890_; uint8_t v___y_1891_; uint8_t v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1935_; uint8_t v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; uint8_t v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; uint8_t v___y_1944_; lean_object* v___y_1968_; lean_object* v___y_1969_; uint8_t v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; uint8_t v___y_1975_; uint8_t v___y_1976_; uint8_t v___y_1977_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; uint8_t v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; uint8_t v___y_2028_; uint8_t v___y_2029_; lean_object* v___y_2030_; uint8_t v___y_2031_; lean_object* v___y_2052_; uint8_t v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; uint8_t v___y_2060_; uint8_t v___y_2061_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; uint8_t v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; uint8_t v___y_2112_; uint8_t v___y_2113_; lean_object* v___y_2114_; uint8_t v___y_2115_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; uint8_t v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; uint8_t v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; uint8_t v___y_2193_; lean_object* v_a_2211_; lean_object* v___y_2302_; lean_object* v___x_2312_; 
v_proc_1171_ = lean_ctor_get(v_cfg_971_, 1);
v_suspend_1172_ = lean_ctor_get(v_cfg_971_, 2);
v_discharge_1173_ = lean_ctor_get(v_cfg_971_, 3);
v___f_1174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1886_ = lean_unsigned_to_nat(1u);
v_n_1887_ = lean_nat_sub(v_n_975_, v_one_1886_);
lean_dec(v_n_975_);
lean_inc_ref(v_proc_1171_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v_curr_976_);
lean_inc(v_goals_974_);
v___x_2312_ = lean_apply_7(v_proc_1171_, v_goals_974_, v_curr_976_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2312_, 1);
v_a_2211_ = v_a_2313_;
goto v___jp_2210_;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2381_; 
v_a_2314_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2316_ = v___x_2312_;
v_isShared_2317_ = v_isSharedCheck_2381_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2312_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2381_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___f_2318_; lean_object* v___y_2320_; lean_object* v___y_2321_; uint8_t v___y_2322_; uint8_t v___y_2323_; uint8_t v___y_2360_; uint8_t v___x_2379_; 
lean_inc(v_a_2314_);
v___f_2318_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(v___f_2318_, 0, v_a_2314_);
v___x_2379_ = l_Lean_Exception_isInterrupt(v_a_2314_);
if (v___x_2379_ == 0)
{
uint8_t v___x_2380_; 
lean_inc(v_a_2314_);
v___x_2380_ = l_Lean_Exception_isRuntime(v_a_2314_);
v___y_2360_ = v___x_2380_;
goto v___jp_2359_;
}
else
{
v___y_2360_ = v___x_2379_;
goto v___jp_2359_;
}
v___jp_2319_:
{
lean_object* v___x_2324_; lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2358_; 
v___x_2324_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2358_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2358_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2329_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2330_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2321_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2331_ = lean_io_mono_nanos_now();
v___x_2332_ = lean_io_mono_nanos_now();
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v_a_2314_);
v___x_2334_ = v___x_2327_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2314_);
v___x_2334_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
double v___x_2335_; double v___x_2336_; double v___x_2337_; double v___x_2338_; double v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2335_ = lean_float_of_nat(v___x_2331_);
v___x_2336_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2337_ = lean_float_div(v___x_2335_, v___x_2336_);
v___x_2338_ = lean_float_of_nat(v___x_2332_);
v___x_2339_ = lean_float_div(v___x_2338_, v___x_2336_);
v___x_2340_ = lean_box_float(v___x_2337_);
v___x_2341_ = lean_box_float(v___x_2339_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2334_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
lean_inc_ref(v___y_2320_);
lean_inc(v_trace_972_);
v___x_2344_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_972_, v___y_2323_, v___y_2320_, v___y_2321_, v___y_2322_, v_a_2325_, v___f_2318_, v___x_2343_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_2302_ = v___x_2344_;
goto v___jp_2301_;
}
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2346_ = lean_io_get_num_heartbeats();
v___x_2347_ = lean_io_get_num_heartbeats();
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v_a_2314_);
v___x_2349_ = v___x_2327_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2314_);
v___x_2349_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
double v___x_2350_; double v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2350_ = lean_float_of_nat(v___x_2346_);
v___x_2351_ = lean_float_of_nat(v___x_2347_);
v___x_2352_ = lean_box_float(v___x_2350_);
v___x_2353_ = lean_box_float(v___x_2351_);
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2352_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2349_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
lean_inc_ref(v___y_2320_);
lean_inc(v_trace_972_);
v___x_2356_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_972_, v___y_2323_, v___y_2320_, v___y_2321_, v___y_2322_, v_a_2325_, v___f_2318_, v___x_2355_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_2302_ = v___x_2356_;
goto v___jp_2301_;
}
}
}
}
v___jp_2359_:
{
if (v___y_2360_ == 0)
{
lean_object* v_options_2361_; uint8_t v_hasTrace_2362_; 
v_options_2361_ = lean_ctor_get(v_a_980_, 2);
v_hasTrace_2362_ = lean_ctor_get_uint8(v_options_2361_, sizeof(void*)*1);
if (v_hasTrace_2362_ == 0)
{
lean_object* v___x_2364_; 
lean_dec_ref(v___f_2318_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_curr_976_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
if (v_isShared_2317_ == 0)
{
v___x_2364_ = v___x_2316_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2314_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v_inheritedTraceOptions_2366_ = lean_ctor_get(v_a_980_, 13);
v___x_2367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_972_);
v___x_2369_ = l_Lean_Name_append(v___x_2368_, v_trace_972_);
v___x_2370_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2366_, v_options_2361_, v___x_2369_);
lean_dec(v___x_2369_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2371_ = l_Lean_trace_profiler;
v___x_2372_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2361_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2374_; 
lean_dec_ref(v___f_2318_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_curr_976_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
if (v_isShared_2317_ == 0)
{
v___x_2374_ = v___x_2316_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2314_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
else
{
lean_del_object(v___x_2316_);
v___y_2320_ = v___x_2367_;
v___y_2321_ = v_options_2361_;
v___y_2322_ = v___x_2370_;
v___y_2323_ = v_hasTrace_2362_;
goto v___jp_2319_;
}
}
else
{
lean_del_object(v___x_2316_);
v___y_2320_ = v___x_2367_;
v___y_2321_ = v_options_2361_;
v___y_2322_ = v___x_2370_;
v___y_2323_ = v_hasTrace_2362_;
goto v___jp_2319_;
}
}
}
else
{
lean_object* v___x_2377_; 
lean_dec_ref(v___f_2318_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_curr_976_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
if (v_isShared_2317_ == 0)
{
v___x_2377_ = v___x_2316_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2314_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
v___jp_1175_:
{
lean_object* v___x_1181_; lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1215_; 
v___x_1181_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1215_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1215_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1187_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1178_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1188_ = lean_io_mono_nanos_now();
v___x_1189_ = lean_io_mono_nanos_now();
if (v_isShared_1185_ == 0)
{
lean_ctor_set_tag(v___x_1184_, 1);
lean_ctor_set(v___x_1184_, 0, v___y_1179_);
v___x_1191_ = v___x_1184_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___y_1179_);
v___x_1191_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
double v___x_1192_; double v___x_1193_; double v___x_1194_; double v___x_1195_; double v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1192_ = lean_float_of_nat(v___x_1188_);
v___x_1193_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1194_ = lean_float_div(v___x_1192_, v___x_1193_);
v___x_1195_ = lean_float_of_nat(v___x_1189_);
v___x_1196_ = lean_float_div(v___x_1195_, v___x_1193_);
v___x_1197_ = lean_box_float(v___x_1194_);
v___x_1198_ = lean_box_float(v___x_1196_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1191_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
lean_inc_ref(v___y_1180_);
v___x_1201_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1176_, v___y_1180_, v___y_1178_, v___y_1177_, v_a_1182_, v___f_1174_, v___x_1200_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1201_;
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = lean_io_get_num_heartbeats();
v___x_1204_ = lean_io_get_num_heartbeats();
if (v_isShared_1185_ == 0)
{
lean_ctor_set_tag(v___x_1184_, 1);
lean_ctor_set(v___x_1184_, 0, v___y_1179_);
v___x_1206_ = v___x_1184_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___y_1179_);
v___x_1206_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
double v___x_1207_; double v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1207_ = lean_float_of_nat(v___x_1203_);
v___x_1208_ = lean_float_of_nat(v___x_1204_);
v___x_1209_ = lean_box_float(v___x_1207_);
v___x_1210_ = lean_box_float(v___x_1208_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1206_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
lean_inc_ref(v___y_1180_);
v___x_1213_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1176_, v___y_1180_, v___y_1178_, v___y_1177_, v_a_1182_, v___f_1174_, v___x_1212_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1213_;
}
}
}
}
v___jp_1217_:
{
lean_object* v___x_1225_; double v___x_1226_; double v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1225_ = lean_io_get_num_heartbeats();
v___x_1226_ = lean_float_of_nat(v___y_1222_);
v___x_1227_ = lean_float_of_nat(v___x_1225_);
v___x_1228_ = lean_box_float(v___x_1226_);
v___x_1229_ = lean_box_float(v___x_1227_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v_a_1224_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
lean_inc_ref(v___y_1220_);
v___x_1232_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1223_, v___y_1220_, v___y_1219_, v___y_1218_, v___y_1221_, v___f_1216_, v___x_1231_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1232_;
}
v___jp_1233_:
{
lean_object* v___x_1241_; double v___x_1242_; double v___x_1243_; double v___x_1244_; double v___x_1245_; double v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1241_ = lean_io_mono_nanos_now();
v___x_1242_ = lean_float_of_nat(v___y_1239_);
v___x_1243_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1244_ = lean_float_div(v___x_1242_, v___x_1243_);
v___x_1245_ = lean_float_of_nat(v___x_1241_);
v___x_1246_ = lean_float_div(v___x_1245_, v___x_1243_);
v___x_1247_ = lean_box_float(v___x_1244_);
v___x_1248_ = lean_box_float(v___x_1246_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_a_1240_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
lean_inc_ref(v___y_1236_);
v___x_1251_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1238_, v___y_1236_, v___y_1235_, v___y_1234_, v___y_1237_, v___f_1216_, v___x_1250_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1251_;
}
v___jp_1252_:
{
lean_object* v___x_1260_; lean_object* v_a_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1260_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref(v___x_1260_);
v___x_1262_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1263_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1257_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_io_mono_nanos_now();
lean_inc(v_trace_972_);
v___x_1265_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1255_, v___y_1258_, v___y_1253_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set_tag(v___x_1268_, 1);
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
v___y_1234_ = v___y_1254_;
v___y_1235_ = v___y_1257_;
v___y_1236_ = v___y_1256_;
v___y_1237_ = v_a_1261_;
v___y_1238_ = v___y_1259_;
v___y_1239_ = v___x_1264_;
v_a_1240_ = v___x_1271_;
goto v___jp_1233_;
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_a_1274_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1265_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1265_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 0);
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v___y_1234_ = v___y_1254_;
v___y_1235_ = v___y_1257_;
v___y_1236_ = v___y_1256_;
v___y_1237_ = v_a_1261_;
v___y_1238_ = v___y_1259_;
v___y_1239_ = v___x_1264_;
v_a_1240_ = v___x_1279_;
goto v___jp_1233_;
}
}
}
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_972_);
v___x_1283_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1255_, v___y_1258_, v___y_1253_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set_tag(v___x_1286_, 1);
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
v___y_1218_ = v___y_1254_;
v___y_1219_ = v___y_1257_;
v___y_1220_ = v___y_1256_;
v___y_1221_ = v_a_1261_;
v___y_1222_ = v___x_1282_;
v___y_1223_ = v___y_1259_;
v_a_1224_ = v___x_1289_;
goto v___jp_1217_;
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_a_1292_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1283_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1283_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set_tag(v___x_1294_, 0);
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
v___y_1218_ = v___y_1254_;
v___y_1219_ = v___y_1257_;
v___y_1220_ = v___y_1256_;
v___y_1221_ = v_a_1261_;
v___y_1222_ = v___x_1282_;
v___y_1223_ = v___y_1259_;
v_a_1224_ = v___x_1297_;
goto v___jp_1217_;
}
}
}
}
}
v___jp_1301_:
{
lean_object* v___x_1309_; double v___x_1310_; double v___x_1311_; double v___x_1312_; double v___x_1313_; double v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1309_ = lean_io_mono_nanos_now();
v___x_1310_ = lean_float_of_nat(v___y_1303_);
v___x_1311_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1312_ = lean_float_div(v___x_1310_, v___x_1311_);
v___x_1313_ = lean_float_of_nat(v___x_1309_);
v___x_1314_ = lean_float_div(v___x_1313_, v___x_1311_);
v___x_1315_ = lean_box_float(v___x_1312_);
v___x_1316_ = lean_box_float(v___x_1314_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v_a_1308_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
lean_inc_ref(v___y_1305_);
v___x_1319_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1307_, v___y_1305_, v___y_1304_, v___y_1306_, v___y_1302_, v___f_1300_, v___x_1318_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1319_;
}
v___jp_1320_:
{
lean_object* v___x_1328_; double v___x_1329_; double v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1328_ = lean_io_get_num_heartbeats();
v___x_1329_ = lean_float_of_nat(v___y_1321_);
v___x_1330_ = lean_float_of_nat(v___x_1328_);
v___x_1331_ = lean_box_float(v___x_1329_);
v___x_1332_ = lean_box_float(v___x_1330_);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_a_1327_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
lean_inc_ref(v___y_1324_);
v___x_1335_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1326_, v___y_1324_, v___y_1323_, v___y_1325_, v___y_1322_, v___f_1300_, v___x_1334_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1335_;
}
v___jp_1337_:
{
lean_object* v___x_1349_; double v___x_1350_; double v___x_1351_; double v___x_1352_; double v___x_1353_; double v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1349_ = lean_io_mono_nanos_now();
v___x_1350_ = lean_float_of_nat(v___y_1341_);
v___x_1351_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1352_ = lean_float_div(v___x_1350_, v___x_1351_);
v___x_1353_ = lean_float_of_nat(v___x_1349_);
v___x_1354_ = lean_float_div(v___x_1353_, v___x_1351_);
v___x_1355_ = lean_box_float(v___x_1352_);
v___x_1356_ = lean_box_float(v___x_1354_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v_a_1348_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
lean_inc_ref(v___y_1343_);
lean_inc(v_trace_972_);
v___x_1359_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1346_, v___y_1343_, v___y_1342_, v___y_1347_, v___y_1344_, v___f_1336_, v___x_1358_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1106_ = v___y_1338_;
v___y_1107_ = v___y_1339_;
v___y_1108_ = v___y_1340_;
v___y_1109_ = v___y_1342_;
v___y_1110_ = v___y_1343_;
v___y_1111_ = v___y_1345_;
v___y_1112_ = v___y_1346_;
v___y_1113_ = v___x_1359_;
goto v___jp_1105_;
}
v___jp_1360_:
{
lean_object* v___x_1372_; double v___x_1373_; double v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1372_ = lean_io_get_num_heartbeats();
v___x_1373_ = lean_float_of_nat(v___y_1368_);
v___x_1374_ = lean_float_of_nat(v___x_1372_);
v___x_1375_ = lean_box_float(v___x_1373_);
v___x_1376_ = lean_box_float(v___x_1374_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_a_1371_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
lean_inc_ref(v___y_1365_);
lean_inc(v_trace_972_);
v___x_1379_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1369_, v___y_1365_, v___y_1364_, v___y_1370_, v___y_1366_, v___f_1336_, v___x_1378_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1106_ = v___y_1361_;
v___y_1107_ = v___y_1362_;
v___y_1108_ = v___y_1363_;
v___y_1109_ = v___y_1364_;
v___y_1110_ = v___y_1365_;
v___y_1111_ = v___y_1367_;
v___y_1112_ = v___y_1369_;
v___y_1113_ = v___x_1379_;
goto v___jp_1105_;
}
v___jp_1380_:
{
lean_object* v___x_1393_; 
v___x_1393_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
if (v___y_1391_ == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___x_1393_);
v___x_1395_ = lean_io_mono_nanos_now();
lean_inc(v_trace_972_);
v___x_1396_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1383_, v___y_1388_, v___y_1390_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set_tag(v___x_1399_, 1);
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
v___y_1338_ = v___y_1385_;
v___y_1339_ = v___y_1386_;
v___y_1340_ = v___y_1381_;
v___y_1341_ = v___x_1395_;
v___y_1342_ = v___y_1382_;
v___y_1343_ = v___y_1387_;
v___y_1344_ = v_a_1394_;
v___y_1345_ = v___y_1389_;
v___y_1346_ = v___y_1392_;
v___y_1347_ = v___y_1384_;
v_a_1348_ = v___x_1402_;
goto v___jp_1337_;
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1396_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1396_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 0);
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
v___y_1338_ = v___y_1385_;
v___y_1339_ = v___y_1386_;
v___y_1340_ = v___y_1381_;
v___y_1341_ = v___x_1395_;
v___y_1342_ = v___y_1382_;
v___y_1343_ = v___y_1387_;
v___y_1344_ = v_a_1394_;
v___y_1345_ = v___y_1389_;
v___y_1346_ = v___y_1392_;
v___y_1347_ = v___y_1384_;
v_a_1348_ = v___x_1410_;
goto v___jp_1337_;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_a_1413_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1413_);
lean_dec_ref(v___x_1393_);
v___x_1414_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_972_);
v___x_1415_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1383_, v___y_1388_, v___y_1390_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
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
v___y_1361_ = v___y_1385_;
v___y_1362_ = v___y_1386_;
v___y_1363_ = v___y_1381_;
v___y_1364_ = v___y_1382_;
v___y_1365_ = v___y_1387_;
v___y_1366_ = v_a_1413_;
v___y_1367_ = v___y_1389_;
v___y_1368_ = v___x_1414_;
v___y_1369_ = v___y_1392_;
v___y_1370_ = v___y_1384_;
v_a_1371_ = v___x_1421_;
goto v___jp_1360_;
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
v___y_1361_ = v___y_1385_;
v___y_1362_ = v___y_1386_;
v___y_1363_ = v___y_1381_;
v___y_1364_ = v___y_1382_;
v___y_1365_ = v___y_1387_;
v___y_1366_ = v_a_1413_;
v___y_1367_ = v___y_1389_;
v___y_1368_ = v___x_1414_;
v___y_1369_ = v___y_1392_;
v___y_1370_ = v___y_1384_;
v_a_1371_ = v___x_1429_;
goto v___jp_1360_;
}
}
}
}
}
v___jp_1432_:
{
lean_object* v___x_1444_; double v___x_1445_; double v___x_1446_; double v___x_1447_; double v___x_1448_; double v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1444_ = lean_io_mono_nanos_now();
v___x_1445_ = lean_float_of_nat(v___y_1434_);
v___x_1446_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1447_ = lean_float_div(v___x_1445_, v___x_1446_);
v___x_1448_ = lean_float_of_nat(v___x_1444_);
v___x_1449_ = lean_float_div(v___x_1448_, v___x_1446_);
v___x_1450_ = lean_box_float(v___x_1447_);
v___x_1451_ = lean_box_float(v___x_1449_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v_a_1443_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
lean_inc_ref(v___y_1440_);
lean_inc(v_trace_972_);
v___x_1454_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1442_, v___y_1440_, v___y_1439_, v___y_1438_, v___y_1436_, v___f_1216_, v___x_1453_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1157_ = v___y_1433_;
v___y_1158_ = v___y_1435_;
v___y_1159_ = v___y_1437_;
v___y_1160_ = v___y_1439_;
v___y_1161_ = v___y_1440_;
v___y_1162_ = v___y_1441_;
v___y_1163_ = v___y_1442_;
v___y_1164_ = v___x_1454_;
goto v___jp_1156_;
}
v___jp_1455_:
{
lean_object* v___x_1467_; double v___x_1468_; double v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1467_ = lean_io_get_num_heartbeats();
v___x_1468_ = lean_float_of_nat(v___y_1463_);
v___x_1469_ = lean_float_of_nat(v___x_1467_);
v___x_1470_ = lean_box_float(v___x_1468_);
v___x_1471_ = lean_box_float(v___x_1469_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_a_1466_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
lean_inc_ref(v___y_1462_);
lean_inc(v_trace_972_);
v___x_1474_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1465_, v___y_1462_, v___y_1461_, v___y_1460_, v___y_1458_, v___f_1216_, v___x_1473_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1157_ = v___y_1456_;
v___y_1158_ = v___y_1457_;
v___y_1159_ = v___y_1459_;
v___y_1160_ = v___y_1461_;
v___y_1161_ = v___y_1462_;
v___y_1162_ = v___y_1464_;
v___y_1163_ = v___y_1465_;
v___y_1164_ = v___x_1474_;
goto v___jp_1156_;
}
v___jp_1475_:
{
lean_object* v___x_1488_; 
v___x_1488_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
if (v___y_1486_ == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref(v___x_1488_);
v___x_1490_ = lean_io_mono_nanos_now();
lean_inc(v_trace_972_);
v___x_1491_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1478_, v___y_1484_, v___y_1482_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1491_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set_tag(v___x_1494_, 1);
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
v___y_1433_ = v___y_1479_;
v___y_1434_ = v___x_1490_;
v___y_1435_ = v___y_1480_;
v___y_1436_ = v_a_1489_;
v___y_1437_ = v___y_1481_;
v___y_1438_ = v___y_1476_;
v___y_1439_ = v___y_1477_;
v___y_1440_ = v___y_1483_;
v___y_1441_ = v___y_1485_;
v___y_1442_ = v___y_1487_;
v_a_1443_ = v___x_1497_;
goto v___jp_1432_;
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_a_1500_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1491_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1491_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 0);
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
v___y_1433_ = v___y_1479_;
v___y_1434_ = v___x_1490_;
v___y_1435_ = v___y_1480_;
v___y_1436_ = v_a_1489_;
v___y_1437_ = v___y_1481_;
v___y_1438_ = v___y_1476_;
v___y_1439_ = v___y_1477_;
v___y_1440_ = v___y_1483_;
v___y_1441_ = v___y_1485_;
v___y_1442_ = v___y_1487_;
v_a_1443_ = v___x_1505_;
goto v___jp_1432_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v_a_1508_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1508_);
lean_dec_ref(v___x_1488_);
v___x_1509_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_972_);
v___x_1510_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1478_, v___y_1484_, v___y_1482_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
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
v___y_1456_ = v___y_1479_;
v___y_1457_ = v___y_1480_;
v___y_1458_ = v_a_1508_;
v___y_1459_ = v___y_1481_;
v___y_1460_ = v___y_1476_;
v___y_1461_ = v___y_1477_;
v___y_1462_ = v___y_1483_;
v___y_1463_ = v___x_1509_;
v___y_1464_ = v___y_1485_;
v___y_1465_ = v___y_1487_;
v_a_1466_ = v___x_1516_;
goto v___jp_1455_;
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
v___y_1456_ = v___y_1479_;
v___y_1457_ = v___y_1480_;
v___y_1458_ = v_a_1508_;
v___y_1459_ = v___y_1481_;
v___y_1460_ = v___y_1476_;
v___y_1461_ = v___y_1477_;
v___y_1462_ = v___y_1483_;
v___y_1463_ = v___x_1509_;
v___y_1464_ = v___y_1485_;
v___y_1465_ = v___y_1487_;
v_a_1466_ = v___x_1524_;
goto v___jp_1455_;
}
}
}
}
}
v___jp_1527_:
{
lean_object* v___x_1539_; double v___x_1540_; double v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1539_ = lean_io_get_num_heartbeats();
v___x_1540_ = lean_float_of_nat(v___y_1537_);
v___x_1541_ = lean_float_of_nat(v___x_1539_);
v___x_1542_ = lean_box_float(v___x_1540_);
v___x_1543_ = lean_box_float(v___x_1541_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_a_1538_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
lean_inc_ref(v___y_1533_);
lean_inc(v_trace_972_);
v___x_1546_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1536_, v___y_1533_, v___y_1532_, v___y_1530_, v___y_1535_, v___f_1300_, v___x_1545_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1157_ = v___y_1528_;
v___y_1158_ = v___y_1529_;
v___y_1159_ = v___y_1531_;
v___y_1160_ = v___y_1532_;
v___y_1161_ = v___y_1533_;
v___y_1162_ = v___y_1534_;
v___y_1163_ = v___y_1536_;
v___y_1164_ = v___x_1546_;
goto v___jp_1156_;
}
v___jp_1547_:
{
lean_object* v___x_1559_; double v___x_1560_; double v___x_1561_; double v___x_1562_; double v___x_1563_; double v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1559_ = lean_io_mono_nanos_now();
v___x_1560_ = lean_float_of_nat(v___y_1552_);
v___x_1561_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1562_ = lean_float_div(v___x_1560_, v___x_1561_);
v___x_1563_ = lean_float_of_nat(v___x_1559_);
v___x_1564_ = lean_float_div(v___x_1563_, v___x_1561_);
v___x_1565_ = lean_box_float(v___x_1562_);
v___x_1566_ = lean_box_float(v___x_1564_);
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v_a_1558_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
lean_inc_ref(v___y_1554_);
lean_inc(v_trace_972_);
v___x_1569_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1557_, v___y_1554_, v___y_1553_, v___y_1550_, v___y_1556_, v___f_1300_, v___x_1568_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1157_ = v___y_1548_;
v___y_1158_ = v___y_1549_;
v___y_1159_ = v___y_1551_;
v___y_1160_ = v___y_1553_;
v___y_1161_ = v___y_1554_;
v___y_1162_ = v___y_1555_;
v___y_1163_ = v___y_1557_;
v___y_1164_ = v___x_1569_;
goto v___jp_1156_;
}
v___jp_1570_:
{
lean_object* v___x_1582_; double v___x_1583_; double v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1582_ = lean_io_get_num_heartbeats();
v___x_1583_ = lean_float_of_nat(v___y_1571_);
v___x_1584_ = lean_float_of_nat(v___x_1582_);
v___x_1585_ = lean_box_float(v___x_1583_);
v___x_1586_ = lean_box_float(v___x_1584_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_a_1581_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
lean_inc_ref(v___y_1577_);
lean_inc(v_trace_972_);
v___x_1589_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1579_, v___y_1577_, v___y_1576_, v___y_1575_, v___y_1580_, v___f_1336_, v___x_1588_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1157_ = v___y_1572_;
v___y_1158_ = v___y_1573_;
v___y_1159_ = v___y_1574_;
v___y_1160_ = v___y_1576_;
v___y_1161_ = v___y_1577_;
v___y_1162_ = v___y_1578_;
v___y_1163_ = v___y_1579_;
v___y_1164_ = v___x_1589_;
goto v___jp_1156_;
}
v___jp_1590_:
{
lean_object* v___x_1602_; double v___x_1603_; double v___x_1604_; double v___x_1605_; double v___x_1606_; double v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1602_ = lean_io_mono_nanos_now();
v___x_1603_ = lean_float_of_nat(v___y_1595_);
v___x_1604_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1605_ = lean_float_div(v___x_1603_, v___x_1604_);
v___x_1606_ = lean_float_of_nat(v___x_1602_);
v___x_1607_ = lean_float_div(v___x_1606_, v___x_1604_);
v___x_1608_ = lean_box_float(v___x_1605_);
v___x_1609_ = lean_box_float(v___x_1607_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_a_1601_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
lean_inc_ref(v___y_1597_);
lean_inc(v_trace_972_);
v___x_1612_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1599_, v___y_1597_, v___y_1596_, v___y_1594_, v___y_1600_, v___f_1336_, v___x_1611_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1157_ = v___y_1591_;
v___y_1158_ = v___y_1592_;
v___y_1159_ = v___y_1593_;
v___y_1160_ = v___y_1596_;
v___y_1161_ = v___y_1597_;
v___y_1162_ = v___y_1598_;
v___y_1163_ = v___y_1599_;
v___y_1164_ = v___x_1612_;
goto v___jp_1156_;
}
v___jp_1613_:
{
lean_object* v___x_1626_; 
v___x_1626_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
if (v___y_1624_ == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref(v___x_1626_);
v___x_1628_ = lean_io_mono_nanos_now();
lean_inc(v_trace_972_);
v___x_1629_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1616_, v___y_1622_, v___y_1615_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 1);
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
v___y_1591_ = v___y_1617_;
v___y_1592_ = v___y_1618_;
v___y_1593_ = v___y_1619_;
v___y_1594_ = v___y_1620_;
v___y_1595_ = v___x_1628_;
v___y_1596_ = v___y_1614_;
v___y_1597_ = v___y_1621_;
v___y_1598_ = v___y_1623_;
v___y_1599_ = v___y_1625_;
v___y_1600_ = v_a_1627_;
v_a_1601_ = v___x_1635_;
goto v___jp_1590_;
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_a_1638_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1629_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1629_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 0);
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
v___y_1591_ = v___y_1617_;
v___y_1592_ = v___y_1618_;
v___y_1593_ = v___y_1619_;
v___y_1594_ = v___y_1620_;
v___y_1595_ = v___x_1628_;
v___y_1596_ = v___y_1614_;
v___y_1597_ = v___y_1621_;
v___y_1598_ = v___y_1623_;
v___y_1599_ = v___y_1625_;
v___y_1600_ = v_a_1627_;
v_a_1601_ = v___x_1643_;
goto v___jp_1590_;
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_a_1646_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1626_);
v___x_1647_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_972_);
v___x_1648_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1616_, v___y_1622_, v___y_1615_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
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
v___y_1571_ = v___x_1647_;
v___y_1572_ = v___y_1617_;
v___y_1573_ = v___y_1618_;
v___y_1574_ = v___y_1619_;
v___y_1575_ = v___y_1620_;
v___y_1576_ = v___y_1614_;
v___y_1577_ = v___y_1621_;
v___y_1578_ = v___y_1623_;
v___y_1579_ = v___y_1625_;
v___y_1580_ = v_a_1646_;
v_a_1581_ = v___x_1654_;
goto v___jp_1570_;
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
v___y_1571_ = v___x_1647_;
v___y_1572_ = v___y_1617_;
v___y_1573_ = v___y_1618_;
v___y_1574_ = v___y_1619_;
v___y_1575_ = v___y_1620_;
v___y_1576_ = v___y_1614_;
v___y_1577_ = v___y_1621_;
v___y_1578_ = v___y_1623_;
v___y_1579_ = v___y_1625_;
v___y_1580_ = v_a_1646_;
v_a_1581_ = v___x_1662_;
goto v___jp_1570_;
}
}
}
}
}
v___jp_1665_:
{
lean_object* v___x_1677_; double v___x_1678_; double v___x_1679_; double v___x_1680_; double v___x_1681_; double v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1677_ = lean_io_mono_nanos_now();
v___x_1678_ = lean_float_of_nat(v___y_1667_);
v___x_1679_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1680_ = lean_float_div(v___x_1678_, v___x_1679_);
v___x_1681_ = lean_float_of_nat(v___x_1677_);
v___x_1682_ = lean_float_div(v___x_1681_, v___x_1679_);
v___x_1683_ = lean_box_float(v___x_1680_);
v___x_1684_ = lean_box_float(v___x_1682_);
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_a_1676_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
lean_inc_ref(v___y_1672_);
lean_inc(v_trace_972_);
v___x_1687_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1674_, v___y_1672_, v___y_1671_, v___y_1675_, v___y_1670_, v___f_1300_, v___x_1686_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1106_ = v___y_1666_;
v___y_1107_ = v___y_1668_;
v___y_1108_ = v___y_1669_;
v___y_1109_ = v___y_1671_;
v___y_1110_ = v___y_1672_;
v___y_1111_ = v___y_1673_;
v___y_1112_ = v___y_1674_;
v___y_1113_ = v___x_1687_;
goto v___jp_1105_;
}
v___jp_1688_:
{
lean_object* v___x_1700_; double v___x_1701_; double v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1700_ = lean_io_get_num_heartbeats();
v___x_1701_ = lean_float_of_nat(v___y_1690_);
v___x_1702_ = lean_float_of_nat(v___x_1700_);
v___x_1703_ = lean_box_float(v___x_1701_);
v___x_1704_ = lean_box_float(v___x_1702_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_a_1699_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
lean_inc_ref(v___y_1695_);
lean_inc(v_trace_972_);
v___x_1707_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1697_, v___y_1695_, v___y_1694_, v___y_1698_, v___y_1693_, v___f_1300_, v___x_1706_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1106_ = v___y_1689_;
v___y_1107_ = v___y_1691_;
v___y_1108_ = v___y_1692_;
v___y_1109_ = v___y_1694_;
v___y_1110_ = v___y_1695_;
v___y_1111_ = v___y_1696_;
v___y_1112_ = v___y_1697_;
v___y_1113_ = v___x_1707_;
goto v___jp_1105_;
}
v___jp_1708_:
{
lean_object* v___x_1720_; double v___x_1721_; double v___x_1722_; double v___x_1723_; double v___x_1724_; double v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1720_ = lean_io_mono_nanos_now();
v___x_1721_ = lean_float_of_nat(v___y_1716_);
v___x_1722_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1723_ = lean_float_div(v___x_1721_, v___x_1722_);
v___x_1724_ = lean_float_of_nat(v___x_1720_);
v___x_1725_ = lean_float_div(v___x_1724_, v___x_1722_);
v___x_1726_ = lean_box_float(v___x_1723_);
v___x_1727_ = lean_box_float(v___x_1725_);
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v_a_1719_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
lean_inc_ref(v___y_1715_);
lean_inc(v_trace_972_);
v___x_1730_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1718_, v___y_1715_, v___y_1714_, v___y_1712_, v___y_1713_, v___f_1216_, v___x_1729_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1106_ = v___y_1709_;
v___y_1107_ = v___y_1710_;
v___y_1108_ = v___y_1711_;
v___y_1109_ = v___y_1714_;
v___y_1110_ = v___y_1715_;
v___y_1111_ = v___y_1717_;
v___y_1112_ = v___y_1718_;
v___y_1113_ = v___x_1730_;
goto v___jp_1105_;
}
v___jp_1731_:
{
lean_object* v___x_1743_; double v___x_1744_; double v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1743_ = lean_io_get_num_heartbeats();
v___x_1744_ = lean_float_of_nat(v___y_1739_);
v___x_1745_ = lean_float_of_nat(v___x_1743_);
v___x_1746_ = lean_box_float(v___x_1744_);
v___x_1747_ = lean_box_float(v___x_1745_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1746_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_a_1742_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
lean_inc_ref(v___y_1738_);
lean_inc(v_trace_972_);
v___x_1750_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1741_, v___y_1738_, v___y_1737_, v___y_1735_, v___y_1736_, v___f_1216_, v___x_1749_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1106_ = v___y_1732_;
v___y_1107_ = v___y_1733_;
v___y_1108_ = v___y_1734_;
v___y_1109_ = v___y_1737_;
v___y_1110_ = v___y_1738_;
v___y_1111_ = v___y_1740_;
v___y_1112_ = v___y_1741_;
v___y_1113_ = v___x_1750_;
goto v___jp_1105_;
}
v___jp_1751_:
{
lean_object* v___x_1764_; 
v___x_1764_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
if (v___y_1762_ == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref(v___x_1764_);
v___x_1766_ = lean_io_mono_nanos_now();
lean_inc(v_trace_972_);
v___x_1767_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1756_, v___y_1760_, v___y_1754_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 1);
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
v___y_1709_ = v___y_1755_;
v___y_1710_ = v___y_1757_;
v___y_1711_ = v___y_1752_;
v___y_1712_ = v___y_1758_;
v___y_1713_ = v_a_1765_;
v___y_1714_ = v___y_1753_;
v___y_1715_ = v___y_1759_;
v___y_1716_ = v___x_1766_;
v___y_1717_ = v___y_1761_;
v___y_1718_ = v___y_1763_;
v_a_1719_ = v___x_1773_;
goto v___jp_1708_;
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_a_1776_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1767_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1767_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 0);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
v___y_1709_ = v___y_1755_;
v___y_1710_ = v___y_1757_;
v___y_1711_ = v___y_1752_;
v___y_1712_ = v___y_1758_;
v___y_1713_ = v_a_1765_;
v___y_1714_ = v___y_1753_;
v___y_1715_ = v___y_1759_;
v___y_1716_ = v___x_1766_;
v___y_1717_ = v___y_1761_;
v___y_1718_ = v___y_1763_;
v_a_1719_ = v___x_1781_;
goto v___jp_1708_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_a_1784_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1764_);
v___x_1785_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_972_);
v___x_1786_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1756_, v___y_1760_, v___y_1754_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
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
v___y_1732_ = v___y_1755_;
v___y_1733_ = v___y_1757_;
v___y_1734_ = v___y_1752_;
v___y_1735_ = v___y_1758_;
v___y_1736_ = v_a_1784_;
v___y_1737_ = v___y_1753_;
v___y_1738_ = v___y_1759_;
v___y_1739_ = v___x_1785_;
v___y_1740_ = v___y_1761_;
v___y_1741_ = v___y_1763_;
v_a_1742_ = v___x_1792_;
goto v___jp_1731_;
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
v___y_1732_ = v___y_1755_;
v___y_1733_ = v___y_1757_;
v___y_1734_ = v___y_1752_;
v___y_1735_ = v___y_1758_;
v___y_1736_ = v_a_1784_;
v___y_1737_ = v___y_1753_;
v___y_1738_ = v___y_1759_;
v___y_1739_ = v___x_1785_;
v___y_1740_ = v___y_1761_;
v___y_1741_ = v___y_1763_;
v_a_1742_ = v___x_1800_;
goto v___jp_1731_;
}
}
}
}
}
v___jp_1803_:
{
lean_object* v___x_1811_; double v___x_1812_; double v___x_1813_; double v___x_1814_; double v___x_1815_; double v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1811_ = lean_io_mono_nanos_now();
v___x_1812_ = lean_float_of_nat(v___y_1806_);
v___x_1813_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1814_ = lean_float_div(v___x_1812_, v___x_1813_);
v___x_1815_ = lean_float_of_nat(v___x_1811_);
v___x_1816_ = lean_float_div(v___x_1815_, v___x_1813_);
v___x_1817_ = lean_box_float(v___x_1814_);
v___x_1818_ = lean_box_float(v___x_1816_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1820_, 0, v_a_1810_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
lean_inc_ref(v___y_1805_);
v___x_1821_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1807_, v___y_1805_, v___y_1804_, v___y_1809_, v___y_1808_, v___f_1336_, v___x_1820_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1821_;
}
v___jp_1822_:
{
lean_object* v___x_1830_; double v___x_1831_; double v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1830_ = lean_io_get_num_heartbeats();
v___x_1831_ = lean_float_of_nat(v___y_1823_);
v___x_1832_ = lean_float_of_nat(v___x_1830_);
v___x_1833_ = lean_box_float(v___x_1831_);
v___x_1834_ = lean_box_float(v___x_1832_);
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v_a_1829_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
lean_inc_ref(v___y_1825_);
v___x_1837_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1826_, v___y_1825_, v___y_1824_, v___y_1828_, v___y_1827_, v___f_1336_, v___x_1836_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1837_;
}
v___jp_1838_:
{
lean_object* v___x_1846_; lean_object* v_a_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1846_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1846_);
v___x_1848_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1849_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1840_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = lean_io_mono_nanos_now();
lean_inc(v_trace_972_);
v___x_1851_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1843_, v___y_1842_, v___y_1841_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set_tag(v___x_1854_, 1);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
v___y_1804_ = v___y_1840_;
v___y_1805_ = v___y_1839_;
v___y_1806_ = v___x_1850_;
v___y_1807_ = v___y_1844_;
v___y_1808_ = v_a_1847_;
v___y_1809_ = v___y_1845_;
v_a_1810_ = v___x_1857_;
goto v___jp_1803_;
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_a_1860_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1851_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1851_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 0);
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
v___y_1804_ = v___y_1840_;
v___y_1805_ = v___y_1839_;
v___y_1806_ = v___x_1850_;
v___y_1807_ = v___y_1844_;
v___y_1808_ = v_a_1847_;
v___y_1809_ = v___y_1845_;
v_a_1810_ = v___x_1865_;
goto v___jp_1803_;
}
}
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_972_);
v___x_1869_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1843_, v___y_1842_, v___y_1841_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set_tag(v___x_1872_, 1);
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
v___y_1823_ = v___x_1868_;
v___y_1824_ = v___y_1840_;
v___y_1825_ = v___y_1839_;
v___y_1826_ = v___y_1844_;
v___y_1827_ = v_a_1847_;
v___y_1828_ = v___y_1845_;
v_a_1829_ = v___x_1875_;
goto v___jp_1822_;
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
v_a_1878_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1869_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1869_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set_tag(v___x_1880_, 0);
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
v___y_1823_ = v___x_1868_;
v___y_1824_ = v___y_1840_;
v___y_1825_ = v___y_1839_;
v___y_1826_ = v___y_1844_;
v___y_1827_ = v_a_1847_;
v___y_1828_ = v___y_1845_;
v_a_1829_ = v___x_1883_;
goto v___jp_1822_;
}
}
}
}
}
v___jp_1888_:
{
lean_object* v___x_1894_; lean_object* v_a_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1894_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
lean_dec_ref(v___x_1894_);
v___x_1896_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1897_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1890_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_io_mono_nanos_now();
lean_inc(v_trace_972_);
v___x_1899_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v_n_1887_, v___y_1893_, v_acc_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1907_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1907_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v___x_1905_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set_tag(v___x_1902_, 1);
v___x_1905_ = v___x_1902_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
v___x_1905_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
v___y_1302_ = v_a_1895_;
v___y_1303_ = v___x_1898_;
v___y_1304_ = v___y_1890_;
v___y_1305_ = v___y_1889_;
v___y_1306_ = v___y_1891_;
v___y_1307_ = v___y_1892_;
v_a_1308_ = v___x_1905_;
goto v___jp_1301_;
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
v_a_1908_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1899_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1899_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set_tag(v___x_1910_, 0);
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
v___y_1302_ = v_a_1895_;
v___y_1303_ = v___x_1898_;
v___y_1304_ = v___y_1890_;
v___y_1305_ = v___y_1889_;
v___y_1306_ = v___y_1891_;
v___y_1307_ = v___y_1892_;
v_a_1308_ = v___x_1913_;
goto v___jp_1301_;
}
}
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_972_);
v___x_1917_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v_n_1887_, v___y_1893_, v_acc_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set_tag(v___x_1920_, 1);
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
v___y_1321_ = v___x_1916_;
v___y_1322_ = v_a_1895_;
v___y_1323_ = v___y_1890_;
v___y_1324_ = v___y_1889_;
v___y_1325_ = v___y_1891_;
v___y_1326_ = v___y_1892_;
v_a_1327_ = v___x_1923_;
goto v___jp_1320_;
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
v_a_1926_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1917_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1917_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set_tag(v___x_1928_, 0);
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
v___y_1321_ = v___x_1916_;
v___y_1322_ = v_a_1895_;
v___y_1323_ = v___y_1890_;
v___y_1324_ = v___y_1889_;
v___y_1325_ = v___y_1891_;
v___y_1326_ = v___y_1892_;
v_a_1327_ = v___x_1931_;
goto v___jp_1320_;
}
}
}
}
}
v___jp_1934_:
{
if (v___y_1944_ == 0)
{
lean_object* v___x_1945_; 
lean_dec_ref(v___y_1943_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v___y_1942_);
v___x_1945_ = lean_apply_6(v___y_1935_, v___y_1942_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1945_, 1);
if (lean_obj_tag(v_a_1946_) == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1947_ = lean_nat_add(v_n_1887_, v_one_1886_);
lean_dec(v_n_1887_);
v___x_1948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___y_1942_);
lean_ctor_set(v___x_1948_, 1, v_acc_977_);
v___x_1949_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_972_);
v___x_1950_ = l_Lean_Name_append(v___x_1949_, v_trace_972_);
v___x_1951_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1939_, v___y_1938_, v___x_1950_);
lean_dec(v___x_1950_);
if (v___x_1951_ == 0)
{
if (v___y_1936_ == 0)
{
v_n_975_ = v___x_1947_;
v_curr_976_ = v___y_1940_;
v_acc_977_ = v___x_1948_;
goto _start;
}
else
{
v___y_1253_ = v___x_1948_;
v___y_1254_ = v___x_1951_;
v___y_1255_ = v___x_1947_;
v___y_1256_ = v___y_1937_;
v___y_1257_ = v___y_1938_;
v___y_1258_ = v___y_1940_;
v___y_1259_ = v___y_1941_;
goto v___jp_1252_;
}
}
else
{
v___y_1253_ = v___x_1948_;
v___y_1254_ = v___x_1951_;
v___y_1255_ = v___x_1947_;
v___y_1256_ = v___y_1937_;
v___y_1257_ = v___y_1938_;
v___y_1258_ = v___y_1940_;
v___y_1259_ = v___y_1941_;
goto v___jp_1252_;
}
}
else
{
lean_object* v_val_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
lean_dec(v___y_1942_);
v_val_1953_ = lean_ctor_get(v_a_1946_, 0);
lean_inc(v_val_1953_);
lean_dec_ref_known(v_a_1946_, 1);
v___x_1954_ = l_List_appendTR___redArg(v_val_1953_, v___y_1940_);
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_972_);
v___x_1956_ = l_Lean_Name_append(v___x_1955_, v_trace_972_);
v___x_1957_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1939_, v___y_1938_, v___x_1956_);
lean_dec(v___x_1956_);
if (v___x_1957_ == 0)
{
if (v___y_1936_ == 0)
{
v_n_975_ = v_n_1887_;
v_curr_976_ = v___x_1954_;
goto _start;
}
else
{
v___y_1889_ = v___y_1937_;
v___y_1890_ = v___y_1938_;
v___y_1891_ = v___x_1957_;
v___y_1892_ = v___y_1941_;
v___y_1893_ = v___x_1954_;
goto v___jp_1888_;
}
}
else
{
v___y_1889_ = v___y_1937_;
v___y_1890_ = v___y_1938_;
v___y_1891_ = v___x_1957_;
v___y_1892_ = v___y_1941_;
v___y_1893_ = v___x_1954_;
goto v___jp_1888_;
}
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec(v___y_1942_);
lean_dec(v___y_1940_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
v_a_1959_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1945_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1945_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
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
return v___x_1964_;
}
}
}
}
else
{
lean_dec(v___y_1942_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1935_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
return v___y_1943_;
}
}
v___jp_1967_:
{
lean_object* v___x_1978_; 
v___x_1978_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
if (v___y_1976_ == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref(v___x_1978_);
v___x_1980_ = lean_io_mono_nanos_now();
lean_inc(v_trace_972_);
v___x_1981_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v_n_1887_, v___y_1968_, v_acc_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set_tag(v___x_1984_, 1);
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
v___y_1666_ = v___y_1969_;
v___y_1667_ = v___x_1980_;
v___y_1668_ = v___y_1970_;
v___y_1669_ = v___y_1971_;
v___y_1670_ = v_a_1979_;
v___y_1671_ = v___y_1973_;
v___y_1672_ = v___y_1972_;
v___y_1673_ = v___y_1974_;
v___y_1674_ = v___y_1975_;
v___y_1675_ = v___y_1977_;
v_a_1676_ = v___x_1987_;
goto v___jp_1665_;
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v_a_1990_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1981_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1981_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 0);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
v___y_1666_ = v___y_1969_;
v___y_1667_ = v___x_1980_;
v___y_1668_ = v___y_1970_;
v___y_1669_ = v___y_1971_;
v___y_1670_ = v_a_1979_;
v___y_1671_ = v___y_1973_;
v___y_1672_ = v___y_1972_;
v___y_1673_ = v___y_1974_;
v___y_1674_ = v___y_1975_;
v___y_1675_ = v___y_1977_;
v_a_1676_ = v___x_1995_;
goto v___jp_1665_;
}
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v_a_1998_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1998_);
lean_dec_ref(v___x_1978_);
v___x_1999_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_972_);
v___x_2000_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v_n_1887_, v___y_1968_, v_acc_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
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
v___y_1689_ = v___y_1969_;
v___y_1690_ = v___x_1999_;
v___y_1691_ = v___y_1970_;
v___y_1692_ = v___y_1971_;
v___y_1693_ = v_a_1998_;
v___y_1694_ = v___y_1973_;
v___y_1695_ = v___y_1972_;
v___y_1696_ = v___y_1974_;
v___y_1697_ = v___y_1975_;
v___y_1698_ = v___y_1977_;
v_a_1699_ = v___x_2006_;
goto v___jp_1688_;
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
v___y_1689_ = v___y_1969_;
v___y_1690_ = v___x_1999_;
v___y_1691_ = v___y_1970_;
v___y_1692_ = v___y_1971_;
v___y_1693_ = v_a_1998_;
v___y_1694_ = v___y_1973_;
v___y_1695_ = v___y_1972_;
v___y_1696_ = v___y_1974_;
v___y_1697_ = v___y_1975_;
v___y_1698_ = v___y_1977_;
v_a_1699_ = v___x_2014_;
goto v___jp_1688_;
}
}
}
}
}
v___jp_2017_:
{
if (v___y_2031_ == 0)
{
lean_object* v___x_2032_; 
lean_dec_ref(v___y_2018_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v___y_2030_);
v___x_2032_ = lean_apply_6(v___y_2021_, v___y_2030_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
if (lean_obj_tag(v_a_2033_) == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2034_ = lean_nat_add(v_n_1887_, v_one_1886_);
lean_dec(v_n_1887_);
v___x_2035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___y_2030_);
lean_ctor_set(v___x_2035_, 1, v_acc_977_);
v___x_2036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_972_);
v___x_2037_ = l_Lean_Name_append(v___x_2036_, v_trace_972_);
v___x_2038_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2024_, v___y_2020_, v___x_2037_);
lean_dec(v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = l_Lean_trace_profiler;
v___x_2040_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2020_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; 
lean_inc(v_trace_972_);
v___x_2041_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___x_2034_, v___y_2026_, v___x_2035_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1106_ = v___y_2022_;
v___y_1107_ = v___y_2023_;
v___y_1108_ = v___y_2019_;
v___y_1109_ = v___y_2020_;
v___y_1110_ = v___y_2025_;
v___y_1111_ = v___y_2027_;
v___y_1112_ = v___y_2029_;
v___y_1113_ = v___x_2041_;
goto v___jp_1105_;
}
else
{
v___y_1752_ = v___y_2019_;
v___y_1753_ = v___y_2020_;
v___y_1754_ = v___x_2035_;
v___y_1755_ = v___y_2022_;
v___y_1756_ = v___x_2034_;
v___y_1757_ = v___y_2023_;
v___y_1758_ = v___x_2038_;
v___y_1759_ = v___y_2025_;
v___y_1760_ = v___y_2026_;
v___y_1761_ = v___y_2027_;
v___y_1762_ = v___y_2028_;
v___y_1763_ = v___y_2029_;
goto v___jp_1751_;
}
}
else
{
v___y_1752_ = v___y_2019_;
v___y_1753_ = v___y_2020_;
v___y_1754_ = v___x_2035_;
v___y_1755_ = v___y_2022_;
v___y_1756_ = v___x_2034_;
v___y_1757_ = v___y_2023_;
v___y_1758_ = v___x_2038_;
v___y_1759_ = v___y_2025_;
v___y_1760_ = v___y_2026_;
v___y_1761_ = v___y_2027_;
v___y_1762_ = v___y_2028_;
v___y_1763_ = v___y_2029_;
goto v___jp_1751_;
}
}
else
{
lean_object* v_val_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
lean_dec(v___y_2030_);
v_val_2042_ = lean_ctor_get(v_a_2033_, 0);
lean_inc(v_val_2042_);
lean_dec_ref_known(v_a_2033_, 1);
v___x_2043_ = l_List_appendTR___redArg(v_val_2042_, v___y_2026_);
v___x_2044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_972_);
v___x_2045_ = l_Lean_Name_append(v___x_2044_, v_trace_972_);
v___x_2046_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2024_, v___y_2020_, v___x_2045_);
lean_dec(v___x_2045_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = l_Lean_trace_profiler;
v___x_2048_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2020_, v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_inc(v_trace_972_);
v___x_2049_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v_n_1887_, v___x_2043_, v_acc_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1106_ = v___y_2022_;
v___y_1107_ = v___y_2023_;
v___y_1108_ = v___y_2019_;
v___y_1109_ = v___y_2020_;
v___y_1110_ = v___y_2025_;
v___y_1111_ = v___y_2027_;
v___y_1112_ = v___y_2029_;
v___y_1113_ = v___x_2049_;
goto v___jp_1105_;
}
else
{
v___y_1968_ = v___x_2043_;
v___y_1969_ = v___y_2022_;
v___y_1970_ = v___y_2023_;
v___y_1971_ = v___y_2019_;
v___y_1972_ = v___y_2025_;
v___y_1973_ = v___y_2020_;
v___y_1974_ = v___y_2027_;
v___y_1975_ = v___y_2029_;
v___y_1976_ = v___y_2028_;
v___y_1977_ = v___x_2046_;
goto v___jp_1967_;
}
}
else
{
v___y_1968_ = v___x_2043_;
v___y_1969_ = v___y_2022_;
v___y_1970_ = v___y_2023_;
v___y_1971_ = v___y_2019_;
v___y_1972_ = v___y_2025_;
v___y_1973_ = v___y_2020_;
v___y_1974_ = v___y_2027_;
v___y_1975_ = v___y_2029_;
v___y_1976_ = v___y_2028_;
v___y_1977_ = v___x_2046_;
goto v___jp_1967_;
}
}
}
else
{
lean_object* v_a_2050_; 
lean_dec(v___y_2030_);
lean_dec(v___y_2026_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec_ref(v_cfg_971_);
v_a_2050_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2032_, 1);
v___y_1096_ = v___y_2022_;
v___y_1097_ = v___y_2023_;
v___y_1098_ = v___y_2019_;
v___y_1099_ = v___y_2025_;
v___y_1100_ = v___y_2020_;
v___y_1101_ = v___y_2027_;
v___y_1102_ = v___y_2029_;
v_a_1103_ = v_a_2050_;
goto v___jp_1095_;
}
}
else
{
lean_dec(v___y_2030_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2021_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec_ref(v_cfg_971_);
v___y_1096_ = v___y_2022_;
v___y_1097_ = v___y_2023_;
v___y_1098_ = v___y_2019_;
v___y_1099_ = v___y_2025_;
v___y_1100_ = v___y_2020_;
v___y_1101_ = v___y_2027_;
v___y_1102_ = v___y_2029_;
v_a_1103_ = v___y_2018_;
goto v___jp_1095_;
}
}
v___jp_2051_:
{
lean_object* v___x_2062_; 
v___x_2062_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
if (v___y_2061_ == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref(v___x_2062_);
v___x_2064_ = lean_io_mono_nanos_now();
lean_inc(v_trace_972_);
v___x_2065_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v_n_1887_, v___y_2055_, v_acc_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
lean_ctor_set_tag(v___x_2068_, 1);
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
v___y_1548_ = v___y_2052_;
v___y_1549_ = v___y_2054_;
v___y_1550_ = v___y_2053_;
v___y_1551_ = v___y_2056_;
v___y_1552_ = v___x_2064_;
v___y_1553_ = v___y_2058_;
v___y_1554_ = v___y_2057_;
v___y_1555_ = v___y_2059_;
v___y_1556_ = v_a_2063_;
v___y_1557_ = v___y_2060_;
v_a_1558_ = v___x_2071_;
goto v___jp_1547_;
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_a_2074_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2065_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2065_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set_tag(v___x_2076_, 0);
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
v___y_1548_ = v___y_2052_;
v___y_1549_ = v___y_2054_;
v___y_1550_ = v___y_2053_;
v___y_1551_ = v___y_2056_;
v___y_1552_ = v___x_2064_;
v___y_1553_ = v___y_2058_;
v___y_1554_ = v___y_2057_;
v___y_1555_ = v___y_2059_;
v___y_1556_ = v_a_2063_;
v___y_1557_ = v___y_2060_;
v_a_1558_ = v___x_2079_;
goto v___jp_1547_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_a_2082_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2082_);
lean_dec_ref(v___x_2062_);
v___x_2083_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_972_);
v___x_2084_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v_n_1887_, v___y_2055_, v_acc_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
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
v___y_1528_ = v___y_2052_;
v___y_1529_ = v___y_2054_;
v___y_1530_ = v___y_2053_;
v___y_1531_ = v___y_2056_;
v___y_1532_ = v___y_2058_;
v___y_1533_ = v___y_2057_;
v___y_1534_ = v___y_2059_;
v___y_1535_ = v_a_2082_;
v___y_1536_ = v___y_2060_;
v___y_1537_ = v___x_2083_;
v_a_1538_ = v___x_2090_;
goto v___jp_1527_;
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
v___y_1528_ = v___y_2052_;
v___y_1529_ = v___y_2054_;
v___y_1530_ = v___y_2053_;
v___y_1531_ = v___y_2056_;
v___y_1532_ = v___y_2058_;
v___y_1533_ = v___y_2057_;
v___y_1534_ = v___y_2059_;
v___y_1535_ = v_a_2082_;
v___y_1536_ = v___y_2060_;
v___y_1537_ = v___x_2083_;
v_a_1538_ = v___x_2098_;
goto v___jp_1527_;
}
}
}
}
}
v___jp_2101_:
{
if (v___y_2115_ == 0)
{
lean_object* v___x_2116_; 
lean_dec_ref(v___y_2103_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v___y_2114_);
v___x_2116_ = lean_apply_6(v___y_2104_, v___y_2114_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
if (lean_obj_tag(v_a_2117_) == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2118_ = lean_nat_add(v_n_1887_, v_one_1886_);
lean_dec(v_n_1887_);
v___x_2119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___y_2114_);
lean_ctor_set(v___x_2119_, 1, v_acc_977_);
v___x_2120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_972_);
v___x_2121_ = l_Lean_Name_append(v___x_2120_, v_trace_972_);
v___x_2122_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2108_, v___y_2102_, v___x_2121_);
lean_dec(v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = l_Lean_trace_profiler;
v___x_2124_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2102_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; 
lean_inc(v_trace_972_);
v___x_2125_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___x_2118_, v___y_2110_, v___x_2119_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1157_ = v___y_2105_;
v___y_1158_ = v___y_2106_;
v___y_1159_ = v___y_2107_;
v___y_1160_ = v___y_2102_;
v___y_1161_ = v___y_2109_;
v___y_1162_ = v___y_2111_;
v___y_1163_ = v___y_2113_;
v___y_1164_ = v___x_2125_;
goto v___jp_1156_;
}
else
{
v___y_1476_ = v___x_2122_;
v___y_1477_ = v___y_2102_;
v___y_1478_ = v___x_2118_;
v___y_1479_ = v___y_2105_;
v___y_1480_ = v___y_2106_;
v___y_1481_ = v___y_2107_;
v___y_1482_ = v___x_2119_;
v___y_1483_ = v___y_2109_;
v___y_1484_ = v___y_2110_;
v___y_1485_ = v___y_2111_;
v___y_1486_ = v___y_2112_;
v___y_1487_ = v___y_2113_;
goto v___jp_1475_;
}
}
else
{
v___y_1476_ = v___x_2122_;
v___y_1477_ = v___y_2102_;
v___y_1478_ = v___x_2118_;
v___y_1479_ = v___y_2105_;
v___y_1480_ = v___y_2106_;
v___y_1481_ = v___y_2107_;
v___y_1482_ = v___x_2119_;
v___y_1483_ = v___y_2109_;
v___y_1484_ = v___y_2110_;
v___y_1485_ = v___y_2111_;
v___y_1486_ = v___y_2112_;
v___y_1487_ = v___y_2113_;
goto v___jp_1475_;
}
}
else
{
lean_object* v_val_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; 
lean_dec(v___y_2114_);
v_val_2126_ = lean_ctor_get(v_a_2117_, 0);
lean_inc(v_val_2126_);
lean_dec_ref_known(v_a_2117_, 1);
v___x_2127_ = l_List_appendTR___redArg(v_val_2126_, v___y_2110_);
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_972_);
v___x_2129_ = l_Lean_Name_append(v___x_2128_, v_trace_972_);
v___x_2130_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2108_, v___y_2102_, v___x_2129_);
lean_dec(v___x_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2131_ = l_Lean_trace_profiler;
v___x_2132_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2102_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_object* v___x_2133_; 
lean_inc(v_trace_972_);
v___x_2133_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v_n_1887_, v___x_2127_, v_acc_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1157_ = v___y_2105_;
v___y_1158_ = v___y_2106_;
v___y_1159_ = v___y_2107_;
v___y_1160_ = v___y_2102_;
v___y_1161_ = v___y_2109_;
v___y_1162_ = v___y_2111_;
v___y_1163_ = v___y_2113_;
v___y_1164_ = v___x_2133_;
goto v___jp_1156_;
}
else
{
v___y_2052_ = v___y_2105_;
v___y_2053_ = v___x_2130_;
v___y_2054_ = v___y_2106_;
v___y_2055_ = v___x_2127_;
v___y_2056_ = v___y_2107_;
v___y_2057_ = v___y_2109_;
v___y_2058_ = v___y_2102_;
v___y_2059_ = v___y_2111_;
v___y_2060_ = v___y_2113_;
v___y_2061_ = v___y_2112_;
goto v___jp_2051_;
}
}
else
{
v___y_2052_ = v___y_2105_;
v___y_2053_ = v___x_2130_;
v___y_2054_ = v___y_2106_;
v___y_2055_ = v___x_2127_;
v___y_2056_ = v___y_2107_;
v___y_2057_ = v___y_2109_;
v___y_2058_ = v___y_2102_;
v___y_2059_ = v___y_2111_;
v___y_2060_ = v___y_2113_;
v___y_2061_ = v___y_2112_;
goto v___jp_2051_;
}
}
}
else
{
lean_object* v_a_2134_; 
lean_dec(v___y_2114_);
lean_dec(v___y_2110_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec_ref(v_cfg_971_);
v_a_2134_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2116_, 1);
v___y_1147_ = v___y_2105_;
v___y_1148_ = v___y_2106_;
v___y_1149_ = v___y_2107_;
v___y_1150_ = v___y_2109_;
v___y_1151_ = v___y_2102_;
v___y_1152_ = v___y_2111_;
v___y_1153_ = v___y_2113_;
v_a_1154_ = v_a_2134_;
goto v___jp_1146_;
}
}
else
{
lean_dec(v___y_2114_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2104_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec_ref(v_cfg_971_);
v___y_1147_ = v___y_2105_;
v___y_1148_ = v___y_2106_;
v___y_1149_ = v___y_2107_;
v___y_1150_ = v___y_2109_;
v___y_1151_ = v___y_2102_;
v___y_1152_ = v___y_2111_;
v___y_1153_ = v___y_2113_;
v_a_1154_ = v___y_2103_;
goto v___jp_1146_;
}
}
v___jp_2135_:
{
lean_object* v___x_2148_; lean_object* v_a_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2148_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
v___x_2150_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2151_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2137_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec_ref(v___y_2136_);
v___x_2152_ = lean_io_mono_nanos_now();
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v___y_2147_);
v___x_2153_ = lean_apply_6(v___y_2138_, v___y_2147_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; uint8_t v___x_2155_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2155_ = lean_unbox(v_a_2154_);
lean_dec(v_a_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; 
lean_inc_ref(v_next_973_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v___y_2147_);
v___x_2156_ = lean_apply_7(v_next_973_, v___y_2147_, v___y_2143_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; 
lean_dec(v___y_2147_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2139_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec_ref(v_cfg_971_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v___y_1137_ = v_a_2149_;
v___y_1138_ = v___y_2140_;
v___y_1139_ = v___x_2152_;
v___y_1140_ = v___y_2141_;
v___y_1141_ = v___y_2137_;
v___y_1142_ = v___y_2145_;
v___y_1143_ = v___y_2146_;
v_a_1144_ = v_a_2157_;
goto v___jp_1136_;
}
else
{
lean_object* v_a_2158_; uint8_t v___x_2159_; 
v_a_2158_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2159_ = l_Lean_Exception_isInterrupt(v_a_2158_);
if (v___x_2159_ == 0)
{
uint8_t v___x_2160_; 
lean_inc(v_a_2158_);
v___x_2160_ = l_Lean_Exception_isRuntime(v_a_2158_);
v___y_2102_ = v___y_2137_;
v___y_2103_ = v_a_2158_;
v___y_2104_ = v___y_2139_;
v___y_2105_ = v_a_2149_;
v___y_2106_ = v___y_2140_;
v___y_2107_ = v___x_2152_;
v___y_2108_ = v___y_2142_;
v___y_2109_ = v___y_2141_;
v___y_2110_ = v___y_2144_;
v___y_2111_ = v___y_2145_;
v___y_2112_ = v___x_2151_;
v___y_2113_ = v___y_2146_;
v___y_2114_ = v___y_2147_;
v___y_2115_ = v___x_2160_;
goto v___jp_2101_;
}
else
{
v___y_2102_ = v___y_2137_;
v___y_2103_ = v_a_2158_;
v___y_2104_ = v___y_2139_;
v___y_2105_ = v_a_2149_;
v___y_2106_ = v___y_2140_;
v___y_2107_ = v___x_2152_;
v___y_2108_ = v___y_2142_;
v___y_2109_ = v___y_2141_;
v___y_2110_ = v___y_2144_;
v___y_2111_ = v___y_2145_;
v___y_2112_ = v___x_2151_;
v___y_2113_ = v___y_2146_;
v___y_2114_ = v___y_2147_;
v___y_2115_ = v___x_2159_;
goto v___jp_2101_;
}
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
lean_dec_ref(v___y_2143_);
lean_dec_ref(v___y_2139_);
v___x_2161_ = lean_nat_add(v_n_1887_, v_one_1886_);
lean_dec(v_n_1887_);
v___x_2162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___y_2147_);
lean_ctor_set(v___x_2162_, 1, v_acc_977_);
v___x_2163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_972_);
v___x_2164_ = l_Lean_Name_append(v___x_2163_, v_trace_972_);
v___x_2165_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2142_, v___y_2137_, v___x_2164_);
lean_dec(v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = l_Lean_trace_profiler;
v___x_2167_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2137_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
lean_inc(v_trace_972_);
v___x_2168_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___x_2161_, v___y_2144_, v___x_2162_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1157_ = v_a_2149_;
v___y_1158_ = v___y_2140_;
v___y_1159_ = v___x_2152_;
v___y_1160_ = v___y_2137_;
v___y_1161_ = v___y_2141_;
v___y_1162_ = v___y_2145_;
v___y_1163_ = v___y_2146_;
v___y_1164_ = v___x_2168_;
goto v___jp_1156_;
}
else
{
v___y_1614_ = v___y_2137_;
v___y_1615_ = v___x_2162_;
v___y_1616_ = v___x_2161_;
v___y_1617_ = v_a_2149_;
v___y_1618_ = v___y_2140_;
v___y_1619_ = v___x_2152_;
v___y_1620_ = v___x_2165_;
v___y_1621_ = v___y_2141_;
v___y_1622_ = v___y_2144_;
v___y_1623_ = v___y_2145_;
v___y_1624_ = v___x_2151_;
v___y_1625_ = v___y_2146_;
goto v___jp_1613_;
}
}
else
{
v___y_1614_ = v___y_2137_;
v___y_1615_ = v___x_2162_;
v___y_1616_ = v___x_2161_;
v___y_1617_ = v_a_2149_;
v___y_1618_ = v___y_2140_;
v___y_1619_ = v___x_2152_;
v___y_1620_ = v___x_2165_;
v___y_1621_ = v___y_2141_;
v___y_1622_ = v___y_2144_;
v___y_1623_ = v___y_2145_;
v___y_1624_ = v___x_2151_;
v___y_1625_ = v___y_2146_;
goto v___jp_1613_;
}
}
}
else
{
lean_object* v_a_2169_; 
lean_dec(v___y_2147_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec_ref(v___y_2139_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec_ref(v_cfg_971_);
v_a_2169_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2153_, 1);
v___y_1147_ = v_a_2149_;
v___y_1148_ = v___y_2140_;
v___y_1149_ = v___x_2152_;
v___y_1150_ = v___y_2141_;
v___y_1151_ = v___y_2137_;
v___y_1152_ = v___y_2145_;
v___y_1153_ = v___y_2146_;
v_a_1154_ = v_a_2169_;
goto v___jp_1146_;
}
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec_ref(v___y_2143_);
v___x_2170_ = lean_io_get_num_heartbeats();
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v___y_2147_);
v___x_2171_ = lean_apply_6(v___y_2138_, v___y_2147_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; uint8_t v___x_2173_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v___x_2173_ = lean_unbox(v_a_2172_);
lean_dec(v_a_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_inc_ref(v_next_973_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v___y_2147_);
v___x_2174_ = lean_apply_7(v_next_973_, v___y_2147_, v___y_2136_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; 
lean_dec(v___y_2147_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2139_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec_ref(v_cfg_971_);
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v___y_1086_ = v_a_2149_;
v___y_1087_ = v___y_2140_;
v___y_1088_ = v___x_2170_;
v___y_1089_ = v___y_2141_;
v___y_1090_ = v___y_2137_;
v___y_1091_ = v___y_2145_;
v___y_1092_ = v___y_2146_;
v_a_1093_ = v_a_2175_;
goto v___jp_1085_;
}
else
{
lean_object* v_a_2176_; uint8_t v___x_2177_; 
v_a_2176_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2177_ = l_Lean_Exception_isInterrupt(v_a_2176_);
if (v___x_2177_ == 0)
{
uint8_t v___x_2178_; 
lean_inc(v_a_2176_);
v___x_2178_ = l_Lean_Exception_isRuntime(v_a_2176_);
v___y_2018_ = v_a_2176_;
v___y_2019_ = v___x_2170_;
v___y_2020_ = v___y_2137_;
v___y_2021_ = v___y_2139_;
v___y_2022_ = v_a_2149_;
v___y_2023_ = v___y_2140_;
v___y_2024_ = v___y_2142_;
v___y_2025_ = v___y_2141_;
v___y_2026_ = v___y_2144_;
v___y_2027_ = v___y_2145_;
v___y_2028_ = v___x_2151_;
v___y_2029_ = v___y_2146_;
v___y_2030_ = v___y_2147_;
v___y_2031_ = v___x_2178_;
goto v___jp_2017_;
}
else
{
v___y_2018_ = v_a_2176_;
v___y_2019_ = v___x_2170_;
v___y_2020_ = v___y_2137_;
v___y_2021_ = v___y_2139_;
v___y_2022_ = v_a_2149_;
v___y_2023_ = v___y_2140_;
v___y_2024_ = v___y_2142_;
v___y_2025_ = v___y_2141_;
v___y_2026_ = v___y_2144_;
v___y_2027_ = v___y_2145_;
v___y_2028_ = v___x_2151_;
v___y_2029_ = v___y_2146_;
v___y_2030_ = v___y_2147_;
v___y_2031_ = v___x_2177_;
goto v___jp_2017_;
}
}
}
else
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
lean_dec_ref(v___y_2139_);
lean_dec_ref(v___y_2136_);
v___x_2179_ = lean_nat_add(v_n_1887_, v_one_1886_);
lean_dec(v_n_1887_);
v___x_2180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___y_2147_);
lean_ctor_set(v___x_2180_, 1, v_acc_977_);
v___x_2181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_972_);
v___x_2182_ = l_Lean_Name_append(v___x_2181_, v_trace_972_);
v___x_2183_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2142_, v___y_2137_, v___x_2182_);
lean_dec(v___x_2182_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = l_Lean_trace_profiler;
v___x_2185_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2137_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
lean_inc(v_trace_972_);
v___x_2186_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___x_2179_, v___y_2144_, v___x_2180_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
v___y_1106_ = v_a_2149_;
v___y_1107_ = v___y_2140_;
v___y_1108_ = v___x_2170_;
v___y_1109_ = v___y_2137_;
v___y_1110_ = v___y_2141_;
v___y_1111_ = v___y_2145_;
v___y_1112_ = v___y_2146_;
v___y_1113_ = v___x_2186_;
goto v___jp_1105_;
}
else
{
v___y_1381_ = v___x_2170_;
v___y_1382_ = v___y_2137_;
v___y_1383_ = v___x_2179_;
v___y_1384_ = v___x_2183_;
v___y_1385_ = v_a_2149_;
v___y_1386_ = v___y_2140_;
v___y_1387_ = v___y_2141_;
v___y_1388_ = v___y_2144_;
v___y_1389_ = v___y_2145_;
v___y_1390_ = v___x_2180_;
v___y_1391_ = v___x_2151_;
v___y_1392_ = v___y_2146_;
goto v___jp_1380_;
}
}
else
{
v___y_1381_ = v___x_2170_;
v___y_1382_ = v___y_2137_;
v___y_1383_ = v___x_2179_;
v___y_1384_ = v___x_2183_;
v___y_1385_ = v_a_2149_;
v___y_1386_ = v___y_2140_;
v___y_1387_ = v___y_2141_;
v___y_1388_ = v___y_2144_;
v___y_1389_ = v___y_2145_;
v___y_1390_ = v___x_2180_;
v___y_1391_ = v___x_2151_;
v___y_1392_ = v___y_2146_;
goto v___jp_1380_;
}
}
}
else
{
lean_object* v_a_2187_; 
lean_dec(v___y_2147_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2139_);
lean_dec_ref(v___y_2136_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec_ref(v_cfg_971_);
v_a_2187_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2171_, 1);
v___y_1096_ = v_a_2149_;
v___y_1097_ = v___y_2140_;
v___y_1098_ = v___x_2170_;
v___y_1099_ = v___y_2141_;
v___y_1100_ = v___y_2137_;
v___y_1101_ = v___y_2145_;
v___y_1102_ = v___y_2146_;
v_a_1103_ = v_a_2187_;
goto v___jp_1095_;
}
}
}
v___jp_2188_:
{
if (v___y_2193_ == 0)
{
lean_object* v___x_2194_; 
lean_dec_ref(v___y_2191_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v___y_2192_);
v___x_2194_ = lean_apply_6(v___y_2189_, v___y_2192_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
if (lean_obj_tag(v_a_2195_) == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_nat_add(v_n_1887_, v_one_1886_);
lean_dec(v_n_1887_);
v___x_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___y_2192_);
lean_ctor_set(v___x_2197_, 1, v_acc_977_);
v_n_975_ = v___x_2196_;
v_curr_976_ = v___y_2190_;
v_acc_977_ = v___x_2197_;
goto _start;
}
else
{
lean_object* v_val_2199_; lean_object* v___x_2200_; 
lean_dec(v___y_2192_);
v_val_2199_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_val_2199_);
lean_dec_ref_known(v_a_2195_, 1);
v___x_2200_ = l_List_appendTR___redArg(v_val_2199_, v___y_2190_);
v_n_975_ = v_n_1887_;
v_curr_976_ = v___x_2200_;
goto _start;
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v___y_2192_);
lean_dec(v___y_2190_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
v_a_2202_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2194_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2194_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_dec(v___y_2192_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
return v___y_2191_;
}
}
v___jp_2210_:
{
if (lean_obj_tag(v_a_2211_) == 0)
{
if (lean_obj_tag(v_curr_976_) == 0)
{
lean_object* v_options_2212_; lean_object* v_inheritedTraceOptions_2213_; uint8_t v_hasTrace_2214_; lean_object* v___x_2215_; 
lean_dec(v_n_1887_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec_ref(v_cfg_971_);
v_options_2212_ = lean_ctor_get(v_a_980_, 2);
v_inheritedTraceOptions_2213_ = lean_ctor_get(v_a_980_, 13);
v_hasTrace_2214_ = lean_ctor_get_uint8(v_options_2212_, sizeof(void*)*1);
v___x_2215_ = l_List_reverse___redArg(v_acc_977_);
if (v_hasTrace_2214_ == 0)
{
lean_object* v___x_2216_; 
lean_dec(v_trace_972_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_972_);
v___x_2219_ = l_Lean_Name_append(v___x_2218_, v_trace_972_);
v___x_2220_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2213_, v_options_2212_, v___x_2219_);
lean_dec(v___x_2219_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2221_ = l_Lean_trace_profiler;
v___x_2222_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2212_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
lean_dec(v_trace_972_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2215_);
return v___x_2223_;
}
else
{
v___y_1176_ = v_hasTrace_2214_;
v___y_1177_ = v___x_2220_;
v___y_1178_ = v_options_2212_;
v___y_1179_ = v___x_2215_;
v___y_1180_ = v___x_2217_;
goto v___jp_1175_;
}
}
else
{
v___y_1176_ = v_hasTrace_2214_;
v___y_1177_ = v___x_2220_;
v___y_1178_ = v_options_2212_;
v___y_1179_ = v___x_2215_;
v___y_1180_ = v___x_2217_;
goto v___jp_1175_;
}
}
}
else
{
lean_object* v_head_2224_; lean_object* v_tail_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2298_; 
v_head_2224_ = lean_ctor_get(v_curr_976_, 0);
v_tail_2225_ = lean_ctor_get(v_curr_976_, 1);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_curr_976_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2227_ = v_curr_976_;
v_isShared_2228_ = v_isSharedCheck_2298_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_tail_2225_);
lean_inc(v_head_2224_);
lean_dec(v_curr_976_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2298_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v_a_2230_; uint8_t v___x_2231_; uint8_t v___x_2232_; 
v___x_2229_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2224_, v_a_979_);
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = 1;
v___x_2232_ = lean_unbox(v_a_2230_);
lean_dec(v_a_2230_);
if (v___x_2232_ == 0)
{
lean_object* v_options_2233_; uint8_t v_hasTrace_2234_; 
v_options_2233_ = lean_ctor_get(v_a_980_, 2);
v_hasTrace_2234_ = lean_ctor_get_uint8(v_options_2233_, sizeof(void*)*1);
if (v_hasTrace_2234_ == 0)
{
lean_object* v___x_2235_; 
lean_inc_ref(v_suspend_1172_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v_head_2224_);
v___x_2235_ = lean_apply_6(v_suspend_1172_, v_head_2224_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; uint8_t v___x_2237_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2237_ = lean_unbox(v_a_2236_);
lean_dec(v_a_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___f_2238_; lean_object* v___x_2239_; 
lean_del_object(v___x_2227_);
lean_inc(v_acc_977_);
lean_inc(v_n_1887_);
lean_inc(v_goals_974_);
lean_inc_ref_n(v_next_973_, 2);
lean_inc(v_trace_972_);
lean_inc_ref(v_cfg_971_);
lean_inc(v_tail_2225_);
v___f_2238_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2238_, 0, v_tail_2225_);
lean_closure_set(v___f_2238_, 1, v_cfg_971_);
lean_closure_set(v___f_2238_, 2, v_trace_972_);
lean_closure_set(v___f_2238_, 3, v_next_973_);
lean_closure_set(v___f_2238_, 4, v_goals_974_);
lean_closure_set(v___f_2238_, 5, v_n_1887_);
lean_closure_set(v___f_2238_, 6, v_acc_977_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v_head_2224_);
v___x_2239_ = lean_apply_7(v_next_973_, v_head_2224_, v___f_2238_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_dec(v_tail_2225_);
lean_dec(v_head_2224_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
return v___x_2239_;
}
else
{
lean_object* v_a_2240_; uint8_t v___x_2241_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
v___x_2241_ = l_Lean_Exception_isInterrupt(v_a_2240_);
if (v___x_2241_ == 0)
{
uint8_t v___x_2242_; 
v___x_2242_ = l_Lean_Exception_isRuntime(v_a_2240_);
lean_inc_ref(v_discharge_1173_);
v___y_2189_ = v_discharge_1173_;
v___y_2190_ = v_tail_2225_;
v___y_2191_ = v___x_2239_;
v___y_2192_ = v_head_2224_;
v___y_2193_ = v___x_2242_;
goto v___jp_2188_;
}
else
{
lean_dec(v_a_2240_);
lean_inc_ref(v_discharge_1173_);
v___y_2189_ = v_discharge_1173_;
v___y_2190_ = v_tail_2225_;
v___y_2191_ = v___x_2239_;
v___y_2192_ = v_head_2224_;
v___y_2193_ = v___x_2241_;
goto v___jp_2188_;
}
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2243_ = lean_nat_add(v_n_1887_, v_one_1886_);
lean_dec(v_n_1887_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v_acc_977_);
v___x_2245_ = v___x_2227_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_head_2224_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_acc_977_);
v___x_2245_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
v_n_975_ = v___x_2243_;
v_curr_976_ = v_tail_2225_;
v_acc_977_ = v___x_2245_;
goto _start;
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_del_object(v___x_2227_);
lean_dec(v_tail_2225_);
lean_dec(v_head_2224_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
v_a_2248_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2235_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2235_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2256_; lean_object* v___f_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v_inheritedTraceOptions_2256_ = lean_ctor_get(v_a_980_, 13);
lean_inc(v_acc_977_);
lean_inc(v_n_1887_);
lean_inc(v_goals_974_);
lean_inc_ref(v_next_973_);
lean_inc_n(v_trace_972_, 2);
lean_inc_ref(v_cfg_971_);
lean_inc(v_tail_2225_);
v___f_2257_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2257_, 0, v_tail_2225_);
lean_closure_set(v___f_2257_, 1, v_cfg_971_);
lean_closure_set(v___f_2257_, 2, v_trace_972_);
lean_closure_set(v___f_2257_, 3, v_next_973_);
lean_closure_set(v___f_2257_, 4, v_goals_974_);
lean_closure_set(v___f_2257_, 5, v_n_1887_);
lean_closure_set(v___f_2257_, 6, v_acc_977_);
lean_inc(v_head_2224_);
v___f_2258_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(v___f_2258_, 0, v_head_2224_);
v___x_2259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
v___x_2261_ = l_Lean_Name_append(v___x_2260_, v_trace_972_);
v___x_2262_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2256_, v_options_2233_, v___x_2261_);
lean_dec(v___x_2261_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = l_Lean_trace_profiler;
v___x_2264_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2233_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; 
lean_dec_ref(v___f_2258_);
lean_inc_ref(v_suspend_1172_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v_head_2224_);
v___x_2265_ = lean_apply_6(v_suspend_1172_, v_head_2224_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; uint8_t v___x_2267_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2267_ = lean_unbox(v_a_2266_);
lean_dec(v_a_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
lean_del_object(v___x_2227_);
lean_inc_ref(v_next_973_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v_head_2224_);
v___x_2268_ = lean_apply_7(v_next_973_, v_head_2224_, v___f_2257_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_dec(v_tail_2225_);
lean_dec(v_head_2224_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
return v___x_2268_;
}
else
{
lean_object* v_a_2269_; uint8_t v___x_2270_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
v___x_2270_ = l_Lean_Exception_isInterrupt(v_a_2269_);
if (v___x_2270_ == 0)
{
uint8_t v___x_2271_; 
v___x_2271_ = l_Lean_Exception_isRuntime(v_a_2269_);
lean_inc_ref(v_discharge_1173_);
v___y_1935_ = v_discharge_1173_;
v___y_1936_ = v___x_2264_;
v___y_1937_ = v___x_2259_;
v___y_1938_ = v_options_2233_;
v___y_1939_ = v_inheritedTraceOptions_2256_;
v___y_1940_ = v_tail_2225_;
v___y_1941_ = v___x_2231_;
v___y_1942_ = v_head_2224_;
v___y_1943_ = v___x_2268_;
v___y_1944_ = v___x_2271_;
goto v___jp_1934_;
}
else
{
lean_dec(v_a_2269_);
lean_inc_ref(v_discharge_1173_);
v___y_1935_ = v_discharge_1173_;
v___y_1936_ = v___x_2264_;
v___y_1937_ = v___x_2259_;
v___y_1938_ = v_options_2233_;
v___y_1939_ = v_inheritedTraceOptions_2256_;
v___y_1940_ = v_tail_2225_;
v___y_1941_ = v___x_2231_;
v___y_1942_ = v_head_2224_;
v___y_1943_ = v___x_2268_;
v___y_1944_ = v___x_2270_;
goto v___jp_1934_;
}
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_dec_ref(v___f_2257_);
v___x_2272_ = lean_nat_add(v_n_1887_, v_one_1886_);
lean_dec(v_n_1887_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v_acc_977_);
v___x_2274_ = v___x_2227_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_head_2224_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_acc_977_);
v___x_2274_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
if (v___x_2262_ == 0)
{
if (v___x_2264_ == 0)
{
v_n_975_ = v___x_2272_;
v_curr_976_ = v_tail_2225_;
v_acc_977_ = v___x_2274_;
goto _start;
}
else
{
v___y_1839_ = v___x_2259_;
v___y_1840_ = v_options_2233_;
v___y_1841_ = v___x_2274_;
v___y_1842_ = v_tail_2225_;
v___y_1843_ = v___x_2272_;
v___y_1844_ = v___x_2231_;
v___y_1845_ = v___x_2262_;
goto v___jp_1838_;
}
}
else
{
v___y_1839_ = v___x_2259_;
v___y_1840_ = v_options_2233_;
v___y_1841_ = v___x_2274_;
v___y_1842_ = v_tail_2225_;
v___y_1843_ = v___x_2272_;
v___y_1844_ = v___x_2231_;
v___y_1845_ = v___x_2262_;
goto v___jp_1838_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref(v___f_2257_);
lean_del_object(v___x_2227_);
lean_dec(v_tail_2225_);
lean_dec(v_head_2224_);
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
v_a_2277_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2265_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2265_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_del_object(v___x_2227_);
lean_inc_ref(v_discharge_1173_);
lean_inc_ref(v_suspend_1172_);
lean_inc_ref(v___f_2257_);
v___y_2136_ = v___f_2257_;
v___y_2137_ = v_options_2233_;
v___y_2138_ = v_suspend_1172_;
v___y_2139_ = v_discharge_1173_;
v___y_2140_ = v___x_2262_;
v___y_2141_ = v___x_2259_;
v___y_2142_ = v_inheritedTraceOptions_2256_;
v___y_2143_ = v___f_2257_;
v___y_2144_ = v_tail_2225_;
v___y_2145_ = v___f_2258_;
v___y_2146_ = v___x_2231_;
v___y_2147_ = v_head_2224_;
goto v___jp_2135_;
}
}
else
{
lean_del_object(v___x_2227_);
lean_inc_ref(v_discharge_1173_);
lean_inc_ref(v_suspend_1172_);
lean_inc_ref(v___f_2257_);
v___y_2136_ = v___f_2257_;
v___y_2137_ = v_options_2233_;
v___y_2138_ = v_suspend_1172_;
v___y_2139_ = v_discharge_1173_;
v___y_2140_ = v___x_2262_;
v___y_2141_ = v___x_2259_;
v___y_2142_ = v_inheritedTraceOptions_2256_;
v___y_2143_ = v___f_2257_;
v___y_2144_ = v_tail_2225_;
v___y_2145_ = v___f_2258_;
v___y_2146_ = v___x_2231_;
v___y_2147_ = v_head_2224_;
goto v___jp_2135_;
}
}
}
else
{
lean_object* v_options_2285_; lean_object* v_inheritedTraceOptions_2286_; uint8_t v_hasTrace_2287_; lean_object* v___x_2288_; 
lean_del_object(v___x_2227_);
v_options_2285_ = lean_ctor_get(v_a_980_, 2);
v_inheritedTraceOptions_2286_ = lean_ctor_get(v_a_980_, 13);
v_hasTrace_2287_ = lean_ctor_get_uint8(v_options_2285_, sizeof(void*)*1);
v___x_2288_ = lean_nat_add(v_n_1887_, v_one_1886_);
lean_dec(v_n_1887_);
if (v_hasTrace_2287_ == 0)
{
lean_dec(v_head_2224_);
v_n_975_ = v___x_2288_;
v_curr_976_ = v_tail_2225_;
goto _start;
}
else
{
lean_object* v___f_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___f_2290_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2290_, 0, v_head_2224_);
v___x_2291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_972_);
v___x_2293_ = l_Lean_Name_append(v___x_2292_, v_trace_972_);
v___x_2294_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2286_, v_options_2285_, v___x_2293_);
lean_dec(v___x_2293_);
if (v___x_2294_ == 0)
{
lean_object* v___x_2295_; uint8_t v___x_2296_; 
v___x_2295_ = l_Lean_trace_profiler;
v___x_2296_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2285_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_dec_ref(v___f_2290_);
v_n_975_ = v___x_2288_;
v_curr_976_ = v_tail_2225_;
goto _start;
}
else
{
v___y_1021_ = v___x_2288_;
v___y_1022_ = v___x_2294_;
v___y_1023_ = v_tail_2225_;
v___y_1024_ = v___f_2290_;
v___y_1025_ = v___x_2291_;
v___y_1026_ = v___x_2231_;
v___y_1027_ = v_options_2285_;
goto v___jp_1020_;
}
}
else
{
v___y_1021_ = v___x_2288_;
v___y_1022_ = v___x_2294_;
v___y_1023_ = v_tail_2225_;
v___y_1024_ = v___f_2290_;
v___y_1025_ = v___x_2291_;
v___y_1026_ = v___x_2231_;
v___y_1027_ = v_options_2285_;
goto v___jp_1020_;
}
}
}
}
}
}
else
{
lean_object* v_val_2299_; 
lean_dec(v_curr_976_);
v_val_2299_ = lean_ctor_get(v_a_2211_, 0);
lean_inc(v_val_2299_);
lean_dec_ref_known(v_a_2211_, 1);
v_n_975_ = v_n_1887_;
v_curr_976_ = v_val_2299_;
goto _start;
}
}
v___jp_2301_:
{
if (lean_obj_tag(v___y_2302_) == 0)
{
lean_object* v_a_2303_; 
v_a_2303_ = lean_ctor_get(v___y_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___y_2302_, 1);
v_a_2211_ = v_a_2303_;
goto v___jp_2210_;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec(v_n_1887_);
lean_dec(v_acc_977_);
lean_dec(v_curr_976_);
lean_dec(v_goals_974_);
lean_dec_ref(v_next_973_);
lean_dec(v_trace_972_);
lean_dec_ref(v_cfg_971_);
v_a_2304_ = lean_ctor_get(v___y_2302_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___y_2302_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___y_2302_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___y_2302_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
v___jp_983_:
{
lean_object* v___x_992_; double v___x_993_; double v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_992_ = lean_io_get_num_heartbeats();
v___x_993_ = lean_float_of_nat(v___y_990_);
v___x_994_ = lean_float_of_nat(v___x_992_);
v___x_995_ = lean_box_float(v___x_993_);
v___x_996_ = lean_box_float(v___x_994_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v_a_991_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
lean_inc_ref(v___y_987_);
v___x_999_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_989_, v___y_987_, v___y_988_, v___y_985_, v___y_984_, v___y_986_, v___x_998_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_999_;
}
v___jp_1000_:
{
lean_object* v___x_1009_; double v___x_1010_; double v___x_1011_; double v___x_1012_; double v___x_1013_; double v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1009_ = lean_io_mono_nanos_now();
v___x_1010_ = lean_float_of_nat(v___y_1007_);
v___x_1011_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1012_ = lean_float_div(v___x_1010_, v___x_1011_);
v___x_1013_ = lean_float_of_nat(v___x_1009_);
v___x_1014_ = lean_float_div(v___x_1013_, v___x_1011_);
v___x_1015_ = lean_box_float(v___x_1012_);
v___x_1016_ = lean_box_float(v___x_1014_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v_a_1008_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
lean_inc_ref(v___y_1004_);
v___x_1019_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1006_, v___y_1004_, v___y_1005_, v___y_1002_, v___y_1001_, v___y_1003_, v___x_1018_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1019_;
}
v___jp_1020_:
{
lean_object* v___x_1028_; lean_object* v_a_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v___x_1028_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_981_);
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1031_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1027_, v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_io_mono_nanos_now();
lean_inc(v_trace_972_);
v___x_1033_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1021_, v___y_1023_, v_acc_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 1);
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
v___y_1001_ = v_a_1029_;
v___y_1002_ = v___y_1022_;
v___y_1003_ = v___y_1024_;
v___y_1004_ = v___y_1025_;
v___y_1005_ = v___y_1027_;
v___y_1006_ = v___y_1026_;
v___y_1007_ = v___x_1032_;
v_a_1008_ = v___x_1039_;
goto v___jp_1000_;
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
v_a_1042_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1033_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1033_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set_tag(v___x_1044_, 0);
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
v___y_1001_ = v_a_1029_;
v___y_1002_ = v___y_1022_;
v___y_1003_ = v___y_1024_;
v___y_1004_ = v___y_1025_;
v___y_1005_ = v___y_1027_;
v___y_1006_ = v___y_1026_;
v___y_1007_ = v___x_1032_;
v_a_1008_ = v___x_1047_;
goto v___jp_1000_;
}
}
}
}
else
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_972_);
v___x_1051_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_971_, v_trace_972_, v_next_973_, v_goals_974_, v___y_1021_, v___y_1023_, v_acc_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 1);
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
v___y_984_ = v_a_1029_;
v___y_985_ = v___y_1022_;
v___y_986_ = v___y_1024_;
v___y_987_ = v___y_1025_;
v___y_988_ = v___y_1027_;
v___y_989_ = v___y_1026_;
v___y_990_ = v___x_1050_;
v_a_991_ = v___x_1057_;
goto v___jp_983_;
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1051_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1051_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
lean_ctor_set_tag(v___x_1062_, 0);
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
v___y_984_ = v_a_1029_;
v___y_985_ = v___y_1022_;
v___y_986_ = v___y_1024_;
v___y_987_ = v___y_1025_;
v___y_988_ = v___y_1027_;
v___y_989_ = v___y_1026_;
v___y_990_ = v___x_1050_;
v_a_991_ = v___x_1065_;
goto v___jp_983_;
}
}
}
}
}
v___jp_1068_:
{
lean_object* v___x_1077_; double v___x_1078_; double v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1077_ = lean_io_get_num_heartbeats();
v___x_1078_ = lean_float_of_nat(v___y_1071_);
v___x_1079_ = lean_float_of_nat(v___x_1077_);
v___x_1080_ = lean_box_float(v___x_1078_);
v___x_1081_ = lean_box_float(v___x_1079_);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v_a_1076_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
lean_inc_ref(v___y_1073_);
v___x_1084_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1075_, v___y_1073_, v___y_1072_, v___y_1070_, v___y_1069_, v___y_1074_, v___x_1083_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1084_;
}
v___jp_1085_:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_a_1093_);
v___y_1069_ = v___y_1086_;
v___y_1070_ = v___y_1087_;
v___y_1071_ = v___y_1088_;
v___y_1072_ = v___y_1090_;
v___y_1073_ = v___y_1089_;
v___y_1074_ = v___y_1091_;
v___y_1075_ = v___y_1092_;
v_a_1076_ = v___x_1094_;
goto v___jp_1068_;
}
v___jp_1095_:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_a_1103_);
v___y_1069_ = v___y_1096_;
v___y_1070_ = v___y_1097_;
v___y_1071_ = v___y_1098_;
v___y_1072_ = v___y_1100_;
v___y_1073_ = v___y_1099_;
v___y_1074_ = v___y_1101_;
v___y_1075_ = v___y_1102_;
v_a_1076_ = v___x_1104_;
goto v___jp_1068_;
}
v___jp_1105_:
{
if (lean_obj_tag(v___y_1113_) == 0)
{
lean_object* v_a_1114_; 
v_a_1114_ = lean_ctor_get(v___y_1113_, 0);
lean_inc(v_a_1114_);
lean_dec_ref_known(v___y_1113_, 1);
v___y_1086_ = v___y_1106_;
v___y_1087_ = v___y_1107_;
v___y_1088_ = v___y_1108_;
v___y_1089_ = v___y_1110_;
v___y_1090_ = v___y_1109_;
v___y_1091_ = v___y_1111_;
v___y_1092_ = v___y_1112_;
v_a_1093_ = v_a_1114_;
goto v___jp_1085_;
}
else
{
lean_object* v_a_1115_; 
v_a_1115_ = lean_ctor_get(v___y_1113_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___y_1113_, 1);
v___y_1096_ = v___y_1106_;
v___y_1097_ = v___y_1107_;
v___y_1098_ = v___y_1108_;
v___y_1099_ = v___y_1110_;
v___y_1100_ = v___y_1109_;
v___y_1101_ = v___y_1111_;
v___y_1102_ = v___y_1112_;
v_a_1103_ = v_a_1115_;
goto v___jp_1095_;
}
}
v___jp_1116_:
{
lean_object* v___x_1125_; double v___x_1126_; double v___x_1127_; double v___x_1128_; double v___x_1129_; double v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1125_ = lean_io_mono_nanos_now();
v___x_1126_ = lean_float_of_nat(v___y_1119_);
v___x_1127_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1128_ = lean_float_div(v___x_1126_, v___x_1127_);
v___x_1129_ = lean_float_of_nat(v___x_1125_);
v___x_1130_ = lean_float_div(v___x_1129_, v___x_1127_);
v___x_1131_ = lean_box_float(v___x_1128_);
v___x_1132_ = lean_box_float(v___x_1130_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_a_1124_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
lean_inc_ref(v___y_1121_);
v___x_1135_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_972_, v___y_1123_, v___y_1121_, v___y_1120_, v___y_1118_, v___y_1117_, v___y_1122_, v___x_1134_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
return v___x_1135_;
}
v___jp_1136_:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_a_1144_);
v___y_1117_ = v___y_1137_;
v___y_1118_ = v___y_1138_;
v___y_1119_ = v___y_1139_;
v___y_1120_ = v___y_1141_;
v___y_1121_ = v___y_1140_;
v___y_1122_ = v___y_1142_;
v___y_1123_ = v___y_1143_;
v_a_1124_ = v___x_1145_;
goto v___jp_1116_;
}
v___jp_1146_:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_a_1154_);
v___y_1117_ = v___y_1147_;
v___y_1118_ = v___y_1148_;
v___y_1119_ = v___y_1149_;
v___y_1120_ = v___y_1151_;
v___y_1121_ = v___y_1150_;
v___y_1122_ = v___y_1152_;
v___y_1123_ = v___y_1153_;
v_a_1124_ = v___x_1155_;
goto v___jp_1116_;
}
v___jp_1156_:
{
if (lean_obj_tag(v___y_1164_) == 0)
{
lean_object* v_a_1165_; 
v_a_1165_ = lean_ctor_get(v___y_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___y_1164_, 1);
v___y_1137_ = v___y_1157_;
v___y_1138_ = v___y_1158_;
v___y_1139_ = v___y_1159_;
v___y_1140_ = v___y_1161_;
v___y_1141_ = v___y_1160_;
v___y_1142_ = v___y_1162_;
v___y_1143_ = v___y_1163_;
v_a_1144_ = v_a_1165_;
goto v___jp_1136_;
}
else
{
lean_object* v_a_1166_; 
v_a_1166_ = lean_ctor_get(v___y_1164_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___y_1164_, 1);
v___y_1147_ = v___y_1157_;
v___y_1148_ = v___y_1158_;
v___y_1149_ = v___y_1159_;
v___y_1150_ = v___y_1161_;
v___y_1151_ = v___y_1160_;
v___y_1152_ = v___y_1162_;
v___y_1153_ = v___y_1163_;
v_a_1154_ = v_a_1166_;
goto v___jp_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2382_, lean_object* v_trace_2383_, lean_object* v_next_2384_, lean_object* v_goals_2385_, lean_object* v_n_2386_, lean_object* v_curr_2387_, lean_object* v_acc_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2382_, v_trace_2383_, v_next_2384_, v_goals_2385_, v_n_2386_, v_curr_2387_, v_acc_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object* v_tail_2395_, lean_object* v_cfg_2396_, lean_object* v_trace_2397_, lean_object* v_next_2398_, lean_object* v_goals_2399_, lean_object* v_n_2400_, lean_object* v_acc_2401_, lean_object* v_r_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = l_List_appendTR___redArg(v_r_2402_, v_tail_2395_);
v___x_2409_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2409_, 0, v_cfg_2396_);
lean_closure_set(v___x_2409_, 1, v_trace_2397_);
lean_closure_set(v___x_2409_, 2, v_next_2398_);
lean_closure_set(v___x_2409_, 3, v_goals_2399_);
lean_closure_set(v___x_2409_, 4, v_n_2400_);
lean_closure_set(v___x_2409_, 5, v___x_2408_);
lean_closure_set(v___x_2409_, 6, v_acc_2401_);
v___x_2410_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v___x_2409_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2411_, lean_object* v_msg_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2419_, lean_object* v_msg_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2419_, v_msg_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object* v_00_u03b1_2427_, lean_object* v_x_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_2428_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2435_, lean_object* v_x_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_00_u03b1_2435_, v_x_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* v_mvarId_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_2443_, v___y_2445_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* v_mvarId_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_mvarId_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v_mvarId_2450_);
return v_res_2456_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_object* v_00_u03b2_2457_, lean_object* v_x_2458_, lean_object* v_x_2459_){
_start:
{
uint8_t v___x_2460_; 
v___x_2460_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_2458_, v_x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_){
_start:
{
uint8_t v_res_2464_; lean_object* v_r_2465_; 
v_res_2464_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(v_00_u03b2_2461_, v_x_2462_, v_x_2463_);
lean_dec(v_x_2463_);
lean_dec_ref(v_x_2462_);
v_r_2465_ = lean_box(v_res_2464_);
return v_r_2465_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_2466_, lean_object* v_x_2467_, size_t v_x_2468_, lean_object* v_x_2469_){
_start:
{
uint8_t v___x_2470_; 
v___x_2470_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_2467_, v_x_2468_, v_x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___boxed(lean_object* v_00_u03b2_2471_, lean_object* v_x_2472_, lean_object* v_x_2473_, lean_object* v_x_2474_){
_start:
{
size_t v_x_85402__boxed_2475_; uint8_t v_res_2476_; lean_object* v_r_2477_; 
v_x_85402__boxed_2475_ = lean_unbox_usize(v_x_2473_);
lean_dec(v_x_2473_);
v_res_2476_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2471_, v_x_2472_, v_x_85402__boxed_2475_, v_x_2474_);
lean_dec(v_x_2474_);
lean_dec_ref(v_x_2472_);
v_r_2477_ = lean_box(v_res_2476_);
return v_r_2477_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_object* v_00_u03b2_2478_, lean_object* v_keys_2479_, lean_object* v_vals_2480_, lean_object* v_heq_2481_, lean_object* v_i_2482_, lean_object* v_k_2483_){
_start:
{
uint8_t v___x_2484_; 
v___x_2484_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_2479_, v_i_2482_, v_k_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2485_, lean_object* v_keys_2486_, lean_object* v_vals_2487_, lean_object* v_heq_2488_, lean_object* v_i_2489_, lean_object* v_k_2490_){
_start:
{
uint8_t v_res_2491_; lean_object* v_r_2492_; 
v_res_2491_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(v_00_u03b2_2485_, v_keys_2486_, v_vals_2487_, v_heq_2488_, v_i_2489_, v_k_2490_);
lean_dec(v_k_2490_);
lean_dec_ref(v_vals_2487_);
lean_dec_ref(v_keys_2486_);
v_r_2492_ = lean_box(v_res_2491_);
return v_r_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2493_, lean_object* v_h__1_2494_, lean_object* v_h__2_2495_){
_start:
{
lean_object* v_zero_2496_; uint8_t v_isZero_2497_; 
v_zero_2496_ = lean_unsigned_to_nat(0u);
v_isZero_2497_ = lean_nat_dec_eq(v_n_2493_, v_zero_2496_);
if (v_isZero_2497_ == 1)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec(v_h__2_2495_);
v___x_2498_ = lean_box(0);
v___x_2499_ = lean_apply_1(v_h__1_2494_, v___x_2498_);
return v___x_2499_;
}
else
{
lean_object* v_one_2500_; lean_object* v_n_2501_; lean_object* v___x_2502_; 
lean_dec(v_h__1_2494_);
v_one_2500_ = lean_unsigned_to_nat(1u);
v_n_2501_ = lean_nat_sub(v_n_2493_, v_one_2500_);
v___x_2502_ = lean_apply_1(v_h__2_2495_, v_n_2501_);
return v___x_2502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2503_, lean_object* v_h__1_2504_, lean_object* v_h__2_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2503_, v_h__1_2504_, v_h__2_2505_);
lean_dec(v_n_2503_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2507_, lean_object* v_n_2508_, lean_object* v_h__1_2509_, lean_object* v_h__2_2510_){
_start:
{
lean_object* v_zero_2511_; uint8_t v_isZero_2512_; 
v_zero_2511_ = lean_unsigned_to_nat(0u);
v_isZero_2512_ = lean_nat_dec_eq(v_n_2508_, v_zero_2511_);
if (v_isZero_2512_ == 1)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_dec(v_h__2_2510_);
v___x_2513_ = lean_box(0);
v___x_2514_ = lean_apply_1(v_h__1_2509_, v___x_2513_);
return v___x_2514_;
}
else
{
lean_object* v_one_2515_; lean_object* v_n_2516_; lean_object* v___x_2517_; 
lean_dec(v_h__1_2509_);
v_one_2515_ = lean_unsigned_to_nat(1u);
v_n_2516_ = lean_nat_sub(v_n_2508_, v_one_2515_);
v___x_2517_ = lean_apply_1(v_h__2_2510_, v_n_2516_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* v_motive_2518_, lean_object* v_n_2519_, lean_object* v_h__1_2520_, lean_object* v_h__2_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(v_motive_2518_, v_n_2519_, v_h__1_2520_, v_h__2_2521_);
lean_dec(v_n_2519_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* v_procResult_x3f_2523_, lean_object* v_h__1_2524_, lean_object* v_h__2_2525_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2523_) == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec(v_h__1_2524_);
v___x_2526_ = lean_box(0);
v___x_2527_ = lean_apply_1(v_h__2_2525_, v___x_2526_);
return v___x_2527_;
}
else
{
lean_object* v_val_2528_; lean_object* v___x_2529_; 
lean_dec(v_h__2_2525_);
v_val_2528_ = lean_ctor_get(v_procResult_x3f_2523_, 0);
lean_inc(v_val_2528_);
lean_dec_ref_known(v_procResult_x3f_2523_, 1);
v___x_2529_ = lean_apply_1(v_h__1_2524_, v_val_2528_);
return v___x_2529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* v_motive_2530_, lean_object* v_procResult_x3f_2531_, lean_object* v_h__1_2532_, lean_object* v_h__2_2533_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2531_) == 0)
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_dec(v_h__1_2532_);
v___x_2534_ = lean_box(0);
v___x_2535_ = lean_apply_1(v_h__2_2533_, v___x_2534_);
return v___x_2535_;
}
else
{
lean_object* v_val_2536_; lean_object* v___x_2537_; 
lean_dec(v_h__2_2533_);
v_val_2536_ = lean_ctor_get(v_procResult_x3f_2531_, 0);
lean_inc(v_val_2536_);
lean_dec_ref_known(v_procResult_x3f_2531_, 1);
v___x_2537_ = lean_apply_1(v_h__1_2532_, v_val_2536_);
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2538_, lean_object* v_h__1_2539_, lean_object* v_h__2_2540_){
_start:
{
if (lean_obj_tag(v_curr_2538_) == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec(v_h__2_2540_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_apply_1(v_h__1_2539_, v___x_2541_);
return v___x_2542_;
}
else
{
lean_object* v_head_2543_; lean_object* v_tail_2544_; lean_object* v___x_2545_; 
lean_dec(v_h__1_2539_);
v_head_2543_ = lean_ctor_get(v_curr_2538_, 0);
lean_inc(v_head_2543_);
v_tail_2544_ = lean_ctor_get(v_curr_2538_, 1);
lean_inc(v_tail_2544_);
lean_dec_ref_known(v_curr_2538_, 2);
v___x_2545_ = lean_apply_2(v_h__2_2540_, v_head_2543_, v_tail_2544_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2546_, lean_object* v_curr_2547_, lean_object* v_h__1_2548_, lean_object* v_h__2_2549_){
_start:
{
if (lean_obj_tag(v_curr_2547_) == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec(v_h__2_2549_);
v___x_2550_ = lean_box(0);
v___x_2551_ = lean_apply_1(v_h__1_2548_, v___x_2550_);
return v___x_2551_;
}
else
{
lean_object* v_head_2552_; lean_object* v_tail_2553_; lean_object* v___x_2554_; 
lean_dec(v_h__1_2548_);
v_head_2552_ = lean_ctor_get(v_curr_2547_, 0);
lean_inc(v_head_2552_);
v_tail_2553_ = lean_ctor_get(v_curr_2547_, 1);
lean_inc(v_tail_2553_);
lean_dec_ref_known(v_curr_2547_, 2);
v___x_2554_ = lean_apply_2(v_h__2_2549_, v_head_2552_, v_tail_2553_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2555_, lean_object* v_h__1_2556_, lean_object* v_h__2_2557_){
_start:
{
if (lean_obj_tag(v_____do__lift_2555_) == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_dec(v_h__2_2557_);
v___x_2558_ = lean_box(0);
v___x_2559_ = lean_apply_1(v_h__1_2556_, v___x_2558_);
return v___x_2559_;
}
else
{
lean_object* v_val_2560_; lean_object* v___x_2561_; 
lean_dec(v_h__1_2556_);
v_val_2560_ = lean_ctor_get(v_____do__lift_2555_, 0);
lean_inc(v_val_2560_);
lean_dec_ref_known(v_____do__lift_2555_, 1);
v___x_2561_ = lean_apply_1(v_h__2_2557_, v_val_2560_);
return v___x_2561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_2562_, lean_object* v_____do__lift_2563_, lean_object* v_h__1_2564_, lean_object* v_h__2_2565_){
_start:
{
if (lean_obj_tag(v_____do__lift_2563_) == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v_h__2_2565_);
v___x_2566_ = lean_box(0);
v___x_2567_ = lean_apply_1(v_h__1_2564_, v___x_2566_);
return v___x_2567_;
}
else
{
lean_object* v_val_2568_; lean_object* v___x_2569_; 
lean_dec(v_h__1_2564_);
v_val_2568_ = lean_ctor_get(v_____do__lift_2563_, 0);
lean_inc(v_val_2568_);
lean_dec_ref_known(v_____do__lift_2563_, 1);
v___x_2569_ = lean_apply_1(v_h__2_2565_, v_val_2568_);
return v___x_2569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_2570_, lean_object* v_trace_2571_, lean_object* v_next_2572_, lean_object* v_orig_2573_, lean_object* v_g_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_maxDepth_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v_maxDepth_2580_ = lean_ctor_get(v_cfg_2570_, 0);
lean_inc(v_maxDepth_2580_);
v___x_2581_ = lean_box(0);
v___x_2582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2582_, 0, v_g_2574_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2570_, v_trace_2571_, v_next_2572_, v_orig_2573_, v_maxDepth_2580_, v___x_2582_, v___x_2581_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_2584_, lean_object* v_trace_2585_, lean_object* v_next_2586_, lean_object* v_orig_2587_, lean_object* v_g_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2584_, v_trace_2585_, v_next_2586_, v_orig_2587_, v_g_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
if (lean_obj_tag(v_a_2595_) == 0)
{
lean_object* v___x_2597_; 
v___x_2597_ = l_List_reverse___redArg(v_a_2596_);
return v___x_2597_;
}
else
{
lean_object* v_head_2598_; lean_object* v_tail_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2608_; 
v_head_2598_ = lean_ctor_get(v_a_2595_, 0);
v_tail_2599_ = lean_ctor_get(v_a_2595_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v_a_2595_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2601_ = v_a_2595_;
v_isShared_2602_ = v_isSharedCheck_2608_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_tail_2599_);
lean_inc(v_head_2598_);
lean_dec(v_a_2595_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2608_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2603_ = l_Lean_MessageData_ofFormat(v_head_2598_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 1, v_a_2596_);
lean_ctor_set(v___x_2601_, 0, v___x_2603_);
v___x_2605_ = v___x_2601_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_a_2596_);
v___x_2605_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
v_a_2595_ = v_tail_2599_;
v_a_2596_ = v___x_2605_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_2611_ = l_Lean_stringToMessageData(v___x_2610_);
return v___x_2611_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_2614_ = l_Lean_stringToMessageData(v___x_2613_);
return v___x_2614_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_2617_ = l_Lean_stringToMessageData(v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_2618_, lean_object* v_snd_2619_, lean_object* v_x_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2618_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2628_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_2619_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2648_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2648_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2648_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2633_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_2634_ = lean_box(0);
v___x_2635_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2627_, v___x_2634_);
v___x_2636_ = l_Lean_MessageData_ofList(v___x_2635_);
v___x_2637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2633_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_2639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2637_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
v___x_2640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_2641_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2629_, v___x_2634_);
v___x_2642_ = l_Lean_MessageData_ofList(v___x_2641_);
v___x_2643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2640_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2639_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2644_);
v___x_2646_ = v___x_2631_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v_a_2627_);
v_a_2649_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2628_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2628_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v_snd_2619_);
v_a_2657_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2626_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2626_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_2665_, lean_object* v_snd_2666_, lean_object* v_x_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2665_, v_snd_2666_, v_x_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec_ref(v_x_2667_);
return v_res_2673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_2676_ = l_Lean_stringToMessageData(v___x_2675_);
return v___x_2676_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_2679_ = l_Lean_stringToMessageData(v___x_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_2680_, lean_object* v___x_2681_, lean_object* v_x_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2680_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2690_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2688_, 1);
v___x_2690_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_2681_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2708_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2693_ = v___x_2690_;
v_isShared_2694_ = v_isSharedCheck_2708_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2690_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2708_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_2696_ = lean_box(0);
v___x_2697_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2689_, v___x_2696_);
v___x_2698_ = l_Lean_MessageData_ofList(v___x_2697_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2695_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2691_, v___x_2696_);
v___x_2703_ = l_Lean_MessageData_ofList(v___x_2702_);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2701_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2704_);
v___x_2706_ = v___x_2693_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec(v_a_2689_);
v_a_2709_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2690_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2690_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v___x_2681_);
v_a_2717_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2688_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2688_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_2725_, lean_object* v___x_2726_, lean_object* v_x_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2725_, v___x_2726_, v_x_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec_ref(v_x_2727_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t v___x_2734_, lean_object* v_x_2735_, lean_object* v_x_2736_, lean_object* v___y_2737_){
_start:
{
if (lean_obj_tag(v_x_2735_) == 0)
{
lean_object* v___x_2739_; 
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v_x_2736_);
return v___x_2739_;
}
else
{
lean_object* v_head_2740_; lean_object* v_tail_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2756_; 
v_head_2740_ = lean_ctor_get(v_x_2735_, 0);
v_tail_2741_ = lean_ctor_get(v_x_2735_, 1);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_x_2735_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2743_ = v_x_2735_;
v_isShared_2744_ = v_isSharedCheck_2756_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_tail_2741_);
lean_inc(v_head_2740_);
lean_dec(v_x_2735_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2756_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
uint8_t v_a_2751_; lean_object* v___x_2753_; lean_object* v_a_2754_; uint8_t v___x_2755_; 
v___x_2753_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2740_, v___y_2737_);
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref(v___x_2753_);
v___x_2755_ = lean_unbox(v_a_2754_);
lean_dec(v_a_2754_);
if (v___x_2755_ == 0)
{
goto v___jp_2745_;
}
else
{
v_a_2751_ = v___x_2734_;
goto v___jp_2750_;
}
v___jp_2745_:
{
lean_object* v___x_2747_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 1, v_x_2736_);
v___x_2747_ = v___x_2743_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_head_2740_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v_x_2736_);
v___x_2747_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
v_x_2735_ = v_tail_2741_;
v_x_2736_ = v___x_2747_;
goto _start;
}
}
v___jp_2750_:
{
if (v_a_2751_ == 0)
{
lean_del_object(v___x_2743_);
lean_dec(v_head_2740_);
v_x_2735_ = v_tail_2741_;
goto _start;
}
else
{
goto v___jp_2745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v___x_2757_, lean_object* v_x_2758_, lean_object* v_x_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v___x_57591__boxed_2762_; lean_object* v_res_2763_; 
v___x_57591__boxed_2762_ = lean_unbox(v___x_2757_);
v_res_2763_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_57591__boxed_2762_, v_x_2758_, v_x_2759_, v___y_2760_);
lean_dec(v___y_2760_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
if (lean_obj_tag(v_a_2764_) == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_array_to_list(v_a_2765_);
return v___x_2766_;
}
else
{
lean_object* v_head_2767_; lean_object* v_tail_2768_; lean_object* v___x_2769_; 
v_head_2767_ = lean_ctor_get(v_a_2764_, 0);
lean_inc(v_head_2767_);
v_tail_2768_ = lean_ctor_get(v_a_2764_, 1);
lean_inc(v_tail_2768_);
lean_dec_ref_known(v_a_2764_, 2);
v___x_2769_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2765_, v_head_2767_);
v_a_2764_ = v_tail_2768_;
v_a_2765_ = v___x_2769_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
if (lean_obj_tag(v_a_2772_) == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_dec(v_goals_2771_);
v___x_2780_ = lean_array_to_list(v_a_2773_);
v___x_2781_ = lean_array_to_list(v_a_2774_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
return v___x_2783_;
}
else
{
lean_object* v_head_2784_; lean_object* v_tail_2785_; lean_object* v___x_2786_; 
v_head_2784_ = lean_ctor_get(v_a_2772_, 0);
lean_inc_n(v_head_2784_, 2);
v_tail_2785_ = lean_ctor_get(v_a_2772_, 1);
lean_inc(v_tail_2785_);
lean_dec_ref_known(v_a_2772_, 2);
lean_inc(v_goals_2771_);
v___x_2786_ = l_Lean_MVarId_isIndependentOf(v_goals_2771_, v_head_2784_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; uint8_t v___x_2788_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v___x_2788_ = lean_unbox(v_a_2787_);
lean_dec(v_a_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; 
v___x_2789_ = lean_array_push(v_a_2774_, v_head_2784_);
v_a_2772_ = v_tail_2785_;
v_a_2774_ = v___x_2789_;
goto _start;
}
else
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_array_push(v_a_2773_, v_head_2784_);
v_a_2772_ = v_tail_2785_;
v_a_2773_ = v___x_2791_;
goto _start;
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_dec(v_tail_2785_);
lean_dec(v_head_2784_);
lean_dec_ref(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_goals_2771_);
v_a_2793_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2786_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2786_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
if (lean_obj_tag(v_a_2811_) == 0)
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_array_to_list(v_a_2812_);
return v___x_2813_;
}
else
{
lean_object* v_head_2814_; 
v_head_2814_ = lean_ctor_get(v_a_2811_, 0);
if (lean_obj_tag(v_head_2814_) == 0)
{
lean_object* v_tail_2815_; lean_object* v_val_2816_; lean_object* v___x_2817_; 
lean_inc_ref(v_head_2814_);
v_tail_2815_ = lean_ctor_get(v_a_2811_, 1);
lean_inc(v_tail_2815_);
lean_dec_ref_known(v_a_2811_, 2);
v_val_2816_ = lean_ctor_get(v_head_2814_, 0);
lean_inc(v_val_2816_);
lean_dec_ref_known(v_head_2814_, 1);
v___x_2817_ = lean_array_push(v_a_2812_, v_val_2816_);
v_a_2811_ = v_tail_2815_;
v_a_2812_ = v___x_2817_;
goto _start;
}
else
{
lean_object* v_tail_2819_; 
v_tail_2819_ = lean_ctor_get(v_a_2811_, 1);
lean_inc(v_tail_2819_);
lean_dec_ref_known(v_a_2811_, 2);
v_a_2811_ = v_tail_2819_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_2821_, lean_object* v_x_2822_, lean_object* v_x_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
if (lean_obj_tag(v_x_2822_) == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec_ref(v_f_2821_);
v___x_2829_ = l_List_reverse___redArg(v_x_2823_);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
else
{
lean_object* v_head_2831_; lean_object* v_tail_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2877_; 
v_head_2831_ = lean_ctor_get(v_x_2822_, 0);
v_tail_2832_ = lean_ctor_get(v_x_2822_, 1);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_x_2822_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2834_ = v_x_2822_;
v_isShared_2835_ = v_isSharedCheck_2877_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_tail_2832_);
lean_inc(v_head_2831_);
lean_dec(v_x_2822_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2877_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v_a_2837_; lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_Meta_saveState___redArg(v___y_2825_, v___y_2827_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v___x_2842_, 1);
lean_inc_ref(v_f_2821_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
lean_inc(v_head_2831_);
v___x_2844_ = lean_apply_6(v_f_2821_, v_head_2831_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, lean_box(0));
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
lean_dec(v_a_2843_);
lean_dec(v_head_2831_);
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2846_, 0, v_a_2845_);
v_a_2837_ = v___x_2846_;
goto v___jp_2836_;
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2868_; 
v_a_2847_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2849_ = v___x_2844_;
v_isShared_2850_ = v_isSharedCheck_2868_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2844_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2868_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
uint8_t v___y_2852_; uint8_t v___x_2866_; 
v___x_2866_ = l_Lean_Exception_isInterrupt(v_a_2847_);
if (v___x_2866_ == 0)
{
uint8_t v___x_2867_; 
lean_inc(v_a_2847_);
v___x_2867_ = l_Lean_Exception_isRuntime(v_a_2847_);
v___y_2852_ = v___x_2867_;
goto v___jp_2851_;
}
else
{
v___y_2852_ = v___x_2866_;
goto v___jp_2851_;
}
v___jp_2851_:
{
if (v___y_2852_ == 0)
{
lean_object* v___x_2853_; 
lean_del_object(v___x_2849_);
lean_dec(v_a_2847_);
v___x_2853_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2843_, v___y_2825_, v___y_2827_);
lean_dec(v_a_2843_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v___x_2854_; 
lean_dec_ref_known(v___x_2853_, 1);
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v_head_2831_);
v_a_2837_ = v___x_2854_;
goto v___jp_2836_;
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_del_object(v___x_2834_);
lean_dec(v_tail_2832_);
lean_dec(v_head_2831_);
lean_dec(v_x_2823_);
lean_dec_ref(v_f_2821_);
v_a_2855_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2853_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2853_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v___x_2864_; 
lean_dec(v_a_2843_);
lean_del_object(v___x_2834_);
lean_dec(v_tail_2832_);
lean_dec(v_head_2831_);
lean_dec(v_x_2823_);
lean_dec_ref(v_f_2821_);
if (v_isShared_2850_ == 0)
{
v___x_2864_ = v___x_2849_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2847_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_del_object(v___x_2834_);
lean_dec(v_tail_2832_);
lean_dec(v_head_2831_);
lean_dec(v_x_2823_);
lean_dec_ref(v_f_2821_);
v_a_2869_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2842_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2842_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
v___jp_2836_:
{
lean_object* v___x_2839_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 1, v_x_2823_);
lean_ctor_set(v___x_2834_, 0, v_a_2837_);
v___x_2839_ = v___x_2834_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2837_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_x_2823_);
v___x_2839_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
v_x_2822_ = v_tail_2832_;
v_x_2823_ = v___x_2839_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_2878_, lean_object* v_x_2879_, lean_object* v_x_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2878_, v_x_2879_, v_x_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
if (lean_obj_tag(v_a_2887_) == 0)
{
lean_object* v___x_2889_; 
v___x_2889_ = lean_array_to_list(v_a_2888_);
return v___x_2889_;
}
else
{
lean_object* v_head_2890_; 
v_head_2890_ = lean_ctor_get(v_a_2887_, 0);
if (lean_obj_tag(v_head_2890_) == 1)
{
lean_object* v_tail_2891_; lean_object* v_val_2892_; lean_object* v___x_2893_; 
lean_inc_ref(v_head_2890_);
v_tail_2891_ = lean_ctor_get(v_a_2887_, 1);
lean_inc(v_tail_2891_);
lean_dec_ref_known(v_a_2887_, 2);
v_val_2892_ = lean_ctor_get(v_head_2890_, 0);
lean_inc(v_val_2892_);
lean_dec_ref_known(v_head_2890_, 1);
v___x_2893_ = lean_array_push(v_a_2888_, v_val_2892_);
v_a_2887_ = v_tail_2891_;
v_a_2888_ = v___x_2893_;
goto _start;
}
else
{
lean_object* v_tail_2895_; 
v_tail_2895_ = lean_ctor_get(v_a_2887_, 1);
lean_inc(v_tail_2895_);
lean_dec_ref_known(v_a_2887_, 2);
v_a_2887_ = v_tail_2895_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_2897_, lean_object* v_f_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = lean_box(0);
v___x_2905_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2898_, v_L_2897_, v___x_2904_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2917_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_2917_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2917_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2915_; 
v___x_2910_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_2906_);
v___x_2911_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_2906_, v___x_2910_);
v___x_2912_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_2906_, v___x_2910_);
v___x_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2911_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_2913_);
v___x_2915_ = v___x_2908_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v___x_2913_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
v_a_2918_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2905_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2905_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* v_L_2926_, lean_object* v_f_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_2926_, v_f_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t v___x_2934_, uint8_t v___x_2935_, lean_object* v_x_2936_, lean_object* v_x_2937_, lean_object* v___y_2938_){
_start:
{
if (lean_obj_tag(v_x_2936_) == 0)
{
lean_object* v___x_2940_; 
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v_x_2937_);
return v___x_2940_;
}
else
{
lean_object* v_head_2941_; lean_object* v_tail_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2956_; 
v_head_2941_ = lean_ctor_get(v_x_2936_, 0);
v_tail_2942_ = lean_ctor_get(v_x_2936_, 1);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_x_2936_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2944_ = v_x_2936_;
v_isShared_2945_ = v_isSharedCheck_2956_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_tail_2942_);
lean_inc(v_head_2941_);
lean_dec(v_x_2936_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2956_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
uint8_t v_a_2947_; lean_object* v___x_2953_; lean_object* v_a_2954_; uint8_t v___x_2955_; 
v___x_2953_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2941_, v___y_2938_);
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref(v___x_2953_);
v___x_2955_ = lean_unbox(v_a_2954_);
lean_dec(v_a_2954_);
if (v___x_2955_ == 0)
{
v_a_2947_ = v___x_2934_;
goto v___jp_2946_;
}
else
{
v_a_2947_ = v___x_2935_;
goto v___jp_2946_;
}
v___jp_2946_:
{
if (v_a_2947_ == 0)
{
lean_del_object(v___x_2944_);
lean_dec(v_head_2941_);
v_x_2936_ = v_tail_2942_;
goto _start;
}
else
{
lean_object* v___x_2950_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v_x_2937_);
v___x_2950_ = v___x_2944_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_head_2941_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_x_2937_);
v___x_2950_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
v_x_2936_ = v_tail_2942_;
v_x_2937_ = v___x_2950_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* v___x_2957_, lean_object* v___x_2958_, lean_object* v_x_2959_, lean_object* v_x_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
uint8_t v___x_57945__boxed_2963_; uint8_t v___x_57946__boxed_2964_; lean_object* v_res_2965_; 
v___x_57945__boxed_2963_ = lean_unbox(v___x_2957_);
v___x_57946__boxed_2964_ = lean_unbox(v___x_2958_);
v_res_2965_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_57945__boxed_2963_, v___x_57946__boxed_2964_, v_x_2959_, v_x_2960_, v___y_2961_);
lean_dec(v___y_2961_);
return v_res_2965_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
v___x_2968_ = l_Lean_stringToMessageData(v___x_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_2971_, lean_object* v_trace_2972_, lean_object* v_next_2973_, lean_object* v_orig_2974_, lean_object* v_goals_2975_, lean_object* v_remaining_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2));
lean_inc(v_remaining_2976_);
lean_inc(v_goals_2975_);
v___x_2986_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2975_, v_remaining_2976_, v___x_2985_, v___x_2985_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v_fst_2988_; lean_object* v_snd_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_4197_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
v_fst_2988_ = lean_ctor_get(v_a_2987_, 0);
v_snd_2989_ = lean_ctor_get(v_a_2987_, 1);
v_isSharedCheck_4197_ = !lean_is_exclusive(v_a_2987_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_2991_ = v_a_2987_;
v_isShared_2992_ = v_isSharedCheck_4197_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_snd_2989_);
lean_inc(v_fst_2988_);
lean_dec(v_a_2987_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_4197_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
uint8_t v___x_2993_; 
v___x_2993_ = l_List_isEmpty___redArg(v_fst_2988_);
if (v___x_2993_ == 0)
{
lean_object* v_options_2994_; lean_object* v_inheritedTraceOptions_2995_; uint8_t v_hasTrace_2996_; lean_object* v___f_2997_; 
lean_dec(v_remaining_2976_);
v_options_2994_ = lean_ctor_get(v_a_2979_, 2);
v_inheritedTraceOptions_2995_ = lean_ctor_get(v_a_2979_, 13);
v_hasTrace_2996_ = lean_ctor_get_uint8(v_options_2994_, sizeof(void*)*1);
lean_inc(v_orig_2974_);
lean_inc_ref(v_next_2973_);
lean_inc(v_trace_2972_);
lean_inc_ref(v_cfg_2971_);
v___f_2997_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2997_, 0, v_cfg_2971_);
lean_closure_set(v___f_2997_, 1, v_trace_2972_);
lean_closure_set(v___f_2997_, 2, v_next_2973_);
lean_closure_set(v___f_2997_, 3, v_orig_2974_);
if (v_hasTrace_2996_ == 0)
{
lean_object* v___x_2998_; 
lean_del_object(v___x_2991_);
v___x_2998_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2988_, v___f_2997_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3068_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3068_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3068_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v_fst_3003_; lean_object* v_snd_3004_; lean_object* v___x_3005_; lean_object* v_a_3007_; lean_object* v___y_3014_; lean_object* v___y_3017_; lean_object* v___y_3018_; uint8_t v___y_3019_; lean_object* v___y_3030_; lean_object* v_a_3045_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v_fst_3003_ = lean_ctor_get(v_a_2999_, 0);
lean_inc(v_fst_3003_);
v_snd_3004_ = lean_ctor_get(v_a_2999_, 1);
lean_inc(v_snd_3004_);
lean_dec(v_a_2999_);
v___x_3005_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3004_, v___x_2985_);
v___x_3063_ = lean_box(0);
v___x_3064_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_hasTrace_2996_, v_goals_2975_, v___x_3063_, v_a_2978_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3066_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v___x_3066_ = l_List_reverse___redArg(v_a_3065_);
v_a_3045_ = v___x_3066_;
goto v___jp_3044_;
}
else
{
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3067_; 
v_a_3067_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___x_3064_, 1);
v_a_3045_ = v_a_3067_;
goto v___jp_3044_;
}
else
{
lean_dec(v___x_3005_);
lean_dec(v_fst_3003_);
lean_del_object(v___x_3001_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
return v___x_3064_;
}
}
v___jp_3006_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3008_ = l_List_appendTR___redArg(v___x_3005_, v_fst_3003_);
v___x_3009_ = l_List_appendTR___redArg(v___x_3008_, v_a_3007_);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3009_);
v___x_3011_ = v___x_3001_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
v___jp_3013_:
{
if (lean_obj_tag(v___y_3014_) == 0)
{
lean_object* v_a_3015_; 
v_a_3015_ = lean_ctor_get(v___y_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___y_3014_, 1);
v_a_3007_ = v_a_3015_;
goto v___jp_3006_;
}
else
{
lean_dec(v___x_3005_);
lean_dec(v_fst_3003_);
lean_del_object(v___x_3001_);
return v___y_3014_;
}
}
v___jp_3016_:
{
if (v___y_3019_ == 0)
{
lean_object* v___x_3020_; 
lean_dec_ref(v___y_3018_);
v___x_3020_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3017_, v_a_2978_, v_a_2980_);
lean_dec_ref(v___y_3017_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_dec_ref_known(v___x_3020_, 1);
v_a_3007_ = v_snd_2989_;
goto v___jp_3006_;
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec(v___x_3005_);
lean_dec(v_fst_3003_);
lean_del_object(v___x_3001_);
lean_dec(v_snd_2989_);
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3020_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3020_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_dec_ref(v___y_3017_);
lean_dec(v_snd_2989_);
v___y_3014_ = v___y_3018_;
goto v___jp_3013_;
}
}
v___jp_3029_:
{
uint8_t v___x_3031_; 
v___x_3031_ = l_List_isEmpty___redArg(v_fst_3003_);
lean_dec(v_fst_3003_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec(v___y_3030_);
lean_dec(v___x_3005_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
v___x_3032_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3033_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3032_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
return v___x_3033_;
}
else
{
lean_object* v___x_3034_; 
v___x_3034_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3030_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3043_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3037_ = v___x_3034_;
v_isShared_3038_ = v_isSharedCheck_3043_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3034_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3043_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3041_; 
v___x_3039_ = l_List_appendTR___redArg(v___x_3005_, v_a_3035_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 0, v___x_3039_);
v___x_3041_ = v___x_3037_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
else
{
lean_dec(v___x_3005_);
return v___x_3034_;
}
}
}
v___jp_3044_:
{
uint8_t v_commitIndependentGoals_3046_; lean_object* v___x_3047_; 
v_commitIndependentGoals_3046_ = lean_ctor_get_uint8(v_cfg_2971_, sizeof(void*)*4);
lean_inc(v___x_3005_);
v___x_3047_ = l_List_appendTR___redArg(v_a_3045_, v___x_3005_);
if (v_commitIndependentGoals_3046_ == 0)
{
lean_del_object(v___x_3001_);
v___y_3030_ = v___x_3047_;
goto v___jp_3029_;
}
else
{
uint8_t v___x_3048_; 
v___x_3048_ = l_List_isEmpty___redArg(v___x_3005_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Lean_Meta_saveState___redArg(v_a_2978_, v_a_2980_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3051_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref_known(v___x_3049_, 1);
lean_inc(v_snd_2989_);
v___x_3051_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___x_3047_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_dec(v_a_3050_);
lean_dec(v_snd_2989_);
v___y_3014_ = v___x_3051_;
goto v___jp_3013_;
}
else
{
lean_object* v_a_3052_; uint8_t v___x_3053_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
v___x_3053_ = l_Lean_Exception_isInterrupt(v_a_3052_);
if (v___x_3053_ == 0)
{
uint8_t v___x_3054_; 
v___x_3054_ = l_Lean_Exception_isRuntime(v_a_3052_);
v___y_3017_ = v_a_3050_;
v___y_3018_ = v___x_3051_;
v___y_3019_ = v___x_3054_;
goto v___jp_3016_;
}
else
{
lean_dec(v_a_3052_);
v___y_3017_ = v_a_3050_;
v___y_3018_ = v___x_3051_;
v___y_3019_ = v___x_3053_;
goto v___jp_3016_;
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v___x_3047_);
lean_dec(v___x_3005_);
lean_dec(v_fst_3003_);
lean_del_object(v___x_3001_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
v_a_3055_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3049_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3049_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_del_object(v___x_3001_);
v___y_3030_ = v___x_3047_;
goto v___jp_3029_;
}
}
}
}
}
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v_snd_2989_);
lean_dec(v_goals_2975_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
v_a_3069_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_2998_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_2998_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
else
{
lean_object* v___f_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v_a_3085_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v_a_3102_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v_a_3109_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v_a_3115_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; uint8_t v___y_3132_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; uint8_t v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v_a_3161_; uint8_t v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v_a_3180_; uint8_t v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v_a_3189_; uint8_t v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v_a_3200_; uint8_t v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3216_; uint8_t v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; uint8_t v___y_3226_; uint8_t v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; uint8_t v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; uint8_t v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; uint8_t v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; uint8_t v___y_3275_; uint8_t v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; uint8_t v___y_3289_; lean_object* v_a_3290_; lean_object* v___y_3295_; uint8_t v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v_a_3301_; lean_object* v___y_3311_; uint8_t v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v_a_3317_; lean_object* v___y_3320_; uint8_t v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v_a_3328_; lean_object* v___y_3332_; uint8_t v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v_a_3338_; lean_object* v___y_3341_; uint8_t v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3351_; lean_object* v___y_3352_; uint8_t v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3363_; uint8_t v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3375_; uint8_t v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; uint8_t v___y_3385_; lean_object* v___y_3389_; lean_object* v___y_3390_; uint8_t v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3406_; uint8_t v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; uint8_t v___y_3414_; lean_object* v_a_3415_; uint8_t v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; uint8_t v___y_3429_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; uint8_t v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; uint8_t v___y_3466_; lean_object* v___y_3467_; lean_object* v_a_3468_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v_a_3475_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v_a_3487_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v_a_3492_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; uint8_t v___y_3505_; lean_object* v___y_3506_; lean_object* v_a_3507_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v_a_3526_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; uint8_t v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v_a_3535_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; uint8_t v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v_a_3546_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; uint8_t v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; uint8_t v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; uint8_t v___y_3572_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; uint8_t v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; uint8_t v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; uint8_t v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; uint8_t v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; uint8_t v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; uint8_t v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; uint8_t v___y_3634_; lean_object* v___y_3635_; lean_object* v_a_3636_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; uint8_t v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v_a_3647_; lean_object* v___y_3657_; lean_object* v___y_3658_; uint8_t v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v_a_3663_; lean_object* v___y_3666_; lean_object* v___y_3667_; uint8_t v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v_a_3672_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; uint8_t v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v_a_3683_; lean_object* v___y_3687_; lean_object* v___y_3688_; uint8_t v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; uint8_t v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; uint8_t v___y_3709_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; uint8_t v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; uint8_t v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; uint8_t v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; uint8_t v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; uint8_t v___y_3761_; lean_object* v___y_3766_; lean_object* v___y_3767_; uint8_t v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; uint8_t v___y_3773_; lean_object* v___y_3774_; lean_object* v_a_3775_; lean_object* v___y_3780_; lean_object* v___y_3781_; uint8_t v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; uint8_t v___y_3787_; lean_object* v___y_3805_; lean_object* v___y_3806_; uint8_t v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v_a_3825_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; uint8_t v___y_3843_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; uint8_t v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v_a_3865_; 
lean_inc(v_snd_2989_);
lean_inc(v_fst_2988_);
v___f_3077_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3077_, 0, v_fst_2988_);
lean_closure_set(v___f_3077_, 1, v_snd_2989_);
v___x_3078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_3079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_2972_);
v___x_3080_ = l_Lean_Name_append(v___x_3079_, v_trace_2972_);
v___x_3081_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2995_, v_options_2994_, v___x_3080_);
lean_dec(v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3914_; uint8_t v___x_3915_; 
v___x_3914_ = l_Lean_trace_profiler;
v___x_3915_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2994_, v___x_3914_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; 
lean_dec_ref(v___f_3077_);
lean_del_object(v___x_2991_);
v___x_3916_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2988_, v___f_2997_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_4185_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_3919_ = v___x_3916_;
v_isShared_3920_ = v_isSharedCheck_4185_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3916_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_4185_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v_fst_3921_; lean_object* v_snd_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_4184_; 
v_fst_3921_ = lean_ctor_get(v_a_3917_, 0);
v_snd_3922_ = lean_ctor_get(v_a_3917_, 1);
v_isSharedCheck_4184_ = !lean_is_exclusive(v_a_3917_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_3924_ = v_a_3917_;
v_isShared_3925_ = v_isSharedCheck_4184_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_snd_3922_);
lean_inc(v_fst_3921_);
lean_dec(v_a_3917_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_4184_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___y_3928_; lean_object* v_a_3941_; lean_object* v___y_3948_; lean_object* v___y_3951_; lean_object* v___y_3952_; uint8_t v___y_3953_; lean_object* v___y_3964_; lean_object* v_a_3980_; lean_object* v___f_3984_; lean_object* v___x_3985_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v_a_3989_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v_a_4006_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v_a_4011_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v_a_4016_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; uint8_t v___y_4030_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4051_; lean_object* v___y_4052_; uint8_t v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; uint8_t v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v_a_4068_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v_a_4075_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v_a_4087_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v_a_4092_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v_a_4098_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; uint8_t v___y_4110_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; uint8_t v___y_4120_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; uint8_t v___y_4133_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; uint8_t v___y_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v_a_4151_; 
v___x_3926_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3922_, v___x_2985_);
lean_inc(v___x_3926_);
lean_inc(v_fst_3921_);
v___f_3984_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3984_, 0, v_fst_3921_);
lean_closure_set(v___f_3984_, 1, v___x_3926_);
v___x_3985_ = lean_box(0);
if (v___x_3081_ == 0)
{
if (v___x_3915_ == 0)
{
lean_object* v___x_4180_; 
lean_dec_ref(v___f_3984_);
lean_del_object(v___x_3924_);
v___x_4180_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2996_, v___x_3915_, v_goals_2975_, v___x_3985_, v_a_2978_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v___x_4182_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v___x_4180_, 1);
v___x_4182_ = l_List_reverse___redArg(v_a_4181_);
v_a_3980_ = v___x_4182_;
goto v___jp_3979_;
}
else
{
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4183_; 
v_a_4183_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v___x_4180_, 1);
v_a_3980_ = v_a_4183_;
goto v___jp_3979_;
}
else
{
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
lean_del_object(v___x_3919_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
return v___x_4180_;
}
}
}
else
{
lean_del_object(v___x_3919_);
goto v___jp_4155_;
}
}
else
{
lean_del_object(v___x_3919_);
goto v___jp_4155_;
}
v___jp_3927_:
{
uint8_t v___x_3929_; 
v___x_3929_ = l_List_isEmpty___redArg(v_fst_3921_);
lean_dec(v_fst_3921_);
if (v___x_3929_ == 0)
{
lean_dec(v___y_3928_);
lean_dec(v___x_3926_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
goto v___jp_2982_;
}
else
{
if (v___x_3915_ == 0)
{
lean_object* v___x_3930_; 
v___x_3930_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3928_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3939_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3933_ = v___x_3930_;
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3930_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3935_ = l_List_appendTR___redArg(v___x_3926_, v_a_3931_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3935_);
v___x_3937_ = v___x_3933_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
else
{
lean_dec(v___x_3926_);
return v___x_3930_;
}
}
else
{
lean_dec(v___y_3928_);
lean_dec(v___x_3926_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
goto v___jp_2982_;
}
}
}
v___jp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3942_ = l_List_appendTR___redArg(v___x_3926_, v_fst_3921_);
v___x_3943_ = l_List_appendTR___redArg(v___x_3942_, v_a_3941_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 0, v___x_3943_);
v___x_3945_ = v___x_3919_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
v___jp_3947_:
{
if (lean_obj_tag(v___y_3948_) == 0)
{
lean_object* v_a_3949_; 
v_a_3949_ = lean_ctor_get(v___y_3948_, 0);
lean_inc(v_a_3949_);
lean_dec_ref_known(v___y_3948_, 1);
v_a_3941_ = v_a_3949_;
goto v___jp_3940_;
}
else
{
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
lean_del_object(v___x_3919_);
return v___y_3948_;
}
}
v___jp_3950_:
{
if (v___y_3953_ == 0)
{
lean_object* v___x_3954_; 
lean_dec_ref(v___y_3952_);
v___x_3954_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3951_, v_a_2978_, v_a_2980_);
lean_dec_ref(v___y_3951_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_dec_ref_known(v___x_3954_, 1);
v_a_3941_ = v_snd_2989_;
goto v___jp_3940_;
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
lean_del_object(v___x_3919_);
lean_dec(v_snd_2989_);
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3954_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3954_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_dec_ref(v___y_3951_);
lean_dec(v_snd_2989_);
v___y_3948_ = v___y_3952_;
goto v___jp_3947_;
}
}
v___jp_3963_:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Lean_Meta_saveState___redArg(v_a_2978_, v_a_2980_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3967_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
lean_inc(v_snd_2989_);
v___x_3967_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3964_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_dec(v_a_3966_);
lean_dec(v_snd_2989_);
v___y_3948_ = v___x_3967_;
goto v___jp_3947_;
}
else
{
lean_object* v_a_3968_; uint8_t v___x_3969_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_a_3968_);
v___x_3969_ = l_Lean_Exception_isInterrupt(v_a_3968_);
if (v___x_3969_ == 0)
{
uint8_t v___x_3970_; 
v___x_3970_ = l_Lean_Exception_isRuntime(v_a_3968_);
v___y_3951_ = v_a_3966_;
v___y_3952_ = v___x_3967_;
v___y_3953_ = v___x_3970_;
goto v___jp_3950_;
}
else
{
lean_dec(v_a_3968_);
v___y_3951_ = v_a_3966_;
v___y_3952_ = v___x_3967_;
v___y_3953_ = v___x_3969_;
goto v___jp_3950_;
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec(v___y_3964_);
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
lean_del_object(v___x_3919_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
v_a_3971_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3965_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3965_);
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
v___jp_3979_:
{
uint8_t v_commitIndependentGoals_3981_; lean_object* v___x_3982_; 
v_commitIndependentGoals_3981_ = lean_ctor_get_uint8(v_cfg_2971_, sizeof(void*)*4);
lean_inc(v___x_3926_);
v___x_3982_ = l_List_appendTR___redArg(v_a_3980_, v___x_3926_);
if (v_commitIndependentGoals_3981_ == 0)
{
lean_del_object(v___x_3919_);
v___y_3928_ = v___x_3982_;
goto v___jp_3927_;
}
else
{
uint8_t v___x_3983_; 
v___x_3983_ = l_List_isEmpty___redArg(v___x_3926_);
if (v___x_3983_ == 0)
{
v___y_3964_ = v___x_3982_;
goto v___jp_3963_;
}
else
{
if (v___x_3915_ == 0)
{
lean_del_object(v___x_3919_);
v___y_3928_ = v___x_3982_;
goto v___jp_3927_;
}
else
{
v___y_3964_ = v___x_3982_;
goto v___jp_3963_;
}
}
}
}
v___jp_3986_:
{
lean_object* v___x_3990_; double v___x_3991_; double v___x_3992_; double v___x_3993_; double v___x_3994_; double v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3999_; 
v___x_3990_ = lean_io_mono_nanos_now();
v___x_3991_ = lean_float_of_nat(v___y_3988_);
v___x_3992_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3993_ = lean_float_div(v___x_3991_, v___x_3992_);
v___x_3994_ = lean_float_of_nat(v___x_3990_);
v___x_3995_ = lean_float_div(v___x_3994_, v___x_3992_);
v___x_3996_ = lean_box_float(v___x_3993_);
v___x_3997_ = lean_box_float(v___x_3995_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 1, v___x_3997_);
lean_ctor_set(v___x_3924_, 0, v___x_3996_);
v___x_3999_ = v___x_3924_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3996_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4002_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4000_, 0, v_a_3989_);
lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2972_, v_hasTrace_2996_, v___x_3078_, v_options_2994_, v___x_3081_, v___y_3987_, v___f_3984_, v___x_4000_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
return v___x_4001_;
}
}
v___jp_4003_:
{
lean_object* v___x_4007_; 
v___x_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4007_, 0, v_a_4006_);
v___y_3987_ = v___y_4004_;
v___y_3988_ = v___y_4005_;
v_a_3989_ = v___x_4007_;
goto v___jp_3986_;
}
v___jp_4008_:
{
lean_object* v___x_4012_; 
v___x_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4012_, 0, v_a_4011_);
v___y_3987_ = v___y_4009_;
v___y_3988_ = v___y_4010_;
v_a_3989_ = v___x_4012_;
goto v___jp_3986_;
}
v___jp_4013_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4017_ = l_List_appendTR___redArg(v___x_3926_, v_fst_3921_);
v___x_4018_ = l_List_appendTR___redArg(v___x_4017_, v_a_4016_);
v___y_4009_ = v___y_4014_;
v___y_4010_ = v___y_4015_;
v_a_4011_ = v___x_4018_;
goto v___jp_4008_;
}
v___jp_4019_:
{
if (lean_obj_tag(v___y_4022_) == 0)
{
lean_object* v_a_4023_; 
v_a_4023_ = lean_ctor_get(v___y_4022_, 0);
lean_inc(v_a_4023_);
lean_dec_ref_known(v___y_4022_, 1);
v___y_4014_ = v___y_4020_;
v___y_4015_ = v___y_4021_;
v_a_4016_ = v_a_4023_;
goto v___jp_4013_;
}
else
{
lean_object* v_a_4024_; 
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
v_a_4024_ = lean_ctor_get(v___y_4022_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___y_4022_, 1);
v___y_4004_ = v___y_4020_;
v___y_4005_ = v___y_4021_;
v_a_4006_ = v_a_4024_;
goto v___jp_4003_;
}
}
v___jp_4025_:
{
if (v___y_4030_ == 0)
{
lean_object* v___x_4031_; 
lean_dec_ref(v___y_4026_);
v___x_4031_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4027_, v_a_2978_, v_a_2980_);
lean_dec_ref(v___y_4027_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_dec_ref_known(v___x_4031_, 1);
v___y_4014_ = v___y_4028_;
v___y_4015_ = v___y_4029_;
v_a_4016_ = v_snd_2989_;
goto v___jp_4013_;
}
else
{
lean_object* v_a_4032_; 
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
lean_dec(v_snd_2989_);
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4031_, 1);
v___y_4004_ = v___y_4028_;
v___y_4005_ = v___y_4029_;
v_a_4006_ = v_a_4032_;
goto v___jp_4003_;
}
}
else
{
lean_dec_ref(v___y_4027_);
lean_dec(v_snd_2989_);
v___y_4020_ = v___y_4028_;
v___y_4021_ = v___y_4029_;
v___y_4022_ = v___y_4026_;
goto v___jp_4019_;
}
}
v___jp_4033_:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Lean_Meta_saveState___redArg(v_a_2978_, v_a_2980_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4039_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
lean_inc(v_snd_2989_);
lean_inc(v_trace_2972_);
v___x_4039_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_4036_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_dec(v_a_4038_);
lean_dec(v_snd_2989_);
v___y_4020_ = v___y_4034_;
v___y_4021_ = v___y_4035_;
v___y_4022_ = v___x_4039_;
goto v___jp_4019_;
}
else
{
lean_object* v_a_4040_; uint8_t v___x_4041_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
v___x_4041_ = l_Lean_Exception_isInterrupt(v_a_4040_);
if (v___x_4041_ == 0)
{
uint8_t v___x_4042_; 
v___x_4042_ = l_Lean_Exception_isRuntime(v_a_4040_);
v___y_4026_ = v___x_4039_;
v___y_4027_ = v_a_4038_;
v___y_4028_ = v___y_4034_;
v___y_4029_ = v___y_4035_;
v___y_4030_ = v___x_4042_;
goto v___jp_4025_;
}
else
{
lean_dec(v_a_4040_);
v___y_4026_ = v___x_4039_;
v___y_4027_ = v_a_4038_;
v___y_4028_ = v___y_4034_;
v___y_4029_ = v___y_4035_;
v___y_4030_ = v___x_4041_;
goto v___jp_4025_;
}
}
}
else
{
lean_object* v_a_4043_; 
lean_dec(v___y_4036_);
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_4043_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4043_);
lean_dec_ref_known(v___x_4037_, 1);
v___y_4004_ = v___y_4034_;
v___y_4005_ = v___y_4035_;
v_a_4006_ = v_a_4043_;
goto v___jp_4003_;
}
}
v___jp_4044_:
{
if (lean_obj_tag(v___y_4047_) == 0)
{
lean_object* v_a_4048_; 
v_a_4048_ = lean_ctor_get(v___y_4047_, 0);
lean_inc(v_a_4048_);
lean_dec_ref_known(v___y_4047_, 1);
v___y_4009_ = v___y_4045_;
v___y_4010_ = v___y_4046_;
v_a_4011_ = v_a_4048_;
goto v___jp_4008_;
}
else
{
lean_object* v_a_4049_; 
v_a_4049_ = lean_ctor_get(v___y_4047_, 0);
lean_inc(v_a_4049_);
lean_dec_ref_known(v___y_4047_, 1);
v___y_4004_ = v___y_4045_;
v___y_4005_ = v___y_4046_;
v_a_4006_ = v_a_4049_;
goto v___jp_4003_;
}
}
v___jp_4050_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4053_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4054_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4053_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_4045_ = v___y_4051_;
v___y_4046_ = v___y_4052_;
v___y_4047_ = v___x_4054_;
goto v___jp_4044_;
}
v___jp_4055_:
{
uint8_t v___x_4060_; 
v___x_4060_ = l_List_isEmpty___redArg(v_fst_3921_);
lean_dec(v_fst_3921_);
if (v___x_4060_ == 0)
{
lean_dec(v___y_4058_);
lean_dec(v___x_3926_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___y_4051_ = v___y_4057_;
v___y_4052_ = v___y_4059_;
goto v___jp_4050_;
}
else
{
if (v___y_4056_ == 0)
{
lean_object* v___x_4061_; 
lean_inc(v_trace_2972_);
v___x_4061_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_4058_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4063_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4061_, 1);
v___x_4063_ = l_List_appendTR___redArg(v___x_3926_, v_a_4062_);
v___y_4009_ = v___y_4057_;
v___y_4010_ = v___y_4059_;
v_a_4011_ = v___x_4063_;
goto v___jp_4008_;
}
else
{
lean_dec(v___x_3926_);
v___y_4045_ = v___y_4057_;
v___y_4046_ = v___y_4059_;
v___y_4047_ = v___x_4061_;
goto v___jp_4044_;
}
}
else
{
lean_dec(v___y_4058_);
lean_dec(v___x_3926_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___y_4051_ = v___y_4057_;
v___y_4052_ = v___y_4059_;
goto v___jp_4050_;
}
}
}
v___jp_4064_:
{
uint8_t v_commitIndependentGoals_4069_; lean_object* v___x_4070_; 
v_commitIndependentGoals_4069_ = lean_ctor_get_uint8(v_cfg_2971_, sizeof(void*)*4);
lean_inc(v___x_3926_);
v___x_4070_ = l_List_appendTR___redArg(v_a_4068_, v___x_3926_);
if (v_commitIndependentGoals_4069_ == 0)
{
v___y_4056_ = v___y_4065_;
v___y_4057_ = v___y_4066_;
v___y_4058_ = v___x_4070_;
v___y_4059_ = v___y_4067_;
goto v___jp_4055_;
}
else
{
uint8_t v___x_4071_; 
v___x_4071_ = l_List_isEmpty___redArg(v___x_3926_);
if (v___x_4071_ == 0)
{
v___y_4034_ = v___y_4066_;
v___y_4035_ = v___y_4067_;
v___y_4036_ = v___x_4070_;
goto v___jp_4033_;
}
else
{
if (v___y_4065_ == 0)
{
v___y_4056_ = v___y_4065_;
v___y_4057_ = v___y_4066_;
v___y_4058_ = v___x_4070_;
v___y_4059_ = v___y_4067_;
goto v___jp_4055_;
}
else
{
v___y_4034_ = v___y_4066_;
v___y_4035_ = v___y_4067_;
v___y_4036_ = v___x_4070_;
goto v___jp_4033_;
}
}
}
}
v___jp_4072_:
{
lean_object* v___x_4076_; double v___x_4077_; double v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4076_ = lean_io_get_num_heartbeats();
v___x_4077_ = lean_float_of_nat(v___y_4074_);
v___x_4078_ = lean_float_of_nat(v___x_4076_);
v___x_4079_ = lean_box_float(v___x_4077_);
v___x_4080_ = lean_box_float(v___x_4078_);
v___x_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4079_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
v___x_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4082_, 0, v_a_4075_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2972_, v_hasTrace_2996_, v___x_3078_, v_options_2994_, v___x_3081_, v___y_4073_, v___f_3984_, v___x_4082_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
return v___x_4083_;
}
v___jp_4084_:
{
lean_object* v___x_4088_; 
v___x_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4088_, 0, v_a_4087_);
v___y_4073_ = v___y_4086_;
v___y_4074_ = v___y_4085_;
v_a_4075_ = v___x_4088_;
goto v___jp_4072_;
}
v___jp_4089_:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4093_ = l_List_appendTR___redArg(v___x_3926_, v_fst_3921_);
v___x_4094_ = l_List_appendTR___redArg(v___x_4093_, v_a_4092_);
v___y_4085_ = v___y_4091_;
v___y_4086_ = v___y_4090_;
v_a_4087_ = v___x_4094_;
goto v___jp_4084_;
}
v___jp_4095_:
{
lean_object* v___x_4099_; 
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v_a_4098_);
v___y_4073_ = v___y_4097_;
v___y_4074_ = v___y_4096_;
v_a_4075_ = v___x_4099_;
goto v___jp_4072_;
}
v___jp_4100_:
{
if (lean_obj_tag(v___y_4103_) == 0)
{
lean_object* v_a_4104_; 
v_a_4104_ = lean_ctor_get(v___y_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref_known(v___y_4103_, 1);
v___y_4085_ = v___y_4102_;
v___y_4086_ = v___y_4101_;
v_a_4087_ = v_a_4104_;
goto v___jp_4084_;
}
else
{
lean_object* v_a_4105_; 
v_a_4105_ = lean_ctor_get(v___y_4103_, 0);
lean_inc(v_a_4105_);
lean_dec_ref_known(v___y_4103_, 1);
v___y_4096_ = v___y_4102_;
v___y_4097_ = v___y_4101_;
v_a_4098_ = v_a_4105_;
goto v___jp_4095_;
}
}
v___jp_4106_:
{
if (v___y_4110_ == 0)
{
lean_object* v___x_4111_; 
lean_inc(v_trace_2972_);
v___x_4111_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_4107_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4113_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v___x_4113_ = l_List_appendTR___redArg(v___x_3926_, v_a_4112_);
v___y_4085_ = v___y_4109_;
v___y_4086_ = v___y_4108_;
v_a_4087_ = v___x_4113_;
goto v___jp_4084_;
}
else
{
lean_dec(v___x_3926_);
v___y_4101_ = v___y_4108_;
v___y_4102_ = v___y_4109_;
v___y_4103_ = v___x_4111_;
goto v___jp_4100_;
}
}
else
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
lean_dec(v___y_4107_);
lean_dec(v___x_3926_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___x_4114_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_4115_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4114_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_4101_ = v___y_4108_;
v___y_4102_ = v___y_4109_;
v___y_4103_ = v___x_4115_;
goto v___jp_4100_;
}
}
v___jp_4116_:
{
uint8_t v___x_4121_; 
v___x_4121_ = l_List_isEmpty___redArg(v_fst_3921_);
lean_dec(v_fst_3921_);
if (v___x_4121_ == 0)
{
v___y_4107_ = v___y_4117_;
v___y_4108_ = v___y_4119_;
v___y_4109_ = v___y_4118_;
v___y_4110_ = v___y_4120_;
goto v___jp_4106_;
}
else
{
v___y_4107_ = v___y_4117_;
v___y_4108_ = v___y_4119_;
v___y_4109_ = v___y_4118_;
v___y_4110_ = v___x_3915_;
goto v___jp_4106_;
}
}
v___jp_4122_:
{
if (lean_obj_tag(v___y_4125_) == 0)
{
lean_object* v_a_4126_; 
v_a_4126_ = lean_ctor_get(v___y_4125_, 0);
lean_inc(v_a_4126_);
lean_dec_ref_known(v___y_4125_, 1);
v___y_4090_ = v___y_4124_;
v___y_4091_ = v___y_4123_;
v_a_4092_ = v_a_4126_;
goto v___jp_4089_;
}
else
{
lean_object* v_a_4127_; 
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
v_a_4127_ = lean_ctor_get(v___y_4125_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___y_4125_, 1);
v___y_4096_ = v___y_4123_;
v___y_4097_ = v___y_4124_;
v_a_4098_ = v_a_4127_;
goto v___jp_4095_;
}
}
v___jp_4128_:
{
if (v___y_4133_ == 0)
{
lean_object* v___x_4134_; 
lean_dec_ref(v___y_4132_);
v___x_4134_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4129_, v_a_2978_, v_a_2980_);
lean_dec_ref(v___y_4129_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_dec_ref_known(v___x_4134_, 1);
v___y_4090_ = v___y_4131_;
v___y_4091_ = v___y_4130_;
v_a_4092_ = v_snd_2989_;
goto v___jp_4089_;
}
else
{
lean_object* v_a_4135_; 
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
lean_dec(v_snd_2989_);
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4134_, 1);
v___y_4096_ = v___y_4130_;
v___y_4097_ = v___y_4131_;
v_a_4098_ = v_a_4135_;
goto v___jp_4095_;
}
}
else
{
lean_dec_ref(v___y_4129_);
lean_dec(v_snd_2989_);
v___y_4123_ = v___y_4130_;
v___y_4124_ = v___y_4131_;
v___y_4125_ = v___y_4132_;
goto v___jp_4122_;
}
}
v___jp_4136_:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_Meta_saveState___redArg(v_a_2978_, v_a_2980_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4142_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
lean_inc(v_snd_2989_);
lean_inc(v_trace_2972_);
v___x_4142_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_4137_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_dec(v_a_4141_);
lean_dec(v_snd_2989_);
v___y_4123_ = v___y_4139_;
v___y_4124_ = v___y_4138_;
v___y_4125_ = v___x_4142_;
goto v___jp_4122_;
}
else
{
lean_object* v_a_4143_; uint8_t v___x_4144_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
v___x_4144_ = l_Lean_Exception_isInterrupt(v_a_4143_);
if (v___x_4144_ == 0)
{
uint8_t v___x_4145_; 
v___x_4145_ = l_Lean_Exception_isRuntime(v_a_4143_);
v___y_4129_ = v_a_4141_;
v___y_4130_ = v___y_4139_;
v___y_4131_ = v___y_4138_;
v___y_4132_ = v___x_4142_;
v___y_4133_ = v___x_4145_;
goto v___jp_4128_;
}
else
{
lean_dec(v_a_4143_);
v___y_4129_ = v_a_4141_;
v___y_4130_ = v___y_4139_;
v___y_4131_ = v___y_4138_;
v___y_4132_ = v___x_4142_;
v___y_4133_ = v___x_4144_;
goto v___jp_4128_;
}
}
}
else
{
lean_object* v_a_4146_; 
lean_dec(v___y_4137_);
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_4146_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4140_, 1);
v___y_4096_ = v___y_4139_;
v___y_4097_ = v___y_4138_;
v_a_4098_ = v_a_4146_;
goto v___jp_4095_;
}
}
v___jp_4147_:
{
uint8_t v_commitIndependentGoals_4152_; lean_object* v___x_4153_; 
v_commitIndependentGoals_4152_ = lean_ctor_get_uint8(v_cfg_2971_, sizeof(void*)*4);
lean_inc(v___x_3926_);
v___x_4153_ = l_List_appendTR___redArg(v_a_4151_, v___x_3926_);
if (v_commitIndependentGoals_4152_ == 0)
{
v___y_4117_ = v___x_4153_;
v___y_4118_ = v___y_4149_;
v___y_4119_ = v___y_4150_;
v___y_4120_ = v___y_4148_;
goto v___jp_4116_;
}
else
{
uint8_t v___x_4154_; 
v___x_4154_ = l_List_isEmpty___redArg(v___x_3926_);
if (v___x_4154_ == 0)
{
v___y_4137_ = v___x_4153_;
v___y_4138_ = v___y_4150_;
v___y_4139_ = v___y_4149_;
goto v___jp_4136_;
}
else
{
if (v___x_3915_ == 0)
{
v___y_4117_ = v___x_4153_;
v___y_4118_ = v___y_4149_;
v___y_4119_ = v___y_4150_;
v___y_4120_ = v___y_4148_;
goto v___jp_4116_;
}
else
{
v___y_4137_ = v___x_4153_;
v___y_4138_ = v___y_4150_;
v___y_4139_ = v___y_4149_;
goto v___jp_4136_;
}
}
}
}
v___jp_4155_:
{
lean_object* v___x_4156_; 
v___x_4156_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2980_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; lean_object* v___x_4158_; uint8_t v___x_4159_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___x_4156_, 1);
v___x_4158_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4159_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2994_, v___x_4158_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4160_ = lean_io_mono_nanos_now();
v___x_4161_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2996_, v___x_3915_, v_goals_2975_, v___x_3985_, v_a_2978_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4163_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v___x_4161_, 1);
v___x_4163_ = l_List_reverse___redArg(v_a_4162_);
v___y_4065_ = v___x_4159_;
v___y_4066_ = v_a_4157_;
v___y_4067_ = v___x_4160_;
v_a_4068_ = v___x_4163_;
goto v___jp_4064_;
}
else
{
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4164_; 
v_a_4164_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4161_, 1);
v___y_4065_ = v___x_4159_;
v___y_4066_ = v_a_4157_;
v___y_4067_ = v___x_4160_;
v_a_4068_ = v_a_4164_;
goto v___jp_4064_;
}
else
{
lean_object* v_a_4165_; 
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_4165_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4161_, 1);
v___y_4004_ = v_a_4157_;
v___y_4005_ = v___x_4160_;
v_a_4006_ = v_a_4165_;
goto v___jp_4003_;
}
}
}
else
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
lean_del_object(v___x_3924_);
v___x_4166_ = lean_io_get_num_heartbeats();
v___x_4167_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2996_, v___x_3915_, v_goals_2975_, v___x_3985_, v_a_2978_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4169_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4168_);
lean_dec_ref_known(v___x_4167_, 1);
v___x_4169_ = l_List_reverse___redArg(v_a_4168_);
v___y_4148_ = v___x_4159_;
v___y_4149_ = v___x_4166_;
v___y_4150_ = v_a_4157_;
v_a_4151_ = v___x_4169_;
goto v___jp_4147_;
}
else
{
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4170_; 
v_a_4170_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4170_);
lean_dec_ref_known(v___x_4167_, 1);
v___y_4148_ = v___x_4159_;
v___y_4149_ = v___x_4166_;
v___y_4150_ = v_a_4157_;
v_a_4151_ = v_a_4170_;
goto v___jp_4147_;
}
else
{
lean_object* v_a_4171_; 
lean_dec(v___x_3926_);
lean_dec(v_fst_3921_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_4171_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v___x_4167_, 1);
v___y_4096_ = v___x_4166_;
v___y_4097_ = v_a_4157_;
v_a_4098_ = v_a_4171_;
goto v___jp_4095_;
}
}
}
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_dec_ref(v___f_3984_);
lean_dec(v___x_3926_);
lean_del_object(v___x_3924_);
lean_dec(v_fst_3921_);
lean_dec(v_snd_2989_);
lean_dec(v_goals_2975_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
v_a_4172_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4156_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4156_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_dec(v_snd_2989_);
lean_dec(v_goals_2975_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
v_a_4186_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_3916_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_3916_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
else
{
goto v___jp_3869_;
}
}
else
{
goto v___jp_3869_;
}
v___jp_3082_:
{
lean_object* v___x_3086_; double v___x_3087_; double v___x_3088_; double v___x_3089_; double v___x_3090_; double v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3086_ = lean_io_mono_nanos_now();
v___x_3087_ = lean_float_of_nat(v___y_3084_);
v___x_3088_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3089_ = lean_float_div(v___x_3087_, v___x_3088_);
v___x_3090_ = lean_float_of_nat(v___x_3086_);
v___x_3091_ = lean_float_div(v___x_3090_, v___x_3088_);
v___x_3092_ = lean_box_float(v___x_3089_);
v___x_3093_ = lean_box_float(v___x_3091_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v___x_3093_);
lean_ctor_set(v___x_2991_, 0, v___x_3092_);
v___x_3095_ = v___x_2991_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3092_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3096_, 0, v_a_3085_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2972_, v_hasTrace_2996_, v___x_3078_, v_options_2994_, v___x_3081_, v___y_3083_, v___f_3077_, v___x_3096_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
return v___x_3097_;
}
}
v___jp_3099_:
{
lean_object* v___x_3103_; 
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v_a_3102_);
v___y_3083_ = v___y_3100_;
v___y_3084_ = v___y_3101_;
v_a_3085_ = v___x_3103_;
goto v___jp_3082_;
}
v___jp_3104_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = l_List_appendTR___redArg(v___y_3106_, v___y_3108_);
v___x_3111_ = l_List_appendTR___redArg(v___x_3110_, v_a_3109_);
v___y_3100_ = v___y_3105_;
v___y_3101_ = v___y_3107_;
v_a_3102_ = v___x_3111_;
goto v___jp_3099_;
}
v___jp_3112_:
{
lean_object* v___x_3116_; 
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v_a_3115_);
v___y_3083_ = v___y_3113_;
v___y_3084_ = v___y_3114_;
v_a_3085_ = v___x_3116_;
goto v___jp_3082_;
}
v___jp_3117_:
{
if (lean_obj_tag(v___y_3122_) == 0)
{
lean_object* v_a_3123_; 
v_a_3123_ = lean_ctor_get(v___y_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref_known(v___y_3122_, 1);
v___y_3105_ = v___y_3118_;
v___y_3106_ = v___y_3119_;
v___y_3107_ = v___y_3120_;
v___y_3108_ = v___y_3121_;
v_a_3109_ = v_a_3123_;
goto v___jp_3104_;
}
else
{
lean_object* v_a_3124_; 
lean_dec(v___y_3121_);
lean_dec(v___y_3119_);
v_a_3124_ = lean_ctor_get(v___y_3122_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___y_3122_, 1);
v___y_3113_ = v___y_3118_;
v___y_3114_ = v___y_3120_;
v_a_3115_ = v_a_3124_;
goto v___jp_3112_;
}
}
v___jp_3125_:
{
if (v___y_3132_ == 0)
{
lean_object* v___x_3133_; 
lean_dec_ref(v___y_3126_);
v___x_3133_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3128_, v_a_2978_, v_a_2980_);
lean_dec_ref(v___y_3128_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_dec_ref_known(v___x_3133_, 1);
v___y_3105_ = v___y_3127_;
v___y_3106_ = v___y_3129_;
v___y_3107_ = v___y_3130_;
v___y_3108_ = v___y_3131_;
v_a_3109_ = v_snd_2989_;
goto v___jp_3104_;
}
else
{
lean_object* v_a_3134_; 
lean_dec(v___y_3131_);
lean_dec(v___y_3129_);
lean_dec(v_snd_2989_);
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3134_);
lean_dec_ref_known(v___x_3133_, 1);
v___y_3113_ = v___y_3127_;
v___y_3114_ = v___y_3130_;
v_a_3115_ = v_a_3134_;
goto v___jp_3112_;
}
}
else
{
lean_dec_ref(v___y_3128_);
lean_dec(v_snd_2989_);
v___y_3118_ = v___y_3127_;
v___y_3119_ = v___y_3129_;
v___y_3120_ = v___y_3130_;
v___y_3121_ = v___y_3131_;
v___y_3122_ = v___y_3126_;
goto v___jp_3117_;
}
}
v___jp_3135_:
{
lean_object* v___x_3141_; 
v___x_3141_ = l_Lean_Meta_saveState___redArg(v_a_2978_, v_a_2980_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3143_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref_known(v___x_3141_, 1);
lean_inc(v_snd_2989_);
lean_inc(v_trace_2972_);
v___x_3143_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3137_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_dec(v_a_3142_);
lean_dec(v_snd_2989_);
v___y_3118_ = v___y_3136_;
v___y_3119_ = v___y_3138_;
v___y_3120_ = v___y_3139_;
v___y_3121_ = v___y_3140_;
v___y_3122_ = v___x_3143_;
goto v___jp_3117_;
}
else
{
lean_object* v_a_3144_; uint8_t v___x_3145_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
v___x_3145_ = l_Lean_Exception_isInterrupt(v_a_3144_);
if (v___x_3145_ == 0)
{
uint8_t v___x_3146_; 
v___x_3146_ = l_Lean_Exception_isRuntime(v_a_3144_);
v___y_3126_ = v___x_3143_;
v___y_3127_ = v___y_3136_;
v___y_3128_ = v_a_3142_;
v___y_3129_ = v___y_3138_;
v___y_3130_ = v___y_3139_;
v___y_3131_ = v___y_3140_;
v___y_3132_ = v___x_3146_;
goto v___jp_3125_;
}
else
{
lean_dec(v_a_3144_);
v___y_3126_ = v___x_3143_;
v___y_3127_ = v___y_3136_;
v___y_3128_ = v_a_3142_;
v___y_3129_ = v___y_3138_;
v___y_3130_ = v___y_3139_;
v___y_3131_ = v___y_3140_;
v___y_3132_ = v___x_3145_;
goto v___jp_3125_;
}
}
}
else
{
lean_object* v_a_3147_; 
lean_dec(v___y_3140_);
lean_dec(v___y_3138_);
lean_dec(v___y_3137_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3147_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3141_, 1);
v___y_3113_ = v___y_3136_;
v___y_3114_ = v___y_3139_;
v_a_3115_ = v_a_3147_;
goto v___jp_3112_;
}
}
v___jp_3148_:
{
if (lean_obj_tag(v___y_3151_) == 0)
{
lean_object* v_a_3152_; 
v_a_3152_ = lean_ctor_get(v___y_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___y_3151_, 1);
v___y_3100_ = v___y_3149_;
v___y_3101_ = v___y_3150_;
v_a_3102_ = v_a_3152_;
goto v___jp_3099_;
}
else
{
lean_object* v_a_3153_; 
v_a_3153_ = lean_ctor_get(v___y_3151_, 0);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___y_3151_, 1);
v___y_3113_ = v___y_3149_;
v___y_3114_ = v___y_3150_;
v_a_3115_ = v_a_3153_;
goto v___jp_3112_;
}
}
v___jp_3154_:
{
lean_object* v___x_3162_; double v___x_3163_; double v___x_3164_; double v___x_3165_; double v___x_3166_; double v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3162_ = lean_io_mono_nanos_now();
v___x_3163_ = lean_float_of_nat(v___y_3158_);
v___x_3164_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3165_ = lean_float_div(v___x_3163_, v___x_3164_);
v___x_3166_ = lean_float_of_nat(v___x_3162_);
v___x_3167_ = lean_float_div(v___x_3166_, v___x_3164_);
v___x_3168_ = lean_box_float(v___x_3165_);
v___x_3169_ = lean_box_float(v___x_3167_);
v___x_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v_a_3161_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
lean_inc(v_trace_2972_);
v___x_3172_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2972_, v_hasTrace_2996_, v___x_3078_, v_options_2994_, v___y_3155_, v___y_3160_, v___y_3159_, v___x_3171_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_3149_ = v___y_3156_;
v___y_3150_ = v___y_3157_;
v___y_3151_ = v___x_3172_;
goto v___jp_3148_;
}
v___jp_3173_:
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_a_3180_);
v___y_3155_ = v___y_3174_;
v___y_3156_ = v___y_3175_;
v___y_3157_ = v___y_3177_;
v___y_3158_ = v___y_3176_;
v___y_3159_ = v___y_3178_;
v___y_3160_ = v___y_3179_;
v_a_3161_ = v___x_3181_;
goto v___jp_3154_;
}
v___jp_3182_:
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3190_, 0, v_a_3189_);
v___y_3155_ = v___y_3183_;
v___y_3156_ = v___y_3184_;
v___y_3157_ = v___y_3186_;
v___y_3158_ = v___y_3185_;
v___y_3159_ = v___y_3187_;
v___y_3160_ = v___y_3188_;
v_a_3161_ = v___x_3190_;
goto v___jp_3154_;
}
v___jp_3191_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = l_List_appendTR___redArg(v___y_3194_, v___y_3198_);
v___x_3202_ = l_List_appendTR___redArg(v___x_3201_, v_a_3200_);
v___y_3183_ = v___y_3192_;
v___y_3184_ = v___y_3193_;
v___y_3185_ = v___y_3196_;
v___y_3186_ = v___y_3195_;
v___y_3187_ = v___y_3197_;
v___y_3188_ = v___y_3199_;
v_a_3189_ = v___x_3202_;
goto v___jp_3182_;
}
v___jp_3203_:
{
if (lean_obj_tag(v___y_3212_) == 0)
{
lean_object* v_a_3213_; 
v_a_3213_ = lean_ctor_get(v___y_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref_known(v___y_3212_, 1);
v___y_3192_ = v___y_3204_;
v___y_3193_ = v___y_3205_;
v___y_3194_ = v___y_3206_;
v___y_3195_ = v___y_3208_;
v___y_3196_ = v___y_3207_;
v___y_3197_ = v___y_3209_;
v___y_3198_ = v___y_3210_;
v___y_3199_ = v___y_3211_;
v_a_3200_ = v_a_3213_;
goto v___jp_3191_;
}
else
{
lean_object* v_a_3214_; 
lean_dec(v___y_3210_);
lean_dec(v___y_3206_);
v_a_3214_ = lean_ctor_get(v___y_3212_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___y_3212_, 1);
v___y_3174_ = v___y_3204_;
v___y_3175_ = v___y_3205_;
v___y_3176_ = v___y_3207_;
v___y_3177_ = v___y_3208_;
v___y_3178_ = v___y_3209_;
v___y_3179_ = v___y_3211_;
v_a_3180_ = v_a_3214_;
goto v___jp_3173_;
}
}
v___jp_3215_:
{
if (v___y_3226_ == 0)
{
lean_object* v___x_3227_; 
lean_dec_ref(v___y_3216_);
v___x_3227_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3225_, v_a_2978_, v_a_2980_);
lean_dec_ref(v___y_3225_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_dec_ref_known(v___x_3227_, 1);
v___y_3192_ = v___y_3217_;
v___y_3193_ = v___y_3218_;
v___y_3194_ = v___y_3219_;
v___y_3195_ = v___y_3221_;
v___y_3196_ = v___y_3220_;
v___y_3197_ = v___y_3222_;
v___y_3198_ = v___y_3223_;
v___y_3199_ = v___y_3224_;
v_a_3200_ = v_snd_2989_;
goto v___jp_3191_;
}
else
{
lean_object* v_a_3228_; 
lean_dec(v___y_3223_);
lean_dec(v___y_3219_);
lean_dec(v_snd_2989_);
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___x_3227_, 1);
v___y_3174_ = v___y_3217_;
v___y_3175_ = v___y_3218_;
v___y_3176_ = v___y_3220_;
v___y_3177_ = v___y_3221_;
v___y_3178_ = v___y_3222_;
v___y_3179_ = v___y_3224_;
v_a_3180_ = v_a_3228_;
goto v___jp_3173_;
}
}
else
{
lean_dec_ref(v___y_3225_);
lean_dec(v_snd_2989_);
v___y_3204_ = v___y_3217_;
v___y_3205_ = v___y_3218_;
v___y_3206_ = v___y_3219_;
v___y_3207_ = v___y_3220_;
v___y_3208_ = v___y_3221_;
v___y_3209_ = v___y_3222_;
v___y_3210_ = v___y_3223_;
v___y_3211_ = v___y_3224_;
v___y_3212_ = v___y_3216_;
goto v___jp_3203_;
}
}
v___jp_3229_:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_Meta_saveState___redArg(v_a_2978_, v_a_2980_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3241_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___x_3239_, 1);
lean_inc(v_snd_2989_);
lean_inc(v_trace_2972_);
v___x_3241_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3236_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_dec(v_a_3240_);
lean_dec(v_snd_2989_);
v___y_3204_ = v___y_3230_;
v___y_3205_ = v___y_3231_;
v___y_3206_ = v___y_3232_;
v___y_3207_ = v___y_3234_;
v___y_3208_ = v___y_3233_;
v___y_3209_ = v___y_3235_;
v___y_3210_ = v___y_3237_;
v___y_3211_ = v___y_3238_;
v___y_3212_ = v___x_3241_;
goto v___jp_3203_;
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
v___y_3216_ = v___x_3241_;
v___y_3217_ = v___y_3230_;
v___y_3218_ = v___y_3231_;
v___y_3219_ = v___y_3232_;
v___y_3220_ = v___y_3234_;
v___y_3221_ = v___y_3233_;
v___y_3222_ = v___y_3235_;
v___y_3223_ = v___y_3237_;
v___y_3224_ = v___y_3238_;
v___y_3225_ = v_a_3240_;
v___y_3226_ = v___x_3244_;
goto v___jp_3215_;
}
else
{
lean_dec(v_a_3242_);
v___y_3216_ = v___x_3241_;
v___y_3217_ = v___y_3230_;
v___y_3218_ = v___y_3231_;
v___y_3219_ = v___y_3232_;
v___y_3220_ = v___y_3234_;
v___y_3221_ = v___y_3233_;
v___y_3222_ = v___y_3235_;
v___y_3223_ = v___y_3237_;
v___y_3224_ = v___y_3238_;
v___y_3225_ = v_a_3240_;
v___y_3226_ = v___x_3243_;
goto v___jp_3215_;
}
}
}
else
{
lean_object* v_a_3245_; 
lean_dec(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec(v___y_3232_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3245_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3245_);
lean_dec_ref_known(v___x_3239_, 1);
v___y_3174_ = v___y_3230_;
v___y_3175_ = v___y_3231_;
v___y_3176_ = v___y_3234_;
v___y_3177_ = v___y_3233_;
v___y_3178_ = v___y_3235_;
v___y_3179_ = v___y_3238_;
v_a_3180_ = v_a_3245_;
goto v___jp_3173_;
}
}
v___jp_3246_:
{
if (lean_obj_tag(v___y_3253_) == 0)
{
lean_object* v_a_3254_; 
v_a_3254_ = lean_ctor_get(v___y_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref_known(v___y_3253_, 1);
v___y_3183_ = v___y_3247_;
v___y_3184_ = v___y_3248_;
v___y_3185_ = v___y_3250_;
v___y_3186_ = v___y_3249_;
v___y_3187_ = v___y_3251_;
v___y_3188_ = v___y_3252_;
v_a_3189_ = v_a_3254_;
goto v___jp_3182_;
}
else
{
lean_object* v_a_3255_; 
v_a_3255_ = lean_ctor_get(v___y_3253_, 0);
lean_inc(v_a_3255_);
lean_dec_ref_known(v___y_3253_, 1);
v___y_3174_ = v___y_3247_;
v___y_3175_ = v___y_3248_;
v___y_3176_ = v___y_3250_;
v___y_3177_ = v___y_3249_;
v___y_3178_ = v___y_3251_;
v___y_3179_ = v___y_3252_;
v_a_3180_ = v_a_3255_;
goto v___jp_3173_;
}
}
v___jp_3256_:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3264_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3263_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_3247_ = v___y_3257_;
v___y_3248_ = v___y_3258_;
v___y_3249_ = v___y_3260_;
v___y_3250_ = v___y_3259_;
v___y_3251_ = v___y_3261_;
v___y_3252_ = v___y_3262_;
v___y_3253_ = v___x_3264_;
goto v___jp_3246_;
}
v___jp_3265_:
{
uint8_t v___x_3276_; 
v___x_3276_ = l_List_isEmpty___redArg(v___y_3273_);
lean_dec(v___y_3273_);
if (v___x_3276_ == 0)
{
lean_dec(v___y_3272_);
lean_dec(v___y_3268_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___y_3257_ = v___y_3266_;
v___y_3258_ = v___y_3267_;
v___y_3259_ = v___y_3270_;
v___y_3260_ = v___y_3269_;
v___y_3261_ = v___y_3271_;
v___y_3262_ = v___y_3274_;
goto v___jp_3256_;
}
else
{
if (v___y_3275_ == 0)
{
lean_object* v___x_3277_; 
lean_inc(v_trace_2972_);
v___x_3277_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3272_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3279_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3279_ = l_List_appendTR___redArg(v___y_3268_, v_a_3278_);
v___y_3183_ = v___y_3266_;
v___y_3184_ = v___y_3267_;
v___y_3185_ = v___y_3270_;
v___y_3186_ = v___y_3269_;
v___y_3187_ = v___y_3271_;
v___y_3188_ = v___y_3274_;
v_a_3189_ = v___x_3279_;
goto v___jp_3182_;
}
else
{
lean_dec(v___y_3268_);
v___y_3247_ = v___y_3266_;
v___y_3248_ = v___y_3267_;
v___y_3249_ = v___y_3269_;
v___y_3250_ = v___y_3270_;
v___y_3251_ = v___y_3271_;
v___y_3252_ = v___y_3274_;
v___y_3253_ = v___x_3277_;
goto v___jp_3246_;
}
}
else
{
lean_dec(v___y_3272_);
lean_dec(v___y_3268_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___y_3257_ = v___y_3266_;
v___y_3258_ = v___y_3267_;
v___y_3259_ = v___y_3270_;
v___y_3260_ = v___y_3269_;
v___y_3261_ = v___y_3271_;
v___y_3262_ = v___y_3274_;
goto v___jp_3256_;
}
}
}
v___jp_3280_:
{
uint8_t v_commitIndependentGoals_3291_; lean_object* v___x_3292_; 
v_commitIndependentGoals_3291_ = lean_ctor_get_uint8(v_cfg_2971_, sizeof(void*)*4);
lean_inc(v___y_3283_);
v___x_3292_ = l_List_appendTR___redArg(v_a_3290_, v___y_3283_);
if (v_commitIndependentGoals_3291_ == 0)
{
v___y_3266_ = v___y_3281_;
v___y_3267_ = v___y_3282_;
v___y_3268_ = v___y_3283_;
v___y_3269_ = v___y_3284_;
v___y_3270_ = v___y_3285_;
v___y_3271_ = v___y_3286_;
v___y_3272_ = v___x_3292_;
v___y_3273_ = v___y_3287_;
v___y_3274_ = v___y_3288_;
v___y_3275_ = v___y_3289_;
goto v___jp_3265_;
}
else
{
uint8_t v___x_3293_; 
v___x_3293_ = l_List_isEmpty___redArg(v___y_3283_);
if (v___x_3293_ == 0)
{
v___y_3230_ = v___y_3281_;
v___y_3231_ = v___y_3282_;
v___y_3232_ = v___y_3283_;
v___y_3233_ = v___y_3284_;
v___y_3234_ = v___y_3285_;
v___y_3235_ = v___y_3286_;
v___y_3236_ = v___x_3292_;
v___y_3237_ = v___y_3287_;
v___y_3238_ = v___y_3288_;
goto v___jp_3229_;
}
else
{
if (v___y_3289_ == 0)
{
v___y_3266_ = v___y_3281_;
v___y_3267_ = v___y_3282_;
v___y_3268_ = v___y_3283_;
v___y_3269_ = v___y_3284_;
v___y_3270_ = v___y_3285_;
v___y_3271_ = v___y_3286_;
v___y_3272_ = v___x_3292_;
v___y_3273_ = v___y_3287_;
v___y_3274_ = v___y_3288_;
v___y_3275_ = v___y_3289_;
goto v___jp_3265_;
}
else
{
v___y_3230_ = v___y_3281_;
v___y_3231_ = v___y_3282_;
v___y_3232_ = v___y_3283_;
v___y_3233_ = v___y_3284_;
v___y_3234_ = v___y_3285_;
v___y_3235_ = v___y_3286_;
v___y_3236_ = v___x_3292_;
v___y_3237_ = v___y_3287_;
v___y_3238_ = v___y_3288_;
goto v___jp_3229_;
}
}
}
}
v___jp_3294_:
{
lean_object* v___x_3302_; double v___x_3303_; double v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3302_ = lean_io_get_num_heartbeats();
v___x_3303_ = lean_float_of_nat(v___y_3295_);
v___x_3304_ = lean_float_of_nat(v___x_3302_);
v___x_3305_ = lean_box_float(v___x_3303_);
v___x_3306_ = lean_box_float(v___x_3304_);
v___x_3307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3308_, 0, v_a_3301_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
lean_inc(v_trace_2972_);
v___x_3309_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2972_, v_hasTrace_2996_, v___x_3078_, v_options_2994_, v___y_3296_, v___y_3300_, v___y_3299_, v___x_3308_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_3149_ = v___y_3297_;
v___y_3150_ = v___y_3298_;
v___y_3151_ = v___x_3309_;
goto v___jp_3148_;
}
v___jp_3310_:
{
lean_object* v___x_3318_; 
v___x_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3318_, 0, v_a_3317_);
v___y_3295_ = v___y_3311_;
v___y_3296_ = v___y_3312_;
v___y_3297_ = v___y_3313_;
v___y_3298_ = v___y_3314_;
v___y_3299_ = v___y_3315_;
v___y_3300_ = v___y_3316_;
v_a_3301_ = v___x_3318_;
goto v___jp_3294_;
}
v___jp_3319_:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = l_List_appendTR___redArg(v___y_3323_, v___y_3326_);
v___x_3330_ = l_List_appendTR___redArg(v___x_3329_, v_a_3328_);
v___y_3311_ = v___y_3320_;
v___y_3312_ = v___y_3321_;
v___y_3313_ = v___y_3322_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3325_;
v___y_3316_ = v___y_3327_;
v_a_3317_ = v___x_3330_;
goto v___jp_3310_;
}
v___jp_3331_:
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3339_, 0, v_a_3338_);
v___y_3295_ = v___y_3332_;
v___y_3296_ = v___y_3333_;
v___y_3297_ = v___y_3334_;
v___y_3298_ = v___y_3335_;
v___y_3299_ = v___y_3336_;
v___y_3300_ = v___y_3337_;
v_a_3301_ = v___x_3339_;
goto v___jp_3294_;
}
v___jp_3340_:
{
if (lean_obj_tag(v___y_3347_) == 0)
{
lean_object* v_a_3348_; 
v_a_3348_ = lean_ctor_get(v___y_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___y_3347_, 1);
v___y_3311_ = v___y_3341_;
v___y_3312_ = v___y_3342_;
v___y_3313_ = v___y_3343_;
v___y_3314_ = v___y_3344_;
v___y_3315_ = v___y_3345_;
v___y_3316_ = v___y_3346_;
v_a_3317_ = v_a_3348_;
goto v___jp_3310_;
}
else
{
lean_object* v_a_3349_; 
v_a_3349_ = lean_ctor_get(v___y_3347_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___y_3347_, 1);
v___y_3332_ = v___y_3341_;
v___y_3333_ = v___y_3342_;
v___y_3334_ = v___y_3343_;
v___y_3335_ = v___y_3344_;
v___y_3336_ = v___y_3345_;
v___y_3337_ = v___y_3346_;
v_a_3338_ = v_a_3349_;
goto v___jp_3331_;
}
}
v___jp_3350_:
{
lean_object* v___x_3359_; 
lean_inc(v_trace_2972_);
v___x_3359_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3352_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3361_ = l_List_appendTR___redArg(v___y_3355_, v_a_3360_);
v___y_3311_ = v___y_3351_;
v___y_3312_ = v___y_3353_;
v___y_3313_ = v___y_3354_;
v___y_3314_ = v___y_3356_;
v___y_3315_ = v___y_3357_;
v___y_3316_ = v___y_3358_;
v_a_3317_ = v___x_3361_;
goto v___jp_3310_;
}
else
{
lean_dec(v___y_3355_);
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3353_;
v___y_3343_ = v___y_3354_;
v___y_3344_ = v___y_3356_;
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___y_3358_;
v___y_3347_ = v___x_3359_;
goto v___jp_3340_;
}
}
v___jp_3362_:
{
if (lean_obj_tag(v___y_3371_) == 0)
{
lean_object* v_a_3372_; 
v_a_3372_ = lean_ctor_get(v___y_3371_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v___y_3371_, 1);
v___y_3320_ = v___y_3363_;
v___y_3321_ = v___y_3364_;
v___y_3322_ = v___y_3365_;
v___y_3323_ = v___y_3366_;
v___y_3324_ = v___y_3367_;
v___y_3325_ = v___y_3368_;
v___y_3326_ = v___y_3369_;
v___y_3327_ = v___y_3370_;
v_a_3328_ = v_a_3372_;
goto v___jp_3319_;
}
else
{
lean_object* v_a_3373_; 
lean_dec(v___y_3369_);
lean_dec(v___y_3366_);
v_a_3373_ = lean_ctor_get(v___y_3371_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___y_3371_, 1);
v___y_3332_ = v___y_3363_;
v___y_3333_ = v___y_3364_;
v___y_3334_ = v___y_3365_;
v___y_3335_ = v___y_3367_;
v___y_3336_ = v___y_3368_;
v___y_3337_ = v___y_3370_;
v_a_3338_ = v_a_3373_;
goto v___jp_3331_;
}
}
v___jp_3374_:
{
if (v___y_3385_ == 0)
{
lean_object* v___x_3386_; 
lean_dec_ref(v___y_3380_);
v___x_3386_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3383_, v_a_2978_, v_a_2980_);
lean_dec_ref(v___y_3383_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_dec_ref_known(v___x_3386_, 1);
v___y_3320_ = v___y_3375_;
v___y_3321_ = v___y_3376_;
v___y_3322_ = v___y_3377_;
v___y_3323_ = v___y_3378_;
v___y_3324_ = v___y_3379_;
v___y_3325_ = v___y_3381_;
v___y_3326_ = v___y_3382_;
v___y_3327_ = v___y_3384_;
v_a_3328_ = v_snd_2989_;
goto v___jp_3319_;
}
else
{
lean_object* v_a_3387_; 
lean_dec(v___y_3382_);
lean_dec(v___y_3378_);
lean_dec(v_snd_2989_);
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___y_3332_ = v___y_3375_;
v___y_3333_ = v___y_3376_;
v___y_3334_ = v___y_3377_;
v___y_3335_ = v___y_3379_;
v___y_3336_ = v___y_3381_;
v___y_3337_ = v___y_3384_;
v_a_3338_ = v_a_3387_;
goto v___jp_3331_;
}
}
else
{
lean_dec_ref(v___y_3383_);
lean_dec(v_snd_2989_);
v___y_3363_ = v___y_3375_;
v___y_3364_ = v___y_3376_;
v___y_3365_ = v___y_3377_;
v___y_3366_ = v___y_3378_;
v___y_3367_ = v___y_3379_;
v___y_3368_ = v___y_3381_;
v___y_3369_ = v___y_3382_;
v___y_3370_ = v___y_3384_;
v___y_3371_ = v___y_3380_;
goto v___jp_3362_;
}
}
v___jp_3388_:
{
lean_object* v___x_3398_; 
v___x_3398_ = l_Lean_Meta_saveState___redArg(v_a_2978_, v_a_2980_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3398_, 1);
lean_inc(v_snd_2989_);
lean_inc(v_trace_2972_);
v___x_3400_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3390_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_dec(v_a_3399_);
lean_dec(v_snd_2989_);
v___y_3363_ = v___y_3389_;
v___y_3364_ = v___y_3391_;
v___y_3365_ = v___y_3392_;
v___y_3366_ = v___y_3393_;
v___y_3367_ = v___y_3394_;
v___y_3368_ = v___y_3395_;
v___y_3369_ = v___y_3396_;
v___y_3370_ = v___y_3397_;
v___y_3371_ = v___x_3400_;
goto v___jp_3362_;
}
else
{
lean_object* v_a_3401_; uint8_t v___x_3402_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
v___x_3402_ = l_Lean_Exception_isInterrupt(v_a_3401_);
if (v___x_3402_ == 0)
{
uint8_t v___x_3403_; 
v___x_3403_ = l_Lean_Exception_isRuntime(v_a_3401_);
v___y_3375_ = v___y_3389_;
v___y_3376_ = v___y_3391_;
v___y_3377_ = v___y_3392_;
v___y_3378_ = v___y_3393_;
v___y_3379_ = v___y_3394_;
v___y_3380_ = v___x_3400_;
v___y_3381_ = v___y_3395_;
v___y_3382_ = v___y_3396_;
v___y_3383_ = v_a_3399_;
v___y_3384_ = v___y_3397_;
v___y_3385_ = v___x_3403_;
goto v___jp_3374_;
}
else
{
lean_dec(v_a_3401_);
v___y_3375_ = v___y_3389_;
v___y_3376_ = v___y_3391_;
v___y_3377_ = v___y_3392_;
v___y_3378_ = v___y_3393_;
v___y_3379_ = v___y_3394_;
v___y_3380_ = v___x_3400_;
v___y_3381_ = v___y_3395_;
v___y_3382_ = v___y_3396_;
v___y_3383_ = v_a_3399_;
v___y_3384_ = v___y_3397_;
v___y_3385_ = v___x_3402_;
goto v___jp_3374_;
}
}
}
else
{
lean_object* v_a_3404_; 
lean_dec(v___y_3396_);
lean_dec(v___y_3393_);
lean_dec(v___y_3390_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3404_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___x_3398_, 1);
v___y_3332_ = v___y_3389_;
v___y_3333_ = v___y_3391_;
v___y_3334_ = v___y_3392_;
v___y_3335_ = v___y_3394_;
v___y_3336_ = v___y_3395_;
v___y_3337_ = v___y_3397_;
v_a_3338_ = v_a_3404_;
goto v___jp_3331_;
}
}
v___jp_3405_:
{
uint8_t v_commitIndependentGoals_3416_; lean_object* v___x_3417_; 
v_commitIndependentGoals_3416_ = lean_ctor_get_uint8(v_cfg_2971_, sizeof(void*)*4);
lean_inc(v___y_3409_);
v___x_3417_ = l_List_appendTR___redArg(v_a_3415_, v___y_3409_);
if (v_commitIndependentGoals_3416_ == 0)
{
lean_dec(v___y_3412_);
if (v___y_3414_ == 0)
{
v___y_3351_ = v___y_3406_;
v___y_3352_ = v___x_3417_;
v___y_3353_ = v___y_3407_;
v___y_3354_ = v___y_3408_;
v___y_3355_ = v___y_3409_;
v___y_3356_ = v___y_3410_;
v___y_3357_ = v___y_3411_;
v___y_3358_ = v___y_3413_;
goto v___jp_3350_;
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec(v___x_3417_);
lean_dec(v___y_3409_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___x_3418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3419_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3418_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_3341_ = v___y_3406_;
v___y_3342_ = v___y_3407_;
v___y_3343_ = v___y_3408_;
v___y_3344_ = v___y_3410_;
v___y_3345_ = v___y_3411_;
v___y_3346_ = v___y_3413_;
v___y_3347_ = v___x_3419_;
goto v___jp_3340_;
}
}
else
{
uint8_t v___x_3420_; 
v___x_3420_ = l_List_isEmpty___redArg(v___y_3409_);
if (v___x_3420_ == 0)
{
v___y_3389_ = v___y_3406_;
v___y_3390_ = v___x_3417_;
v___y_3391_ = v___y_3407_;
v___y_3392_ = v___y_3408_;
v___y_3393_ = v___y_3409_;
v___y_3394_ = v___y_3410_;
v___y_3395_ = v___y_3411_;
v___y_3396_ = v___y_3412_;
v___y_3397_ = v___y_3413_;
goto v___jp_3388_;
}
else
{
if (v___y_3414_ == 0)
{
lean_dec(v___y_3412_);
v___y_3351_ = v___y_3406_;
v___y_3352_ = v___x_3417_;
v___y_3353_ = v___y_3407_;
v___y_3354_ = v___y_3408_;
v___y_3355_ = v___y_3409_;
v___y_3356_ = v___y_3410_;
v___y_3357_ = v___y_3411_;
v___y_3358_ = v___y_3413_;
goto v___jp_3350_;
}
else
{
v___y_3389_ = v___y_3406_;
v___y_3390_ = v___x_3417_;
v___y_3391_ = v___y_3407_;
v___y_3392_ = v___y_3408_;
v___y_3393_ = v___y_3409_;
v___y_3394_ = v___y_3410_;
v___y_3395_ = v___y_3411_;
v___y_3396_ = v___y_3412_;
v___y_3397_ = v___y_3413_;
goto v___jp_3388_;
}
}
}
}
v___jp_3421_:
{
lean_object* v___x_3430_; 
v___x_3430_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2980_);
if (lean_obj_tag(v___x_3430_) == 0)
{
if (v___y_3429_ == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3432_ = lean_io_mono_nanos_now();
v___x_3433_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2996_, v___y_3429_, v_goals_2975_, v___y_3426_, v_a_2978_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3435_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3433_, 1);
v___x_3435_ = l_List_reverse___redArg(v_a_3434_);
v___y_3281_ = v___y_3422_;
v___y_3282_ = v___y_3423_;
v___y_3283_ = v___y_3424_;
v___y_3284_ = v___y_3425_;
v___y_3285_ = v___x_3432_;
v___y_3286_ = v___y_3427_;
v___y_3287_ = v___y_3428_;
v___y_3288_ = v_a_3431_;
v___y_3289_ = v___y_3429_;
v_a_3290_ = v___x_3435_;
goto v___jp_3280_;
}
else
{
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3436_; 
v_a_3436_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3436_);
lean_dec_ref_known(v___x_3433_, 1);
v___y_3281_ = v___y_3422_;
v___y_3282_ = v___y_3423_;
v___y_3283_ = v___y_3424_;
v___y_3284_ = v___y_3425_;
v___y_3285_ = v___x_3432_;
v___y_3286_ = v___y_3427_;
v___y_3287_ = v___y_3428_;
v___y_3288_ = v_a_3431_;
v___y_3289_ = v___y_3429_;
v_a_3290_ = v_a_3436_;
goto v___jp_3280_;
}
else
{
lean_object* v_a_3437_; 
lean_dec(v___y_3428_);
lean_dec(v___y_3424_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3437_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3433_, 1);
v___y_3174_ = v___y_3422_;
v___y_3175_ = v___y_3423_;
v___y_3176_ = v___x_3432_;
v___y_3177_ = v___y_3425_;
v___y_3178_ = v___y_3427_;
v___y_3179_ = v_a_3431_;
v_a_3180_ = v_a_3437_;
goto v___jp_3173_;
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v_a_3438_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3439_ = lean_io_get_num_heartbeats();
v___x_3440_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2996_, v___y_3429_, v_goals_2975_, v___y_3426_, v_a_2978_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3442_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3440_, 1);
v___x_3442_ = l_List_reverse___redArg(v_a_3441_);
v___y_3406_ = v___x_3439_;
v___y_3407_ = v___y_3422_;
v___y_3408_ = v___y_3423_;
v___y_3409_ = v___y_3424_;
v___y_3410_ = v___y_3425_;
v___y_3411_ = v___y_3427_;
v___y_3412_ = v___y_3428_;
v___y_3413_ = v_a_3438_;
v___y_3414_ = v___y_3429_;
v_a_3415_ = v___x_3442_;
goto v___jp_3405_;
}
else
{
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3443_; 
v_a_3443_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v___x_3440_, 1);
v___y_3406_ = v___x_3439_;
v___y_3407_ = v___y_3422_;
v___y_3408_ = v___y_3423_;
v___y_3409_ = v___y_3424_;
v___y_3410_ = v___y_3425_;
v___y_3411_ = v___y_3427_;
v___y_3412_ = v___y_3428_;
v___y_3413_ = v_a_3438_;
v___y_3414_ = v___y_3429_;
v_a_3415_ = v_a_3443_;
goto v___jp_3405_;
}
else
{
lean_object* v_a_3444_; 
lean_dec(v___y_3428_);
lean_dec(v___y_3424_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3444_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3444_);
lean_dec_ref_known(v___x_3440_, 1);
v___y_3332_ = v___x_3439_;
v___y_3333_ = v___y_3422_;
v___y_3334_ = v___y_3423_;
v___y_3335_ = v___y_3425_;
v___y_3336_ = v___y_3427_;
v___y_3337_ = v_a_3438_;
v_a_3338_ = v_a_3444_;
goto v___jp_3331_;
}
}
}
}
else
{
lean_object* v_a_3445_; 
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v___y_3424_);
lean_dec(v_snd_2989_);
lean_dec(v_goals_2975_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3445_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3445_);
lean_dec_ref_known(v___x_3430_, 1);
v___y_3113_ = v___y_3423_;
v___y_3114_ = v___y_3425_;
v_a_3115_ = v_a_3445_;
goto v___jp_3112_;
}
}
v___jp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3450_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3449_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_3149_ = v___y_3447_;
v___y_3150_ = v___y_3448_;
v___y_3151_ = v___x_3450_;
goto v___jp_3148_;
}
v___jp_3451_:
{
uint8_t v___x_3458_; 
v___x_3458_ = l_List_isEmpty___redArg(v___y_3457_);
lean_dec(v___y_3457_);
if (v___x_3458_ == 0)
{
lean_dec(v___y_3454_);
lean_dec(v___y_3452_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___y_3447_ = v___y_3453_;
v___y_3448_ = v___y_3455_;
goto v___jp_3446_;
}
else
{
if (v___y_3456_ == 0)
{
lean_object* v___x_3459_; 
lean_inc(v_trace_2972_);
v___x_3459_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3452_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v___x_3461_ = l_List_appendTR___redArg(v___y_3454_, v_a_3460_);
v___y_3100_ = v___y_3453_;
v___y_3101_ = v___y_3455_;
v_a_3102_ = v___x_3461_;
goto v___jp_3099_;
}
else
{
lean_dec(v___y_3454_);
v___y_3149_ = v___y_3453_;
v___y_3150_ = v___y_3455_;
v___y_3151_ = v___x_3459_;
goto v___jp_3148_;
}
}
else
{
lean_dec(v___y_3454_);
lean_dec(v___y_3452_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___y_3447_ = v___y_3453_;
v___y_3448_ = v___y_3455_;
goto v___jp_3446_;
}
}
}
v___jp_3462_:
{
uint8_t v_commitIndependentGoals_3469_; lean_object* v___x_3470_; 
v_commitIndependentGoals_3469_ = lean_ctor_get_uint8(v_cfg_2971_, sizeof(void*)*4);
lean_inc(v___y_3464_);
v___x_3470_ = l_List_appendTR___redArg(v_a_3468_, v___y_3464_);
if (v_commitIndependentGoals_3469_ == 0)
{
v___y_3452_ = v___x_3470_;
v___y_3453_ = v___y_3463_;
v___y_3454_ = v___y_3464_;
v___y_3455_ = v___y_3465_;
v___y_3456_ = v___y_3466_;
v___y_3457_ = v___y_3467_;
goto v___jp_3451_;
}
else
{
uint8_t v___x_3471_; 
v___x_3471_ = l_List_isEmpty___redArg(v___y_3464_);
if (v___x_3471_ == 0)
{
v___y_3136_ = v___y_3463_;
v___y_3137_ = v___x_3470_;
v___y_3138_ = v___y_3464_;
v___y_3139_ = v___y_3465_;
v___y_3140_ = v___y_3467_;
goto v___jp_3135_;
}
else
{
if (v___y_3466_ == 0)
{
v___y_3452_ = v___x_3470_;
v___y_3453_ = v___y_3463_;
v___y_3454_ = v___y_3464_;
v___y_3455_ = v___y_3465_;
v___y_3456_ = v___y_3466_;
v___y_3457_ = v___y_3467_;
goto v___jp_3451_;
}
else
{
v___y_3136_ = v___y_3463_;
v___y_3137_ = v___x_3470_;
v___y_3138_ = v___y_3464_;
v___y_3139_ = v___y_3465_;
v___y_3140_ = v___y_3467_;
goto v___jp_3135_;
}
}
}
}
v___jp_3472_:
{
lean_object* v___x_3476_; double v___x_3477_; double v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3476_ = lean_io_get_num_heartbeats();
v___x_3477_ = lean_float_of_nat(v___y_3474_);
v___x_3478_ = lean_float_of_nat(v___x_3476_);
v___x_3479_ = lean_box_float(v___x_3477_);
v___x_3480_ = lean_box_float(v___x_3478_);
v___x_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3479_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3482_, 0, v_a_3475_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2972_, v_hasTrace_2996_, v___x_3078_, v_options_2994_, v___x_3081_, v___y_3473_, v___f_3077_, v___x_3482_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
return v___x_3483_;
}
v___jp_3484_:
{
lean_object* v___x_3488_; 
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_a_3487_);
v___y_3473_ = v___y_3485_;
v___y_3474_ = v___y_3486_;
v_a_3475_ = v___x_3488_;
goto v___jp_3472_;
}
v___jp_3489_:
{
lean_object* v___x_3493_; 
v___x_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3493_, 0, v_a_3492_);
v___y_3473_ = v___y_3490_;
v___y_3474_ = v___y_3491_;
v_a_3475_ = v___x_3493_;
goto v___jp_3472_;
}
v___jp_3494_:
{
if (lean_obj_tag(v___y_3497_) == 0)
{
lean_object* v_a_3498_; 
v_a_3498_ = lean_ctor_get(v___y_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___y_3497_, 1);
v___y_3490_ = v___y_3495_;
v___y_3491_ = v___y_3496_;
v_a_3492_ = v_a_3498_;
goto v___jp_3489_;
}
else
{
lean_object* v_a_3499_; 
v_a_3499_ = lean_ctor_get(v___y_3497_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___y_3497_, 1);
v___y_3485_ = v___y_3495_;
v___y_3486_ = v___y_3496_;
v_a_3487_ = v_a_3499_;
goto v___jp_3484_;
}
}
v___jp_3500_:
{
lean_object* v___x_3508_; double v___x_3509_; double v___x_3510_; double v___x_3511_; double v___x_3512_; double v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3508_ = lean_io_mono_nanos_now();
v___x_3509_ = lean_float_of_nat(v___y_3503_);
v___x_3510_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3511_ = lean_float_div(v___x_3509_, v___x_3510_);
v___x_3512_ = lean_float_of_nat(v___x_3508_);
v___x_3513_ = lean_float_div(v___x_3512_, v___x_3510_);
v___x_3514_ = lean_box_float(v___x_3511_);
v___x_3515_ = lean_box_float(v___x_3513_);
v___x_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3514_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
v___x_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3517_, 0, v_a_3507_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
lean_inc(v_trace_2972_);
v___x_3518_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2972_, v_hasTrace_2996_, v___x_3078_, v_options_2994_, v___y_3505_, v___y_3506_, v___y_3501_, v___x_3517_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_3495_ = v___y_3502_;
v___y_3496_ = v___y_3504_;
v___y_3497_ = v___x_3518_;
goto v___jp_3494_;
}
v___jp_3519_:
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3527_, 0, v_a_3526_);
v___y_3501_ = v___y_3520_;
v___y_3502_ = v___y_3521_;
v___y_3503_ = v___y_3522_;
v___y_3504_ = v___y_3524_;
v___y_3505_ = v___y_3523_;
v___y_3506_ = v___y_3525_;
v_a_3507_ = v___x_3527_;
goto v___jp_3500_;
}
v___jp_3528_:
{
lean_object* v___x_3536_; 
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v_a_3535_);
v___y_3501_ = v___y_3529_;
v___y_3502_ = v___y_3530_;
v___y_3503_ = v___y_3531_;
v___y_3504_ = v___y_3533_;
v___y_3505_ = v___y_3532_;
v___y_3506_ = v___y_3534_;
v_a_3507_ = v___x_3536_;
goto v___jp_3500_;
}
v___jp_3537_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = l_List_appendTR___redArg(v___y_3544_, v___y_3543_);
v___x_3548_ = l_List_appendTR___redArg(v___x_3547_, v_a_3546_);
v___y_3529_ = v___y_3538_;
v___y_3530_ = v___y_3539_;
v___y_3531_ = v___y_3540_;
v___y_3532_ = v___y_3542_;
v___y_3533_ = v___y_3541_;
v___y_3534_ = v___y_3545_;
v_a_3535_ = v___x_3548_;
goto v___jp_3528_;
}
v___jp_3549_:
{
if (lean_obj_tag(v___y_3558_) == 0)
{
lean_object* v_a_3559_; 
v_a_3559_ = lean_ctor_get(v___y_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___y_3558_, 1);
v___y_3538_ = v___y_3550_;
v___y_3539_ = v___y_3551_;
v___y_3540_ = v___y_3552_;
v___y_3541_ = v___y_3554_;
v___y_3542_ = v___y_3553_;
v___y_3543_ = v___y_3555_;
v___y_3544_ = v___y_3556_;
v___y_3545_ = v___y_3557_;
v_a_3546_ = v_a_3559_;
goto v___jp_3537_;
}
else
{
lean_object* v_a_3560_; 
lean_dec(v___y_3556_);
lean_dec(v___y_3555_);
v_a_3560_ = lean_ctor_get(v___y_3558_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___y_3558_, 1);
v___y_3520_ = v___y_3550_;
v___y_3521_ = v___y_3551_;
v___y_3522_ = v___y_3552_;
v___y_3523_ = v___y_3553_;
v___y_3524_ = v___y_3554_;
v___y_3525_ = v___y_3557_;
v_a_3526_ = v_a_3560_;
goto v___jp_3519_;
}
}
v___jp_3561_:
{
if (v___y_3572_ == 0)
{
lean_object* v___x_3573_; 
lean_dec_ref(v___y_3562_);
v___x_3573_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3565_, v_a_2978_, v_a_2980_);
lean_dec_ref(v___y_3565_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_dec_ref_known(v___x_3573_, 1);
v___y_3538_ = v___y_3563_;
v___y_3539_ = v___y_3564_;
v___y_3540_ = v___y_3566_;
v___y_3541_ = v___y_3568_;
v___y_3542_ = v___y_3567_;
v___y_3543_ = v___y_3569_;
v___y_3544_ = v___y_3570_;
v___y_3545_ = v___y_3571_;
v_a_3546_ = v_snd_2989_;
goto v___jp_3537_;
}
else
{
lean_object* v_a_3574_; 
lean_dec(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec(v_snd_2989_);
v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_a_3574_);
lean_dec_ref_known(v___x_3573_, 1);
v___y_3520_ = v___y_3563_;
v___y_3521_ = v___y_3564_;
v___y_3522_ = v___y_3566_;
v___y_3523_ = v___y_3567_;
v___y_3524_ = v___y_3568_;
v___y_3525_ = v___y_3571_;
v_a_3526_ = v_a_3574_;
goto v___jp_3519_;
}
}
else
{
lean_dec_ref(v___y_3565_);
lean_dec(v_snd_2989_);
v___y_3550_ = v___y_3563_;
v___y_3551_ = v___y_3564_;
v___y_3552_ = v___y_3566_;
v___y_3553_ = v___y_3567_;
v___y_3554_ = v___y_3568_;
v___y_3555_ = v___y_3569_;
v___y_3556_ = v___y_3570_;
v___y_3557_ = v___y_3571_;
v___y_3558_ = v___y_3562_;
goto v___jp_3549_;
}
}
v___jp_3575_:
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Lean_Meta_saveState___redArg(v_a_2978_, v_a_2980_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3587_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
lean_dec_ref_known(v___x_3585_, 1);
lean_inc(v_snd_2989_);
lean_inc(v_trace_2972_);
v___x_3587_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3581_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_dec(v_a_3586_);
lean_dec(v_snd_2989_);
v___y_3550_ = v___y_3576_;
v___y_3551_ = v___y_3577_;
v___y_3552_ = v___y_3578_;
v___y_3553_ = v___y_3580_;
v___y_3554_ = v___y_3579_;
v___y_3555_ = v___y_3582_;
v___y_3556_ = v___y_3583_;
v___y_3557_ = v___y_3584_;
v___y_3558_ = v___x_3587_;
goto v___jp_3549_;
}
else
{
lean_object* v_a_3588_; uint8_t v___x_3589_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_a_3588_);
v___x_3589_ = l_Lean_Exception_isInterrupt(v_a_3588_);
if (v___x_3589_ == 0)
{
uint8_t v___x_3590_; 
v___x_3590_ = l_Lean_Exception_isRuntime(v_a_3588_);
v___y_3562_ = v___x_3587_;
v___y_3563_ = v___y_3576_;
v___y_3564_ = v___y_3577_;
v___y_3565_ = v_a_3586_;
v___y_3566_ = v___y_3578_;
v___y_3567_ = v___y_3580_;
v___y_3568_ = v___y_3579_;
v___y_3569_ = v___y_3582_;
v___y_3570_ = v___y_3583_;
v___y_3571_ = v___y_3584_;
v___y_3572_ = v___x_3590_;
goto v___jp_3561_;
}
else
{
lean_dec(v_a_3588_);
v___y_3562_ = v___x_3587_;
v___y_3563_ = v___y_3576_;
v___y_3564_ = v___y_3577_;
v___y_3565_ = v_a_3586_;
v___y_3566_ = v___y_3578_;
v___y_3567_ = v___y_3580_;
v___y_3568_ = v___y_3579_;
v___y_3569_ = v___y_3582_;
v___y_3570_ = v___y_3583_;
v___y_3571_ = v___y_3584_;
v___y_3572_ = v___x_3589_;
goto v___jp_3561_;
}
}
}
else
{
lean_object* v_a_3591_; 
lean_dec(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3591_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3585_, 1);
v___y_3520_ = v___y_3576_;
v___y_3521_ = v___y_3577_;
v___y_3522_ = v___y_3578_;
v___y_3523_ = v___y_3580_;
v___y_3524_ = v___y_3579_;
v___y_3525_ = v___y_3584_;
v_a_3526_ = v_a_3591_;
goto v___jp_3519_;
}
}
v___jp_3592_:
{
if (lean_obj_tag(v___y_3599_) == 0)
{
lean_object* v_a_3600_; 
v_a_3600_ = lean_ctor_get(v___y_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___y_3599_, 1);
v___y_3529_ = v___y_3593_;
v___y_3530_ = v___y_3594_;
v___y_3531_ = v___y_3595_;
v___y_3532_ = v___y_3597_;
v___y_3533_ = v___y_3596_;
v___y_3534_ = v___y_3598_;
v_a_3535_ = v_a_3600_;
goto v___jp_3528_;
}
else
{
lean_object* v_a_3601_; 
v_a_3601_ = lean_ctor_get(v___y_3599_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___y_3599_, 1);
v___y_3520_ = v___y_3593_;
v___y_3521_ = v___y_3594_;
v___y_3522_ = v___y_3595_;
v___y_3523_ = v___y_3597_;
v___y_3524_ = v___y_3596_;
v___y_3525_ = v___y_3598_;
v_a_3526_ = v_a_3601_;
goto v___jp_3519_;
}
}
v___jp_3602_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3610_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3609_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_3593_ = v___y_3603_;
v___y_3594_ = v___y_3604_;
v___y_3595_ = v___y_3605_;
v___y_3596_ = v___y_3607_;
v___y_3597_ = v___y_3606_;
v___y_3598_ = v___y_3608_;
v___y_3599_ = v___x_3610_;
goto v___jp_3592_;
}
v___jp_3611_:
{
uint8_t v___x_3622_; 
v___x_3622_ = l_List_isEmpty___redArg(v___y_3618_);
lean_dec(v___y_3618_);
if (v___x_3622_ == 0)
{
lean_dec(v___y_3619_);
lean_dec(v___y_3617_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___y_3603_ = v___y_3612_;
v___y_3604_ = v___y_3613_;
v___y_3605_ = v___y_3614_;
v___y_3606_ = v___y_3616_;
v___y_3607_ = v___y_3615_;
v___y_3608_ = v___y_3621_;
goto v___jp_3602_;
}
else
{
if (v___y_3620_ == 0)
{
lean_object* v___x_3623_; 
lean_inc(v_trace_2972_);
v___x_3623_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3617_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3625_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3623_, 1);
v___x_3625_ = l_List_appendTR___redArg(v___y_3619_, v_a_3624_);
v___y_3529_ = v___y_3612_;
v___y_3530_ = v___y_3613_;
v___y_3531_ = v___y_3614_;
v___y_3532_ = v___y_3616_;
v___y_3533_ = v___y_3615_;
v___y_3534_ = v___y_3621_;
v_a_3535_ = v___x_3625_;
goto v___jp_3528_;
}
else
{
lean_dec(v___y_3619_);
v___y_3593_ = v___y_3612_;
v___y_3594_ = v___y_3613_;
v___y_3595_ = v___y_3614_;
v___y_3596_ = v___y_3615_;
v___y_3597_ = v___y_3616_;
v___y_3598_ = v___y_3621_;
v___y_3599_ = v___x_3623_;
goto v___jp_3592_;
}
}
else
{
lean_dec(v___y_3619_);
lean_dec(v___y_3617_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___y_3603_ = v___y_3612_;
v___y_3604_ = v___y_3613_;
v___y_3605_ = v___y_3614_;
v___y_3606_ = v___y_3616_;
v___y_3607_ = v___y_3615_;
v___y_3608_ = v___y_3621_;
goto v___jp_3602_;
}
}
}
v___jp_3626_:
{
uint8_t v_commitIndependentGoals_3637_; lean_object* v___x_3638_; 
v_commitIndependentGoals_3637_ = lean_ctor_get_uint8(v_cfg_2971_, sizeof(void*)*4);
lean_inc(v___y_3633_);
v___x_3638_ = l_List_appendTR___redArg(v_a_3636_, v___y_3633_);
if (v_commitIndependentGoals_3637_ == 0)
{
v___y_3612_ = v___y_3627_;
v___y_3613_ = v___y_3628_;
v___y_3614_ = v___y_3629_;
v___y_3615_ = v___y_3630_;
v___y_3616_ = v___y_3631_;
v___y_3617_ = v___x_3638_;
v___y_3618_ = v___y_3632_;
v___y_3619_ = v___y_3633_;
v___y_3620_ = v___y_3634_;
v___y_3621_ = v___y_3635_;
goto v___jp_3611_;
}
else
{
uint8_t v___x_3639_; 
v___x_3639_ = l_List_isEmpty___redArg(v___y_3633_);
if (v___x_3639_ == 0)
{
v___y_3576_ = v___y_3627_;
v___y_3577_ = v___y_3628_;
v___y_3578_ = v___y_3629_;
v___y_3579_ = v___y_3630_;
v___y_3580_ = v___y_3631_;
v___y_3581_ = v___x_3638_;
v___y_3582_ = v___y_3632_;
v___y_3583_ = v___y_3633_;
v___y_3584_ = v___y_3635_;
goto v___jp_3575_;
}
else
{
if (v___y_3634_ == 0)
{
v___y_3612_ = v___y_3627_;
v___y_3613_ = v___y_3628_;
v___y_3614_ = v___y_3629_;
v___y_3615_ = v___y_3630_;
v___y_3616_ = v___y_3631_;
v___y_3617_ = v___x_3638_;
v___y_3618_ = v___y_3632_;
v___y_3619_ = v___y_3633_;
v___y_3620_ = v___y_3634_;
v___y_3621_ = v___y_3635_;
goto v___jp_3611_;
}
else
{
v___y_3576_ = v___y_3627_;
v___y_3577_ = v___y_3628_;
v___y_3578_ = v___y_3629_;
v___y_3579_ = v___y_3630_;
v___y_3580_ = v___y_3631_;
v___y_3581_ = v___x_3638_;
v___y_3582_ = v___y_3632_;
v___y_3583_ = v___y_3633_;
v___y_3584_ = v___y_3635_;
goto v___jp_3575_;
}
}
}
}
v___jp_3640_:
{
lean_object* v___x_3648_; double v___x_3649_; double v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3648_ = lean_io_get_num_heartbeats();
v___x_3649_ = lean_float_of_nat(v___y_3645_);
v___x_3650_ = lean_float_of_nat(v___x_3648_);
v___x_3651_ = lean_box_float(v___x_3649_);
v___x_3652_ = lean_box_float(v___x_3650_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3651_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3654_, 0, v_a_3647_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
lean_inc(v_trace_2972_);
v___x_3655_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2972_, v_hasTrace_2996_, v___x_3078_, v_options_2994_, v___y_3644_, v___y_3646_, v___y_3641_, v___x_3654_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_3495_ = v___y_3642_;
v___y_3496_ = v___y_3643_;
v___y_3497_ = v___x_3655_;
goto v___jp_3494_;
}
v___jp_3656_:
{
lean_object* v___x_3664_; 
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v_a_3663_);
v___y_3641_ = v___y_3657_;
v___y_3642_ = v___y_3658_;
v___y_3643_ = v___y_3660_;
v___y_3644_ = v___y_3659_;
v___y_3645_ = v___y_3661_;
v___y_3646_ = v___y_3662_;
v_a_3647_ = v___x_3664_;
goto v___jp_3640_;
}
v___jp_3665_:
{
lean_object* v___x_3673_; 
v___x_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3673_, 0, v_a_3672_);
v___y_3641_ = v___y_3666_;
v___y_3642_ = v___y_3667_;
v___y_3643_ = v___y_3669_;
v___y_3644_ = v___y_3668_;
v___y_3645_ = v___y_3670_;
v___y_3646_ = v___y_3671_;
v_a_3647_ = v___x_3673_;
goto v___jp_3640_;
}
v___jp_3674_:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = l_List_appendTR___redArg(v___y_3681_, v___y_3679_);
v___x_3685_ = l_List_appendTR___redArg(v___x_3684_, v_a_3683_);
v___y_3666_ = v___y_3675_;
v___y_3667_ = v___y_3676_;
v___y_3668_ = v___y_3678_;
v___y_3669_ = v___y_3677_;
v___y_3670_ = v___y_3680_;
v___y_3671_ = v___y_3682_;
v_a_3672_ = v___x_3685_;
goto v___jp_3665_;
}
v___jp_3686_:
{
if (lean_obj_tag(v___y_3695_) == 0)
{
lean_object* v_a_3696_; 
v_a_3696_ = lean_ctor_get(v___y_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___y_3695_, 1);
v___y_3675_ = v___y_3687_;
v___y_3676_ = v___y_3688_;
v___y_3677_ = v___y_3690_;
v___y_3678_ = v___y_3689_;
v___y_3679_ = v___y_3691_;
v___y_3680_ = v___y_3692_;
v___y_3681_ = v___y_3693_;
v___y_3682_ = v___y_3694_;
v_a_3683_ = v_a_3696_;
goto v___jp_3674_;
}
else
{
lean_object* v_a_3697_; 
lean_dec(v___y_3693_);
lean_dec(v___y_3691_);
v_a_3697_ = lean_ctor_get(v___y_3695_, 0);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___y_3695_, 1);
v___y_3657_ = v___y_3687_;
v___y_3658_ = v___y_3688_;
v___y_3659_ = v___y_3689_;
v___y_3660_ = v___y_3690_;
v___y_3661_ = v___y_3692_;
v___y_3662_ = v___y_3694_;
v_a_3663_ = v_a_3697_;
goto v___jp_3656_;
}
}
v___jp_3698_:
{
if (v___y_3709_ == 0)
{
lean_object* v___x_3710_; 
lean_dec_ref(v___y_3705_);
v___x_3710_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3701_, v_a_2978_, v_a_2980_);
lean_dec_ref(v___y_3701_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_dec_ref_known(v___x_3710_, 1);
v___y_3675_ = v___y_3699_;
v___y_3676_ = v___y_3700_;
v___y_3677_ = v___y_3703_;
v___y_3678_ = v___y_3702_;
v___y_3679_ = v___y_3704_;
v___y_3680_ = v___y_3706_;
v___y_3681_ = v___y_3707_;
v___y_3682_ = v___y_3708_;
v_a_3683_ = v_snd_2989_;
goto v___jp_3674_;
}
else
{
lean_object* v_a_3711_; 
lean_dec(v___y_3707_);
lean_dec(v___y_3704_);
lean_dec(v_snd_2989_);
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3710_, 1);
v___y_3657_ = v___y_3699_;
v___y_3658_ = v___y_3700_;
v___y_3659_ = v___y_3702_;
v___y_3660_ = v___y_3703_;
v___y_3661_ = v___y_3706_;
v___y_3662_ = v___y_3708_;
v_a_3663_ = v_a_3711_;
goto v___jp_3656_;
}
}
else
{
lean_dec_ref(v___y_3701_);
lean_dec(v_snd_2989_);
v___y_3687_ = v___y_3699_;
v___y_3688_ = v___y_3700_;
v___y_3689_ = v___y_3702_;
v___y_3690_ = v___y_3703_;
v___y_3691_ = v___y_3704_;
v___y_3692_ = v___y_3706_;
v___y_3693_ = v___y_3707_;
v___y_3694_ = v___y_3708_;
v___y_3695_ = v___y_3705_;
goto v___jp_3686_;
}
}
v___jp_3712_:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Meta_saveState___redArg(v_a_2978_, v_a_2980_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
lean_inc(v_snd_2989_);
lean_inc(v_trace_2972_);
v___x_3724_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3715_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_dec(v_a_3723_);
lean_dec(v_snd_2989_);
v___y_3687_ = v___y_3713_;
v___y_3688_ = v___y_3714_;
v___y_3689_ = v___y_3717_;
v___y_3690_ = v___y_3716_;
v___y_3691_ = v___y_3718_;
v___y_3692_ = v___y_3719_;
v___y_3693_ = v___y_3720_;
v___y_3694_ = v___y_3721_;
v___y_3695_ = v___x_3724_;
goto v___jp_3686_;
}
else
{
lean_object* v_a_3725_; uint8_t v___x_3726_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
v___x_3726_ = l_Lean_Exception_isInterrupt(v_a_3725_);
if (v___x_3726_ == 0)
{
uint8_t v___x_3727_; 
v___x_3727_ = l_Lean_Exception_isRuntime(v_a_3725_);
v___y_3699_ = v___y_3713_;
v___y_3700_ = v___y_3714_;
v___y_3701_ = v_a_3723_;
v___y_3702_ = v___y_3717_;
v___y_3703_ = v___y_3716_;
v___y_3704_ = v___y_3718_;
v___y_3705_ = v___x_3724_;
v___y_3706_ = v___y_3719_;
v___y_3707_ = v___y_3720_;
v___y_3708_ = v___y_3721_;
v___y_3709_ = v___x_3727_;
goto v___jp_3698_;
}
else
{
lean_dec(v_a_3725_);
v___y_3699_ = v___y_3713_;
v___y_3700_ = v___y_3714_;
v___y_3701_ = v_a_3723_;
v___y_3702_ = v___y_3717_;
v___y_3703_ = v___y_3716_;
v___y_3704_ = v___y_3718_;
v___y_3705_ = v___x_3724_;
v___y_3706_ = v___y_3719_;
v___y_3707_ = v___y_3720_;
v___y_3708_ = v___y_3721_;
v___y_3709_ = v___x_3726_;
goto v___jp_3698_;
}
}
}
else
{
lean_object* v_a_3728_; 
lean_dec(v___y_3720_);
lean_dec(v___y_3718_);
lean_dec(v___y_3715_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3728_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3722_, 1);
v___y_3657_ = v___y_3713_;
v___y_3658_ = v___y_3714_;
v___y_3659_ = v___y_3717_;
v___y_3660_ = v___y_3716_;
v___y_3661_ = v___y_3719_;
v___y_3662_ = v___y_3721_;
v_a_3663_ = v_a_3728_;
goto v___jp_3656_;
}
}
v___jp_3729_:
{
if (lean_obj_tag(v___y_3736_) == 0)
{
lean_object* v_a_3737_; 
v_a_3737_ = lean_ctor_get(v___y_3736_, 0);
lean_inc(v_a_3737_);
lean_dec_ref_known(v___y_3736_, 1);
v___y_3666_ = v___y_3730_;
v___y_3667_ = v___y_3731_;
v___y_3668_ = v___y_3733_;
v___y_3669_ = v___y_3732_;
v___y_3670_ = v___y_3734_;
v___y_3671_ = v___y_3735_;
v_a_3672_ = v_a_3737_;
goto v___jp_3665_;
}
else
{
lean_object* v_a_3738_; 
v_a_3738_ = lean_ctor_get(v___y_3736_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___y_3736_, 1);
v___y_3657_ = v___y_3730_;
v___y_3658_ = v___y_3731_;
v___y_3659_ = v___y_3733_;
v___y_3660_ = v___y_3732_;
v___y_3661_ = v___y_3734_;
v___y_3662_ = v___y_3735_;
v_a_3663_ = v_a_3738_;
goto v___jp_3656_;
}
}
v___jp_3739_:
{
lean_object* v___x_3748_; 
lean_inc(v_trace_2972_);
v___x_3748_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3742_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; lean_object* v___x_3750_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3748_, 1);
v___x_3750_ = l_List_appendTR___redArg(v___y_3746_, v_a_3749_);
v___y_3666_ = v___y_3740_;
v___y_3667_ = v___y_3741_;
v___y_3668_ = v___y_3744_;
v___y_3669_ = v___y_3743_;
v___y_3670_ = v___y_3745_;
v___y_3671_ = v___y_3747_;
v_a_3672_ = v___x_3750_;
goto v___jp_3665_;
}
else
{
lean_dec(v___y_3746_);
v___y_3730_ = v___y_3740_;
v___y_3731_ = v___y_3741_;
v___y_3732_ = v___y_3743_;
v___y_3733_ = v___y_3744_;
v___y_3734_ = v___y_3745_;
v___y_3735_ = v___y_3747_;
v___y_3736_ = v___x_3748_;
goto v___jp_3729_;
}
}
v___jp_3751_:
{
uint8_t v___x_3762_; 
v___x_3762_ = l_List_isEmpty___redArg(v___y_3757_);
lean_dec(v___y_3757_);
if (v___x_3762_ == 0)
{
if (v___y_3761_ == 0)
{
v___y_3740_ = v___y_3752_;
v___y_3741_ = v___y_3753_;
v___y_3742_ = v___y_3754_;
v___y_3743_ = v___y_3756_;
v___y_3744_ = v___y_3755_;
v___y_3745_ = v___y_3758_;
v___y_3746_ = v___y_3759_;
v___y_3747_ = v___y_3760_;
goto v___jp_3739_;
}
else
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
lean_dec(v___y_3759_);
lean_dec(v___y_3754_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___x_3763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3764_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3763_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_3730_ = v___y_3752_;
v___y_3731_ = v___y_3753_;
v___y_3732_ = v___y_3756_;
v___y_3733_ = v___y_3755_;
v___y_3734_ = v___y_3758_;
v___y_3735_ = v___y_3760_;
v___y_3736_ = v___x_3764_;
goto v___jp_3729_;
}
}
else
{
v___y_3740_ = v___y_3752_;
v___y_3741_ = v___y_3753_;
v___y_3742_ = v___y_3754_;
v___y_3743_ = v___y_3756_;
v___y_3744_ = v___y_3755_;
v___y_3745_ = v___y_3758_;
v___y_3746_ = v___y_3759_;
v___y_3747_ = v___y_3760_;
goto v___jp_3739_;
}
}
v___jp_3765_:
{
uint8_t v_commitIndependentGoals_3776_; lean_object* v___x_3777_; 
v_commitIndependentGoals_3776_ = lean_ctor_get_uint8(v_cfg_2971_, sizeof(void*)*4);
lean_inc(v___y_3772_);
v___x_3777_ = l_List_appendTR___redArg(v_a_3775_, v___y_3772_);
if (v_commitIndependentGoals_3776_ == 0)
{
v___y_3752_ = v___y_3766_;
v___y_3753_ = v___y_3767_;
v___y_3754_ = v___x_3777_;
v___y_3755_ = v___y_3768_;
v___y_3756_ = v___y_3769_;
v___y_3757_ = v___y_3770_;
v___y_3758_ = v___y_3771_;
v___y_3759_ = v___y_3772_;
v___y_3760_ = v___y_3774_;
v___y_3761_ = v___y_3773_;
goto v___jp_3751_;
}
else
{
uint8_t v___x_3778_; 
v___x_3778_ = l_List_isEmpty___redArg(v___y_3772_);
if (v___x_3778_ == 0)
{
v___y_3713_ = v___y_3766_;
v___y_3714_ = v___y_3767_;
v___y_3715_ = v___x_3777_;
v___y_3716_ = v___y_3769_;
v___y_3717_ = v___y_3768_;
v___y_3718_ = v___y_3770_;
v___y_3719_ = v___y_3771_;
v___y_3720_ = v___y_3772_;
v___y_3721_ = v___y_3774_;
goto v___jp_3712_;
}
else
{
if (v___x_2993_ == 0)
{
v___y_3752_ = v___y_3766_;
v___y_3753_ = v___y_3767_;
v___y_3754_ = v___x_3777_;
v___y_3755_ = v___y_3768_;
v___y_3756_ = v___y_3769_;
v___y_3757_ = v___y_3770_;
v___y_3758_ = v___y_3771_;
v___y_3759_ = v___y_3772_;
v___y_3760_ = v___y_3774_;
v___y_3761_ = v___y_3773_;
goto v___jp_3751_;
}
else
{
v___y_3713_ = v___y_3766_;
v___y_3714_ = v___y_3767_;
v___y_3715_ = v___x_3777_;
v___y_3716_ = v___y_3769_;
v___y_3717_ = v___y_3768_;
v___y_3718_ = v___y_3770_;
v___y_3719_ = v___y_3771_;
v___y_3720_ = v___y_3772_;
v___y_3721_ = v___y_3774_;
goto v___jp_3712_;
}
}
}
}
v___jp_3779_:
{
lean_object* v___x_3788_; 
v___x_3788_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2980_);
if (lean_obj_tag(v___x_3788_) == 0)
{
if (v___y_3787_ == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3788_, 1);
v___x_3790_ = lean_io_mono_nanos_now();
v___x_3791_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3787_, v___x_2993_, v_goals_2975_, v___y_3784_, v_a_2978_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3793_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v___x_3793_ = l_List_reverse___redArg(v_a_3792_);
v___y_3627_ = v___y_3780_;
v___y_3628_ = v___y_3781_;
v___y_3629_ = v___x_3790_;
v___y_3630_ = v___y_3783_;
v___y_3631_ = v___y_3782_;
v___y_3632_ = v___y_3785_;
v___y_3633_ = v___y_3786_;
v___y_3634_ = v___y_3787_;
v___y_3635_ = v_a_3789_;
v_a_3636_ = v___x_3793_;
goto v___jp_3626_;
}
else
{
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3794_; 
v_a_3794_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3794_);
lean_dec_ref_known(v___x_3791_, 1);
v___y_3627_ = v___y_3780_;
v___y_3628_ = v___y_3781_;
v___y_3629_ = v___x_3790_;
v___y_3630_ = v___y_3783_;
v___y_3631_ = v___y_3782_;
v___y_3632_ = v___y_3785_;
v___y_3633_ = v___y_3786_;
v___y_3634_ = v___y_3787_;
v___y_3635_ = v_a_3789_;
v_a_3636_ = v_a_3794_;
goto v___jp_3626_;
}
else
{
lean_object* v_a_3795_; 
lean_dec(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3795_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3791_, 1);
v___y_3520_ = v___y_3780_;
v___y_3521_ = v___y_3781_;
v___y_3522_ = v___x_3790_;
v___y_3523_ = v___y_3782_;
v___y_3524_ = v___y_3783_;
v___y_3525_ = v_a_3789_;
v_a_3526_ = v_a_3795_;
goto v___jp_3519_;
}
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_a_3796_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3788_, 1);
v___x_3797_ = lean_io_get_num_heartbeats();
v___x_3798_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3787_, v___x_2993_, v_goals_2975_, v___y_3784_, v_a_2978_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3800_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3798_, 1);
v___x_3800_ = l_List_reverse___redArg(v_a_3799_);
v___y_3766_ = v___y_3780_;
v___y_3767_ = v___y_3781_;
v___y_3768_ = v___y_3782_;
v___y_3769_ = v___y_3783_;
v___y_3770_ = v___y_3785_;
v___y_3771_ = v___x_3797_;
v___y_3772_ = v___y_3786_;
v___y_3773_ = v___y_3787_;
v___y_3774_ = v_a_3796_;
v_a_3775_ = v___x_3800_;
goto v___jp_3765_;
}
else
{
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3801_; 
v_a_3801_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3801_);
lean_dec_ref_known(v___x_3798_, 1);
v___y_3766_ = v___y_3780_;
v___y_3767_ = v___y_3781_;
v___y_3768_ = v___y_3782_;
v___y_3769_ = v___y_3783_;
v___y_3770_ = v___y_3785_;
v___y_3771_ = v___x_3797_;
v___y_3772_ = v___y_3786_;
v___y_3773_ = v___y_3787_;
v___y_3774_ = v_a_3796_;
v_a_3775_ = v_a_3801_;
goto v___jp_3765_;
}
else
{
lean_object* v_a_3802_; 
lean_dec(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3802_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3798_, 1);
v___y_3657_ = v___y_3780_;
v___y_3658_ = v___y_3781_;
v___y_3659_ = v___y_3782_;
v___y_3660_ = v___y_3783_;
v___y_3661_ = v___x_3797_;
v___y_3662_ = v_a_3796_;
v_a_3663_ = v_a_3802_;
goto v___jp_3656_;
}
}
}
}
else
{
lean_object* v_a_3803_; 
lean_dec(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3780_);
lean_dec(v_snd_2989_);
lean_dec(v_goals_2975_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3803_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3803_);
lean_dec_ref_known(v___x_3788_, 1);
v___y_3485_ = v___y_3781_;
v___y_3486_ = v___y_3783_;
v_a_3487_ = v_a_3803_;
goto v___jp_3484_;
}
}
v___jp_3804_:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3807_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_3808_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3807_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
v___y_3495_ = v___y_3805_;
v___y_3496_ = v___y_3806_;
v___y_3497_ = v___x_3808_;
goto v___jp_3494_;
}
v___jp_3809_:
{
uint8_t v___x_3816_; 
v___x_3816_ = l_List_isEmpty___redArg(v___y_3814_);
lean_dec(v___y_3814_);
if (v___x_3816_ == 0)
{
lean_dec(v___y_3815_);
lean_dec(v___y_3813_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___y_3805_ = v___y_3811_;
v___y_3806_ = v___y_3812_;
goto v___jp_3804_;
}
else
{
if (v___y_3810_ == 0)
{
lean_object* v___x_3817_; 
lean_inc(v_trace_2972_);
v___x_3817_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3813_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3819_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3817_, 1);
v___x_3819_ = l_List_appendTR___redArg(v___y_3815_, v_a_3818_);
v___y_3490_ = v___y_3811_;
v___y_3491_ = v___y_3812_;
v_a_3492_ = v___x_3819_;
goto v___jp_3489_;
}
else
{
lean_dec(v___y_3815_);
v___y_3495_ = v___y_3811_;
v___y_3496_ = v___y_3812_;
v___y_3497_ = v___x_3817_;
goto v___jp_3494_;
}
}
else
{
lean_dec(v___y_3815_);
lean_dec(v___y_3813_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v___y_3805_ = v___y_3811_;
v___y_3806_ = v___y_3812_;
goto v___jp_3804_;
}
}
}
v___jp_3820_:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3826_ = l_List_appendTR___redArg(v___y_3824_, v___y_3823_);
v___x_3827_ = l_List_appendTR___redArg(v___x_3826_, v_a_3825_);
v___y_3490_ = v___y_3821_;
v___y_3491_ = v___y_3822_;
v_a_3492_ = v___x_3827_;
goto v___jp_3489_;
}
v___jp_3828_:
{
if (lean_obj_tag(v___y_3833_) == 0)
{
lean_object* v_a_3834_; 
v_a_3834_ = lean_ctor_get(v___y_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___y_3833_, 1);
v___y_3821_ = v___y_3829_;
v___y_3822_ = v___y_3830_;
v___y_3823_ = v___y_3831_;
v___y_3824_ = v___y_3832_;
v_a_3825_ = v_a_3834_;
goto v___jp_3820_;
}
else
{
lean_object* v_a_3835_; 
lean_dec(v___y_3832_);
lean_dec(v___y_3831_);
v_a_3835_ = lean_ctor_get(v___y_3833_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v___y_3833_, 1);
v___y_3485_ = v___y_3829_;
v___y_3486_ = v___y_3830_;
v_a_3487_ = v_a_3835_;
goto v___jp_3484_;
}
}
v___jp_3836_:
{
if (v___y_3843_ == 0)
{
lean_object* v___x_3844_; 
lean_dec_ref(v___y_3837_);
v___x_3844_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3839_, v_a_2978_, v_a_2980_);
lean_dec_ref(v___y_3839_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_dec_ref_known(v___x_3844_, 1);
v___y_3821_ = v___y_3838_;
v___y_3822_ = v___y_3840_;
v___y_3823_ = v___y_3841_;
v___y_3824_ = v___y_3842_;
v_a_3825_ = v_snd_2989_;
goto v___jp_3820_;
}
else
{
lean_object* v_a_3845_; 
lean_dec(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec(v_snd_2989_);
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
v___y_3485_ = v___y_3838_;
v___y_3486_ = v___y_3840_;
v_a_3487_ = v_a_3845_;
goto v___jp_3484_;
}
}
else
{
lean_dec_ref(v___y_3839_);
lean_dec(v_snd_2989_);
v___y_3829_ = v___y_3838_;
v___y_3830_ = v___y_3840_;
v___y_3831_ = v___y_3841_;
v___y_3832_ = v___y_3842_;
v___y_3833_ = v___y_3837_;
goto v___jp_3828_;
}
}
v___jp_3846_:
{
lean_object* v___x_3852_; 
v___x_3852_ = l_Lean_Meta_saveState___redArg(v_a_2978_, v_a_2980_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3854_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3852_, 1);
lean_inc(v_snd_2989_);
lean_inc(v_trace_2972_);
v___x_3854_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v___y_3850_, v_snd_2989_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_dec(v_a_3853_);
lean_dec(v_snd_2989_);
v___y_3829_ = v___y_3847_;
v___y_3830_ = v___y_3848_;
v___y_3831_ = v___y_3849_;
v___y_3832_ = v___y_3851_;
v___y_3833_ = v___x_3854_;
goto v___jp_3828_;
}
else
{
lean_object* v_a_3855_; uint8_t v___x_3856_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
v___x_3856_ = l_Lean_Exception_isInterrupt(v_a_3855_);
if (v___x_3856_ == 0)
{
uint8_t v___x_3857_; 
v___x_3857_ = l_Lean_Exception_isRuntime(v_a_3855_);
v___y_3837_ = v___x_3854_;
v___y_3838_ = v___y_3847_;
v___y_3839_ = v_a_3853_;
v___y_3840_ = v___y_3848_;
v___y_3841_ = v___y_3849_;
v___y_3842_ = v___y_3851_;
v___y_3843_ = v___x_3857_;
goto v___jp_3836_;
}
else
{
lean_dec(v_a_3855_);
v___y_3837_ = v___x_3854_;
v___y_3838_ = v___y_3847_;
v___y_3839_ = v_a_3853_;
v___y_3840_ = v___y_3848_;
v___y_3841_ = v___y_3849_;
v___y_3842_ = v___y_3851_;
v___y_3843_ = v___x_3856_;
goto v___jp_3836_;
}
}
}
else
{
lean_object* v_a_3858_; 
lean_dec(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3858_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___x_3852_, 1);
v___y_3485_ = v___y_3847_;
v___y_3486_ = v___y_3848_;
v_a_3487_ = v_a_3858_;
goto v___jp_3484_;
}
}
v___jp_3859_:
{
uint8_t v_commitIndependentGoals_3866_; lean_object* v___x_3867_; 
v_commitIndependentGoals_3866_ = lean_ctor_get_uint8(v_cfg_2971_, sizeof(void*)*4);
lean_inc(v___y_3864_);
v___x_3867_ = l_List_appendTR___redArg(v_a_3865_, v___y_3864_);
if (v_commitIndependentGoals_3866_ == 0)
{
v___y_3810_ = v___y_3860_;
v___y_3811_ = v___y_3861_;
v___y_3812_ = v___y_3862_;
v___y_3813_ = v___x_3867_;
v___y_3814_ = v___y_3863_;
v___y_3815_ = v___y_3864_;
goto v___jp_3809_;
}
else
{
uint8_t v___x_3868_; 
v___x_3868_ = l_List_isEmpty___redArg(v___y_3864_);
if (v___x_3868_ == 0)
{
v___y_3847_ = v___y_3861_;
v___y_3848_ = v___y_3862_;
v___y_3849_ = v___y_3863_;
v___y_3850_ = v___x_3867_;
v___y_3851_ = v___y_3864_;
goto v___jp_3846_;
}
else
{
if (v___y_3860_ == 0)
{
v___y_3810_ = v___y_3860_;
v___y_3811_ = v___y_3861_;
v___y_3812_ = v___y_3862_;
v___y_3813_ = v___x_3867_;
v___y_3814_ = v___y_3863_;
v___y_3815_ = v___y_3864_;
goto v___jp_3809_;
}
else
{
v___y_3847_ = v___y_3861_;
v___y_3848_ = v___y_3862_;
v___y_3849_ = v___y_3863_;
v___y_3850_ = v___x_3867_;
v___y_3851_ = v___y_3864_;
goto v___jp_3846_;
}
}
}
}
v___jp_3869_:
{
lean_object* v___x_3870_; 
v___x_3870_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2980_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v___x_3872_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3873_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2994_, v___x_3872_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = lean_io_mono_nanos_now();
v___x_3875_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2988_, v___f_2997_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; lean_object* v_fst_3877_; lean_object* v_snd_3878_; lean_object* v___x_3879_; lean_object* v___f_3880_; lean_object* v___x_3881_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___x_3875_, 1);
v_fst_3877_ = lean_ctor_get(v_a_3876_, 0);
lean_inc_n(v_fst_3877_, 2);
v_snd_3878_ = lean_ctor_get(v_a_3876_, 1);
lean_inc(v_snd_3878_);
lean_dec(v_a_3876_);
v___x_3879_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3878_, v___x_2985_);
lean_inc(v___x_3879_);
v___f_3880_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3880_, 0, v_fst_3877_);
lean_closure_set(v___f_3880_, 1, v___x_3879_);
v___x_3881_ = lean_box(0);
if (v___x_3081_ == 0)
{
lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3882_ = l_Lean_trace_profiler;
v___x_3883_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2994_, v___x_3882_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; 
lean_dec_ref(v___f_3880_);
v___x_3884_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2996_, v___x_3873_, v_goals_2975_, v___x_3881_, v_a_2978_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3886_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
v___x_3886_ = l_List_reverse___redArg(v_a_3885_);
v___y_3463_ = v_a_3871_;
v___y_3464_ = v___x_3879_;
v___y_3465_ = v___x_3874_;
v___y_3466_ = v___x_3883_;
v___y_3467_ = v_fst_3877_;
v_a_3468_ = v___x_3886_;
goto v___jp_3462_;
}
else
{
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3887_; 
v_a_3887_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3884_, 1);
v___y_3463_ = v_a_3871_;
v___y_3464_ = v___x_3879_;
v___y_3465_ = v___x_3874_;
v___y_3466_ = v___x_3883_;
v___y_3467_ = v_fst_3877_;
v_a_3468_ = v_a_3887_;
goto v___jp_3462_;
}
else
{
lean_object* v_a_3888_; 
lean_dec(v___x_3879_);
lean_dec(v_fst_3877_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3888_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3884_, 1);
v___y_3113_ = v_a_3871_;
v___y_3114_ = v___x_3874_;
v_a_3115_ = v_a_3888_;
goto v___jp_3112_;
}
}
}
else
{
v___y_3422_ = v___x_3081_;
v___y_3423_ = v_a_3871_;
v___y_3424_ = v___x_3879_;
v___y_3425_ = v___x_3874_;
v___y_3426_ = v___x_3881_;
v___y_3427_ = v___f_3880_;
v___y_3428_ = v_fst_3877_;
v___y_3429_ = v___x_3873_;
goto v___jp_3421_;
}
}
else
{
v___y_3422_ = v___x_3081_;
v___y_3423_ = v_a_3871_;
v___y_3424_ = v___x_3879_;
v___y_3425_ = v___x_3874_;
v___y_3426_ = v___x_3881_;
v___y_3427_ = v___f_3880_;
v___y_3428_ = v_fst_3877_;
v___y_3429_ = v___x_3873_;
goto v___jp_3421_;
}
}
else
{
lean_object* v_a_3889_; 
lean_dec(v_snd_2989_);
lean_dec(v_goals_2975_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3889_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___x_3875_, 1);
v___y_3113_ = v_a_3871_;
v___y_3114_ = v___x_3874_;
v_a_3115_ = v_a_3889_;
goto v___jp_3112_;
}
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
lean_del_object(v___x_2991_);
v___x_3890_ = lean_io_get_num_heartbeats();
v___x_3891_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2988_, v___f_2997_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v_fst_3893_; lean_object* v_snd_3894_; lean_object* v___x_3895_; lean_object* v___f_3896_; lean_object* v___x_3897_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3891_, 1);
v_fst_3893_ = lean_ctor_get(v_a_3892_, 0);
lean_inc_n(v_fst_3893_, 2);
v_snd_3894_ = lean_ctor_get(v_a_3892_, 1);
lean_inc(v_snd_3894_);
lean_dec(v_a_3892_);
v___x_3895_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3894_, v___x_2985_);
lean_inc(v___x_3895_);
v___f_3896_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3896_, 0, v_fst_3893_);
lean_closure_set(v___f_3896_, 1, v___x_3895_);
v___x_3897_ = lean_box(0);
if (v___x_3081_ == 0)
{
lean_object* v___x_3898_; uint8_t v___x_3899_; 
v___x_3898_ = l_Lean_trace_profiler;
v___x_3899_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2994_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; 
lean_dec_ref(v___f_3896_);
v___x_3900_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3873_, v___x_2993_, v_goals_2975_, v___x_3897_, v_a_2978_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3902_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref_known(v___x_3900_, 1);
v___x_3902_ = l_List_reverse___redArg(v_a_3901_);
v___y_3860_ = v___x_3899_;
v___y_3861_ = v_a_3871_;
v___y_3862_ = v___x_3890_;
v___y_3863_ = v_fst_3893_;
v___y_3864_ = v___x_3895_;
v_a_3865_ = v___x_3902_;
goto v___jp_3859_;
}
else
{
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3903_; 
v_a_3903_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3900_, 1);
v___y_3860_ = v___x_3899_;
v___y_3861_ = v_a_3871_;
v___y_3862_ = v___x_3890_;
v___y_3863_ = v_fst_3893_;
v___y_3864_ = v___x_3895_;
v_a_3865_ = v_a_3903_;
goto v___jp_3859_;
}
else
{
lean_object* v_a_3904_; 
lean_dec(v___x_3895_);
lean_dec(v_fst_3893_);
lean_dec(v_snd_2989_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3904_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3900_, 1);
v___y_3485_ = v_a_3871_;
v___y_3486_ = v___x_3890_;
v_a_3487_ = v_a_3904_;
goto v___jp_3484_;
}
}
}
else
{
v___y_3780_ = v___f_3896_;
v___y_3781_ = v_a_3871_;
v___y_3782_ = v___x_3081_;
v___y_3783_ = v___x_3890_;
v___y_3784_ = v___x_3897_;
v___y_3785_ = v_fst_3893_;
v___y_3786_ = v___x_3895_;
v___y_3787_ = v___x_3873_;
goto v___jp_3779_;
}
}
else
{
v___y_3780_ = v___f_3896_;
v___y_3781_ = v_a_3871_;
v___y_3782_ = v___x_3081_;
v___y_3783_ = v___x_3890_;
v___y_3784_ = v___x_3897_;
v___y_3785_ = v_fst_3893_;
v___y_3786_ = v___x_3895_;
v___y_3787_ = v___x_3873_;
goto v___jp_3779_;
}
}
else
{
lean_object* v_a_3905_; 
lean_dec(v_snd_2989_);
lean_dec(v_goals_2975_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec_ref(v_cfg_2971_);
v_a_3905_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3891_, 1);
v___y_3485_ = v_a_3871_;
v___y_3486_ = v___x_3890_;
v_a_3487_ = v_a_3905_;
goto v___jp_3484_;
}
}
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec_ref(v___f_3077_);
lean_dec_ref(v___f_2997_);
lean_del_object(v___x_2991_);
lean_dec(v_snd_2989_);
lean_dec(v_fst_2988_);
lean_dec(v_goals_2975_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
v_a_3906_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3870_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3870_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
}
}
else
{
lean_object* v_maxDepth_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
lean_del_object(v___x_2991_);
lean_dec(v_snd_2989_);
lean_dec(v_fst_2988_);
lean_dec(v_goals_2975_);
v_maxDepth_4194_ = lean_ctor_get(v_cfg_2971_, 0);
lean_inc(v_maxDepth_4194_);
v___x_4195_ = lean_box(0);
v___x_4196_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2971_, v_trace_2972_, v_next_2973_, v_orig_2974_, v_maxDepth_4194_, v_remaining_2976_, v___x_4195_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
return v___x_4196_;
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec(v_remaining_2976_);
lean_dec(v_goals_2975_);
lean_dec(v_orig_2974_);
lean_dec_ref(v_next_2973_);
lean_dec(v_trace_2972_);
lean_dec_ref(v_cfg_2971_);
v_a_4198_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_2986_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_2986_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
v___jp_2982_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
v___x_2984_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_2983_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_);
return v___x_2984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_4206_, lean_object* v_trace_4207_, lean_object* v_next_4208_, lean_object* v_orig_4209_, lean_object* v_goals_4210_, lean_object* v_remaining_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_){
_start:
{
lean_object* v_res_4217_; 
v_res_4217_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4206_, v_trace_4207_, v_next_4208_, v_orig_4209_, v_goals_4210_, v_remaining_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_4218_, lean_object* v_00_u03b2_4219_, lean_object* v_L_4220_, lean_object* v_f_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_4220_, v_f_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_4228_, lean_object* v_00_u03b2_4229_, lean_object* v_L_4230_, lean_object* v_f_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_4228_, v_00_u03b2_4229_, v_L_4230_, v_f_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_4238_, lean_object* v_x_4239_, lean_object* v_x_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_4238_, v_x_4239_, v_x_4240_, v___y_4242_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_4247_, lean_object* v_x_4248_, lean_object* v_x_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
uint8_t v___x_60526__boxed_4255_; lean_object* v_res_4256_; 
v___x_60526__boxed_4255_ = lean_unbox(v___x_4247_);
v_res_4256_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_60526__boxed_4255_, v_x_4248_, v_x_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_4257_, uint8_t v___x_4258_, lean_object* v_x_4259_, lean_object* v_x_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v___x_4266_; 
v___x_4266_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_4257_, v___x_4258_, v_x_4259_, v_x_4260_, v___y_4262_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_4267_, lean_object* v___x_4268_, lean_object* v_x_4269_, lean_object* v_x_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
uint8_t v___x_60552__boxed_4276_; uint8_t v___x_60553__boxed_4277_; lean_object* v_res_4278_; 
v___x_60552__boxed_4276_ = lean_unbox(v___x_4267_);
v___x_60553__boxed_4277_ = lean_unbox(v___x_4268_);
v_res_4278_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_60552__boxed_4276_, v___x_60553__boxed_4277_, v_x_4269_, v_x_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_4279_, lean_object* v_00_u03b2_4280_, lean_object* v_f_4281_, lean_object* v_x_4282_, lean_object* v_x_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_4281_, v_x_4282_, v_x_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4290_, lean_object* v_00_u03b2_4291_, lean_object* v_f_4292_, lean_object* v_x_4293_, lean_object* v_x_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_4290_, v_00_u03b2_4291_, v_f_4292_, v_x_4293_, v_x_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_4301_, lean_object* v_00_u03b2_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_4303_, v_a_4304_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_4306_, lean_object* v_00_u03b2_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_4308_, v_a_4309_);
return v___x_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_4311_, lean_object* v_g_4312_, lean_object* v_f_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
lean_object* v___x_4319_; 
lean_inc(v___y_4317_);
lean_inc_ref(v___y_4316_);
lean_inc(v___y_4315_);
lean_inc_ref(v___y_4314_);
v___x_4319_ = lean_apply_6(v_next_4311_, v_g_4312_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, lean_box(0));
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4321_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4319_, 1);
v___x_4321_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_4320_, v_f_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_);
return v___x_4321_;
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec_ref(v_f_4313_);
v_a_4322_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4319_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4319_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_4330_, lean_object* v_g_4331_, lean_object* v_f_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_4330_, v_g_4331_, v_f_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
return v_res_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_4339_, lean_object* v_trace_4340_, lean_object* v_next_4341_, lean_object* v_goals_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_){
_start:
{
lean_object* v_resolve_4348_; lean_object* v___x_4349_; 
v_resolve_4348_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_4348_, 0, v_next_4341_);
lean_inc_n(v_goals_4342_, 2);
v___x_4349_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4339_, v_trace_4340_, v_resolve_4348_, v_goals_4342_, v_goals_4342_, v_goals_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_);
return v___x_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_4350_, lean_object* v_trace_4351_, lean_object* v_next_4352_, lean_object* v_goals_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_4350_, v_trace_4351_, v_next_4352_, v_goals_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
return v_res_4359_;
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

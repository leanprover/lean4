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
lean_object* v___x_312_; lean_object* v_env_313_; lean_object* v___x_314_; lean_object* v_toCold_315_; lean_object* v_mctx_316_; lean_object* v_lctx_317_; lean_object* v_options_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_312_ = lean_st_ref_get(v___y_310_);
v_env_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc_ref(v_env_313_);
lean_dec(v___x_312_);
v___x_314_ = lean_st_ref_get(v___y_308_);
v_toCold_315_ = lean_ctor_get(v___y_309_, 0);
v_mctx_316_ = lean_ctor_get(v___x_314_, 0);
lean_inc_ref(v_mctx_316_);
lean_dec(v___x_314_);
v_lctx_317_ = lean_ctor_get(v___y_307_, 2);
v_options_318_ = lean_ctor_get(v_toCold_315_, 2);
lean_inc_ref(v_options_318_);
lean_inc_ref(v_lctx_317_);
v___x_319_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_319_, 0, v_env_313_);
lean_ctor_set(v___x_319_, 1, v_mctx_316_);
lean_ctor_set(v___x_319_, 2, v_lctx_317_);
lean_ctor_set(v___x_319_, 3, v_options_318_);
v___x_320_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_msgData_306_);
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___boxed(lean_object* v_msgData_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msgData_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
return v_res_328_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0));
v___x_331_ = l_Lean_stringToMessageData(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object* v_x_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object* v_x_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(v_x_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec_ref(v_x_340_);
return v_res_346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0));
v___x_349_ = l_Lean_stringToMessageData(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object* v_x_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object* v_x_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(v_x_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec_ref(v_x_358_);
return v_res_364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0));
v___x_367_ = l_Lean_stringToMessageData(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object* v_x_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object* v_x_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(v_x_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec_ref(v_x_376_);
return v_res_382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object* v_x_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object* v_x_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(v_x_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec_ref(v_x_394_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(lean_object* v_opts_401_, lean_object* v_opt_402_){
_start:
{
lean_object* v_name_403_; lean_object* v_defValue_404_; lean_object* v_map_405_; lean_object* v___x_406_; 
v_name_403_ = lean_ctor_get(v_opt_402_, 0);
v_defValue_404_ = lean_ctor_get(v_opt_402_, 1);
v_map_405_ = lean_ctor_get(v_opts_401_, 0);
v___x_406_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_405_, v_name_403_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_inc(v_defValue_404_);
return v_defValue_404_;
}
else
{
lean_object* v_val_407_; 
v_val_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_val_407_);
lean_dec_ref_known(v___x_406_, 1);
if (lean_obj_tag(v_val_407_) == 3)
{
lean_object* v_v_408_; 
v_v_408_ = lean_ctor_get(v_val_407_, 0);
lean_inc(v_v_408_);
lean_dec_ref_known(v_val_407_, 1);
return v_v_408_;
}
else
{
lean_dec(v_val_407_);
lean_inc(v_defValue_404_);
return v_defValue_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6___boxed(lean_object* v_opts_409_, lean_object* v_opt_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_409_, v_opt_410_);
lean_dec_ref(v_opt_410_);
lean_dec_ref(v_opts_409_);
return v_res_411_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object* v_e_412_){
_start:
{
if (lean_obj_tag(v_e_412_) == 0)
{
uint8_t v___x_413_; 
v___x_413_ = 2;
return v___x_413_;
}
else
{
lean_object* v_a_414_; 
v_a_414_ = lean_ctor_get(v_e_412_, 0);
if (lean_obj_tag(v_a_414_) == 0)
{
uint8_t v___x_415_; 
v___x_415_ = 1;
return v___x_415_;
}
else
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object* v_e_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_e_417_);
lean_dec_ref(v_e_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_420_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
v_a_422_ = lean_ctor_get(v_x_420_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v_x_420_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v_x_420_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v_x_420_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 1);
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_a_430_ = lean_ctor_get(v_x_420_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_420_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v_x_420_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v_x_420_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set_tag(v___x_432_, 0);
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg___boxed(lean_object* v_x_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(size_t v_sz_441_, size_t v_i_442_, lean_object* v_bs_443_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_usize_dec_lt(v_i_442_, v_sz_441_);
if (v___x_444_ == 0)
{
return v_bs_443_;
}
else
{
lean_object* v_v_445_; lean_object* v_msg_446_; lean_object* v___x_447_; lean_object* v_bs_x27_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v_v_445_ = lean_array_uget_borrowed(v_bs_443_, v_i_442_);
v_msg_446_ = lean_ctor_get(v_v_445_, 1);
lean_inc_ref(v_msg_446_);
v___x_447_ = lean_unsigned_to_nat(0u);
v_bs_x27_448_ = lean_array_uset(v_bs_443_, v_i_442_, v___x_447_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_442_, v___x_449_);
v___x_451_ = lean_array_uset(v_bs_x27_448_, v_i_442_, v_msg_446_);
v_i_442_ = v___x_450_;
v_bs_443_ = v___x_451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6___boxed(lean_object* v_sz_453_, lean_object* v_i_454_, lean_object* v_bs_455_){
_start:
{
size_t v_sz_boxed_456_; size_t v_i_boxed_457_; lean_object* v_res_458_; 
v_sz_boxed_456_ = lean_unbox_usize(v_sz_453_);
lean_dec(v_sz_453_);
v_i_boxed_457_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_res_458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_boxed_456_, v_i_boxed_457_, v_bs_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object* v_oldTraces_459_, lean_object* v_data_460_, lean_object* v_ref_461_, lean_object* v_msg_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_toCold_468_; lean_object* v_currRecDepth_469_; lean_object* v_ref_470_; uint16_t v_optionFlags_471_; uint8_t v_suppressElabErrors_472_; uint8_t v_isRecordingDeps_473_; lean_object* v_ref_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_traceState_477_; lean_object* v_traces_478_; lean_object* v___x_479_; size_t v_sz_480_; size_t v___x_481_; lean_object* v___x_482_; lean_object* v_msg_483_; lean_object* v___x_484_; lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_523_; 
v_toCold_468_ = lean_ctor_get(v___y_465_, 0);
v_currRecDepth_469_ = lean_ctor_get(v___y_465_, 1);
v_ref_470_ = lean_ctor_get(v___y_465_, 2);
v_optionFlags_471_ = lean_ctor_get_uint16(v___y_465_, sizeof(void*)*3);
v_suppressElabErrors_472_ = lean_ctor_get_uint8(v___y_465_, sizeof(void*)*3 + 2);
v_isRecordingDeps_473_ = lean_ctor_get_uint8(v___y_465_, sizeof(void*)*3 + 3);
v_ref_474_ = l_Lean_replaceRef(v_ref_461_, v_ref_470_);
lean_inc(v_currRecDepth_469_);
lean_inc_ref(v_toCold_468_);
v___x_475_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_475_, 0, v_toCold_468_);
lean_ctor_set(v___x_475_, 1, v_currRecDepth_469_);
lean_ctor_set(v___x_475_, 2, v_ref_474_);
lean_ctor_set_uint16(v___x_475_, sizeof(void*)*3, v_optionFlags_471_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*3 + 2, v_suppressElabErrors_472_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*3 + 3, v_isRecordingDeps_473_);
v___x_476_ = lean_st_ref_get(v___y_466_);
v_traceState_477_ = lean_ctor_get(v___x_476_, 4);
lean_inc_ref(v_traceState_477_);
lean_dec(v___x_476_);
v_traces_478_ = lean_ctor_get(v_traceState_477_, 0);
lean_inc_ref(v_traces_478_);
lean_dec_ref(v_traceState_477_);
v___x_479_ = l_Lean_PersistentArray_toArray___redArg(v_traces_478_);
lean_dec_ref(v_traces_478_);
v_sz_480_ = lean_array_size(v___x_479_);
v___x_481_ = ((size_t)0ULL);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_480_, v___x_481_, v___x_479_);
v_msg_483_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_483_, 0, v_data_460_);
lean_ctor_set(v_msg_483_, 1, v_msg_462_);
lean_ctor_set(v_msg_483_, 2, v___x_482_);
v___x_484_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_483_, v___y_463_, v___y_464_, v___x_475_, v___y_466_);
lean_dec_ref_known(v___x_475_, 3);
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_523_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_523_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_523_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v_traceState_490_; lean_object* v_env_491_; lean_object* v_nextMacroScope_492_; lean_object* v_ngen_493_; lean_object* v_auxDeclNGen_494_; lean_object* v_cache_495_; lean_object* v_recordedDeps_496_; lean_object* v_messages_497_; lean_object* v_infoState_498_; lean_object* v_snapshotTasks_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_522_; 
v___x_489_ = lean_st_ref_take(v___y_466_);
v_traceState_490_ = lean_ctor_get(v___x_489_, 4);
v_env_491_ = lean_ctor_get(v___x_489_, 0);
v_nextMacroScope_492_ = lean_ctor_get(v___x_489_, 1);
v_ngen_493_ = lean_ctor_get(v___x_489_, 2);
v_auxDeclNGen_494_ = lean_ctor_get(v___x_489_, 3);
v_cache_495_ = lean_ctor_get(v___x_489_, 5);
v_recordedDeps_496_ = lean_ctor_get(v___x_489_, 6);
v_messages_497_ = lean_ctor_get(v___x_489_, 7);
v_infoState_498_ = lean_ctor_get(v___x_489_, 8);
v_snapshotTasks_499_ = lean_ctor_get(v___x_489_, 9);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_522_ == 0)
{
v___x_501_ = v___x_489_;
v_isShared_502_ = v_isSharedCheck_522_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_snapshotTasks_499_);
lean_inc(v_infoState_498_);
lean_inc(v_messages_497_);
lean_inc(v_recordedDeps_496_);
lean_inc(v_cache_495_);
lean_inc(v_traceState_490_);
lean_inc(v_auxDeclNGen_494_);
lean_inc(v_ngen_493_);
lean_inc(v_nextMacroScope_492_);
lean_inc(v_env_491_);
lean_dec(v___x_489_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_522_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
uint64_t v_tid_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_520_; 
v_tid_503_ = lean_ctor_get_uint64(v_traceState_490_, sizeof(void*)*1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_traceState_490_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v_traceState_490_, 0);
lean_dec(v_unused_521_);
v___x_505_ = v_traceState_490_;
v_isShared_506_ = v_isSharedCheck_520_;
goto v_resetjp_504_;
}
else
{
lean_dec(v_traceState_490_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_520_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_ref_461_);
lean_ctor_set(v___x_508_, 1, v_a_485_);
v___x_509_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_459_, v___x_508_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_509_);
v___x_511_ = v___x_505_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_509_);
lean_ctor_set_uint64(v_reuseFailAlloc_519_, sizeof(void*)*1, v_tid_503_);
v___x_511_ = v_reuseFailAlloc_519_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 4, v___x_511_);
v___x_513_ = v___x_501_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_env_491_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_nextMacroScope_492_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_ngen_493_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_auxDeclNGen_494_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_518_, 5, v_cache_495_);
lean_ctor_set(v_reuseFailAlloc_518_, 6, v_recordedDeps_496_);
lean_ctor_set(v_reuseFailAlloc_518_, 7, v_messages_497_);
lean_ctor_set(v_reuseFailAlloc_518_, 8, v_infoState_498_);
lean_ctor_set(v_reuseFailAlloc_518_, 9, v_snapshotTasks_499_);
v___x_513_ = v_reuseFailAlloc_518_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_st_ref_put(v___y_466_, v___x_513_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_507_);
v___x_516_ = v___x_487_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_507_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object* v_oldTraces_524_, lean_object* v_data_525_, lean_object* v_ref_526_, lean_object* v_msg_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_524_, v_data_525_, v_ref_526_, v_msg_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_533_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0(void){
_start:
{
lean_object* v___x_534_; double v___x_535_; 
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = lean_float_of_nat(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1));
v___x_538_ = l_Lean_stringToMessageData(v___x_537_);
return v___x_538_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3(void){
_start:
{
lean_object* v___x_539_; double v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(1000u);
v___x_540_ = lean_float_of_nat(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_cls_541_, uint8_t v_collapsed_542_, lean_object* v_tag_543_, lean_object* v_opts_544_, uint8_t v_clsEnabled_545_, lean_object* v_oldTraces_546_, lean_object* v_msg_547_, lean_object* v_resStartStop_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v_data_559_; lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___y_575_; lean_object* v_a_576_; uint8_t v___y_591_; double v___y_623_; 
v_fst_554_ = lean_ctor_get(v_resStartStop_548_, 0);
lean_inc(v_fst_554_);
v_snd_555_ = lean_ctor_get(v_resStartStop_548_, 1);
lean_inc(v_snd_555_);
lean_dec_ref(v_resStartStop_548_);
v_fst_570_ = lean_ctor_get(v_snd_555_, 0);
lean_inc(v_fst_570_);
v_snd_571_ = lean_ctor_get(v_snd_555_, 1);
lean_inc(v_snd_571_);
lean_dec(v_snd_555_);
v___x_572_ = l_Lean_trace_profiler;
v___x_573_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_544_, v___x_572_);
if (v___x_573_ == 0)
{
v___y_591_ = v___x_573_;
goto v___jp_590_;
}
else
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = l_Lean_trace_profiler_useHeartbeats;
v___x_629_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_544_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; double v___x_632_; double v___x_633_; double v___x_634_; 
v___x_630_ = l_Lean_trace_profiler_threshold;
v___x_631_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_544_, v___x_630_);
v___x_632_ = lean_float_of_nat(v___x_631_);
v___x_633_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_634_ = lean_float_div(v___x_632_, v___x_633_);
v___y_623_ = v___x_634_;
goto v___jp_622_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; double v___x_637_; 
v___x_635_ = l_Lean_trace_profiler_threshold;
v___x_636_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_544_, v___x_635_);
v___x_637_ = lean_float_of_nat(v___x_636_);
v___y_623_ = v___x_637_;
goto v___jp_622_;
}
}
v___jp_556_:
{
lean_object* v___x_560_; 
lean_inc(v___y_557_);
v___x_560_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_546_, v_data_559_, v___y_557_, v___y_558_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___x_561_; 
lean_dec_ref_known(v___x_560_, 1);
v___x_561_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_554_);
return v___x_561_;
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_fst_554_);
v_a_562_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_560_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
v___jp_574_:
{
uint8_t v_result_577_; lean_object* v___x_578_; lean_object* v___x_579_; double v___x_580_; lean_object* v_data_581_; 
v_result_577_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_fst_554_);
v___x_578_ = lean_box(v_result_577_);
v___x_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
v___x_580_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_543_);
lean_inc_ref(v___x_579_);
lean_inc(v_cls_541_);
v_data_581_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_581_, 0, v_cls_541_);
lean_ctor_set(v_data_581_, 1, v___x_579_);
lean_ctor_set(v_data_581_, 2, v_tag_543_);
lean_ctor_set_float(v_data_581_, sizeof(void*)*3, v___x_580_);
lean_ctor_set_float(v_data_581_, sizeof(void*)*3 + 8, v___x_580_);
lean_ctor_set_uint8(v_data_581_, sizeof(void*)*3 + 16, v_collapsed_542_);
if (v___x_573_ == 0)
{
lean_dec_ref_known(v___x_579_, 1);
lean_dec(v_snd_571_);
lean_dec(v_fst_570_);
lean_dec_ref(v_tag_543_);
lean_dec(v_cls_541_);
v___y_557_ = v___y_575_;
v___y_558_ = v_a_576_;
v_data_559_ = v_data_581_;
goto v___jp_556_;
}
else
{
lean_object* v_data_582_; double v___x_583_; double v___x_584_; 
lean_dec_ref_known(v_data_581_, 3);
v_data_582_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_582_, 0, v_cls_541_);
lean_ctor_set(v_data_582_, 1, v___x_579_);
lean_ctor_set(v_data_582_, 2, v_tag_543_);
v___x_583_ = lean_unbox_float(v_fst_570_);
lean_dec(v_fst_570_);
lean_ctor_set_float(v_data_582_, sizeof(void*)*3, v___x_583_);
v___x_584_ = lean_unbox_float(v_snd_571_);
lean_dec(v_snd_571_);
lean_ctor_set_float(v_data_582_, sizeof(void*)*3 + 8, v___x_584_);
lean_ctor_set_uint8(v_data_582_, sizeof(void*)*3 + 16, v_collapsed_542_);
v___y_557_ = v___y_575_;
v___y_558_ = v_a_576_;
v_data_559_ = v_data_582_;
goto v___jp_556_;
}
}
v___jp_585_:
{
lean_object* v_ref_586_; lean_object* v___x_587_; 
v_ref_586_ = lean_ctor_get(v___y_551_, 2);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v_fst_554_);
v___x_587_ = lean_apply_6(v_msg_547_, v_fst_554_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, lean_box(0));
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___y_575_ = v_ref_586_;
v_a_576_ = v_a_588_;
goto v___jp_574_;
}
else
{
lean_object* v___x_589_; 
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_575_ = v_ref_586_;
v_a_576_ = v___x_589_;
goto v___jp_574_;
}
}
v___jp_590_:
{
if (v_clsEnabled_545_ == 0)
{
if (v___y_591_ == 0)
{
lean_object* v___x_592_; lean_object* v_traceState_593_; lean_object* v_env_594_; lean_object* v_nextMacroScope_595_; lean_object* v_ngen_596_; lean_object* v_auxDeclNGen_597_; lean_object* v_cache_598_; lean_object* v_recordedDeps_599_; lean_object* v_messages_600_; lean_object* v_infoState_601_; lean_object* v_snapshotTasks_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_621_; 
lean_dec(v_snd_571_);
lean_dec(v_fst_570_);
lean_dec_ref(v_msg_547_);
lean_dec_ref(v_tag_543_);
lean_dec(v_cls_541_);
v___x_592_ = lean_st_ref_take(v___y_552_);
v_traceState_593_ = lean_ctor_get(v___x_592_, 4);
v_env_594_ = lean_ctor_get(v___x_592_, 0);
v_nextMacroScope_595_ = lean_ctor_get(v___x_592_, 1);
v_ngen_596_ = lean_ctor_get(v___x_592_, 2);
v_auxDeclNGen_597_ = lean_ctor_get(v___x_592_, 3);
v_cache_598_ = lean_ctor_get(v___x_592_, 5);
v_recordedDeps_599_ = lean_ctor_get(v___x_592_, 6);
v_messages_600_ = lean_ctor_get(v___x_592_, 7);
v_infoState_601_ = lean_ctor_get(v___x_592_, 8);
v_snapshotTasks_602_ = lean_ctor_get(v___x_592_, 9);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_621_ == 0)
{
v___x_604_ = v___x_592_;
v_isShared_605_ = v_isSharedCheck_621_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_snapshotTasks_602_);
lean_inc(v_infoState_601_);
lean_inc(v_messages_600_);
lean_inc(v_recordedDeps_599_);
lean_inc(v_cache_598_);
lean_inc(v_traceState_593_);
lean_inc(v_auxDeclNGen_597_);
lean_inc(v_ngen_596_);
lean_inc(v_nextMacroScope_595_);
lean_inc(v_env_594_);
lean_dec(v___x_592_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_621_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
uint64_t v_tid_606_; lean_object* v_traces_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_620_; 
v_tid_606_ = lean_ctor_get_uint64(v_traceState_593_, sizeof(void*)*1);
v_traces_607_ = lean_ctor_get(v_traceState_593_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_traceState_593_);
if (v_isSharedCheck_620_ == 0)
{
v___x_609_ = v_traceState_593_;
v_isShared_610_ = v_isSharedCheck_620_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_traces_607_);
lean_dec(v_traceState_593_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_620_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_546_, v_traces_607_);
lean_dec_ref(v_traces_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_611_);
lean_ctor_set_uint64(v_reuseFailAlloc_619_, sizeof(void*)*1, v_tid_606_);
v___x_613_ = v_reuseFailAlloc_619_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 4, v___x_613_);
v___x_615_ = v___x_604_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_env_594_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_nextMacroScope_595_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_ngen_596_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_auxDeclNGen_597_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_618_, 5, v_cache_598_);
lean_ctor_set(v_reuseFailAlloc_618_, 6, v_recordedDeps_599_);
lean_ctor_set(v_reuseFailAlloc_618_, 7, v_messages_600_);
lean_ctor_set(v_reuseFailAlloc_618_, 8, v_infoState_601_);
lean_ctor_set(v_reuseFailAlloc_618_, 9, v_snapshotTasks_602_);
v___x_615_ = v_reuseFailAlloc_618_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_st_ref_put(v___y_552_, v___x_615_);
v___x_617_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_554_);
return v___x_617_;
}
}
}
}
}
else
{
goto v___jp_585_;
}
}
else
{
goto v___jp_585_;
}
}
v___jp_622_:
{
double v___x_624_; double v___x_625_; double v___x_626_; uint8_t v___x_627_; 
v___x_624_ = lean_unbox_float(v_snd_571_);
v___x_625_ = lean_unbox_float(v_fst_570_);
v___x_626_ = lean_float_sub(v___x_624_, v___x_625_);
v___x_627_ = lean_float_decLt(v___y_623_, v___x_626_);
v___y_591_ = v___x_627_;
goto v___jp_590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_cls_638_, lean_object* v_collapsed_639_, lean_object* v_tag_640_, lean_object* v_opts_641_, lean_object* v_clsEnabled_642_, lean_object* v_oldTraces_643_, lean_object* v_msg_644_, lean_object* v_resStartStop_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
uint8_t v_collapsed_boxed_651_; uint8_t v_clsEnabled_boxed_652_; lean_object* v_res_653_; 
v_collapsed_boxed_651_ = lean_unbox(v_collapsed_639_);
v_clsEnabled_boxed_652_ = lean_unbox(v_clsEnabled_642_);
v_res_653_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_cls_638_, v_collapsed_boxed_651_, v_tag_640_, v_opts_641_, v_clsEnabled_boxed_652_, v_oldTraces_643_, v_msg_644_, v_resStartStop_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v_opts_641_);
return v_res_653_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* v_head_657_, lean_object* v_x_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_675_; 
v___x_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_664_, 0, v_head_657_);
v___x_665_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v___x_664_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_675_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_675_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_675_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v_a_666_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_671_);
v___x_673_ = v___x_668_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* v_head_676_, lean_object* v_x_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_head_676_, v_x_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec_ref(v_x_677_);
return v_res_683_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object* v_keys_684_, lean_object* v_i_685_, lean_object* v_k_686_){
_start:
{
lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_687_ = lean_array_get_size(v_keys_684_);
v___x_688_ = lean_nat_dec_lt(v_i_685_, v___x_687_);
if (v___x_688_ == 0)
{
lean_dec(v_i_685_);
return v___x_688_;
}
else
{
lean_object* v_k_x27_689_; uint8_t v___x_690_; 
v_k_x27_689_ = lean_array_fget_borrowed(v_keys_684_, v_i_685_);
v___x_690_ = l_Lean_instBEqMVarId_beq(v_k_686_, v_k_x27_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_nat_add(v_i_685_, v___x_691_);
lean_dec(v_i_685_);
v_i_685_ = v___x_692_;
goto _start;
}
else
{
lean_dec(v_i_685_);
return v___x_688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object* v_keys_694_, lean_object* v_i_695_, lean_object* v_k_696_){
_start:
{
uint8_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_694_, v_i_695_, v_k_696_);
lean_dec(v_k_696_);
lean_dec_ref(v_keys_694_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_699_, size_t v_x_700_, lean_object* v_x_701_){
_start:
{
if (lean_obj_tag(v_x_699_) == 0)
{
lean_object* v_es_702_; lean_object* v___x_703_; size_t v___x_704_; size_t v___x_705_; lean_object* v_j_706_; lean_object* v___x_707_; 
v_es_702_ = lean_ctor_get(v_x_699_, 0);
v___x_703_ = lean_box(2);
v___x_704_ = ((size_t)31ULL);
v___x_705_ = lean_usize_land(v_x_700_, v___x_704_);
v_j_706_ = lean_usize_to_nat(v___x_705_);
v___x_707_ = lean_array_get_borrowed(v___x_703_, v_es_702_, v_j_706_);
lean_dec(v_j_706_);
switch(lean_obj_tag(v___x_707_))
{
case 0:
{
lean_object* v_key_708_; uint8_t v___x_709_; 
v_key_708_ = lean_ctor_get(v___x_707_, 0);
v___x_709_ = l_Lean_instBEqMVarId_beq(v_x_701_, v_key_708_);
return v___x_709_;
}
case 1:
{
lean_object* v_node_710_; size_t v___x_711_; size_t v___x_712_; 
v_node_710_ = lean_ctor_get(v___x_707_, 0);
v___x_711_ = ((size_t)5ULL);
v___x_712_ = lean_usize_shift_right(v_x_700_, v___x_711_);
v_x_699_ = v_node_710_;
v_x_700_ = v___x_712_;
goto _start;
}
default: 
{
uint8_t v___x_714_; 
v___x_714_ = 0;
return v___x_714_;
}
}
}
else
{
lean_object* v_ks_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_ks_715_ = lean_ctor_get(v_x_699_, 0);
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_ks_715_, v___x_716_, v_x_701_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
size_t v_x_74464__boxed_721_; uint8_t v_res_722_; lean_object* v_r_723_; 
v_x_74464__boxed_721_ = lean_unbox_usize(v_x_719_);
lean_dec(v_x_719_);
v_res_722_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_718_, v_x_74464__boxed_721_, v_x_720_);
lean_dec(v_x_720_);
lean_dec_ref(v_x_718_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object* v_x_724_, lean_object* v_x_725_){
_start:
{
uint64_t v___x_726_; size_t v___x_727_; uint8_t v___x_728_; 
v___x_726_ = l_Lean_instHashableMVarId_hash(v_x_725_);
v___x_727_ = lean_uint64_to_usize(v___x_726_);
v___x_728_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_724_, v___x_727_, v_x_725_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
uint8_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_729_, v_x_730_);
lean_dec(v_x_730_);
lean_dec_ref(v_x_729_);
v_r_732_ = lean_box(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object* v_mvarId_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; lean_object* v_mctx_737_; lean_object* v_eAssignment_738_; uint8_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_736_ = lean_st_ref_get(v___y_734_);
v_mctx_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc_ref(v_mctx_737_);
lean_dec(v___x_736_);
v_eAssignment_738_ = lean_ctor_get(v_mctx_737_, 8);
lean_inc_ref(v_eAssignment_738_);
lean_dec_ref(v_mctx_737_);
v___x_739_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_eAssignment_738_, v_mvarId_733_);
lean_dec_ref(v_eAssignment_738_);
v___x_740_ = lean_box(v___x_739_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object* v_mvarId_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec(v_mvarId_742_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_ref_752_; lean_object* v___x_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_ref_752_ = lean_ctor_get(v___y_749_, 2);
v___x_753_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_762_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
lean_inc(v_ref_752_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_ref_752_);
lean_ctor_set(v___x_758_, 1, v_a_754_);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 1);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_760_ = v___x_756_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_769_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_a_773_, lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_781_ = l_Lean_Exception_toMessageData(v_a_773_);
v___x_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_a_784_, lean_object* v_x_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_a_784_, v_x_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec_ref(v_x_785_);
return v_res_791_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_e_792_){
_start:
{
if (lean_obj_tag(v_e_792_) == 0)
{
uint8_t v___x_793_; 
v___x_793_ = 2;
return v___x_793_;
}
else
{
uint8_t v___x_794_; 
v___x_794_ = 0;
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_e_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_e_795_);
lean_dec_ref(v_e_795_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_798_, uint8_t v_collapsed_799_, lean_object* v_tag_800_, lean_object* v_opts_801_, uint8_t v_clsEnabled_802_, lean_object* v_oldTraces_803_, lean_object* v_msg_804_, lean_object* v_resStartStop_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_fst_811_; lean_object* v_snd_812_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v_data_816_; lean_object* v_fst_827_; lean_object* v_snd_828_; lean_object* v___x_829_; uint8_t v___x_830_; lean_object* v___y_832_; lean_object* v_a_833_; uint8_t v___y_848_; double v___y_880_; 
v_fst_811_ = lean_ctor_get(v_resStartStop_805_, 0);
lean_inc(v_fst_811_);
v_snd_812_ = lean_ctor_get(v_resStartStop_805_, 1);
lean_inc(v_snd_812_);
lean_dec_ref(v_resStartStop_805_);
v_fst_827_ = lean_ctor_get(v_snd_812_, 0);
lean_inc(v_fst_827_);
v_snd_828_ = lean_ctor_get(v_snd_812_, 1);
lean_inc(v_snd_828_);
lean_dec(v_snd_812_);
v___x_829_ = l_Lean_trace_profiler;
v___x_830_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_801_, v___x_829_);
if (v___x_830_ == 0)
{
v___y_848_ = v___x_830_;
goto v___jp_847_;
}
else
{
lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_885_ = l_Lean_trace_profiler_useHeartbeats;
v___x_886_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_801_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; double v___x_889_; double v___x_890_; double v___x_891_; 
v___x_887_ = l_Lean_trace_profiler_threshold;
v___x_888_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_801_, v___x_887_);
v___x_889_ = lean_float_of_nat(v___x_888_);
v___x_890_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_891_ = lean_float_div(v___x_889_, v___x_890_);
v___y_880_ = v___x_891_;
goto v___jp_879_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_893_; double v___x_894_; 
v___x_892_ = l_Lean_trace_profiler_threshold;
v___x_893_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_801_, v___x_892_);
v___x_894_ = lean_float_of_nat(v___x_893_);
v___y_880_ = v___x_894_;
goto v___jp_879_;
}
}
v___jp_813_:
{
lean_object* v___x_817_; 
lean_inc(v___y_814_);
v___x_817_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_803_, v_data_816_, v___y_814_, v___y_815_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_818_; 
lean_dec_ref_known(v___x_817_, 1);
v___x_818_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_811_);
return v___x_818_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_fst_811_);
v_a_819_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_817_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_817_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
v___jp_831_:
{
uint8_t v_result_834_; lean_object* v___x_835_; lean_object* v___x_836_; double v___x_837_; lean_object* v_data_838_; 
v_result_834_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_fst_811_);
v___x_835_ = lean_box(v_result_834_);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
v___x_837_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_800_);
lean_inc_ref(v___x_836_);
lean_inc(v_cls_798_);
v_data_838_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_838_, 0, v_cls_798_);
lean_ctor_set(v_data_838_, 1, v___x_836_);
lean_ctor_set(v_data_838_, 2, v_tag_800_);
lean_ctor_set_float(v_data_838_, sizeof(void*)*3, v___x_837_);
lean_ctor_set_float(v_data_838_, sizeof(void*)*3 + 8, v___x_837_);
lean_ctor_set_uint8(v_data_838_, sizeof(void*)*3 + 16, v_collapsed_799_);
if (v___x_830_ == 0)
{
lean_dec_ref_known(v___x_836_, 1);
lean_dec(v_snd_828_);
lean_dec(v_fst_827_);
lean_dec_ref(v_tag_800_);
lean_dec(v_cls_798_);
v___y_814_ = v___y_832_;
v___y_815_ = v_a_833_;
v_data_816_ = v_data_838_;
goto v___jp_813_;
}
else
{
lean_object* v_data_839_; double v___x_840_; double v___x_841_; 
lean_dec_ref_known(v_data_838_, 3);
v_data_839_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_839_, 0, v_cls_798_);
lean_ctor_set(v_data_839_, 1, v___x_836_);
lean_ctor_set(v_data_839_, 2, v_tag_800_);
v___x_840_ = lean_unbox_float(v_fst_827_);
lean_dec(v_fst_827_);
lean_ctor_set_float(v_data_839_, sizeof(void*)*3, v___x_840_);
v___x_841_ = lean_unbox_float(v_snd_828_);
lean_dec(v_snd_828_);
lean_ctor_set_float(v_data_839_, sizeof(void*)*3 + 8, v___x_841_);
lean_ctor_set_uint8(v_data_839_, sizeof(void*)*3 + 16, v_collapsed_799_);
v___y_814_ = v___y_832_;
v___y_815_ = v_a_833_;
v_data_816_ = v_data_839_;
goto v___jp_813_;
}
}
v___jp_842_:
{
lean_object* v_ref_843_; lean_object* v___x_844_; 
v_ref_843_ = lean_ctor_get(v___y_808_, 2);
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
lean_inc(v___y_807_);
lean_inc_ref(v___y_806_);
lean_inc(v_fst_811_);
v___x_844_ = lean_apply_6(v_msg_804_, v_fst_811_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, lean_box(0));
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
v___y_832_ = v_ref_843_;
v_a_833_ = v_a_845_;
goto v___jp_831_;
}
else
{
lean_object* v___x_846_; 
lean_dec_ref_known(v___x_844_, 1);
v___x_846_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_832_ = v_ref_843_;
v_a_833_ = v___x_846_;
goto v___jp_831_;
}
}
v___jp_847_:
{
if (v_clsEnabled_802_ == 0)
{
if (v___y_848_ == 0)
{
lean_object* v___x_849_; lean_object* v_traceState_850_; lean_object* v_env_851_; lean_object* v_nextMacroScope_852_; lean_object* v_ngen_853_; lean_object* v_auxDeclNGen_854_; lean_object* v_cache_855_; lean_object* v_recordedDeps_856_; lean_object* v_messages_857_; lean_object* v_infoState_858_; lean_object* v_snapshotTasks_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_878_; 
lean_dec(v_snd_828_);
lean_dec(v_fst_827_);
lean_dec_ref(v_msg_804_);
lean_dec_ref(v_tag_800_);
lean_dec(v_cls_798_);
v___x_849_ = lean_st_ref_take(v___y_809_);
v_traceState_850_ = lean_ctor_get(v___x_849_, 4);
v_env_851_ = lean_ctor_get(v___x_849_, 0);
v_nextMacroScope_852_ = lean_ctor_get(v___x_849_, 1);
v_ngen_853_ = lean_ctor_get(v___x_849_, 2);
v_auxDeclNGen_854_ = lean_ctor_get(v___x_849_, 3);
v_cache_855_ = lean_ctor_get(v___x_849_, 5);
v_recordedDeps_856_ = lean_ctor_get(v___x_849_, 6);
v_messages_857_ = lean_ctor_get(v___x_849_, 7);
v_infoState_858_ = lean_ctor_get(v___x_849_, 8);
v_snapshotTasks_859_ = lean_ctor_get(v___x_849_, 9);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_878_ == 0)
{
v___x_861_ = v___x_849_;
v_isShared_862_ = v_isSharedCheck_878_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_snapshotTasks_859_);
lean_inc(v_infoState_858_);
lean_inc(v_messages_857_);
lean_inc(v_recordedDeps_856_);
lean_inc(v_cache_855_);
lean_inc(v_traceState_850_);
lean_inc(v_auxDeclNGen_854_);
lean_inc(v_ngen_853_);
lean_inc(v_nextMacroScope_852_);
lean_inc(v_env_851_);
lean_dec(v___x_849_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_878_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
uint64_t v_tid_863_; lean_object* v_traces_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_877_; 
v_tid_863_ = lean_ctor_get_uint64(v_traceState_850_, sizeof(void*)*1);
v_traces_864_ = lean_ctor_get(v_traceState_850_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_traceState_850_);
if (v_isSharedCheck_877_ == 0)
{
v___x_866_ = v_traceState_850_;
v_isShared_867_ = v_isSharedCheck_877_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_traces_864_);
lean_dec(v_traceState_850_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_877_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_803_, v_traces_864_);
lean_dec_ref(v_traces_864_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_868_);
lean_ctor_set_uint64(v_reuseFailAlloc_876_, sizeof(void*)*1, v_tid_863_);
v___x_870_ = v_reuseFailAlloc_876_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_872_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 4, v___x_870_);
v___x_872_ = v___x_861_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_env_851_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_nextMacroScope_852_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_ngen_853_);
lean_ctor_set(v_reuseFailAlloc_875_, 3, v_auxDeclNGen_854_);
lean_ctor_set(v_reuseFailAlloc_875_, 4, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_875_, 5, v_cache_855_);
lean_ctor_set(v_reuseFailAlloc_875_, 6, v_recordedDeps_856_);
lean_ctor_set(v_reuseFailAlloc_875_, 7, v_messages_857_);
lean_ctor_set(v_reuseFailAlloc_875_, 8, v_infoState_858_);
lean_ctor_set(v_reuseFailAlloc_875_, 9, v_snapshotTasks_859_);
v___x_872_ = v_reuseFailAlloc_875_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_st_ref_put(v___y_809_, v___x_872_);
v___x_874_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_811_);
return v___x_874_;
}
}
}
}
}
else
{
goto v___jp_842_;
}
}
else
{
goto v___jp_842_;
}
}
v___jp_879_:
{
double v___x_881_; double v___x_882_; double v___x_883_; uint8_t v___x_884_; 
v___x_881_ = lean_unbox_float(v_snd_828_);
v___x_882_ = lean_unbox_float(v_fst_827_);
v___x_883_ = lean_float_sub(v___x_881_, v___x_882_);
v___x_884_ = lean_float_decLt(v___y_880_, v___x_883_);
v___y_848_ = v___x_884_;
goto v___jp_847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_895_, lean_object* v_collapsed_896_, lean_object* v_tag_897_, lean_object* v_opts_898_, lean_object* v_clsEnabled_899_, lean_object* v_oldTraces_900_, lean_object* v_msg_901_, lean_object* v_resStartStop_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
uint8_t v_collapsed_boxed_908_; uint8_t v_clsEnabled_boxed_909_; lean_object* v_res_910_; 
v_collapsed_boxed_908_ = lean_unbox(v_collapsed_896_);
v_clsEnabled_boxed_909_ = lean_unbox(v_clsEnabled_899_);
v_res_910_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_895_, v_collapsed_boxed_908_, v_tag_897_, v_opts_898_, v_clsEnabled_boxed_909_, v_oldTraces_900_, v_msg_901_, v_resStartStop_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec_ref(v_opts_898_);
return v_res_910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__0));
v___x_913_ = l_Lean_stringToMessageData(v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(lean_object* v_head_914_, lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_921_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1);
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v_head_914_);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___boxed(lean_object* v_head_925_, lean_object* v_x_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(v_head_925_, v_x_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec_ref(v_x_926_);
return v_res_932_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_933_; double v___x_934_; 
v___x_933_ = lean_unsigned_to_nat(1000000000u);
v___x_934_ = lean_float_of_nat(v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* v_tail_946_, lean_object* v_cfg_947_, lean_object* v_trace_948_, lean_object* v_next_949_, lean_object* v_goals_950_, lean_object* v_n_951_, lean_object* v_acc_952_, lean_object* v_r_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_946_, v_cfg_947_, v_trace_948_, v_next_949_, v_goals_950_, v_n_951_, v_acc_952_, v_r_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_960_, lean_object* v_trace_961_, lean_object* v_next_962_, lean_object* v_goals_963_, lean_object* v_n_964_, lean_object* v_curr_965_, lean_object* v_acc_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
uint8_t v___y_973_; lean_object* v___y_974_; uint8_t v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v_a_980_; uint8_t v___y_990_; lean_object* v___y_991_; uint8_t v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v_a_997_; lean_object* v___y_1010_; uint8_t v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; uint8_t v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1058_; uint8_t v___y_1059_; uint8_t v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v_a_1065_; lean_object* v___y_1075_; uint8_t v___y_1076_; uint8_t v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v_a_1082_; lean_object* v___y_1085_; uint8_t v___y_1086_; uint8_t v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v_a_1092_; lean_object* v___y_1095_; uint8_t v___y_1096_; uint8_t v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1106_; uint8_t v___y_1107_; uint8_t v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v_a_1113_; lean_object* v___y_1126_; uint8_t v___y_1127_; uint8_t v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v_a_1133_; lean_object* v___y_1136_; uint8_t v___y_1137_; uint8_t v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v_a_1143_; lean_object* v___y_1146_; uint8_t v___y_1147_; uint8_t v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v_zero_1156_; uint8_t v_isZero_1157_; 
v_zero_1156_ = lean_unsigned_to_nat(0u);
v_isZero_1157_ = lean_nat_dec_eq(v_n_964_, v_zero_1156_);
if (v_isZero_1157_ == 1)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_dec(v_acc_966_);
lean_dec(v_curr_965_);
lean_dec(v_n_964_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
v___x_1158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1159_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1158_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1159_;
}
else
{
lean_object* v_proc_1160_; lean_object* v_suspend_1161_; lean_object* v_discharge_1162_; lean_object* v___f_1163_; lean_object* v___y_1165_; uint8_t v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; uint8_t v___y_1169_; lean_object* v___f_1205_; lean_object* v___y_1207_; uint8_t v___y_1208_; uint8_t v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v_a_1213_; lean_object* v___y_1223_; uint8_t v___y_1224_; uint8_t v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v_a_1229_; lean_object* v___y_1242_; uint8_t v___y_1243_; uint8_t v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___f_1289_; uint8_t v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; uint8_t v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v_a_1297_; uint8_t v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; uint8_t v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v_a_1316_; lean_object* v___f_1325_; lean_object* v___y_1327_; uint8_t v___y_1328_; uint8_t v___y_1329_; lean_object* v___y_1330_; uint8_t v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v_a_1337_; lean_object* v___y_1350_; uint8_t v___y_1351_; uint8_t v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v_a_1360_; lean_object* v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1372_; uint8_t v___y_1373_; lean_object* v___y_1374_; uint8_t v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; uint8_t v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1422_; lean_object* v___y_1423_; uint8_t v___y_1424_; uint8_t v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; uint8_t v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v_a_1432_; lean_object* v___y_1445_; uint8_t v___y_1446_; uint8_t v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; uint8_t v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v_a_1455_; lean_object* v___y_1465_; lean_object* v___y_1466_; uint8_t v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; uint8_t v___y_1470_; uint8_t v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; uint8_t v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1517_; uint8_t v___y_1518_; uint8_t v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; uint8_t v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v_a_1527_; lean_object* v___y_1537_; uint8_t v___y_1538_; uint8_t v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; uint8_t v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v_a_1547_; lean_object* v___y_1560_; uint8_t v___y_1561_; uint8_t v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; uint8_t v___y_1568_; lean_object* v___y_1569_; lean_object* v_a_1570_; lean_object* v___y_1580_; uint8_t v___y_1581_; uint8_t v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; uint8_t v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v_a_1590_; lean_object* v___y_1603_; lean_object* v___y_1604_; uint8_t v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; uint8_t v___y_1609_; uint8_t v___y_1610_; lean_object* v___y_1611_; uint8_t v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1655_; uint8_t v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1658_; uint8_t v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v_a_1665_; lean_object* v___y_1678_; uint8_t v___y_1679_; uint8_t v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; uint8_t v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v_a_1688_; lean_object* v___y_1698_; lean_object* v___y_1699_; uint8_t v___y_1700_; uint8_t v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; uint8_t v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v_a_1708_; lean_object* v___y_1721_; lean_object* v___y_1722_; uint8_t v___y_1723_; uint8_t v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; uint8_t v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v_a_1731_; lean_object* v___y_1741_; lean_object* v___y_1742_; uint8_t v___y_1743_; lean_object* v___y_1744_; uint8_t v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; uint8_t v___y_1749_; uint8_t v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; uint8_t v___y_1793_; uint8_t v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v_a_1799_; uint8_t v___y_1812_; uint8_t v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v_a_1818_; lean_object* v___y_1828_; uint8_t v___y_1829_; lean_object* v___y_1830_; uint8_t v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v_one_1875_; lean_object* v_n_1876_; uint8_t v___y_1878_; lean_object* v___y_1879_; lean_object* v___y_1880_; uint8_t v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1924_; uint8_t v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; uint8_t v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; uint8_t v___y_1933_; lean_object* v___y_1957_; uint8_t v___y_1958_; uint8_t v___y_1959_; lean_object* v___y_1960_; uint8_t v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; uint8_t v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_2007_; lean_object* v___y_2008_; uint8_t v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; uint8_t v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; uint8_t v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; uint8_t v___y_2020_; lean_object* v___y_2041_; uint8_t v___y_2042_; uint8_t v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; uint8_t v___y_2047_; lean_object* v___y_2048_; uint8_t v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2091_; lean_object* v___y_2092_; uint8_t v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; uint8_t v___y_2098_; lean_object* v___y_2099_; uint8_t v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; uint8_t v___y_2104_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; uint8_t v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; uint8_t v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; uint8_t v___y_2182_; lean_object* v_a_2200_; lean_object* v___y_2293_; lean_object* v___x_2303_; 
v_proc_1160_ = lean_ctor_get(v_cfg_960_, 1);
v_suspend_1161_ = lean_ctor_get(v_cfg_960_, 2);
v_discharge_1162_ = lean_ctor_get(v_cfg_960_, 3);
v___f_1163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1875_ = lean_unsigned_to_nat(1u);
v_n_1876_ = lean_nat_sub(v_n_964_, v_one_1875_);
lean_dec(v_n_964_);
lean_inc_ref(v_proc_1160_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v_curr_965_);
lean_inc(v_goals_963_);
v___x_2303_ = lean_apply_7(v_proc_1160_, v_goals_963_, v_curr_965_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v_a_2200_ = v_a_2304_;
goto v___jp_2199_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2373_; 
v_a_2305_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2307_ = v___x_2303_;
v_isShared_2308_ = v_isSharedCheck_2373_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2303_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2373_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___f_2309_; lean_object* v___y_2311_; uint8_t v___y_2312_; uint8_t v___y_2313_; lean_object* v___y_2314_; uint8_t v___y_2351_; uint8_t v___x_2371_; 
lean_inc(v_a_2305_);
v___f_2309_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2309_, 0, v_a_2305_);
v___x_2371_ = l_Lean_Exception_isInterrupt(v_a_2305_);
if (v___x_2371_ == 0)
{
uint8_t v___x_2372_; 
lean_inc(v_a_2305_);
v___x_2372_ = l_Lean_Exception_isRuntime(v_a_2305_);
v___y_2351_ = v___x_2372_;
goto v___jp_2350_;
}
else
{
v___y_2351_ = v___x_2371_;
goto v___jp_2350_;
}
v___jp_2310_:
{
lean_object* v___x_2315_; lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2349_; 
v___x_2315_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2349_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2349_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2321_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2314_, v___x_2320_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; lean_object* v___x_2324_; 
v___x_2322_ = lean_io_mono_nanos_now();
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v_a_2305_);
v___x_2324_ = v___x_2318_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2305_);
v___x_2324_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2325_; double v___x_2326_; double v___x_2327_; double v___x_2328_; double v___x_2329_; double v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2325_ = lean_io_mono_nanos_now();
v___x_2326_ = lean_float_of_nat(v___x_2322_);
v___x_2327_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2328_ = lean_float_div(v___x_2326_, v___x_2327_);
v___x_2329_ = lean_float_of_nat(v___x_2325_);
v___x_2330_ = lean_float_div(v___x_2329_, v___x_2327_);
v___x_2331_ = lean_box_float(v___x_2328_);
v___x_2332_ = lean_box_float(v___x_2330_);
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2324_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
lean_inc_ref(v___y_2311_);
lean_inc(v_trace_961_);
v___x_2335_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_961_, v___y_2312_, v___y_2311_, v___y_2314_, v___y_2313_, v_a_2316_, v___f_2309_, v___x_2334_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_2293_ = v___x_2335_;
goto v___jp_2292_;
}
}
else
{
lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2337_ = lean_io_get_num_heartbeats();
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v_a_2305_);
v___x_2339_ = v___x_2318_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2305_);
v___x_2339_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; double v___x_2341_; double v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2340_ = lean_io_get_num_heartbeats();
v___x_2341_ = lean_float_of_nat(v___x_2337_);
v___x_2342_ = lean_float_of_nat(v___x_2340_);
v___x_2343_ = lean_box_float(v___x_2341_);
v___x_2344_ = lean_box_float(v___x_2342_);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2339_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
lean_inc_ref(v___y_2311_);
lean_inc(v_trace_961_);
v___x_2347_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_961_, v___y_2312_, v___y_2311_, v___y_2314_, v___y_2313_, v_a_2316_, v___f_2309_, v___x_2346_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_2293_ = v___x_2347_;
goto v___jp_2292_;
}
}
}
}
v___jp_2350_:
{
if (v___y_2351_ == 0)
{
lean_object* v_toCold_2352_; lean_object* v_options_2353_; uint8_t v_hasTrace_2354_; 
v_toCold_2352_ = lean_ctor_get(v_a_969_, 0);
v_options_2353_ = lean_ctor_get(v_toCold_2352_, 2);
v_hasTrace_2354_ = lean_ctor_get_uint8(v_options_2353_, sizeof(void*)*1);
if (v_hasTrace_2354_ == 0)
{
lean_object* v___x_2356_; 
lean_dec_ref(v___f_2309_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_curr_965_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
if (v_isShared_2308_ == 0)
{
v___x_2356_ = v___x_2307_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2305_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v_inheritedTraceOptions_2358_ = lean_ctor_get(v_toCold_2352_, 11);
v___x_2359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_2361_ = l_Lean_Name_append(v___x_2360_, v_trace_961_);
v___x_2362_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2358_, v_options_2353_, v___x_2361_);
lean_dec(v___x_2361_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2363_ = l_Lean_trace_profiler;
v___x_2364_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2353_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2366_; 
lean_dec_ref(v___f_2309_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_curr_965_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
if (v_isShared_2308_ == 0)
{
v___x_2366_ = v___x_2307_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2305_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
else
{
lean_del_object(v___x_2307_);
v___y_2311_ = v___x_2359_;
v___y_2312_ = v_hasTrace_2354_;
v___y_2313_ = v___x_2362_;
v___y_2314_ = v_options_2353_;
goto v___jp_2310_;
}
}
else
{
lean_del_object(v___x_2307_);
v___y_2311_ = v___x_2359_;
v___y_2312_ = v_hasTrace_2354_;
v___y_2313_ = v___x_2362_;
v___y_2314_ = v_options_2353_;
goto v___jp_2310_;
}
}
}
else
{
lean_object* v___x_2369_; 
lean_dec_ref(v___f_2309_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_curr_965_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
if (v_isShared_2308_ == 0)
{
v___x_2369_ = v___x_2307_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2305_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
v___jp_1164_:
{
lean_object* v___x_1170_; lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1204_; 
v___x_1170_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1204_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1204_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1176_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1167_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1177_ = lean_io_mono_nanos_now();
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 1);
lean_ctor_set(v___x_1173_, 0, v___y_1168_);
v___x_1179_ = v___x_1173_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___y_1168_);
v___x_1179_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; double v___x_1181_; double v___x_1182_; double v___x_1183_; double v___x_1184_; double v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1180_ = lean_io_mono_nanos_now();
v___x_1181_ = lean_float_of_nat(v___x_1177_);
v___x_1182_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1183_ = lean_float_div(v___x_1181_, v___x_1182_);
v___x_1184_ = lean_float_of_nat(v___x_1180_);
v___x_1185_ = lean_float_div(v___x_1184_, v___x_1182_);
v___x_1186_ = lean_box_float(v___x_1183_);
v___x_1187_ = lean_box_float(v___x_1185_);
v___x_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1179_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
lean_inc_ref(v___y_1165_);
v___x_1190_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1169_, v___y_1165_, v___y_1167_, v___y_1166_, v_a_1171_, v___f_1163_, v___x_1189_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1190_;
}
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = lean_io_get_num_heartbeats();
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 1);
lean_ctor_set(v___x_1173_, 0, v___y_1168_);
v___x_1194_ = v___x_1173_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___y_1168_);
v___x_1194_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; double v___x_1196_; double v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1195_ = lean_io_get_num_heartbeats();
v___x_1196_ = lean_float_of_nat(v___x_1192_);
v___x_1197_ = lean_float_of_nat(v___x_1195_);
v___x_1198_ = lean_box_float(v___x_1196_);
v___x_1199_ = lean_box_float(v___x_1197_);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1194_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
lean_inc_ref(v___y_1165_);
v___x_1202_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1169_, v___y_1165_, v___y_1167_, v___y_1166_, v_a_1171_, v___f_1163_, v___x_1201_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1202_;
}
}
}
}
v___jp_1206_:
{
lean_object* v___x_1214_; double v___x_1215_; double v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1214_ = lean_io_get_num_heartbeats();
v___x_1215_ = lean_float_of_nat(v___y_1212_);
v___x_1216_ = lean_float_of_nat(v___x_1214_);
v___x_1217_ = lean_box_float(v___x_1215_);
v___x_1218_ = lean_box_float(v___x_1216_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_a_1213_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
lean_inc_ref(v___y_1211_);
v___x_1221_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1208_, v___y_1211_, v___y_1210_, v___y_1209_, v___y_1207_, v___f_1205_, v___x_1220_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1221_;
}
v___jp_1222_:
{
lean_object* v___x_1230_; double v___x_1231_; double v___x_1232_; double v___x_1233_; double v___x_1234_; double v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1230_ = lean_io_mono_nanos_now();
v___x_1231_ = lean_float_of_nat(v___y_1227_);
v___x_1232_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1233_ = lean_float_div(v___x_1231_, v___x_1232_);
v___x_1234_ = lean_float_of_nat(v___x_1230_);
v___x_1235_ = lean_float_div(v___x_1234_, v___x_1232_);
v___x_1236_ = lean_box_float(v___x_1233_);
v___x_1237_ = lean_box_float(v___x_1235_);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1236_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_a_1229_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
lean_inc_ref(v___y_1228_);
v___x_1240_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1224_, v___y_1228_, v___y_1226_, v___y_1225_, v___y_1223_, v___f_1205_, v___x_1239_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1240_;
}
v___jp_1241_:
{
lean_object* v___x_1249_; lean_object* v_a_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1249_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref(v___x_1249_);
v___x_1251_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1252_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1245_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_io_mono_nanos_now();
lean_inc(v_trace_961_);
v___x_1254_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1247_, v___y_1242_, v___y_1246_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 1);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
v___y_1223_ = v_a_1250_;
v___y_1224_ = v___y_1243_;
v___y_1225_ = v___y_1244_;
v___y_1226_ = v___y_1245_;
v___y_1227_ = v___x_1253_;
v___y_1228_ = v___y_1248_;
v_a_1229_ = v___x_1260_;
goto v___jp_1222_;
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_a_1263_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1254_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1254_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set_tag(v___x_1265_, 0);
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
v___y_1223_ = v_a_1250_;
v___y_1224_ = v___y_1243_;
v___y_1225_ = v___y_1244_;
v___y_1226_ = v___y_1245_;
v___y_1227_ = v___x_1253_;
v___y_1228_ = v___y_1248_;
v_a_1229_ = v___x_1268_;
goto v___jp_1222_;
}
}
}
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_961_);
v___x_1272_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1247_, v___y_1242_, v___y_1246_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set_tag(v___x_1275_, 1);
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
v___y_1207_ = v_a_1250_;
v___y_1208_ = v___y_1243_;
v___y_1209_ = v___y_1244_;
v___y_1210_ = v___y_1245_;
v___y_1211_ = v___y_1248_;
v___y_1212_ = v___x_1271_;
v_a_1213_ = v___x_1278_;
goto v___jp_1206_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
v_a_1281_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1272_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1272_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set_tag(v___x_1283_, 0);
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
v___y_1207_ = v_a_1250_;
v___y_1208_ = v___y_1243_;
v___y_1209_ = v___y_1244_;
v___y_1210_ = v___y_1245_;
v___y_1211_ = v___y_1248_;
v___y_1212_ = v___x_1271_;
v_a_1213_ = v___x_1286_;
goto v___jp_1206_;
}
}
}
}
}
v___jp_1290_:
{
lean_object* v___x_1298_; double v___x_1299_; double v___x_1300_; double v___x_1301_; double v___x_1302_; double v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1298_ = lean_io_mono_nanos_now();
v___x_1299_ = lean_float_of_nat(v___y_1295_);
v___x_1300_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1301_ = lean_float_div(v___x_1299_, v___x_1300_);
v___x_1302_ = lean_float_of_nat(v___x_1298_);
v___x_1303_ = lean_float_div(v___x_1302_, v___x_1300_);
v___x_1304_ = lean_box_float(v___x_1301_);
v___x_1305_ = lean_box_float(v___x_1303_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_a_1297_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
lean_inc_ref(v___y_1296_);
v___x_1308_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1291_, v___y_1296_, v___y_1292_, v___y_1294_, v___y_1293_, v___f_1289_, v___x_1307_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1308_;
}
v___jp_1309_:
{
lean_object* v___x_1317_; double v___x_1318_; double v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1317_ = lean_io_get_num_heartbeats();
v___x_1318_ = lean_float_of_nat(v___y_1315_);
v___x_1319_ = lean_float_of_nat(v___x_1317_);
v___x_1320_ = lean_box_float(v___x_1318_);
v___x_1321_ = lean_box_float(v___x_1319_);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_a_1316_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
lean_inc_ref(v___y_1314_);
v___x_1324_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1310_, v___y_1314_, v___y_1311_, v___y_1313_, v___y_1312_, v___f_1289_, v___x_1323_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1324_;
}
v___jp_1326_:
{
lean_object* v___x_1338_; double v___x_1339_; double v___x_1340_; double v___x_1341_; double v___x_1342_; double v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1338_ = lean_io_mono_nanos_now();
v___x_1339_ = lean_float_of_nat(v___y_1335_);
v___x_1340_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1341_ = lean_float_div(v___x_1339_, v___x_1340_);
v___x_1342_ = lean_float_of_nat(v___x_1338_);
v___x_1343_ = lean_float_div(v___x_1342_, v___x_1340_);
v___x_1344_ = lean_box_float(v___x_1341_);
v___x_1345_ = lean_box_float(v___x_1343_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_a_1337_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
lean_inc_ref(v___y_1336_);
lean_inc(v_trace_961_);
v___x_1348_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1329_, v___y_1336_, v___y_1332_, v___y_1331_, v___y_1330_, v___f_1325_, v___x_1347_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1095_ = v___y_1327_;
v___y_1096_ = v___y_1328_;
v___y_1097_ = v___y_1329_;
v___y_1098_ = v___y_1332_;
v___y_1099_ = v___y_1333_;
v___y_1100_ = v___y_1334_;
v___y_1101_ = v___y_1336_;
v___y_1102_ = v___x_1348_;
goto v___jp_1094_;
}
v___jp_1349_:
{
lean_object* v___x_1361_; double v___x_1362_; double v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1361_ = lean_io_get_num_heartbeats();
v___x_1362_ = lean_float_of_nat(v___y_1356_);
v___x_1363_ = lean_float_of_nat(v___x_1361_);
v___x_1364_ = lean_box_float(v___x_1362_);
v___x_1365_ = lean_box_float(v___x_1363_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v_a_1360_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
lean_inc_ref(v___y_1359_);
lean_inc(v_trace_961_);
v___x_1368_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1352_, v___y_1359_, v___y_1355_, v___y_1354_, v___y_1353_, v___f_1325_, v___x_1367_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1095_ = v___y_1350_;
v___y_1096_ = v___y_1351_;
v___y_1097_ = v___y_1352_;
v___y_1098_ = v___y_1355_;
v___y_1099_ = v___y_1357_;
v___y_1100_ = v___y_1358_;
v___y_1101_ = v___y_1359_;
v___y_1102_ = v___x_1368_;
goto v___jp_1094_;
}
v___jp_1369_:
{
lean_object* v___x_1382_; 
v___x_1382_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
if (v___y_1375_ == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
v___x_1384_ = lean_io_mono_nanos_now();
lean_inc(v_trace_961_);
v___x_1385_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1378_, v___y_1371_, v___y_1381_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set_tag(v___x_1388_, 1);
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
v___y_1327_ = v___y_1370_;
v___y_1328_ = v___y_1379_;
v___y_1329_ = v___y_1372_;
v___y_1330_ = v_a_1383_;
v___y_1331_ = v___y_1373_;
v___y_1332_ = v___y_1374_;
v___y_1333_ = v___y_1380_;
v___y_1334_ = v___y_1376_;
v___y_1335_ = v___x_1384_;
v___y_1336_ = v___y_1377_;
v_a_1337_ = v___x_1391_;
goto v___jp_1326_;
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
v_a_1394_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1385_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1385_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set_tag(v___x_1396_, 0);
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
v___y_1327_ = v___y_1370_;
v___y_1328_ = v___y_1379_;
v___y_1329_ = v___y_1372_;
v___y_1330_ = v_a_1383_;
v___y_1331_ = v___y_1373_;
v___y_1332_ = v___y_1374_;
v___y_1333_ = v___y_1380_;
v___y_1334_ = v___y_1376_;
v___y_1335_ = v___x_1384_;
v___y_1336_ = v___y_1377_;
v_a_1337_ = v___x_1399_;
goto v___jp_1326_;
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v_a_1402_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1402_);
lean_dec_ref(v___x_1382_);
v___x_1403_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_961_);
v___x_1404_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1378_, v___y_1371_, v___y_1381_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set_tag(v___x_1407_, 1);
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
v___y_1350_ = v___y_1370_;
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1372_;
v___y_1353_ = v_a_1402_;
v___y_1354_ = v___y_1373_;
v___y_1355_ = v___y_1374_;
v___y_1356_ = v___x_1403_;
v___y_1357_ = v___y_1380_;
v___y_1358_ = v___y_1376_;
v___y_1359_ = v___y_1377_;
v_a_1360_ = v___x_1410_;
goto v___jp_1349_;
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
v_a_1413_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1404_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1404_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 0);
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
v___y_1350_ = v___y_1370_;
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1372_;
v___y_1353_ = v_a_1402_;
v___y_1354_ = v___y_1373_;
v___y_1355_ = v___y_1374_;
v___y_1356_ = v___x_1403_;
v___y_1357_ = v___y_1380_;
v___y_1358_ = v___y_1376_;
v___y_1359_ = v___y_1377_;
v_a_1360_ = v___x_1418_;
goto v___jp_1349_;
}
}
}
}
}
v___jp_1421_:
{
lean_object* v___x_1433_; double v___x_1434_; double v___x_1435_; double v___x_1436_; double v___x_1437_; double v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1433_ = lean_io_mono_nanos_now();
v___x_1434_ = lean_float_of_nat(v___y_1423_);
v___x_1435_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1436_ = lean_float_div(v___x_1434_, v___x_1435_);
v___x_1437_ = lean_float_of_nat(v___x_1433_);
v___x_1438_ = lean_float_div(v___x_1437_, v___x_1435_);
v___x_1439_ = lean_box_float(v___x_1436_);
v___x_1440_ = lean_box_float(v___x_1438_);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v_a_1432_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
lean_inc_ref(v___y_1431_);
lean_inc(v_trace_961_);
v___x_1443_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1425_, v___y_1431_, v___y_1427_, v___y_1429_, v___y_1430_, v___f_1205_, v___x_1442_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1146_ = v___y_1422_;
v___y_1147_ = v___y_1424_;
v___y_1148_ = v___y_1425_;
v___y_1149_ = v___y_1426_;
v___y_1150_ = v___y_1427_;
v___y_1151_ = v___y_1428_;
v___y_1152_ = v___y_1431_;
v___y_1153_ = v___x_1443_;
goto v___jp_1145_;
}
v___jp_1444_:
{
lean_object* v___x_1456_; double v___x_1457_; double v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1456_ = lean_io_get_num_heartbeats();
v___x_1457_ = lean_float_of_nat(v___y_1450_);
v___x_1458_ = lean_float_of_nat(v___x_1456_);
v___x_1459_ = lean_box_float(v___x_1457_);
v___x_1460_ = lean_box_float(v___x_1458_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v_a_1455_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
lean_inc_ref(v___y_1454_);
lean_inc(v_trace_961_);
v___x_1463_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1447_, v___y_1454_, v___y_1449_, v___y_1452_, v___y_1453_, v___f_1205_, v___x_1462_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1146_ = v___y_1445_;
v___y_1147_ = v___y_1446_;
v___y_1148_ = v___y_1447_;
v___y_1149_ = v___y_1448_;
v___y_1150_ = v___y_1449_;
v___y_1151_ = v___y_1451_;
v___y_1152_ = v___y_1454_;
v___y_1153_ = v___x_1463_;
goto v___jp_1145_;
}
v___jp_1464_:
{
lean_object* v___x_1477_; 
v___x_1477_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
if (v___y_1470_ == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref(v___x_1477_);
v___x_1479_ = lean_io_mono_nanos_now();
lean_inc(v_trace_961_);
v___x_1480_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1473_, v___y_1466_, v___y_1475_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set_tag(v___x_1483_, 1);
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
v___y_1422_ = v___y_1465_;
v___y_1423_ = v___x_1479_;
v___y_1424_ = v___y_1474_;
v___y_1425_ = v___y_1467_;
v___y_1426_ = v___y_1468_;
v___y_1427_ = v___y_1469_;
v___y_1428_ = v___y_1476_;
v___y_1429_ = v___y_1471_;
v___y_1430_ = v_a_1478_;
v___y_1431_ = v___y_1472_;
v_a_1432_ = v___x_1486_;
goto v___jp_1421_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_a_1489_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1480_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1480_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set_tag(v___x_1491_, 0);
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
v___y_1422_ = v___y_1465_;
v___y_1423_ = v___x_1479_;
v___y_1424_ = v___y_1474_;
v___y_1425_ = v___y_1467_;
v___y_1426_ = v___y_1468_;
v___y_1427_ = v___y_1469_;
v___y_1428_ = v___y_1476_;
v___y_1429_ = v___y_1471_;
v___y_1430_ = v_a_1478_;
v___y_1431_ = v___y_1472_;
v_a_1432_ = v___x_1494_;
goto v___jp_1421_;
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_a_1497_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1497_);
lean_dec_ref(v___x_1477_);
v___x_1498_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_961_);
v___x_1499_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1473_, v___y_1466_, v___y_1475_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1499_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1499_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 1);
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
v___y_1445_ = v___y_1465_;
v___y_1446_ = v___y_1474_;
v___y_1447_ = v___y_1467_;
v___y_1448_ = v___y_1468_;
v___y_1449_ = v___y_1469_;
v___y_1450_ = v___x_1498_;
v___y_1451_ = v___y_1476_;
v___y_1452_ = v___y_1471_;
v___y_1453_ = v_a_1497_;
v___y_1454_ = v___y_1472_;
v_a_1455_ = v___x_1505_;
goto v___jp_1444_;
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
v_a_1508_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1499_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1499_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 0);
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
v___y_1445_ = v___y_1465_;
v___y_1446_ = v___y_1474_;
v___y_1447_ = v___y_1467_;
v___y_1448_ = v___y_1468_;
v___y_1449_ = v___y_1469_;
v___y_1450_ = v___x_1498_;
v___y_1451_ = v___y_1476_;
v___y_1452_ = v___y_1471_;
v___y_1453_ = v_a_1497_;
v___y_1454_ = v___y_1472_;
v_a_1455_ = v___x_1513_;
goto v___jp_1444_;
}
}
}
}
}
v___jp_1516_:
{
lean_object* v___x_1528_; double v___x_1529_; double v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1528_ = lean_io_get_num_heartbeats();
v___x_1529_ = lean_float_of_nat(v___y_1525_);
v___x_1530_ = lean_float_of_nat(v___x_1528_);
v___x_1531_ = lean_box_float(v___x_1529_);
v___x_1532_ = lean_box_float(v___x_1530_);
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v_a_1527_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
lean_inc_ref(v___y_1526_);
lean_inc(v_trace_961_);
v___x_1535_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1519_, v___y_1526_, v___y_1521_, v___y_1524_, v___y_1522_, v___f_1289_, v___x_1534_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1146_ = v___y_1517_;
v___y_1147_ = v___y_1518_;
v___y_1148_ = v___y_1519_;
v___y_1149_ = v___y_1520_;
v___y_1150_ = v___y_1521_;
v___y_1151_ = v___y_1523_;
v___y_1152_ = v___y_1526_;
v___y_1153_ = v___x_1535_;
goto v___jp_1145_;
}
v___jp_1536_:
{
lean_object* v___x_1548_; double v___x_1549_; double v___x_1550_; double v___x_1551_; double v___x_1552_; double v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1548_ = lean_io_mono_nanos_now();
v___x_1549_ = lean_float_of_nat(v___y_1546_);
v___x_1550_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1551_ = lean_float_div(v___x_1549_, v___x_1550_);
v___x_1552_ = lean_float_of_nat(v___x_1548_);
v___x_1553_ = lean_float_div(v___x_1552_, v___x_1550_);
v___x_1554_ = lean_box_float(v___x_1551_);
v___x_1555_ = lean_box_float(v___x_1553_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v_a_1547_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
lean_inc_ref(v___y_1545_);
lean_inc(v_trace_961_);
v___x_1558_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1539_, v___y_1545_, v___y_1541_, v___y_1544_, v___y_1542_, v___f_1289_, v___x_1557_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1146_ = v___y_1537_;
v___y_1147_ = v___y_1538_;
v___y_1148_ = v___y_1539_;
v___y_1149_ = v___y_1540_;
v___y_1150_ = v___y_1541_;
v___y_1151_ = v___y_1543_;
v___y_1152_ = v___y_1545_;
v___y_1153_ = v___x_1558_;
goto v___jp_1145_;
}
v___jp_1559_:
{
lean_object* v___x_1571_; double v___x_1572_; double v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1571_ = lean_io_get_num_heartbeats();
v___x_1572_ = lean_float_of_nat(v___y_1564_);
v___x_1573_ = lean_float_of_nat(v___x_1571_);
v___x_1574_ = lean_box_float(v___x_1572_);
v___x_1575_ = lean_box_float(v___x_1573_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v_a_1570_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
lean_inc_ref(v___y_1569_);
lean_inc(v_trace_961_);
v___x_1578_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1562_, v___y_1569_, v___y_1565_, v___y_1568_, v___y_1567_, v___f_1325_, v___x_1577_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1146_ = v___y_1560_;
v___y_1147_ = v___y_1561_;
v___y_1148_ = v___y_1562_;
v___y_1149_ = v___y_1563_;
v___y_1150_ = v___y_1565_;
v___y_1151_ = v___y_1566_;
v___y_1152_ = v___y_1569_;
v___y_1153_ = v___x_1578_;
goto v___jp_1145_;
}
v___jp_1579_:
{
lean_object* v___x_1591_; double v___x_1592_; double v___x_1593_; double v___x_1594_; double v___x_1595_; double v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1591_ = lean_io_mono_nanos_now();
v___x_1592_ = lean_float_of_nat(v___y_1589_);
v___x_1593_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1594_ = lean_float_div(v___x_1592_, v___x_1593_);
v___x_1595_ = lean_float_of_nat(v___x_1591_);
v___x_1596_ = lean_float_div(v___x_1595_, v___x_1593_);
v___x_1597_ = lean_box_float(v___x_1594_);
v___x_1598_ = lean_box_float(v___x_1596_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v_a_1590_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
lean_inc_ref(v___y_1588_);
lean_inc(v_trace_961_);
v___x_1601_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1582_, v___y_1588_, v___y_1584_, v___y_1587_, v___y_1586_, v___f_1325_, v___x_1600_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1146_ = v___y_1580_;
v___y_1147_ = v___y_1581_;
v___y_1148_ = v___y_1582_;
v___y_1149_ = v___y_1583_;
v___y_1150_ = v___y_1584_;
v___y_1151_ = v___y_1585_;
v___y_1152_ = v___y_1588_;
v___y_1153_ = v___x_1601_;
goto v___jp_1145_;
}
v___jp_1602_:
{
lean_object* v___x_1615_; 
v___x_1615_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
if (v___y_1609_ == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref(v___x_1615_);
v___x_1617_ = lean_io_mono_nanos_now();
lean_inc(v_trace_961_);
v___x_1618_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1608_, v___y_1604_, v___y_1614_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 1);
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
v___y_1580_ = v___y_1603_;
v___y_1581_ = v___y_1612_;
v___y_1582_ = v___y_1605_;
v___y_1583_ = v___y_1606_;
v___y_1584_ = v___y_1607_;
v___y_1585_ = v___y_1613_;
v___y_1586_ = v_a_1616_;
v___y_1587_ = v___y_1610_;
v___y_1588_ = v___y_1611_;
v___y_1589_ = v___x_1617_;
v_a_1590_ = v___x_1624_;
goto v___jp_1579_;
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_a_1627_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1618_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1618_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set_tag(v___x_1629_, 0);
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
v___y_1580_ = v___y_1603_;
v___y_1581_ = v___y_1612_;
v___y_1582_ = v___y_1605_;
v___y_1583_ = v___y_1606_;
v___y_1584_ = v___y_1607_;
v___y_1585_ = v___y_1613_;
v___y_1586_ = v_a_1616_;
v___y_1587_ = v___y_1610_;
v___y_1588_ = v___y_1611_;
v___y_1589_ = v___x_1617_;
v_a_1590_ = v___x_1632_;
goto v___jp_1579_;
}
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v_a_1635_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1635_);
lean_dec_ref(v___x_1615_);
v___x_1636_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_961_);
v___x_1637_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1608_, v___y_1604_, v___y_1614_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
v___y_1560_ = v___y_1603_;
v___y_1561_ = v___y_1612_;
v___y_1562_ = v___y_1605_;
v___y_1563_ = v___y_1606_;
v___y_1564_ = v___x_1636_;
v___y_1565_ = v___y_1607_;
v___y_1566_ = v___y_1613_;
v___y_1567_ = v_a_1635_;
v___y_1568_ = v___y_1610_;
v___y_1569_ = v___y_1611_;
v_a_1570_ = v___x_1643_;
goto v___jp_1559_;
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_a_1646_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1637_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1637_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 0);
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
v___y_1560_ = v___y_1603_;
v___y_1561_ = v___y_1612_;
v___y_1562_ = v___y_1605_;
v___y_1563_ = v___y_1606_;
v___y_1564_ = v___x_1636_;
v___y_1565_ = v___y_1607_;
v___y_1566_ = v___y_1613_;
v___y_1567_ = v_a_1635_;
v___y_1568_ = v___y_1610_;
v___y_1569_ = v___y_1611_;
v_a_1570_ = v___x_1651_;
goto v___jp_1559_;
}
}
}
}
}
v___jp_1654_:
{
lean_object* v___x_1666_; double v___x_1667_; double v___x_1668_; double v___x_1669_; double v___x_1670_; double v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1666_ = lean_io_mono_nanos_now();
v___x_1667_ = lean_float_of_nat(v___y_1660_);
v___x_1668_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1669_ = lean_float_div(v___x_1667_, v___x_1668_);
v___x_1670_ = lean_float_of_nat(v___x_1666_);
v___x_1671_ = lean_float_div(v___x_1670_, v___x_1668_);
v___x_1672_ = lean_box_float(v___x_1669_);
v___x_1673_ = lean_box_float(v___x_1671_);
v___x_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_a_1665_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
lean_inc_ref(v___y_1664_);
lean_inc(v_trace_961_);
v___x_1676_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1657_, v___y_1664_, v___y_1658_, v___y_1659_, v___y_1662_, v___f_1289_, v___x_1675_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1095_ = v___y_1655_;
v___y_1096_ = v___y_1656_;
v___y_1097_ = v___y_1657_;
v___y_1098_ = v___y_1658_;
v___y_1099_ = v___y_1661_;
v___y_1100_ = v___y_1663_;
v___y_1101_ = v___y_1664_;
v___y_1102_ = v___x_1676_;
goto v___jp_1094_;
}
v___jp_1677_:
{
lean_object* v___x_1689_; double v___x_1690_; double v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1689_ = lean_io_get_num_heartbeats();
v___x_1690_ = lean_float_of_nat(v___y_1681_);
v___x_1691_ = lean_float_of_nat(v___x_1689_);
v___x_1692_ = lean_box_float(v___x_1690_);
v___x_1693_ = lean_box_float(v___x_1691_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_a_1688_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
lean_inc_ref(v___y_1687_);
lean_inc(v_trace_961_);
v___x_1696_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1680_, v___y_1687_, v___y_1682_, v___y_1683_, v___y_1685_, v___f_1289_, v___x_1695_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1095_ = v___y_1678_;
v___y_1096_ = v___y_1679_;
v___y_1097_ = v___y_1680_;
v___y_1098_ = v___y_1682_;
v___y_1099_ = v___y_1684_;
v___y_1100_ = v___y_1686_;
v___y_1101_ = v___y_1687_;
v___y_1102_ = v___x_1696_;
goto v___jp_1094_;
}
v___jp_1697_:
{
lean_object* v___x_1709_; double v___x_1710_; double v___x_1711_; double v___x_1712_; double v___x_1713_; double v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1709_ = lean_io_mono_nanos_now();
v___x_1710_ = lean_float_of_nat(v___y_1702_);
v___x_1711_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1712_ = lean_float_div(v___x_1710_, v___x_1711_);
v___x_1713_ = lean_float_of_nat(v___x_1709_);
v___x_1714_ = lean_float_div(v___x_1713_, v___x_1711_);
v___x_1715_ = lean_box_float(v___x_1712_);
v___x_1716_ = lean_box_float(v___x_1714_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_a_1708_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
lean_inc_ref(v___y_1707_);
lean_inc(v_trace_961_);
v___x_1719_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1701_, v___y_1707_, v___y_1703_, v___y_1704_, v___y_1699_, v___f_1205_, v___x_1718_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1095_ = v___y_1698_;
v___y_1096_ = v___y_1700_;
v___y_1097_ = v___y_1701_;
v___y_1098_ = v___y_1703_;
v___y_1099_ = v___y_1705_;
v___y_1100_ = v___y_1706_;
v___y_1101_ = v___y_1707_;
v___y_1102_ = v___x_1719_;
goto v___jp_1094_;
}
v___jp_1720_:
{
lean_object* v___x_1732_; double v___x_1733_; double v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1732_ = lean_io_get_num_heartbeats();
v___x_1733_ = lean_float_of_nat(v___y_1726_);
v___x_1734_ = lean_float_of_nat(v___x_1732_);
v___x_1735_ = lean_box_float(v___x_1733_);
v___x_1736_ = lean_box_float(v___x_1734_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1735_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v_a_1731_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
lean_inc_ref(v___y_1730_);
lean_inc(v_trace_961_);
v___x_1739_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1724_, v___y_1730_, v___y_1725_, v___y_1727_, v___y_1722_, v___f_1205_, v___x_1738_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1095_ = v___y_1721_;
v___y_1096_ = v___y_1723_;
v___y_1097_ = v___y_1724_;
v___y_1098_ = v___y_1725_;
v___y_1099_ = v___y_1728_;
v___y_1100_ = v___y_1729_;
v___y_1101_ = v___y_1730_;
v___y_1102_ = v___x_1739_;
goto v___jp_1094_;
}
v___jp_1740_:
{
lean_object* v___x_1753_; 
v___x_1753_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
if (v___y_1745_ == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = lean_io_mono_nanos_now();
lean_inc(v_trace_961_);
v___x_1756_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1748_, v___y_1742_, v___y_1752_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set_tag(v___x_1759_, 1);
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
v___y_1698_ = v___y_1741_;
v___y_1699_ = v_a_1754_;
v___y_1700_ = v___y_1749_;
v___y_1701_ = v___y_1743_;
v___y_1702_ = v___x_1755_;
v___y_1703_ = v___y_1744_;
v___y_1704_ = v___y_1750_;
v___y_1705_ = v___y_1751_;
v___y_1706_ = v___y_1746_;
v___y_1707_ = v___y_1747_;
v_a_1708_ = v___x_1762_;
goto v___jp_1697_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
v_a_1765_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1756_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1756_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 0);
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
v___y_1698_ = v___y_1741_;
v___y_1699_ = v_a_1754_;
v___y_1700_ = v___y_1749_;
v___y_1701_ = v___y_1743_;
v___y_1702_ = v___x_1755_;
v___y_1703_ = v___y_1744_;
v___y_1704_ = v___y_1750_;
v___y_1705_ = v___y_1751_;
v___y_1706_ = v___y_1746_;
v___y_1707_ = v___y_1747_;
v_a_1708_ = v___x_1770_;
goto v___jp_1697_;
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_a_1773_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1773_);
lean_dec_ref(v___x_1753_);
v___x_1774_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_961_);
v___x_1775_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1748_, v___y_1742_, v___y_1752_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 1);
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
v___y_1721_ = v___y_1741_;
v___y_1722_ = v_a_1773_;
v___y_1723_ = v___y_1749_;
v___y_1724_ = v___y_1743_;
v___y_1725_ = v___y_1744_;
v___y_1726_ = v___x_1774_;
v___y_1727_ = v___y_1750_;
v___y_1728_ = v___y_1751_;
v___y_1729_ = v___y_1746_;
v___y_1730_ = v___y_1747_;
v_a_1731_ = v___x_1781_;
goto v___jp_1720_;
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1775_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1775_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 0);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
v___y_1721_ = v___y_1741_;
v___y_1722_ = v_a_1773_;
v___y_1723_ = v___y_1749_;
v___y_1724_ = v___y_1743_;
v___y_1725_ = v___y_1744_;
v___y_1726_ = v___x_1774_;
v___y_1727_ = v___y_1750_;
v___y_1728_ = v___y_1751_;
v___y_1729_ = v___y_1746_;
v___y_1730_ = v___y_1747_;
v_a_1731_ = v___x_1789_;
goto v___jp_1720_;
}
}
}
}
}
v___jp_1792_:
{
lean_object* v___x_1800_; double v___x_1801_; double v___x_1802_; double v___x_1803_; double v___x_1804_; double v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1800_ = lean_io_mono_nanos_now();
v___x_1801_ = lean_float_of_nat(v___y_1798_);
v___x_1802_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1803_ = lean_float_div(v___x_1801_, v___x_1802_);
v___x_1804_ = lean_float_of_nat(v___x_1800_);
v___x_1805_ = lean_float_div(v___x_1804_, v___x_1802_);
v___x_1806_ = lean_box_float(v___x_1803_);
v___x_1807_ = lean_box_float(v___x_1805_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v_a_1799_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
lean_inc_ref(v___y_1797_);
v___x_1810_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1794_, v___y_1797_, v___y_1795_, v___y_1793_, v___y_1796_, v___f_1325_, v___x_1809_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1810_;
}
v___jp_1811_:
{
lean_object* v___x_1819_; double v___x_1820_; double v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1819_ = lean_io_get_num_heartbeats();
v___x_1820_ = lean_float_of_nat(v___y_1817_);
v___x_1821_ = lean_float_of_nat(v___x_1819_);
v___x_1822_ = lean_box_float(v___x_1820_);
v___x_1823_ = lean_box_float(v___x_1821_);
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_a_1818_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
lean_inc_ref(v___y_1816_);
v___x_1826_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1813_, v___y_1816_, v___y_1814_, v___y_1812_, v___y_1815_, v___f_1325_, v___x_1825_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1826_;
}
v___jp_1827_:
{
lean_object* v___x_1835_; lean_object* v_a_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1835_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1838_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1832_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_io_mono_nanos_now();
lean_inc(v_trace_961_);
v___x_1840_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1833_, v___y_1828_, v___y_1830_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set_tag(v___x_1843_, 1);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
v___y_1793_ = v___y_1829_;
v___y_1794_ = v___y_1831_;
v___y_1795_ = v___y_1832_;
v___y_1796_ = v_a_1836_;
v___y_1797_ = v___y_1834_;
v___y_1798_ = v___x_1839_;
v_a_1799_ = v___x_1846_;
goto v___jp_1792_;
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_a_1849_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1840_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1840_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
lean_ctor_set_tag(v___x_1851_, 0);
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
v___y_1793_ = v___y_1829_;
v___y_1794_ = v___y_1831_;
v___y_1795_ = v___y_1832_;
v___y_1796_ = v_a_1836_;
v___y_1797_ = v___y_1834_;
v___y_1798_ = v___x_1839_;
v_a_1799_ = v___x_1854_;
goto v___jp_1792_;
}
}
}
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_961_);
v___x_1858_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1833_, v___y_1828_, v___y_1830_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set_tag(v___x_1861_, 1);
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
v___y_1812_ = v___y_1829_;
v___y_1813_ = v___y_1831_;
v___y_1814_ = v___y_1832_;
v___y_1815_ = v_a_1836_;
v___y_1816_ = v___y_1834_;
v___y_1817_ = v___x_1857_;
v_a_1818_ = v___x_1864_;
goto v___jp_1811_;
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1858_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1858_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 0);
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
v___y_1812_ = v___y_1829_;
v___y_1813_ = v___y_1831_;
v___y_1814_ = v___y_1832_;
v___y_1815_ = v_a_1836_;
v___y_1816_ = v___y_1834_;
v___y_1817_ = v___x_1857_;
v_a_1818_ = v___x_1872_;
goto v___jp_1811_;
}
}
}
}
}
v___jp_1877_:
{
lean_object* v___x_1883_; lean_object* v_a_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1883_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1886_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1879_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_io_mono_nanos_now();
lean_inc(v_trace_961_);
v___x_1888_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v_n_1876_, v___y_1880_, v_acc_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
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
v___y_1291_ = v___y_1878_;
v___y_1292_ = v___y_1879_;
v___y_1293_ = v_a_1884_;
v___y_1294_ = v___y_1881_;
v___y_1295_ = v___x_1887_;
v___y_1296_ = v___y_1882_;
v_a_1297_ = v___x_1894_;
goto v___jp_1290_;
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
v___y_1291_ = v___y_1878_;
v___y_1292_ = v___y_1879_;
v___y_1293_ = v_a_1884_;
v___y_1294_ = v___y_1881_;
v___y_1295_ = v___x_1887_;
v___y_1296_ = v___y_1882_;
v_a_1297_ = v___x_1902_;
goto v___jp_1290_;
}
}
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_961_);
v___x_1906_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v_n_1876_, v___y_1880_, v_acc_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
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
v___y_1310_ = v___y_1878_;
v___y_1311_ = v___y_1879_;
v___y_1312_ = v_a_1884_;
v___y_1313_ = v___y_1881_;
v___y_1314_ = v___y_1882_;
v___y_1315_ = v___x_1905_;
v_a_1316_ = v___x_1912_;
goto v___jp_1309_;
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
v___y_1310_ = v___y_1878_;
v___y_1311_ = v___y_1879_;
v___y_1312_ = v_a_1884_;
v___y_1313_ = v___y_1881_;
v___y_1314_ = v___y_1882_;
v___y_1315_ = v___x_1905_;
v_a_1316_ = v___x_1920_;
goto v___jp_1309_;
}
}
}
}
}
v___jp_1923_:
{
if (v___y_1933_ == 0)
{
lean_object* v___x_1934_; 
lean_dec_ref(v___y_1927_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v___y_1931_);
v___x_1934_ = lean_apply_6(v___y_1930_, v___y_1931_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
if (lean_obj_tag(v_a_1935_) == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1936_ = lean_nat_add(v_n_1876_, v_one_1875_);
lean_dec(v_n_1876_);
v___x_1937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___y_1931_);
lean_ctor_set(v___x_1937_, 1, v_acc_966_);
v___x_1938_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_1939_ = l_Lean_Name_append(v___x_1938_, v_trace_961_);
v___x_1940_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1929_, v___y_1926_, v___x_1939_);
lean_dec(v___x_1939_);
if (v___x_1940_ == 0)
{
if (v___y_1928_ == 0)
{
v_n_964_ = v___x_1936_;
v_curr_965_ = v___y_1924_;
v_acc_966_ = v___x_1937_;
goto _start;
}
else
{
v___y_1242_ = v___y_1924_;
v___y_1243_ = v___y_1925_;
v___y_1244_ = v___x_1940_;
v___y_1245_ = v___y_1926_;
v___y_1246_ = v___x_1937_;
v___y_1247_ = v___x_1936_;
v___y_1248_ = v___y_1932_;
goto v___jp_1241_;
}
}
else
{
v___y_1242_ = v___y_1924_;
v___y_1243_ = v___y_1925_;
v___y_1244_ = v___x_1940_;
v___y_1245_ = v___y_1926_;
v___y_1246_ = v___x_1937_;
v___y_1247_ = v___x_1936_;
v___y_1248_ = v___y_1932_;
goto v___jp_1241_;
}
}
else
{
lean_object* v_val_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
lean_dec(v___y_1931_);
v_val_1942_ = lean_ctor_get(v_a_1935_, 0);
lean_inc(v_val_1942_);
lean_dec_ref_known(v_a_1935_, 1);
v___x_1943_ = l_List_appendTR___redArg(v_val_1942_, v___y_1924_);
v___x_1944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_1945_ = l_Lean_Name_append(v___x_1944_, v_trace_961_);
v___x_1946_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1929_, v___y_1926_, v___x_1945_);
lean_dec(v___x_1945_);
if (v___x_1946_ == 0)
{
if (v___y_1928_ == 0)
{
v_n_964_ = v_n_1876_;
v_curr_965_ = v___x_1943_;
goto _start;
}
else
{
v___y_1878_ = v___y_1925_;
v___y_1879_ = v___y_1926_;
v___y_1880_ = v___x_1943_;
v___y_1881_ = v___x_1946_;
v___y_1882_ = v___y_1932_;
goto v___jp_1877_;
}
}
else
{
v___y_1878_ = v___y_1925_;
v___y_1879_ = v___y_1926_;
v___y_1880_ = v___x_1943_;
v___y_1881_ = v___x_1946_;
v___y_1882_ = v___y_1932_;
goto v___jp_1877_;
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec(v___y_1931_);
lean_dec(v___y_1924_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
v_a_1948_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1934_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1934_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
else
{
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1924_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
return v___y_1927_;
}
}
v___jp_1956_:
{
lean_object* v___x_1967_; 
v___x_1967_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
if (v___y_1964_ == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1967_);
v___x_1969_ = lean_io_mono_nanos_now();
lean_inc(v_trace_961_);
v___x_1970_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v_n_1876_, v___y_1962_, v_acc_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1970_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1970_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
lean_ctor_set_tag(v___x_1973_, 1);
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
v___y_1655_ = v___y_1957_;
v___y_1656_ = v___y_1959_;
v___y_1657_ = v___y_1958_;
v___y_1658_ = v___y_1960_;
v___y_1659_ = v___y_1961_;
v___y_1660_ = v___x_1969_;
v___y_1661_ = v___y_1963_;
v___y_1662_ = v_a_1968_;
v___y_1663_ = v___y_1965_;
v___y_1664_ = v___y_1966_;
v_a_1665_ = v___x_1976_;
goto v___jp_1654_;
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
v_a_1979_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1970_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1970_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set_tag(v___x_1981_, 0);
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
v___y_1655_ = v___y_1957_;
v___y_1656_ = v___y_1959_;
v___y_1657_ = v___y_1958_;
v___y_1658_ = v___y_1960_;
v___y_1659_ = v___y_1961_;
v___y_1660_ = v___x_1969_;
v___y_1661_ = v___y_1963_;
v___y_1662_ = v_a_1968_;
v___y_1663_ = v___y_1965_;
v___y_1664_ = v___y_1966_;
v_a_1665_ = v___x_1984_;
goto v___jp_1654_;
}
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_a_1987_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1967_);
v___x_1988_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_961_);
v___x_1989_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v_n_1876_, v___y_1962_, v_acc_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 1);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
v___y_1678_ = v___y_1957_;
v___y_1679_ = v___y_1959_;
v___y_1680_ = v___y_1958_;
v___y_1681_ = v___x_1988_;
v___y_1682_ = v___y_1960_;
v___y_1683_ = v___y_1961_;
v___y_1684_ = v___y_1963_;
v___y_1685_ = v_a_1987_;
v___y_1686_ = v___y_1965_;
v___y_1687_ = v___y_1966_;
v_a_1688_ = v___x_1995_;
goto v___jp_1677_;
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
v_a_1998_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1989_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1989_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set_tag(v___x_2000_, 0);
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
v___y_1678_ = v___y_1957_;
v___y_1679_ = v___y_1959_;
v___y_1680_ = v___y_1958_;
v___y_1681_ = v___x_1988_;
v___y_1682_ = v___y_1960_;
v___y_1683_ = v___y_1961_;
v___y_1684_ = v___y_1963_;
v___y_1685_ = v_a_1987_;
v___y_1686_ = v___y_1965_;
v___y_1687_ = v___y_1966_;
v_a_1688_ = v___x_2003_;
goto v___jp_1677_;
}
}
}
}
}
v___jp_2006_:
{
if (v___y_2020_ == 0)
{
lean_object* v___x_2021_; 
lean_dec_ref(v___y_2018_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v___y_2012_);
v___x_2021_ = lean_apply_6(v___y_2011_, v___y_2012_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
if (lean_obj_tag(v_a_2022_) == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2023_ = lean_nat_add(v_n_1876_, v_one_1875_);
lean_dec(v_n_1876_);
v___x_2024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___y_2012_);
lean_ctor_set(v___x_2024_, 1, v_acc_966_);
v___x_2025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_2026_ = l_Lean_Name_append(v___x_2025_, v_trace_961_);
v___x_2027_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2017_, v___y_2010_, v___x_2026_);
lean_dec(v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = l_Lean_trace_profiler;
v___x_2029_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2010_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
lean_inc(v_trace_961_);
v___x_2030_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___x_2023_, v___y_2008_, v___x_2024_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1095_ = v___y_2007_;
v___y_1096_ = v___y_2016_;
v___y_1097_ = v___y_2009_;
v___y_1098_ = v___y_2010_;
v___y_1099_ = v___y_2019_;
v___y_1100_ = v___y_2014_;
v___y_1101_ = v___y_2015_;
v___y_1102_ = v___x_2030_;
goto v___jp_1094_;
}
else
{
v___y_1741_ = v___y_2007_;
v___y_1742_ = v___y_2008_;
v___y_1743_ = v___y_2009_;
v___y_1744_ = v___y_2010_;
v___y_1745_ = v___y_2013_;
v___y_1746_ = v___y_2014_;
v___y_1747_ = v___y_2015_;
v___y_1748_ = v___x_2023_;
v___y_1749_ = v___y_2016_;
v___y_1750_ = v___x_2027_;
v___y_1751_ = v___y_2019_;
v___y_1752_ = v___x_2024_;
goto v___jp_1740_;
}
}
else
{
v___y_1741_ = v___y_2007_;
v___y_1742_ = v___y_2008_;
v___y_1743_ = v___y_2009_;
v___y_1744_ = v___y_2010_;
v___y_1745_ = v___y_2013_;
v___y_1746_ = v___y_2014_;
v___y_1747_ = v___y_2015_;
v___y_1748_ = v___x_2023_;
v___y_1749_ = v___y_2016_;
v___y_1750_ = v___x_2027_;
v___y_1751_ = v___y_2019_;
v___y_1752_ = v___x_2024_;
goto v___jp_1740_;
}
}
else
{
lean_object* v_val_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
lean_dec(v___y_2012_);
v_val_2031_ = lean_ctor_get(v_a_2022_, 0);
lean_inc(v_val_2031_);
lean_dec_ref_known(v_a_2022_, 1);
v___x_2032_ = l_List_appendTR___redArg(v_val_2031_, v___y_2008_);
v___x_2033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_2034_ = l_Lean_Name_append(v___x_2033_, v_trace_961_);
v___x_2035_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2017_, v___y_2010_, v___x_2034_);
lean_dec(v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = l_Lean_trace_profiler;
v___x_2037_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2010_, v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; 
lean_inc(v_trace_961_);
v___x_2038_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v_n_1876_, v___x_2032_, v_acc_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1095_ = v___y_2007_;
v___y_1096_ = v___y_2016_;
v___y_1097_ = v___y_2009_;
v___y_1098_ = v___y_2010_;
v___y_1099_ = v___y_2019_;
v___y_1100_ = v___y_2014_;
v___y_1101_ = v___y_2015_;
v___y_1102_ = v___x_2038_;
goto v___jp_1094_;
}
else
{
v___y_1957_ = v___y_2007_;
v___y_1958_ = v___y_2009_;
v___y_1959_ = v___y_2016_;
v___y_1960_ = v___y_2010_;
v___y_1961_ = v___x_2035_;
v___y_1962_ = v___x_2032_;
v___y_1963_ = v___y_2019_;
v___y_1964_ = v___y_2013_;
v___y_1965_ = v___y_2014_;
v___y_1966_ = v___y_2015_;
goto v___jp_1956_;
}
}
else
{
v___y_1957_ = v___y_2007_;
v___y_1958_ = v___y_2009_;
v___y_1959_ = v___y_2016_;
v___y_1960_ = v___y_2010_;
v___y_1961_ = v___x_2035_;
v___y_1962_ = v___x_2032_;
v___y_1963_ = v___y_2019_;
v___y_1964_ = v___y_2013_;
v___y_1965_ = v___y_2014_;
v___y_1966_ = v___y_2015_;
goto v___jp_1956_;
}
}
}
else
{
lean_object* v_a_2039_; 
lean_dec(v___y_2012_);
lean_dec(v___y_2008_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec_ref(v_cfg_960_);
v_a_2039_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2021_, 1);
v___y_1085_ = v___y_2007_;
v___y_1086_ = v___y_2009_;
v___y_1087_ = v___y_2016_;
v___y_1088_ = v___y_2010_;
v___y_1089_ = v___y_2019_;
v___y_1090_ = v___y_2014_;
v___y_1091_ = v___y_2015_;
v_a_1092_ = v_a_2039_;
goto v___jp_1084_;
}
}
else
{
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2008_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec_ref(v_cfg_960_);
v___y_1085_ = v___y_2007_;
v___y_1086_ = v___y_2009_;
v___y_1087_ = v___y_2016_;
v___y_1088_ = v___y_2010_;
v___y_1089_ = v___y_2019_;
v___y_1090_ = v___y_2014_;
v___y_1091_ = v___y_2015_;
v_a_1092_ = v___y_2018_;
goto v___jp_1084_;
}
}
v___jp_2040_:
{
lean_object* v___x_2051_; 
v___x_2051_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
if (v___y_2047_ == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
v___x_2053_ = lean_io_mono_nanos_now();
lean_inc(v_trace_961_);
v___x_2054_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v_n_1876_, v___y_2048_, v_acc_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set_tag(v___x_2057_, 1);
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
v___y_1537_ = v___y_2041_;
v___y_1538_ = v___y_2043_;
v___y_1539_ = v___y_2042_;
v___y_1540_ = v___y_2044_;
v___y_1541_ = v___y_2045_;
v___y_1542_ = v_a_2052_;
v___y_1543_ = v___y_2046_;
v___y_1544_ = v___y_2049_;
v___y_1545_ = v___y_2050_;
v___y_1546_ = v___x_2053_;
v_a_1547_ = v___x_2060_;
goto v___jp_1536_;
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
v_a_2063_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2054_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2054_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set_tag(v___x_2065_, 0);
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
v___y_1537_ = v___y_2041_;
v___y_1538_ = v___y_2043_;
v___y_1539_ = v___y_2042_;
v___y_1540_ = v___y_2044_;
v___y_1541_ = v___y_2045_;
v___y_1542_ = v_a_2052_;
v___y_1543_ = v___y_2046_;
v___y_1544_ = v___y_2049_;
v___y_1545_ = v___y_2050_;
v___y_1546_ = v___x_2053_;
v_a_1547_ = v___x_2068_;
goto v___jp_1536_;
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v_a_2071_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2071_);
lean_dec_ref(v___x_2051_);
v___x_2072_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_961_);
v___x_2073_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v_n_1876_, v___y_2048_, v_acc_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
lean_ctor_set_tag(v___x_2076_, 1);
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
v___y_1517_ = v___y_2041_;
v___y_1518_ = v___y_2043_;
v___y_1519_ = v___y_2042_;
v___y_1520_ = v___y_2044_;
v___y_1521_ = v___y_2045_;
v___y_1522_ = v_a_2071_;
v___y_1523_ = v___y_2046_;
v___y_1524_ = v___y_2049_;
v___y_1525_ = v___x_2072_;
v___y_1526_ = v___y_2050_;
v_a_1527_ = v___x_2079_;
goto v___jp_1516_;
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2073_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2073_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 0);
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
v___y_1517_ = v___y_2041_;
v___y_1518_ = v___y_2043_;
v___y_1519_ = v___y_2042_;
v___y_1520_ = v___y_2044_;
v___y_1521_ = v___y_2045_;
v___y_1522_ = v_a_2071_;
v___y_1523_ = v___y_2046_;
v___y_1524_ = v___y_2049_;
v___y_1525_ = v___x_2072_;
v___y_1526_ = v___y_2050_;
v_a_1527_ = v___x_2087_;
goto v___jp_1516_;
}
}
}
}
}
v___jp_2090_:
{
if (v___y_2104_ == 0)
{
lean_object* v___x_2105_; 
lean_dec_ref(v___y_2102_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v___y_2097_);
v___x_2105_ = lean_apply_6(v___y_2096_, v___y_2097_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
if (lean_obj_tag(v_a_2106_) == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2107_ = lean_nat_add(v_n_1876_, v_one_1875_);
lean_dec(v_n_1876_);
v___x_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___y_2097_);
lean_ctor_set(v___x_2108_, 1, v_acc_966_);
v___x_2109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_2110_ = l_Lean_Name_append(v___x_2109_, v_trace_961_);
v___x_2111_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2101_, v___y_2095_, v___x_2110_);
lean_dec(v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = l_Lean_trace_profiler;
v___x_2113_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2095_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_inc(v_trace_961_);
v___x_2114_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___x_2107_, v___y_2092_, v___x_2108_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1146_ = v___y_2091_;
v___y_1147_ = v___y_2100_;
v___y_1148_ = v___y_2093_;
v___y_1149_ = v___y_2094_;
v___y_1150_ = v___y_2095_;
v___y_1151_ = v___y_2103_;
v___y_1152_ = v___y_2099_;
v___y_1153_ = v___x_2114_;
goto v___jp_1145_;
}
else
{
v___y_1465_ = v___y_2091_;
v___y_1466_ = v___y_2092_;
v___y_1467_ = v___y_2093_;
v___y_1468_ = v___y_2094_;
v___y_1469_ = v___y_2095_;
v___y_1470_ = v___y_2098_;
v___y_1471_ = v___x_2111_;
v___y_1472_ = v___y_2099_;
v___y_1473_ = v___x_2107_;
v___y_1474_ = v___y_2100_;
v___y_1475_ = v___x_2108_;
v___y_1476_ = v___y_2103_;
goto v___jp_1464_;
}
}
else
{
v___y_1465_ = v___y_2091_;
v___y_1466_ = v___y_2092_;
v___y_1467_ = v___y_2093_;
v___y_1468_ = v___y_2094_;
v___y_1469_ = v___y_2095_;
v___y_1470_ = v___y_2098_;
v___y_1471_ = v___x_2111_;
v___y_1472_ = v___y_2099_;
v___y_1473_ = v___x_2107_;
v___y_1474_ = v___y_2100_;
v___y_1475_ = v___x_2108_;
v___y_1476_ = v___y_2103_;
goto v___jp_1464_;
}
}
else
{
lean_object* v_val_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
lean_dec(v___y_2097_);
v_val_2115_ = lean_ctor_get(v_a_2106_, 0);
lean_inc(v_val_2115_);
lean_dec_ref_known(v_a_2106_, 1);
v___x_2116_ = l_List_appendTR___redArg(v_val_2115_, v___y_2092_);
v___x_2117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_2118_ = l_Lean_Name_append(v___x_2117_, v_trace_961_);
v___x_2119_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2101_, v___y_2095_, v___x_2118_);
lean_dec(v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = l_Lean_trace_profiler;
v___x_2121_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2095_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; 
lean_inc(v_trace_961_);
v___x_2122_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v_n_1876_, v___x_2116_, v_acc_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1146_ = v___y_2091_;
v___y_1147_ = v___y_2100_;
v___y_1148_ = v___y_2093_;
v___y_1149_ = v___y_2094_;
v___y_1150_ = v___y_2095_;
v___y_1151_ = v___y_2103_;
v___y_1152_ = v___y_2099_;
v___y_1153_ = v___x_2122_;
goto v___jp_1145_;
}
else
{
v___y_2041_ = v___y_2091_;
v___y_2042_ = v___y_2093_;
v___y_2043_ = v___y_2100_;
v___y_2044_ = v___y_2094_;
v___y_2045_ = v___y_2095_;
v___y_2046_ = v___y_2103_;
v___y_2047_ = v___y_2098_;
v___y_2048_ = v___x_2116_;
v___y_2049_ = v___x_2119_;
v___y_2050_ = v___y_2099_;
goto v___jp_2040_;
}
}
else
{
v___y_2041_ = v___y_2091_;
v___y_2042_ = v___y_2093_;
v___y_2043_ = v___y_2100_;
v___y_2044_ = v___y_2094_;
v___y_2045_ = v___y_2095_;
v___y_2046_ = v___y_2103_;
v___y_2047_ = v___y_2098_;
v___y_2048_ = v___x_2116_;
v___y_2049_ = v___x_2119_;
v___y_2050_ = v___y_2099_;
goto v___jp_2040_;
}
}
}
else
{
lean_object* v_a_2123_; 
lean_dec(v___y_2097_);
lean_dec(v___y_2092_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec_ref(v_cfg_960_);
v_a_2123_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2105_, 1);
v___y_1136_ = v___y_2091_;
v___y_1137_ = v___y_2093_;
v___y_1138_ = v___y_2100_;
v___y_1139_ = v___y_2094_;
v___y_1140_ = v___y_2095_;
v___y_1141_ = v___y_2103_;
v___y_1142_ = v___y_2099_;
v_a_1143_ = v_a_2123_;
goto v___jp_1135_;
}
}
else
{
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2092_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec_ref(v_cfg_960_);
v___y_1136_ = v___y_2091_;
v___y_1137_ = v___y_2093_;
v___y_1138_ = v___y_2100_;
v___y_1139_ = v___y_2094_;
v___y_1140_ = v___y_2095_;
v___y_1141_ = v___y_2103_;
v___y_1142_ = v___y_2099_;
v_a_1143_ = v___y_2102_;
goto v___jp_1135_;
}
}
v___jp_2124_:
{
lean_object* v___x_2137_; lean_object* v_a_2138_; lean_object* v___x_2139_; uint8_t v___x_2140_; 
v___x_2137_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref(v___x_2137_);
v___x_2139_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2140_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2129_, v___x_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec_ref(v___y_2135_);
v___x_2141_ = lean_io_mono_nanos_now();
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v___y_2131_);
v___x_2142_ = lean_apply_6(v___y_2126_, v___y_2131_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; uint8_t v___x_2144_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2144_ = lean_unbox(v_a_2143_);
lean_dec(v_a_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; 
lean_inc_ref(v_next_962_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v___y_2131_);
v___x_2145_ = lean_apply_7(v_next_962_, v___y_2131_, v___y_2136_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; 
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2127_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec_ref(v_cfg_960_);
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v___y_1126_ = v___y_2125_;
v___y_1127_ = v___y_2128_;
v___y_1128_ = v___y_2133_;
v___y_1129_ = v___x_2141_;
v___y_1130_ = v___y_2129_;
v___y_1131_ = v_a_2138_;
v___y_1132_ = v___y_2132_;
v_a_1133_ = v_a_2146_;
goto v___jp_1125_;
}
else
{
lean_object* v_a_2147_; uint8_t v___x_2148_; 
v_a_2147_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2148_ = l_Lean_Exception_isInterrupt(v_a_2147_);
if (v___x_2148_ == 0)
{
uint8_t v___x_2149_; 
lean_inc(v_a_2147_);
v___x_2149_ = l_Lean_Exception_isRuntime(v_a_2147_);
v___y_2091_ = v___y_2125_;
v___y_2092_ = v___y_2127_;
v___y_2093_ = v___y_2128_;
v___y_2094_ = v___x_2141_;
v___y_2095_ = v___y_2129_;
v___y_2096_ = v___y_2130_;
v___y_2097_ = v___y_2131_;
v___y_2098_ = v___x_2140_;
v___y_2099_ = v___y_2132_;
v___y_2100_ = v___y_2133_;
v___y_2101_ = v___y_2134_;
v___y_2102_ = v_a_2147_;
v___y_2103_ = v_a_2138_;
v___y_2104_ = v___x_2149_;
goto v___jp_2090_;
}
else
{
v___y_2091_ = v___y_2125_;
v___y_2092_ = v___y_2127_;
v___y_2093_ = v___y_2128_;
v___y_2094_ = v___x_2141_;
v___y_2095_ = v___y_2129_;
v___y_2096_ = v___y_2130_;
v___y_2097_ = v___y_2131_;
v___y_2098_ = v___x_2140_;
v___y_2099_ = v___y_2132_;
v___y_2100_ = v___y_2133_;
v___y_2101_ = v___y_2134_;
v___y_2102_ = v_a_2147_;
v___y_2103_ = v_a_2138_;
v___y_2104_ = v___x_2148_;
goto v___jp_2090_;
}
}
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
lean_dec_ref(v___y_2136_);
lean_dec_ref(v___y_2130_);
v___x_2150_ = lean_nat_add(v_n_1876_, v_one_1875_);
lean_dec(v_n_1876_);
v___x_2151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___y_2131_);
lean_ctor_set(v___x_2151_, 1, v_acc_966_);
v___x_2152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_2153_ = l_Lean_Name_append(v___x_2152_, v_trace_961_);
v___x_2154_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2134_, v___y_2129_, v___x_2153_);
lean_dec(v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = l_Lean_trace_profiler;
v___x_2156_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2129_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
lean_inc(v_trace_961_);
v___x_2157_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___x_2150_, v___y_2127_, v___x_2151_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1146_ = v___y_2125_;
v___y_1147_ = v___y_2133_;
v___y_1148_ = v___y_2128_;
v___y_1149_ = v___x_2141_;
v___y_1150_ = v___y_2129_;
v___y_1151_ = v_a_2138_;
v___y_1152_ = v___y_2132_;
v___y_1153_ = v___x_2157_;
goto v___jp_1145_;
}
else
{
v___y_1603_ = v___y_2125_;
v___y_1604_ = v___y_2127_;
v___y_1605_ = v___y_2128_;
v___y_1606_ = v___x_2141_;
v___y_1607_ = v___y_2129_;
v___y_1608_ = v___x_2150_;
v___y_1609_ = v___x_2140_;
v___y_1610_ = v___x_2154_;
v___y_1611_ = v___y_2132_;
v___y_1612_ = v___y_2133_;
v___y_1613_ = v_a_2138_;
v___y_1614_ = v___x_2151_;
goto v___jp_1602_;
}
}
else
{
v___y_1603_ = v___y_2125_;
v___y_1604_ = v___y_2127_;
v___y_1605_ = v___y_2128_;
v___y_1606_ = v___x_2141_;
v___y_1607_ = v___y_2129_;
v___y_1608_ = v___x_2150_;
v___y_1609_ = v___x_2140_;
v___y_1610_ = v___x_2154_;
v___y_1611_ = v___y_2132_;
v___y_1612_ = v___y_2133_;
v___y_1613_ = v_a_2138_;
v___y_1614_ = v___x_2151_;
goto v___jp_1602_;
}
}
}
else
{
lean_object* v_a_2158_; 
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2127_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec_ref(v_cfg_960_);
v_a_2158_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2142_, 1);
v___y_1136_ = v___y_2125_;
v___y_1137_ = v___y_2128_;
v___y_1138_ = v___y_2133_;
v___y_1139_ = v___x_2141_;
v___y_1140_ = v___y_2129_;
v___y_1141_ = v_a_2138_;
v___y_1142_ = v___y_2132_;
v_a_1143_ = v_a_2158_;
goto v___jp_1135_;
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec_ref(v___y_2136_);
v___x_2159_ = lean_io_get_num_heartbeats();
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v___y_2131_);
v___x_2160_ = lean_apply_6(v___y_2126_, v___y_2131_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; uint8_t v___x_2162_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = lean_unbox(v_a_2161_);
lean_dec(v_a_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; 
lean_inc_ref(v_next_962_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v___y_2131_);
v___x_2163_ = lean_apply_7(v_next_962_, v___y_2131_, v___y_2135_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; 
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2127_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec_ref(v_cfg_960_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v___y_1075_ = v___y_2125_;
v___y_1076_ = v___y_2128_;
v___y_1077_ = v___y_2133_;
v___y_1078_ = v___y_2129_;
v___y_1079_ = v_a_2138_;
v___y_1080_ = v___x_2159_;
v___y_1081_ = v___y_2132_;
v_a_1082_ = v_a_2164_;
goto v___jp_1074_;
}
else
{
lean_object* v_a_2165_; uint8_t v___x_2166_; 
v_a_2165_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2163_, 1);
v___x_2166_ = l_Lean_Exception_isInterrupt(v_a_2165_);
if (v___x_2166_ == 0)
{
uint8_t v___x_2167_; 
lean_inc(v_a_2165_);
v___x_2167_ = l_Lean_Exception_isRuntime(v_a_2165_);
v___y_2007_ = v___y_2125_;
v___y_2008_ = v___y_2127_;
v___y_2009_ = v___y_2128_;
v___y_2010_ = v___y_2129_;
v___y_2011_ = v___y_2130_;
v___y_2012_ = v___y_2131_;
v___y_2013_ = v___x_2140_;
v___y_2014_ = v___x_2159_;
v___y_2015_ = v___y_2132_;
v___y_2016_ = v___y_2133_;
v___y_2017_ = v___y_2134_;
v___y_2018_ = v_a_2165_;
v___y_2019_ = v_a_2138_;
v___y_2020_ = v___x_2167_;
goto v___jp_2006_;
}
else
{
v___y_2007_ = v___y_2125_;
v___y_2008_ = v___y_2127_;
v___y_2009_ = v___y_2128_;
v___y_2010_ = v___y_2129_;
v___y_2011_ = v___y_2130_;
v___y_2012_ = v___y_2131_;
v___y_2013_ = v___x_2140_;
v___y_2014_ = v___x_2159_;
v___y_2015_ = v___y_2132_;
v___y_2016_ = v___y_2133_;
v___y_2017_ = v___y_2134_;
v___y_2018_ = v_a_2165_;
v___y_2019_ = v_a_2138_;
v___y_2020_ = v___x_2166_;
goto v___jp_2006_;
}
}
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
lean_dec_ref(v___y_2135_);
lean_dec_ref(v___y_2130_);
v___x_2168_ = lean_nat_add(v_n_1876_, v_one_1875_);
lean_dec(v_n_1876_);
v___x_2169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___y_2131_);
lean_ctor_set(v___x_2169_, 1, v_acc_966_);
v___x_2170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_2171_ = l_Lean_Name_append(v___x_2170_, v_trace_961_);
v___x_2172_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2134_, v___y_2129_, v___x_2171_);
lean_dec(v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = l_Lean_trace_profiler;
v___x_2174_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2129_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; 
lean_inc(v_trace_961_);
v___x_2175_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___x_2168_, v___y_2127_, v___x_2169_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
v___y_1095_ = v___y_2125_;
v___y_1096_ = v___y_2133_;
v___y_1097_ = v___y_2128_;
v___y_1098_ = v___y_2129_;
v___y_1099_ = v_a_2138_;
v___y_1100_ = v___x_2159_;
v___y_1101_ = v___y_2132_;
v___y_1102_ = v___x_2175_;
goto v___jp_1094_;
}
else
{
v___y_1370_ = v___y_2125_;
v___y_1371_ = v___y_2127_;
v___y_1372_ = v___y_2128_;
v___y_1373_ = v___x_2172_;
v___y_1374_ = v___y_2129_;
v___y_1375_ = v___x_2140_;
v___y_1376_ = v___x_2159_;
v___y_1377_ = v___y_2132_;
v___y_1378_ = v___x_2168_;
v___y_1379_ = v___y_2133_;
v___y_1380_ = v_a_2138_;
v___y_1381_ = v___x_2169_;
goto v___jp_1369_;
}
}
else
{
v___y_1370_ = v___y_2125_;
v___y_1371_ = v___y_2127_;
v___y_1372_ = v___y_2128_;
v___y_1373_ = v___x_2172_;
v___y_1374_ = v___y_2129_;
v___y_1375_ = v___x_2140_;
v___y_1376_ = v___x_2159_;
v___y_1377_ = v___y_2132_;
v___y_1378_ = v___x_2168_;
v___y_1379_ = v___y_2133_;
v___y_1380_ = v_a_2138_;
v___y_1381_ = v___x_2169_;
goto v___jp_1369_;
}
}
}
else
{
lean_object* v_a_2176_; 
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2127_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec_ref(v_cfg_960_);
v_a_2176_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2160_, 1);
v___y_1085_ = v___y_2125_;
v___y_1086_ = v___y_2128_;
v___y_1087_ = v___y_2133_;
v___y_1088_ = v___y_2129_;
v___y_1089_ = v_a_2138_;
v___y_1090_ = v___x_2159_;
v___y_1091_ = v___y_2132_;
v_a_1092_ = v_a_2176_;
goto v___jp_1084_;
}
}
}
v___jp_2177_:
{
if (v___y_2182_ == 0)
{
lean_object* v___x_2183_; 
lean_dec_ref(v___y_2179_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v___y_2181_);
v___x_2183_ = lean_apply_6(v___y_2180_, v___y_2181_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___x_2183_, 1);
if (lean_obj_tag(v_a_2184_) == 0)
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = lean_nat_add(v_n_1876_, v_one_1875_);
lean_dec(v_n_1876_);
v___x_2186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___y_2181_);
lean_ctor_set(v___x_2186_, 1, v_acc_966_);
v_n_964_ = v___x_2185_;
v_curr_965_ = v___y_2178_;
v_acc_966_ = v___x_2186_;
goto _start;
}
else
{
lean_object* v_val_2188_; lean_object* v___x_2189_; 
lean_dec(v___y_2181_);
v_val_2188_ = lean_ctor_get(v_a_2184_, 0);
lean_inc(v_val_2188_);
lean_dec_ref_known(v_a_2184_, 1);
v___x_2189_ = l_List_appendTR___redArg(v_val_2188_, v___y_2178_);
v_n_964_ = v_n_1876_;
v_curr_965_ = v___x_2189_;
goto _start;
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec(v___y_2181_);
lean_dec(v___y_2178_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
v_a_2191_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2183_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2183_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2178_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
return v___y_2179_;
}
}
v___jp_2199_:
{
if (lean_obj_tag(v_a_2200_) == 0)
{
if (lean_obj_tag(v_curr_965_) == 0)
{
lean_object* v_toCold_2201_; lean_object* v_options_2202_; lean_object* v_inheritedTraceOptions_2203_; uint8_t v_hasTrace_2204_; lean_object* v___x_2205_; 
lean_dec(v_n_1876_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec_ref(v_cfg_960_);
v_toCold_2201_ = lean_ctor_get(v_a_969_, 0);
v_options_2202_ = lean_ctor_get(v_toCold_2201_, 2);
v_inheritedTraceOptions_2203_ = lean_ctor_get(v_toCold_2201_, 11);
v_hasTrace_2204_ = lean_ctor_get_uint8(v_options_2202_, sizeof(void*)*1);
v___x_2205_ = l_List_reverse___redArg(v_acc_966_);
if (v_hasTrace_2204_ == 0)
{
lean_object* v___x_2206_; 
lean_dec(v_trace_961_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_2209_ = l_Lean_Name_append(v___x_2208_, v_trace_961_);
v___x_2210_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2203_, v_options_2202_, v___x_2209_);
lean_dec(v___x_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = l_Lean_trace_profiler;
v___x_2212_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2202_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; 
lean_dec(v_trace_961_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2205_);
return v___x_2213_;
}
else
{
v___y_1165_ = v___x_2207_;
v___y_1166_ = v___x_2210_;
v___y_1167_ = v_options_2202_;
v___y_1168_ = v___x_2205_;
v___y_1169_ = v_hasTrace_2204_;
goto v___jp_1164_;
}
}
else
{
v___y_1165_ = v___x_2207_;
v___y_1166_ = v___x_2210_;
v___y_1167_ = v_options_2202_;
v___y_1168_ = v___x_2205_;
v___y_1169_ = v_hasTrace_2204_;
goto v___jp_1164_;
}
}
}
else
{
lean_object* v_head_2214_; lean_object* v_tail_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2289_; 
v_head_2214_ = lean_ctor_get(v_curr_965_, 0);
v_tail_2215_ = lean_ctor_get(v_curr_965_, 1);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_curr_965_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2217_ = v_curr_965_;
v_isShared_2218_ = v_isSharedCheck_2289_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_tail_2215_);
lean_inc(v_head_2214_);
lean_dec(v_curr_965_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2289_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___f_2219_; lean_object* v___f_2220_; lean_object* v___f_2221_; lean_object* v___x_2222_; lean_object* v_a_2223_; uint8_t v___x_2224_; uint8_t v___x_2225_; 
lean_inc(v_acc_966_);
lean_inc(v_n_1876_);
lean_inc(v_goals_963_);
lean_inc_ref(v_next_962_);
lean_inc(v_trace_961_);
lean_inc_ref(v_cfg_960_);
lean_inc(v_tail_2215_);
v___f_2219_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2219_, 0, v_tail_2215_);
lean_closure_set(v___f_2219_, 1, v_cfg_960_);
lean_closure_set(v___f_2219_, 2, v_trace_961_);
lean_closure_set(v___f_2219_, 3, v_next_962_);
lean_closure_set(v___f_2219_, 4, v_goals_963_);
lean_closure_set(v___f_2219_, 5, v_n_1876_);
lean_closure_set(v___f_2219_, 6, v_acc_966_);
lean_inc_n(v_head_2214_, 2);
v___f_2220_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___boxed), 7, 1);
lean_closure_set(v___f_2220_, 0, v_head_2214_);
v___f_2221_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(v___f_2221_, 0, v_head_2214_);
v___x_2222_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2214_, v_a_968_);
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = 1;
v___x_2225_ = lean_unbox(v_a_2223_);
lean_dec(v_a_2223_);
if (v___x_2225_ == 0)
{
lean_object* v_toCold_2226_; lean_object* v_options_2227_; uint8_t v_hasTrace_2228_; 
lean_dec_ref(v___f_2220_);
v_toCold_2226_ = lean_ctor_get(v_a_969_, 0);
v_options_2227_ = lean_ctor_get(v_toCold_2226_, 2);
v_hasTrace_2228_ = lean_ctor_get_uint8(v_options_2227_, sizeof(void*)*1);
if (v_hasTrace_2228_ == 0)
{
lean_object* v___x_2229_; 
lean_dec_ref(v___f_2221_);
lean_inc_ref(v_suspend_1161_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v_head_2214_);
v___x_2229_ = lean_apply_6(v_suspend_1161_, v_head_2214_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
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
lean_object* v___x_2232_; 
lean_del_object(v___x_2217_);
lean_inc_ref(v_next_962_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v_head_2214_);
v___x_2232_ = lean_apply_7(v_next_962_, v_head_2214_, v___f_2219_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_dec(v_tail_2215_);
lean_dec(v_head_2214_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
return v___x_2232_;
}
else
{
lean_object* v_a_2233_; uint8_t v___x_2234_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
v___x_2234_ = l_Lean_Exception_isInterrupt(v_a_2233_);
if (v___x_2234_ == 0)
{
uint8_t v___x_2235_; 
v___x_2235_ = l_Lean_Exception_isRuntime(v_a_2233_);
lean_inc_ref(v_discharge_1162_);
v___y_2178_ = v_tail_2215_;
v___y_2179_ = v___x_2232_;
v___y_2180_ = v_discharge_1162_;
v___y_2181_ = v_head_2214_;
v___y_2182_ = v___x_2235_;
goto v___jp_2177_;
}
else
{
lean_dec(v_a_2233_);
lean_inc_ref(v_discharge_1162_);
v___y_2178_ = v_tail_2215_;
v___y_2179_ = v___x_2232_;
v___y_2180_ = v_discharge_1162_;
v___y_2181_ = v_head_2214_;
v___y_2182_ = v___x_2234_;
goto v___jp_2177_;
}
}
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
lean_dec_ref(v___f_2219_);
v___x_2236_ = lean_nat_add(v_n_1876_, v_one_1875_);
lean_dec(v_n_1876_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v_acc_966_);
v___x_2238_ = v___x_2217_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_head_2214_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_acc_966_);
v___x_2238_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
v_n_964_ = v___x_2236_;
v_curr_965_ = v_tail_2215_;
v_acc_966_ = v___x_2238_;
goto _start;
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec_ref(v___f_2219_);
lean_del_object(v___x_2217_);
lean_dec(v_tail_2215_);
lean_dec(v_head_2214_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
v_a_2241_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2229_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2229_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; 
v_inheritedTraceOptions_2249_ = lean_ctor_get(v_toCold_2226_, 11);
v___x_2250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_2252_ = l_Lean_Name_append(v___x_2251_, v_trace_961_);
v___x_2253_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2249_, v_options_2227_, v___x_2252_);
lean_dec(v___x_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2254_ = l_Lean_trace_profiler;
v___x_2255_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2227_, v___x_2254_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; 
lean_dec_ref(v___f_2221_);
lean_inc_ref(v_suspend_1161_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v_head_2214_);
v___x_2256_ = lean_apply_6(v_suspend_1161_, v_head_2214_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; uint8_t v___x_2258_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2256_, 1);
v___x_2258_ = lean_unbox(v_a_2257_);
lean_dec(v_a_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; 
lean_del_object(v___x_2217_);
lean_inc_ref(v_next_962_);
lean_inc(v_a_970_);
lean_inc_ref(v_a_969_);
lean_inc(v_a_968_);
lean_inc_ref(v_a_967_);
lean_inc(v_head_2214_);
v___x_2259_ = lean_apply_7(v_next_962_, v_head_2214_, v___f_2219_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, lean_box(0));
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_dec(v_tail_2215_);
lean_dec(v_head_2214_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
return v___x_2259_;
}
else
{
lean_object* v_a_2260_; uint8_t v___x_2261_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
v___x_2261_ = l_Lean_Exception_isInterrupt(v_a_2260_);
if (v___x_2261_ == 0)
{
uint8_t v___x_2262_; 
v___x_2262_ = l_Lean_Exception_isRuntime(v_a_2260_);
lean_inc_ref(v_discharge_1162_);
v___y_1924_ = v_tail_2215_;
v___y_1925_ = v___x_2224_;
v___y_1926_ = v_options_2227_;
v___y_1927_ = v___x_2259_;
v___y_1928_ = v___x_2255_;
v___y_1929_ = v_inheritedTraceOptions_2249_;
v___y_1930_ = v_discharge_1162_;
v___y_1931_ = v_head_2214_;
v___y_1932_ = v___x_2250_;
v___y_1933_ = v___x_2262_;
goto v___jp_1923_;
}
else
{
lean_dec(v_a_2260_);
lean_inc_ref(v_discharge_1162_);
v___y_1924_ = v_tail_2215_;
v___y_1925_ = v___x_2224_;
v___y_1926_ = v_options_2227_;
v___y_1927_ = v___x_2259_;
v___y_1928_ = v___x_2255_;
v___y_1929_ = v_inheritedTraceOptions_2249_;
v___y_1930_ = v_discharge_1162_;
v___y_1931_ = v_head_2214_;
v___y_1932_ = v___x_2250_;
v___y_1933_ = v___x_2261_;
goto v___jp_1923_;
}
}
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2265_; 
lean_dec_ref(v___f_2219_);
v___x_2263_ = lean_nat_add(v_n_1876_, v_one_1875_);
lean_dec(v_n_1876_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v_acc_966_);
v___x_2265_ = v___x_2217_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_head_2214_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_acc_966_);
v___x_2265_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
if (v___x_2253_ == 0)
{
if (v___x_2255_ == 0)
{
v_n_964_ = v___x_2263_;
v_curr_965_ = v_tail_2215_;
v_acc_966_ = v___x_2265_;
goto _start;
}
else
{
v___y_1828_ = v_tail_2215_;
v___y_1829_ = v___x_2253_;
v___y_1830_ = v___x_2265_;
v___y_1831_ = v___x_2224_;
v___y_1832_ = v_options_2227_;
v___y_1833_ = v___x_2263_;
v___y_1834_ = v___x_2250_;
goto v___jp_1827_;
}
}
else
{
v___y_1828_ = v_tail_2215_;
v___y_1829_ = v___x_2253_;
v___y_1830_ = v___x_2265_;
v___y_1831_ = v___x_2224_;
v___y_1832_ = v_options_2227_;
v___y_1833_ = v___x_2263_;
v___y_1834_ = v___x_2250_;
goto v___jp_1827_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v___f_2219_);
lean_del_object(v___x_2217_);
lean_dec(v_tail_2215_);
lean_dec(v_head_2214_);
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
v_a_2268_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2256_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2256_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_del_object(v___x_2217_);
lean_inc_ref(v___f_2219_);
lean_inc_ref(v_discharge_1162_);
lean_inc_ref(v_suspend_1161_);
v___y_2125_ = v___f_2221_;
v___y_2126_ = v_suspend_1161_;
v___y_2127_ = v_tail_2215_;
v___y_2128_ = v___x_2224_;
v___y_2129_ = v_options_2227_;
v___y_2130_ = v_discharge_1162_;
v___y_2131_ = v_head_2214_;
v___y_2132_ = v___x_2250_;
v___y_2133_ = v___x_2253_;
v___y_2134_ = v_inheritedTraceOptions_2249_;
v___y_2135_ = v___f_2219_;
v___y_2136_ = v___f_2219_;
goto v___jp_2124_;
}
}
else
{
lean_del_object(v___x_2217_);
lean_inc_ref(v___f_2219_);
lean_inc_ref(v_discharge_1162_);
lean_inc_ref(v_suspend_1161_);
v___y_2125_ = v___f_2221_;
v___y_2126_ = v_suspend_1161_;
v___y_2127_ = v_tail_2215_;
v___y_2128_ = v___x_2224_;
v___y_2129_ = v_options_2227_;
v___y_2130_ = v_discharge_1162_;
v___y_2131_ = v_head_2214_;
v___y_2132_ = v___x_2250_;
v___y_2133_ = v___x_2253_;
v___y_2134_ = v_inheritedTraceOptions_2249_;
v___y_2135_ = v___f_2219_;
v___y_2136_ = v___f_2219_;
goto v___jp_2124_;
}
}
}
else
{
lean_object* v_toCold_2276_; lean_object* v_options_2277_; lean_object* v_inheritedTraceOptions_2278_; uint8_t v_hasTrace_2279_; lean_object* v___x_2280_; 
lean_dec_ref(v___f_2221_);
lean_dec_ref(v___f_2219_);
lean_del_object(v___x_2217_);
lean_dec(v_head_2214_);
v_toCold_2276_ = lean_ctor_get(v_a_969_, 0);
v_options_2277_ = lean_ctor_get(v_toCold_2276_, 2);
v_inheritedTraceOptions_2278_ = lean_ctor_get(v_toCold_2276_, 11);
v_hasTrace_2279_ = lean_ctor_get_uint8(v_options_2277_, sizeof(void*)*1);
v___x_2280_ = lean_nat_add(v_n_1876_, v_one_1875_);
lean_dec(v_n_1876_);
if (v_hasTrace_2279_ == 0)
{
lean_dec_ref(v___f_2220_);
v_n_964_ = v___x_2280_;
v_curr_965_ = v_tail_2215_;
goto _start;
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v___x_2282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_961_);
v___x_2284_ = l_Lean_Name_append(v___x_2283_, v_trace_961_);
v___x_2285_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2278_, v_options_2277_, v___x_2284_);
lean_dec(v___x_2284_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = l_Lean_trace_profiler;
v___x_2287_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2277_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_dec_ref(v___f_2220_);
v_n_964_ = v___x_2280_;
v_curr_965_ = v_tail_2215_;
goto _start;
}
else
{
v___y_1010_ = v___x_2280_;
v___y_1011_ = v___x_2285_;
v___y_1012_ = v_tail_2215_;
v___y_1013_ = v_options_2277_;
v___y_1014_ = v___x_2224_;
v___y_1015_ = v___f_2220_;
v___y_1016_ = v___x_2282_;
goto v___jp_1009_;
}
}
else
{
v___y_1010_ = v___x_2280_;
v___y_1011_ = v___x_2285_;
v___y_1012_ = v_tail_2215_;
v___y_1013_ = v_options_2277_;
v___y_1014_ = v___x_2224_;
v___y_1015_ = v___f_2220_;
v___y_1016_ = v___x_2282_;
goto v___jp_1009_;
}
}
}
}
}
}
else
{
lean_object* v_val_2290_; 
lean_dec(v_curr_965_);
v_val_2290_ = lean_ctor_get(v_a_2200_, 0);
lean_inc(v_val_2290_);
lean_dec_ref_known(v_a_2200_, 1);
v_n_964_ = v_n_1876_;
v_curr_965_ = v_val_2290_;
goto _start;
}
}
v___jp_2292_:
{
if (lean_obj_tag(v___y_2293_) == 0)
{
lean_object* v_a_2294_; 
v_a_2294_ = lean_ctor_get(v___y_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___y_2293_, 1);
v_a_2200_ = v_a_2294_;
goto v___jp_2199_;
}
else
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
lean_dec(v_n_1876_);
lean_dec(v_acc_966_);
lean_dec(v_curr_965_);
lean_dec(v_goals_963_);
lean_dec_ref(v_next_962_);
lean_dec(v_trace_961_);
lean_dec_ref(v_cfg_960_);
v_a_2295_ = lean_ctor_get(v___y_2293_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___y_2293_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___y_2293_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___y_2293_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
}
v___jp_972_:
{
lean_object* v___x_981_; double v___x_982_; double v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_981_ = lean_io_get_num_heartbeats();
v___x_982_ = lean_float_of_nat(v___y_978_);
v___x_983_ = lean_float_of_nat(v___x_981_);
v___x_984_ = lean_box_float(v___x_982_);
v___x_985_ = lean_box_float(v___x_983_);
v___x_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_a_980_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
lean_inc_ref(v___y_979_);
v___x_988_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_975_, v___y_979_, v___y_974_, v___y_973_, v___y_977_, v___y_976_, v___x_987_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_988_;
}
v___jp_989_:
{
lean_object* v___x_998_; double v___x_999_; double v___x_1000_; double v___x_1001_; double v___x_1002_; double v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_998_ = lean_io_mono_nanos_now();
v___x_999_ = lean_float_of_nat(v___y_996_);
v___x_1000_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1001_ = lean_float_div(v___x_999_, v___x_1000_);
v___x_1002_ = lean_float_of_nat(v___x_998_);
v___x_1003_ = lean_float_div(v___x_1002_, v___x_1000_);
v___x_1004_ = lean_box_float(v___x_1001_);
v___x_1005_ = lean_box_float(v___x_1003_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_a_997_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
lean_inc_ref(v___y_995_);
v___x_1008_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_992_, v___y_995_, v___y_991_, v___y_990_, v___y_994_, v___y_993_, v___x_1007_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1008_;
}
v___jp_1009_:
{
lean_object* v___x_1017_; lean_object* v_a_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1017_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_970_);
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref(v___x_1017_);
v___x_1019_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1020_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1013_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_io_mono_nanos_now();
lean_inc(v_trace_961_);
v___x_1022_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1010_, v___y_1012_, v_acc_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 1);
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
v___y_990_ = v___y_1011_;
v___y_991_ = v___y_1013_;
v___y_992_ = v___y_1014_;
v___y_993_ = v___y_1015_;
v___y_994_ = v_a_1018_;
v___y_995_ = v___y_1016_;
v___y_996_ = v___x_1021_;
v_a_997_ = v___x_1028_;
goto v___jp_989_;
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
v_a_1031_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1022_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1022_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set_tag(v___x_1033_, 0);
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
v___y_990_ = v___y_1011_;
v___y_991_ = v___y_1013_;
v___y_992_ = v___y_1014_;
v___y_993_ = v___y_1015_;
v___y_994_ = v_a_1018_;
v___y_995_ = v___y_1016_;
v___y_996_ = v___x_1021_;
v_a_997_ = v___x_1036_;
goto v___jp_989_;
}
}
}
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_961_);
v___x_1040_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_960_, v_trace_961_, v_next_962_, v_goals_963_, v___y_1010_, v___y_1012_, v_acc_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 1);
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
v___y_973_ = v___y_1011_;
v___y_974_ = v___y_1013_;
v___y_975_ = v___y_1014_;
v___y_976_ = v___y_1015_;
v___y_977_ = v_a_1018_;
v___y_978_ = v___x_1039_;
v___y_979_ = v___y_1016_;
v_a_980_ = v___x_1046_;
goto v___jp_972_;
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
v_a_1049_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1040_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1040_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 0);
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
v___y_973_ = v___y_1011_;
v___y_974_ = v___y_1013_;
v___y_975_ = v___y_1014_;
v___y_976_ = v___y_1015_;
v___y_977_ = v_a_1018_;
v___y_978_ = v___x_1039_;
v___y_979_ = v___y_1016_;
v_a_980_ = v___x_1054_;
goto v___jp_972_;
}
}
}
}
}
v___jp_1057_:
{
lean_object* v___x_1066_; double v___x_1067_; double v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1066_ = lean_io_get_num_heartbeats();
v___x_1067_ = lean_float_of_nat(v___y_1063_);
v___x_1068_ = lean_float_of_nat(v___x_1066_);
v___x_1069_ = lean_box_float(v___x_1067_);
v___x_1070_ = lean_box_float(v___x_1068_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_a_1065_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
lean_inc_ref(v___y_1064_);
v___x_1073_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1060_, v___y_1064_, v___y_1061_, v___y_1059_, v___y_1062_, v___y_1058_, v___x_1072_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1073_;
}
v___jp_1074_:
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_a_1082_);
v___y_1058_ = v___y_1075_;
v___y_1059_ = v___y_1077_;
v___y_1060_ = v___y_1076_;
v___y_1061_ = v___y_1078_;
v___y_1062_ = v___y_1079_;
v___y_1063_ = v___y_1080_;
v___y_1064_ = v___y_1081_;
v_a_1065_ = v___x_1083_;
goto v___jp_1057_;
}
v___jp_1084_:
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_a_1092_);
v___y_1058_ = v___y_1085_;
v___y_1059_ = v___y_1087_;
v___y_1060_ = v___y_1086_;
v___y_1061_ = v___y_1088_;
v___y_1062_ = v___y_1089_;
v___y_1063_ = v___y_1090_;
v___y_1064_ = v___y_1091_;
v_a_1065_ = v___x_1093_;
goto v___jp_1057_;
}
v___jp_1094_:
{
if (lean_obj_tag(v___y_1102_) == 0)
{
lean_object* v_a_1103_; 
v_a_1103_ = lean_ctor_get(v___y_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___y_1102_, 1);
v___y_1075_ = v___y_1095_;
v___y_1076_ = v___y_1097_;
v___y_1077_ = v___y_1096_;
v___y_1078_ = v___y_1098_;
v___y_1079_ = v___y_1099_;
v___y_1080_ = v___y_1100_;
v___y_1081_ = v___y_1101_;
v_a_1082_ = v_a_1103_;
goto v___jp_1074_;
}
else
{
lean_object* v_a_1104_; 
v_a_1104_ = lean_ctor_get(v___y_1102_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___y_1102_, 1);
v___y_1085_ = v___y_1095_;
v___y_1086_ = v___y_1097_;
v___y_1087_ = v___y_1096_;
v___y_1088_ = v___y_1098_;
v___y_1089_ = v___y_1099_;
v___y_1090_ = v___y_1100_;
v___y_1091_ = v___y_1101_;
v_a_1092_ = v_a_1104_;
goto v___jp_1084_;
}
}
v___jp_1105_:
{
lean_object* v___x_1114_; double v___x_1115_; double v___x_1116_; double v___x_1117_; double v___x_1118_; double v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1114_ = lean_io_mono_nanos_now();
v___x_1115_ = lean_float_of_nat(v___y_1109_);
v___x_1116_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1117_ = lean_float_div(v___x_1115_, v___x_1116_);
v___x_1118_ = lean_float_of_nat(v___x_1114_);
v___x_1119_ = lean_float_div(v___x_1118_, v___x_1116_);
v___x_1120_ = lean_box_float(v___x_1117_);
v___x_1121_ = lean_box_float(v___x_1119_);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v_a_1113_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
lean_inc_ref(v___y_1112_);
v___x_1124_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_961_, v___y_1108_, v___y_1112_, v___y_1110_, v___y_1107_, v___y_1111_, v___y_1106_, v___x_1123_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1124_;
}
v___jp_1125_:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_a_1133_);
v___y_1106_ = v___y_1126_;
v___y_1107_ = v___y_1128_;
v___y_1108_ = v___y_1127_;
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___y_1130_;
v___y_1111_ = v___y_1131_;
v___y_1112_ = v___y_1132_;
v_a_1113_ = v___x_1134_;
goto v___jp_1105_;
}
v___jp_1135_:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_a_1143_);
v___y_1106_ = v___y_1136_;
v___y_1107_ = v___y_1138_;
v___y_1108_ = v___y_1137_;
v___y_1109_ = v___y_1139_;
v___y_1110_ = v___y_1140_;
v___y_1111_ = v___y_1141_;
v___y_1112_ = v___y_1142_;
v_a_1113_ = v___x_1144_;
goto v___jp_1105_;
}
v___jp_1145_:
{
if (lean_obj_tag(v___y_1153_) == 0)
{
lean_object* v_a_1154_; 
v_a_1154_ = lean_ctor_get(v___y_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___y_1153_, 1);
v___y_1126_ = v___y_1146_;
v___y_1127_ = v___y_1148_;
v___y_1128_ = v___y_1147_;
v___y_1129_ = v___y_1149_;
v___y_1130_ = v___y_1150_;
v___y_1131_ = v___y_1151_;
v___y_1132_ = v___y_1152_;
v_a_1133_ = v_a_1154_;
goto v___jp_1125_;
}
else
{
lean_object* v_a_1155_; 
v_a_1155_ = lean_ctor_get(v___y_1153_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___y_1153_, 1);
v___y_1136_ = v___y_1146_;
v___y_1137_ = v___y_1148_;
v___y_1138_ = v___y_1147_;
v___y_1139_ = v___y_1149_;
v___y_1140_ = v___y_1150_;
v___y_1141_ = v___y_1151_;
v___y_1142_ = v___y_1152_;
v_a_1143_ = v_a_1155_;
goto v___jp_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2374_, lean_object* v_trace_2375_, lean_object* v_next_2376_, lean_object* v_goals_2377_, lean_object* v_n_2378_, lean_object* v_curr_2379_, lean_object* v_acc_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2374_, v_trace_2375_, v_next_2376_, v_goals_2377_, v_n_2378_, v_curr_2379_, v_acc_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object* v_tail_2387_, lean_object* v_cfg_2388_, lean_object* v_trace_2389_, lean_object* v_next_2390_, lean_object* v_goals_2391_, lean_object* v_n_2392_, lean_object* v_acc_2393_, lean_object* v_r_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = l_List_appendTR___redArg(v_r_2394_, v_tail_2387_);
v___x_2401_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2401_, 0, v_cfg_2388_);
lean_closure_set(v___x_2401_, 1, v_trace_2389_);
lean_closure_set(v___x_2401_, 2, v_next_2390_);
lean_closure_set(v___x_2401_, 3, v_goals_2391_);
lean_closure_set(v___x_2401_, 4, v_n_2392_);
lean_closure_set(v___x_2401_, 5, v___x_2400_);
lean_closure_set(v___x_2401_, 6, v_acc_2393_);
v___x_2402_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v___x_2401_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2403_, lean_object* v_msg_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2411_, lean_object* v_msg_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2411_, v_msg_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object* v_00_u03b1_2419_, lean_object* v_x_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_2420_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2427_, lean_object* v_x_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_00_u03b1_2427_, v_x_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* v_mvarId_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_2435_, v___y_2437_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* v_mvarId_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_mvarId_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v_mvarId_2442_);
return v_res_2448_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_object* v_00_u03b2_2449_, lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
uint8_t v___x_2452_; 
v___x_2452_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_2450_, v_x_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2453_, lean_object* v_x_2454_, lean_object* v_x_2455_){
_start:
{
uint8_t v_res_2456_; lean_object* v_r_2457_; 
v_res_2456_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(v_00_u03b2_2453_, v_x_2454_, v_x_2455_);
lean_dec(v_x_2455_);
lean_dec_ref(v_x_2454_);
v_r_2457_ = lean_box(v_res_2456_);
return v_r_2457_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_2458_, lean_object* v_x_2459_, size_t v_x_2460_, lean_object* v_x_2461_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_2459_, v_x_2460_, v_x_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___boxed(lean_object* v_00_u03b2_2463_, lean_object* v_x_2464_, lean_object* v_x_2465_, lean_object* v_x_2466_){
_start:
{
size_t v_x_77777__boxed_2467_; uint8_t v_res_2468_; lean_object* v_r_2469_; 
v_x_77777__boxed_2467_ = lean_unbox_usize(v_x_2465_);
lean_dec(v_x_2465_);
v_res_2468_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2463_, v_x_2464_, v_x_77777__boxed_2467_, v_x_2466_);
lean_dec(v_x_2466_);
lean_dec_ref(v_x_2464_);
v_r_2469_ = lean_box(v_res_2468_);
return v_r_2469_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_object* v_00_u03b2_2470_, lean_object* v_keys_2471_, lean_object* v_vals_2472_, lean_object* v_heq_2473_, lean_object* v_i_2474_, lean_object* v_k_2475_){
_start:
{
uint8_t v___x_2476_; 
v___x_2476_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_2471_, v_i_2474_, v_k_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2477_, lean_object* v_keys_2478_, lean_object* v_vals_2479_, lean_object* v_heq_2480_, lean_object* v_i_2481_, lean_object* v_k_2482_){
_start:
{
uint8_t v_res_2483_; lean_object* v_r_2484_; 
v_res_2483_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(v_00_u03b2_2477_, v_keys_2478_, v_vals_2479_, v_heq_2480_, v_i_2481_, v_k_2482_);
lean_dec(v_k_2482_);
lean_dec_ref(v_vals_2479_);
lean_dec_ref(v_keys_2478_);
v_r_2484_ = lean_box(v_res_2483_);
return v_r_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2485_, lean_object* v_h__1_2486_, lean_object* v_h__2_2487_){
_start:
{
lean_object* v_zero_2488_; uint8_t v_isZero_2489_; 
v_zero_2488_ = lean_unsigned_to_nat(0u);
v_isZero_2489_ = lean_nat_dec_eq(v_n_2485_, v_zero_2488_);
if (v_isZero_2489_ == 1)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_dec(v_h__2_2487_);
v___x_2490_ = lean_box(0);
v___x_2491_ = lean_apply_1(v_h__1_2486_, v___x_2490_);
return v___x_2491_;
}
else
{
lean_object* v_one_2492_; lean_object* v_n_2493_; lean_object* v___x_2494_; 
lean_dec(v_h__1_2486_);
v_one_2492_ = lean_unsigned_to_nat(1u);
v_n_2493_ = lean_nat_sub(v_n_2485_, v_one_2492_);
v___x_2494_ = lean_apply_1(v_h__2_2487_, v_n_2493_);
return v___x_2494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2495_, lean_object* v_h__1_2496_, lean_object* v_h__2_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2495_, v_h__1_2496_, v_h__2_2497_);
lean_dec(v_n_2495_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2499_, lean_object* v_n_2500_, lean_object* v_h__1_2501_, lean_object* v_h__2_2502_){
_start:
{
lean_object* v_zero_2503_; uint8_t v_isZero_2504_; 
v_zero_2503_ = lean_unsigned_to_nat(0u);
v_isZero_2504_ = lean_nat_dec_eq(v_n_2500_, v_zero_2503_);
if (v_isZero_2504_ == 1)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec(v_h__2_2502_);
v___x_2505_ = lean_box(0);
v___x_2506_ = lean_apply_1(v_h__1_2501_, v___x_2505_);
return v___x_2506_;
}
else
{
lean_object* v_one_2507_; lean_object* v_n_2508_; lean_object* v___x_2509_; 
lean_dec(v_h__1_2501_);
v_one_2507_ = lean_unsigned_to_nat(1u);
v_n_2508_ = lean_nat_sub(v_n_2500_, v_one_2507_);
v___x_2509_ = lean_apply_1(v_h__2_2502_, v_n_2508_);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* v_motive_2510_, lean_object* v_n_2511_, lean_object* v_h__1_2512_, lean_object* v_h__2_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(v_motive_2510_, v_n_2511_, v_h__1_2512_, v_h__2_2513_);
lean_dec(v_n_2511_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* v_procResult_x3f_2515_, lean_object* v_h__1_2516_, lean_object* v_h__2_2517_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2515_) == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec(v_h__1_2516_);
v___x_2518_ = lean_box(0);
v___x_2519_ = lean_apply_1(v_h__2_2517_, v___x_2518_);
return v___x_2519_;
}
else
{
lean_object* v_val_2520_; lean_object* v___x_2521_; 
lean_dec(v_h__2_2517_);
v_val_2520_ = lean_ctor_get(v_procResult_x3f_2515_, 0);
lean_inc(v_val_2520_);
lean_dec_ref_known(v_procResult_x3f_2515_, 1);
v___x_2521_ = lean_apply_1(v_h__1_2516_, v_val_2520_);
return v___x_2521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* v_motive_2522_, lean_object* v_procResult_x3f_2523_, lean_object* v_h__1_2524_, lean_object* v_h__2_2525_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2530_, lean_object* v_h__1_2531_, lean_object* v_h__2_2532_){
_start:
{
if (lean_obj_tag(v_curr_2530_) == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_dec(v_h__2_2532_);
v___x_2533_ = lean_box(0);
v___x_2534_ = lean_apply_1(v_h__1_2531_, v___x_2533_);
return v___x_2534_;
}
else
{
lean_object* v_head_2535_; lean_object* v_tail_2536_; lean_object* v___x_2537_; 
lean_dec(v_h__1_2531_);
v_head_2535_ = lean_ctor_get(v_curr_2530_, 0);
lean_inc(v_head_2535_);
v_tail_2536_ = lean_ctor_get(v_curr_2530_, 1);
lean_inc(v_tail_2536_);
lean_dec_ref_known(v_curr_2530_, 2);
v___x_2537_ = lean_apply_2(v_h__2_2532_, v_head_2535_, v_tail_2536_);
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2538_, lean_object* v_curr_2539_, lean_object* v_h__1_2540_, lean_object* v_h__2_2541_){
_start:
{
if (lean_obj_tag(v_curr_2539_) == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_dec(v_h__2_2541_);
v___x_2542_ = lean_box(0);
v___x_2543_ = lean_apply_1(v_h__1_2540_, v___x_2542_);
return v___x_2543_;
}
else
{
lean_object* v_head_2544_; lean_object* v_tail_2545_; lean_object* v___x_2546_; 
lean_dec(v_h__1_2540_);
v_head_2544_ = lean_ctor_get(v_curr_2539_, 0);
lean_inc(v_head_2544_);
v_tail_2545_ = lean_ctor_get(v_curr_2539_, 1);
lean_inc(v_tail_2545_);
lean_dec_ref_known(v_curr_2539_, 2);
v___x_2546_ = lean_apply_2(v_h__2_2541_, v_head_2544_, v_tail_2545_);
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2547_, lean_object* v_h__1_2548_, lean_object* v_h__2_2549_){
_start:
{
if (lean_obj_tag(v_____do__lift_2547_) == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec(v_h__2_2549_);
v___x_2550_ = lean_box(0);
v___x_2551_ = lean_apply_1(v_h__1_2548_, v___x_2550_);
return v___x_2551_;
}
else
{
lean_object* v_val_2552_; lean_object* v___x_2553_; 
lean_dec(v_h__1_2548_);
v_val_2552_ = lean_ctor_get(v_____do__lift_2547_, 0);
lean_inc(v_val_2552_);
lean_dec_ref_known(v_____do__lift_2547_, 1);
v___x_2553_ = lean_apply_1(v_h__2_2549_, v_val_2552_);
return v___x_2553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_2554_, lean_object* v_____do__lift_2555_, lean_object* v_h__1_2556_, lean_object* v_h__2_2557_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_2562_, lean_object* v_trace_2563_, lean_object* v_next_2564_, lean_object* v_orig_2565_, lean_object* v_g_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_maxDepth_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_maxDepth_2572_ = lean_ctor_get(v_cfg_2562_, 0);
lean_inc(v_maxDepth_2572_);
v___x_2573_ = lean_box(0);
v___x_2574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_g_2566_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2562_, v_trace_2563_, v_next_2564_, v_orig_2565_, v_maxDepth_2572_, v___x_2574_, v___x_2573_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_2576_, lean_object* v_trace_2577_, lean_object* v_next_2578_, lean_object* v_orig_2579_, lean_object* v_g_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2576_, v_trace_2577_, v_next_2578_, v_orig_2579_, v_g_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
if (lean_obj_tag(v_a_2587_) == 0)
{
lean_object* v___x_2589_; 
v___x_2589_ = l_List_reverse___redArg(v_a_2588_);
return v___x_2589_;
}
else
{
lean_object* v_head_2590_; lean_object* v_tail_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2600_; 
v_head_2590_ = lean_ctor_get(v_a_2587_, 0);
v_tail_2591_ = lean_ctor_get(v_a_2587_, 1);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_a_2587_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2593_ = v_a_2587_;
v_isShared_2594_ = v_isSharedCheck_2600_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_tail_2591_);
lean_inc(v_head_2590_);
lean_dec(v_a_2587_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2600_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = l_Lean_MessageData_ofFormat(v_head_2590_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 1, v_a_2588_);
lean_ctor_set(v___x_2593_, 0, v___x_2595_);
v___x_2597_ = v___x_2593_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v_a_2588_);
v___x_2597_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
v_a_2587_ = v_tail_2591_;
v_a_2588_ = v___x_2597_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_2603_ = l_Lean_stringToMessageData(v___x_2602_);
return v___x_2603_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_2606_ = l_Lean_stringToMessageData(v___x_2605_);
return v___x_2606_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_2609_ = l_Lean_stringToMessageData(v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_2610_, lean_object* v_snd_2611_, lean_object* v_x_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2610_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2620_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_2611_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2640_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2640_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2640_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
v___x_2625_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_2626_ = lean_box(0);
v___x_2627_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2619_, v___x_2626_);
v___x_2628_ = l_Lean_MessageData_ofList(v___x_2627_);
v___x_2629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2625_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_2631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2629_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_2633_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2621_, v___x_2626_);
v___x_2634_ = l_Lean_MessageData_ofList(v___x_2633_);
v___x_2635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2632_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2631_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2636_);
v___x_2638_ = v___x_2623_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v_a_2619_);
v_a_2641_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2620_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2620_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v_snd_2611_);
v_a_2649_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2618_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2618_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_2657_, lean_object* v_snd_2658_, lean_object* v_x_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2657_, v_snd_2658_, v_x_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec_ref(v_x_2659_);
return v_res_2665_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_2668_ = l_Lean_stringToMessageData(v___x_2667_);
return v___x_2668_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_2671_ = l_Lean_stringToMessageData(v___x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_2672_, lean_object* v___x_2673_, lean_object* v_x_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2672_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_2673_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2700_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2700_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2700_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2687_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_2688_ = lean_box(0);
v___x_2689_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2681_, v___x_2688_);
v___x_2690_ = l_Lean_MessageData_ofList(v___x_2689_);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2687_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2683_, v___x_2688_);
v___x_2695_ = l_Lean_MessageData_ofList(v___x_2694_);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2693_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v___x_2696_);
v___x_2698_ = v___x_2685_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec(v_a_2681_);
v_a_2701_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2682_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2682_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec(v___x_2673_);
v_a_2709_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2680_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2680_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_2717_, lean_object* v___x_2718_, lean_object* v_x_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2717_, v___x_2718_, v_x_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec_ref(v_x_2719_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t v___x_2726_, lean_object* v_x_2727_, lean_object* v_x_2728_, lean_object* v___y_2729_){
_start:
{
if (lean_obj_tag(v_x_2727_) == 0)
{
lean_object* v___x_2731_; 
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_x_2728_);
return v___x_2731_;
}
else
{
lean_object* v_head_2732_; lean_object* v_tail_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2748_; 
v_head_2732_ = lean_ctor_get(v_x_2727_, 0);
v_tail_2733_ = lean_ctor_get(v_x_2727_, 1);
v_isSharedCheck_2748_ = !lean_is_exclusive(v_x_2727_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2735_ = v_x_2727_;
v_isShared_2736_ = v_isSharedCheck_2748_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_tail_2733_);
lean_inc(v_head_2732_);
lean_dec(v_x_2727_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2748_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
uint8_t v_a_2743_; lean_object* v___x_2745_; lean_object* v_a_2746_; uint8_t v___x_2747_; 
v___x_2745_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2732_, v___y_2729_);
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref(v___x_2745_);
v___x_2747_ = lean_unbox(v_a_2746_);
lean_dec(v_a_2746_);
if (v___x_2747_ == 0)
{
goto v___jp_2737_;
}
else
{
v_a_2743_ = v___x_2726_;
goto v___jp_2742_;
}
v___jp_2737_:
{
lean_object* v___x_2739_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 1, v_x_2728_);
v___x_2739_ = v___x_2735_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_head_2732_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_x_2728_);
v___x_2739_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
v_x_2727_ = v_tail_2733_;
v_x_2728_ = v___x_2739_;
goto _start;
}
}
v___jp_2742_:
{
if (v_a_2743_ == 0)
{
lean_del_object(v___x_2735_);
lean_dec(v_head_2732_);
v_x_2727_ = v_tail_2733_;
goto _start;
}
else
{
goto v___jp_2737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v___x_2749_, lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
uint8_t v___x_45712__boxed_2754_; lean_object* v_res_2755_; 
v___x_45712__boxed_2754_ = lean_unbox(v___x_2749_);
v_res_2755_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_45712__boxed_2754_, v_x_2750_, v_x_2751_, v___y_2752_);
lean_dec(v___y_2752_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_2756_, lean_object* v_a_2757_){
_start:
{
if (lean_obj_tag(v_a_2756_) == 0)
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_array_to_list(v_a_2757_);
return v___x_2758_;
}
else
{
lean_object* v_head_2759_; lean_object* v_tail_2760_; lean_object* v___x_2761_; 
v_head_2759_ = lean_ctor_get(v_a_2756_, 0);
lean_inc(v_head_2759_);
v_tail_2760_ = lean_ctor_get(v_a_2756_, 1);
lean_inc(v_tail_2760_);
lean_dec_ref_known(v_a_2756_, 2);
v___x_2761_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2757_, v_head_2759_);
v_a_2756_ = v_tail_2760_;
v_a_2757_ = v___x_2761_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
if (lean_obj_tag(v_a_2764_) == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_dec(v_goals_2763_);
v___x_2772_ = lean_array_to_list(v_a_2765_);
v___x_2773_ = lean_array_to_list(v_a_2766_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2772_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
return v___x_2775_;
}
else
{
lean_object* v_head_2776_; lean_object* v_tail_2777_; lean_object* v___x_2778_; 
v_head_2776_ = lean_ctor_get(v_a_2764_, 0);
lean_inc_n(v_head_2776_, 2);
v_tail_2777_ = lean_ctor_get(v_a_2764_, 1);
lean_inc(v_tail_2777_);
lean_dec_ref_known(v_a_2764_, 2);
lean_inc(v_goals_2763_);
v___x_2778_ = l_Lean_MVarId_isIndependentOf(v_goals_2763_, v_head_2776_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; uint8_t v___x_2780_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = lean_unbox(v_a_2779_);
lean_dec(v_a_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_array_push(v_a_2766_, v_head_2776_);
v_a_2764_ = v_tail_2777_;
v_a_2766_ = v___x_2781_;
goto _start;
}
else
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_array_push(v_a_2765_, v_head_2776_);
v_a_2764_ = v_tail_2777_;
v_a_2765_ = v___x_2783_;
goto _start;
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec(v_tail_2777_);
lean_dec(v_head_2776_);
lean_dec_ref(v_a_2766_);
lean_dec_ref(v_a_2765_);
lean_dec(v_goals_2763_);
v_a_2785_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2778_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2778_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
if (lean_obj_tag(v_a_2803_) == 0)
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_array_to_list(v_a_2804_);
return v___x_2805_;
}
else
{
lean_object* v_head_2806_; 
v_head_2806_ = lean_ctor_get(v_a_2803_, 0);
if (lean_obj_tag(v_head_2806_) == 0)
{
lean_object* v_tail_2807_; lean_object* v_val_2808_; lean_object* v___x_2809_; 
lean_inc_ref(v_head_2806_);
v_tail_2807_ = lean_ctor_get(v_a_2803_, 1);
lean_inc(v_tail_2807_);
lean_dec_ref_known(v_a_2803_, 2);
v_val_2808_ = lean_ctor_get(v_head_2806_, 0);
lean_inc(v_val_2808_);
lean_dec_ref_known(v_head_2806_, 1);
v___x_2809_ = lean_array_push(v_a_2804_, v_val_2808_);
v_a_2803_ = v_tail_2807_;
v_a_2804_ = v___x_2809_;
goto _start;
}
else
{
lean_object* v_tail_2811_; 
v_tail_2811_ = lean_ctor_get(v_a_2803_, 1);
lean_inc(v_tail_2811_);
lean_dec_ref_known(v_a_2803_, 2);
v_a_2803_ = v_tail_2811_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_2813_, lean_object* v_x_2814_, lean_object* v_x_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
if (lean_obj_tag(v_x_2814_) == 0)
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
lean_dec_ref(v_f_2813_);
v___x_2821_ = l_List_reverse___redArg(v_x_2815_);
v___x_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
return v___x_2822_;
}
else
{
lean_object* v_head_2823_; lean_object* v_tail_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2869_; 
v_head_2823_ = lean_ctor_get(v_x_2814_, 0);
v_tail_2824_ = lean_ctor_get(v_x_2814_, 1);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_x_2814_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2826_ = v_x_2814_;
v_isShared_2827_ = v_isSharedCheck_2869_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_tail_2824_);
lean_inc(v_head_2823_);
lean_dec(v_x_2814_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2869_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v_a_2829_; lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_Meta_saveState___redArg(v___y_2817_, v___y_2819_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
lean_inc_ref(v_f_2813_);
lean_inc(v___y_2819_);
lean_inc_ref(v___y_2818_);
lean_inc(v___y_2817_);
lean_inc_ref(v___y_2816_);
lean_inc(v_head_2823_);
v___x_2836_ = lean_apply_6(v_f_2813_, v_head_2823_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, lean_box(0));
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2838_; 
lean_dec(v_a_2835_);
lean_dec(v_head_2823_);
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v___x_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2838_, 0, v_a_2837_);
v_a_2829_ = v___x_2838_;
goto v___jp_2828_;
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2860_; 
v_a_2839_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2841_ = v___x_2836_;
v_isShared_2842_ = v_isSharedCheck_2860_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2836_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2860_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
uint8_t v___y_2844_; uint8_t v___x_2858_; 
v___x_2858_ = l_Lean_Exception_isInterrupt(v_a_2839_);
if (v___x_2858_ == 0)
{
uint8_t v___x_2859_; 
lean_inc(v_a_2839_);
v___x_2859_ = l_Lean_Exception_isRuntime(v_a_2839_);
v___y_2844_ = v___x_2859_;
goto v___jp_2843_;
}
else
{
v___y_2844_ = v___x_2858_;
goto v___jp_2843_;
}
v___jp_2843_:
{
if (v___y_2844_ == 0)
{
lean_object* v___x_2845_; 
lean_del_object(v___x_2841_);
lean_dec(v_a_2839_);
v___x_2845_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2835_, v___y_2817_, v___y_2819_);
lean_dec(v_a_2835_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v___x_2846_; 
lean_dec_ref_known(v___x_2845_, 1);
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v_head_2823_);
v_a_2829_ = v___x_2846_;
goto v___jp_2828_;
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_del_object(v___x_2826_);
lean_dec(v_tail_2824_);
lean_dec(v_head_2823_);
lean_dec(v_x_2815_);
lean_dec_ref(v_f_2813_);
v_a_2847_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2845_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2845_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v___x_2856_; 
lean_dec(v_a_2835_);
lean_del_object(v___x_2826_);
lean_dec(v_tail_2824_);
lean_dec(v_head_2823_);
lean_dec(v_x_2815_);
lean_dec_ref(v_f_2813_);
if (v_isShared_2842_ == 0)
{
v___x_2856_ = v___x_2841_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2839_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_del_object(v___x_2826_);
lean_dec(v_tail_2824_);
lean_dec(v_head_2823_);
lean_dec(v_x_2815_);
lean_dec_ref(v_f_2813_);
v_a_2861_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2834_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2834_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
v___jp_2828_:
{
lean_object* v___x_2831_; 
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 1, v_x_2815_);
lean_ctor_set(v___x_2826_, 0, v_a_2829_);
v___x_2831_ = v___x_2826_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2829_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_x_2815_);
v___x_2831_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
v_x_2814_ = v_tail_2824_;
v_x_2815_ = v___x_2831_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_2870_, lean_object* v_x_2871_, lean_object* v_x_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2870_, v_x_2871_, v_x_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
if (lean_obj_tag(v_a_2879_) == 0)
{
lean_object* v___x_2881_; 
v___x_2881_ = lean_array_to_list(v_a_2880_);
return v___x_2881_;
}
else
{
lean_object* v_head_2882_; 
v_head_2882_ = lean_ctor_get(v_a_2879_, 0);
if (lean_obj_tag(v_head_2882_) == 1)
{
lean_object* v_tail_2883_; lean_object* v_val_2884_; lean_object* v___x_2885_; 
lean_inc_ref(v_head_2882_);
v_tail_2883_ = lean_ctor_get(v_a_2879_, 1);
lean_inc(v_tail_2883_);
lean_dec_ref_known(v_a_2879_, 2);
v_val_2884_ = lean_ctor_get(v_head_2882_, 0);
lean_inc(v_val_2884_);
lean_dec_ref_known(v_head_2882_, 1);
v___x_2885_ = lean_array_push(v_a_2880_, v_val_2884_);
v_a_2879_ = v_tail_2883_;
v_a_2880_ = v___x_2885_;
goto _start;
}
else
{
lean_object* v_tail_2887_; 
v_tail_2887_ = lean_ctor_get(v_a_2879_, 1);
lean_inc(v_tail_2887_);
lean_dec_ref_known(v_a_2879_, 2);
v_a_2879_ = v_tail_2887_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_2889_, lean_object* v_f_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_box(0);
v___x_2897_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2890_, v_L_2889_, v___x_2896_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2909_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2909_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2909_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2902_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_2898_);
v___x_2903_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_2898_, v___x_2902_);
v___x_2904_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_2898_, v___x_2902_);
v___x_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2905_);
v___x_2907_ = v___x_2900_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
v_a_2910_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2897_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2897_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* v_L_2918_, lean_object* v_f_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_2918_, v_f_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t v___x_2926_, uint8_t v___x_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_, lean_object* v___y_2930_){
_start:
{
if (lean_obj_tag(v_x_2928_) == 0)
{
lean_object* v___x_2932_; 
v___x_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2932_, 0, v_x_2929_);
return v___x_2932_;
}
else
{
lean_object* v_head_2933_; lean_object* v_tail_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2948_; 
v_head_2933_ = lean_ctor_get(v_x_2928_, 0);
v_tail_2934_ = lean_ctor_get(v_x_2928_, 1);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_x_2928_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2936_ = v_x_2928_;
v_isShared_2937_ = v_isSharedCheck_2948_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_tail_2934_);
lean_inc(v_head_2933_);
lean_dec(v_x_2928_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2948_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
uint8_t v_a_2939_; lean_object* v___x_2945_; lean_object* v_a_2946_; uint8_t v___x_2947_; 
v___x_2945_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2933_, v___y_2930_);
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v___x_2945_);
v___x_2947_ = lean_unbox(v_a_2946_);
lean_dec(v_a_2946_);
if (v___x_2947_ == 0)
{
v_a_2939_ = v___x_2926_;
goto v___jp_2938_;
}
else
{
v_a_2939_ = v___x_2927_;
goto v___jp_2938_;
}
v___jp_2938_:
{
if (v_a_2939_ == 0)
{
lean_del_object(v___x_2936_);
lean_dec(v_head_2933_);
v_x_2928_ = v_tail_2934_;
goto _start;
}
else
{
lean_object* v___x_2942_; 
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 1, v_x_2929_);
v___x_2942_ = v___x_2936_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_head_2933_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_x_2929_);
v___x_2942_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
v_x_2928_ = v_tail_2934_;
v_x_2929_ = v___x_2942_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* v___x_2949_, lean_object* v___x_2950_, lean_object* v_x_2951_, lean_object* v_x_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
uint8_t v___x_46066__boxed_2955_; uint8_t v___x_46067__boxed_2956_; lean_object* v_res_2957_; 
v___x_46066__boxed_2955_ = lean_unbox(v___x_2949_);
v___x_46067__boxed_2956_ = lean_unbox(v___x_2950_);
v_res_2957_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_46066__boxed_2955_, v___x_46067__boxed_2956_, v_x_2951_, v_x_2952_, v___y_2953_);
lean_dec(v___y_2953_);
return v_res_2957_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1));
v___x_2962_ = l_Lean_stringToMessageData(v___x_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_2963_, lean_object* v_trace_2964_, lean_object* v_next_2965_, lean_object* v_orig_2966_, lean_object* v_goals_2967_, lean_object* v_remaining_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v___f_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_inc(v_orig_2966_);
lean_inc_ref(v_next_2965_);
lean_inc(v_trace_2964_);
lean_inc_ref(v_cfg_2963_);
v___f_2974_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2974_, 0, v_cfg_2963_);
lean_closure_set(v___f_2974_, 1, v_trace_2964_);
lean_closure_set(v___f_2974_, 2, v_next_2965_);
lean_closure_set(v___f_2974_, 3, v_orig_2966_);
v___x_2975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
lean_inc(v_remaining_2968_);
lean_inc(v_goals_2967_);
v___x_2976_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2967_, v_remaining_2968_, v___x_2975_, v___x_2975_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v_fst_2978_; lean_object* v_snd_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_4179_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2976_, 1);
v_fst_2978_ = lean_ctor_get(v_a_2977_, 0);
v_snd_2979_ = lean_ctor_get(v_a_2977_, 1);
v_isSharedCheck_4179_ = !lean_is_exclusive(v_a_2977_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_2981_ = v_a_2977_;
v_isShared_2982_ = v_isSharedCheck_4179_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_snd_2979_);
lean_inc(v_fst_2978_);
lean_dec(v_a_2977_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_4179_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
uint8_t v___x_2983_; 
v___x_2983_ = l_List_isEmpty___redArg(v_fst_2978_);
if (v___x_2983_ == 0)
{
lean_object* v_toCold_2984_; lean_object* v_options_2985_; uint8_t v_hasTrace_2986_; 
lean_dec(v_remaining_2968_);
v_toCold_2984_ = lean_ctor_get(v_a_2971_, 0);
v_options_2985_ = lean_ctor_get(v_toCold_2984_, 2);
v_hasTrace_2986_ = lean_ctor_get_uint8(v_options_2985_, sizeof(void*)*1);
if (v_hasTrace_2986_ == 0)
{
lean_object* v___x_2987_; 
lean_del_object(v___x_2981_);
v___x_2987_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2978_, v___f_2974_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3060_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_2990_ = v___x_2987_;
v_isShared_2991_ = v_isSharedCheck_3060_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3060_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v_fst_2992_; lean_object* v_snd_2993_; lean_object* v___x_2994_; lean_object* v_a_2996_; lean_object* v___y_3003_; lean_object* v___y_3006_; lean_object* v___y_3007_; uint8_t v___y_3008_; lean_object* v___y_3019_; lean_object* v___y_3035_; uint8_t v___y_3036_; lean_object* v_a_3051_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_fst_2992_ = lean_ctor_get(v_a_2988_, 0);
lean_inc(v_fst_2992_);
v_snd_2993_ = lean_ctor_get(v_a_2988_, 1);
lean_inc(v_snd_2993_);
lean_dec(v_a_2988_);
v___x_2994_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_2993_, v___x_2975_);
v___x_3055_ = lean_box(0);
v___x_3056_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_2983_, v_goals_2967_, v___x_3055_, v_a_2970_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; lean_object* v___x_3058_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v___x_3058_ = l_List_reverse___redArg(v_a_3057_);
v_a_3051_ = v___x_3058_;
goto v___jp_3050_;
}
else
{
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3059_; 
v_a_3059_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3056_, 1);
v_a_3051_ = v_a_3059_;
goto v___jp_3050_;
}
else
{
lean_dec(v___x_2994_);
lean_dec(v_fst_2992_);
lean_del_object(v___x_2990_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec(v_trace_2964_);
lean_dec_ref(v_cfg_2963_);
return v___x_3056_;
}
}
v___jp_2995_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2997_ = l_List_appendTR___redArg(v___x_2994_, v_fst_2992_);
v___x_2998_ = l_List_appendTR___redArg(v___x_2997_, v_a_2996_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v___x_2998_);
v___x_3000_ = v___x_2990_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
v___jp_3002_:
{
if (lean_obj_tag(v___y_3003_) == 0)
{
lean_object* v_a_3004_; 
v_a_3004_ = lean_ctor_get(v___y_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___y_3003_, 1);
v_a_2996_ = v_a_3004_;
goto v___jp_2995_;
}
else
{
lean_dec(v___x_2994_);
lean_dec(v_fst_2992_);
lean_del_object(v___x_2990_);
return v___y_3003_;
}
}
v___jp_3005_:
{
if (v___y_3008_ == 0)
{
lean_object* v___x_3009_; 
lean_dec_ref(v___y_3006_);
v___x_3009_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3007_, v_a_2970_, v_a_2972_);
lean_dec_ref(v___y_3007_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_dec_ref_known(v___x_3009_, 1);
v_a_2996_ = v_snd_2979_;
goto v___jp_2995_;
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec(v___x_2994_);
lean_dec(v_fst_2992_);
lean_del_object(v___x_2990_);
lean_dec(v_snd_2979_);
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
else
{
lean_dec_ref(v___y_3007_);
lean_dec(v_snd_2979_);
v___y_3003_ = v___y_3006_;
goto v___jp_3002_;
}
}
v___jp_3018_:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_Meta_saveState___redArg(v_a_2970_, v_a_2972_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
lean_inc(v_snd_2979_);
v___x_3022_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3019_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_dec(v_a_3021_);
lean_dec(v_snd_2979_);
v___y_3003_ = v___x_3022_;
goto v___jp_3002_;
}
else
{
lean_object* v_a_3023_; uint8_t v___x_3024_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
v___x_3024_ = l_Lean_Exception_isInterrupt(v_a_3023_);
if (v___x_3024_ == 0)
{
uint8_t v___x_3025_; 
v___x_3025_ = l_Lean_Exception_isRuntime(v_a_3023_);
v___y_3006_ = v___x_3022_;
v___y_3007_ = v_a_3021_;
v___y_3008_ = v___x_3025_;
goto v___jp_3005_;
}
else
{
lean_dec(v_a_3023_);
v___y_3006_ = v___x_3022_;
v___y_3007_ = v_a_3021_;
v___y_3008_ = v___x_3024_;
goto v___jp_3005_;
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec(v___y_3019_);
lean_dec(v___x_2994_);
lean_dec(v_fst_2992_);
lean_del_object(v___x_2990_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec(v_trace_2964_);
lean_dec_ref(v_cfg_2963_);
v_a_3026_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3020_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3020_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
v___jp_3034_:
{
if (v___y_3036_ == 0)
{
uint8_t v___x_3037_; 
lean_del_object(v___x_2990_);
v___x_3037_ = l_List_isEmpty___redArg(v_fst_2992_);
lean_dec(v_fst_2992_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_dec(v___y_3035_);
lean_dec(v___x_2994_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec(v_trace_2964_);
lean_dec_ref(v_cfg_2963_);
v___x_3038_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3039_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3038_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
return v___x_3039_;
}
else
{
lean_object* v___x_3040_; 
v___x_3040_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3035_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3049_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3049_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3045_ = l_List_appendTR___redArg(v___x_2994_, v_a_3041_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3045_);
v___x_3047_ = v___x_3043_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
else
{
lean_dec(v___x_2994_);
return v___x_3040_;
}
}
}
else
{
v___y_3019_ = v___y_3035_;
goto v___jp_3018_;
}
}
v___jp_3050_:
{
uint8_t v_commitIndependentGoals_3052_; lean_object* v___x_3053_; 
v_commitIndependentGoals_3052_ = lean_ctor_get_uint8(v_cfg_2963_, sizeof(void*)*4);
lean_inc(v___x_2994_);
v___x_3053_ = l_List_appendTR___redArg(v_a_3051_, v___x_2994_);
if (v_commitIndependentGoals_3052_ == 0)
{
v___y_3035_ = v___x_3053_;
v___y_3036_ = v___x_2983_;
goto v___jp_3034_;
}
else
{
uint8_t v___x_3054_; 
v___x_3054_ = l_List_isEmpty___redArg(v___x_2994_);
if (v___x_3054_ == 0)
{
v___y_3019_ = v___x_3053_;
goto v___jp_3018_;
}
else
{
v___y_3035_ = v___x_3053_;
v___y_3036_ = v___x_2983_;
goto v___jp_3034_;
}
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec(v_snd_2979_);
lean_dec(v_goals_2967_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec(v_trace_2964_);
lean_dec_ref(v_cfg_2963_);
v_a_3061_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_2987_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_2987_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3069_; lean_object* v___f_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v_a_3078_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v_a_3092_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v_a_3097_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v_a_3104_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; uint8_t v___y_3122_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; uint8_t v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v_a_3151_; uint8_t v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v_a_3170_; uint8_t v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v_a_3179_; lean_object* v___y_3182_; uint8_t v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v_a_3190_; lean_object* v___y_3194_; uint8_t v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3206_; lean_object* v___y_3207_; uint8_t v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; uint8_t v___y_3216_; lean_object* v___y_3220_; uint8_t v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; uint8_t v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3247_; uint8_t v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; uint8_t v___y_3256_; lean_object* v___y_3264_; uint8_t v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v_a_3272_; lean_object* v___y_3277_; uint8_t v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v_a_3283_; lean_object* v___y_3293_; uint8_t v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v_a_3299_; lean_object* v___y_3302_; uint8_t v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v_a_3308_; lean_object* v___y_3311_; lean_object* v___y_3312_; uint8_t v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v_a_3319_; lean_object* v___y_3323_; lean_object* v___y_3324_; uint8_t v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; uint8_t v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; uint8_t v___y_3345_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; uint8_t v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3366_; uint8_t v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; uint8_t v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; uint8_t v___y_3391_; uint8_t v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; uint8_t v___y_3398_; lean_object* v___y_3403_; uint8_t v___y_3404_; lean_object* v___y_3405_; uint8_t v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v_a_3412_; lean_object* v___y_3417_; lean_object* v___y_3418_; uint8_t v___y_3419_; uint8_t v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; uint8_t v___y_3447_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v_a_3459_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v_a_3466_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v_a_3481_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v_a_3486_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v_a_3493_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; uint8_t v___y_3511_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; uint8_t v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v_a_3540_; lean_object* v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v_a_3556_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; uint8_t v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v_a_3567_; lean_object* v___y_3571_; lean_object* v___y_3572_; uint8_t v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v_a_3577_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; uint8_t v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; uint8_t v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; uint8_t v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; uint8_t v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; uint8_t v___y_3624_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; uint8_t v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; uint8_t v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; uint8_t v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; uint8_t v___y_3655_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; uint8_t v___y_3663_; lean_object* v___y_3664_; uint8_t v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v_a_3669_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; uint8_t v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v_a_3680_; lean_object* v___y_3693_; lean_object* v___y_3694_; uint8_t v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v_a_3699_; lean_object* v___y_3702_; lean_object* v___y_3703_; uint8_t v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v_a_3708_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; uint8_t v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v_a_3719_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; uint8_t v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; uint8_t v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; uint8_t v___y_3745_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; uint8_t v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; uint8_t v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; uint8_t v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; uint8_t v___y_3785_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v_a_3801_; lean_object* v___y_3806_; lean_object* v___y_3807_; uint8_t v___y_3808_; lean_object* v___y_3809_; uint8_t v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; uint8_t v___y_3836_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v_a_3848_; 
v_inheritedTraceOptions_3069_ = lean_ctor_get(v_toCold_2984_, 11);
lean_inc(v_snd_2979_);
lean_inc(v_fst_2978_);
v___f_3070_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3070_, 0, v_fst_2978_);
lean_closure_set(v___f_3070_, 1, v_snd_2979_);
v___x_3071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_3072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_2964_);
v___x_3073_ = l_Lean_Name_append(v___x_3072_, v_trace_2964_);
v___x_3074_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3069_, v_options_2985_, v___x_3073_);
lean_dec(v___x_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3897_; uint8_t v___x_3898_; 
v___x_3897_ = l_Lean_trace_profiler;
v___x_3898_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2985_, v___x_3897_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; 
lean_dec_ref(v___f_3070_);
lean_del_object(v___x_2981_);
v___x_3899_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2978_, v___f_2974_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_4167_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_4167_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_4167_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v_fst_3904_; lean_object* v_snd_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_4166_; 
v_fst_3904_ = lean_ctor_get(v_a_3900_, 0);
v_snd_3905_ = lean_ctor_get(v_a_3900_, 1);
v_isSharedCheck_4166_ = !lean_is_exclusive(v_a_3900_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_3907_ = v_a_3900_;
v_isShared_3908_ = v_isSharedCheck_4166_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_snd_3905_);
lean_inc(v_fst_3904_);
lean_dec(v_a_3900_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_4166_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v_a_3911_; lean_object* v___y_3918_; lean_object* v___y_3921_; lean_object* v___y_3922_; uint8_t v___y_3923_; lean_object* v___y_3934_; lean_object* v___y_3950_; uint8_t v___y_3951_; lean_object* v_a_3966_; lean_object* v___f_3970_; lean_object* v___x_3971_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v_a_3975_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v_a_3992_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v_a_3997_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v_a_4003_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; uint8_t v___y_4022_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; uint8_t v___y_4040_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v_a_4050_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v_a_4057_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v_a_4069_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v_a_4074_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v_a_4079_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; uint8_t v___y_4093_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; uint8_t v___y_4124_; uint8_t v___y_4125_; lean_object* v___y_4130_; lean_object* v___y_4131_; uint8_t v___y_4132_; lean_object* v_a_4133_; 
v___x_3909_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3905_, v___x_2975_);
lean_inc(v___x_3909_);
lean_inc(v_fst_3904_);
v___f_3970_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3970_, 0, v_fst_3904_);
lean_closure_set(v___f_3970_, 1, v___x_3909_);
v___x_3971_ = lean_box(0);
if (v___x_3074_ == 0)
{
if (v___x_3898_ == 0)
{
lean_object* v___x_4162_; 
lean_dec_ref(v___f_3970_);
lean_del_object(v___x_3907_);
v___x_4162_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2986_, v___x_2983_, v_goals_2967_, v___x_3971_, v_a_2970_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4164_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v___x_4164_ = l_List_reverse___redArg(v_a_4163_);
v_a_3966_ = v___x_4164_;
goto v___jp_3965_;
}
else
{
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4165_; 
v_a_4165_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4162_, 1);
v_a_3966_ = v_a_4165_;
goto v___jp_3965_;
}
else
{
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
lean_del_object(v___x_3902_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec(v_trace_2964_);
lean_dec_ref(v_cfg_2963_);
return v___x_4162_;
}
}
}
else
{
lean_del_object(v___x_3902_);
goto v___jp_4137_;
}
}
else
{
lean_del_object(v___x_3902_);
goto v___jp_4137_;
}
v___jp_3910_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3915_; 
v___x_3912_ = l_List_appendTR___redArg(v___x_3909_, v_fst_3904_);
v___x_3913_ = l_List_appendTR___redArg(v___x_3912_, v_a_3911_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3913_);
v___x_3915_ = v___x_3902_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
v___jp_3917_:
{
if (lean_obj_tag(v___y_3918_) == 0)
{
lean_object* v_a_3919_; 
v_a_3919_ = lean_ctor_get(v___y_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___y_3918_, 1);
v_a_3911_ = v_a_3919_;
goto v___jp_3910_;
}
else
{
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
lean_del_object(v___x_3902_);
return v___y_3918_;
}
}
v___jp_3920_:
{
if (v___y_3923_ == 0)
{
lean_object* v___x_3924_; 
lean_dec_ref(v___y_3921_);
v___x_3924_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3922_, v_a_2970_, v_a_2972_);
lean_dec_ref(v___y_3922_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_dec_ref_known(v___x_3924_, 1);
v_a_3911_ = v_snd_2979_;
goto v___jp_3910_;
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
lean_del_object(v___x_3902_);
lean_dec(v_snd_2979_);
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3924_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3924_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
else
{
lean_dec_ref(v___y_3922_);
lean_dec(v_snd_2979_);
v___y_3918_ = v___y_3921_;
goto v___jp_3917_;
}
}
v___jp_3933_:
{
lean_object* v___x_3935_; 
v___x_3935_ = l_Lean_Meta_saveState___redArg(v_a_2970_, v_a_2972_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3937_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v___x_3935_, 1);
lean_inc(v_snd_2979_);
v___x_3937_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3934_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_dec(v_a_3936_);
lean_dec(v_snd_2979_);
v___y_3918_ = v___x_3937_;
goto v___jp_3917_;
}
else
{
lean_object* v_a_3938_; uint8_t v___x_3939_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
v___x_3939_ = l_Lean_Exception_isInterrupt(v_a_3938_);
if (v___x_3939_ == 0)
{
uint8_t v___x_3940_; 
v___x_3940_ = l_Lean_Exception_isRuntime(v_a_3938_);
v___y_3921_ = v___x_3937_;
v___y_3922_ = v_a_3936_;
v___y_3923_ = v___x_3940_;
goto v___jp_3920_;
}
else
{
lean_dec(v_a_3938_);
v___y_3921_ = v___x_3937_;
v___y_3922_ = v_a_3936_;
v___y_3923_ = v___x_3939_;
goto v___jp_3920_;
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_dec(v___y_3934_);
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
lean_del_object(v___x_3902_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec(v_trace_2964_);
lean_dec_ref(v_cfg_2963_);
v_a_3941_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3935_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3935_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
v___jp_3949_:
{
if (v___y_3951_ == 0)
{
uint8_t v___x_3952_; 
lean_del_object(v___x_3902_);
v___x_3952_ = l_List_isEmpty___redArg(v_fst_3904_);
lean_dec(v_fst_3904_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
lean_dec(v___y_3950_);
lean_dec(v___x_3909_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec(v_trace_2964_);
lean_dec_ref(v_cfg_2963_);
v___x_3953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3954_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3953_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
return v___x_3954_;
}
else
{
lean_object* v___x_3955_; 
v___x_3955_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3950_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3964_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3958_ = v___x_3955_;
v_isShared_3959_ = v_isSharedCheck_3964_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3955_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3964_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3960_ = l_List_appendTR___redArg(v___x_3909_, v_a_3956_);
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 0, v___x_3960_);
v___x_3962_ = v___x_3958_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
else
{
lean_dec(v___x_3909_);
return v___x_3955_;
}
}
}
else
{
v___y_3934_ = v___y_3950_;
goto v___jp_3933_;
}
}
v___jp_3965_:
{
uint8_t v_commitIndependentGoals_3967_; lean_object* v___x_3968_; 
v_commitIndependentGoals_3967_ = lean_ctor_get_uint8(v_cfg_2963_, sizeof(void*)*4);
lean_inc(v___x_3909_);
v___x_3968_ = l_List_appendTR___redArg(v_a_3966_, v___x_3909_);
if (v_commitIndependentGoals_3967_ == 0)
{
v___y_3950_ = v___x_3968_;
v___y_3951_ = v___x_2983_;
goto v___jp_3949_;
}
else
{
uint8_t v___x_3969_; 
v___x_3969_ = l_List_isEmpty___redArg(v___x_3909_);
if (v___x_3969_ == 0)
{
v___y_3934_ = v___x_3968_;
goto v___jp_3933_;
}
else
{
v___y_3950_ = v___x_3968_;
v___y_3951_ = v___x_2983_;
goto v___jp_3949_;
}
}
}
v___jp_3972_:
{
lean_object* v___x_3976_; double v___x_3977_; double v___x_3978_; double v___x_3979_; double v___x_3980_; double v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3985_; 
v___x_3976_ = lean_io_mono_nanos_now();
v___x_3977_ = lean_float_of_nat(v___y_3973_);
v___x_3978_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3979_ = lean_float_div(v___x_3977_, v___x_3978_);
v___x_3980_ = lean_float_of_nat(v___x_3976_);
v___x_3981_ = lean_float_div(v___x_3980_, v___x_3978_);
v___x_3982_ = lean_box_float(v___x_3979_);
v___x_3983_ = lean_box_float(v___x_3981_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 1, v___x_3983_);
lean_ctor_set(v___x_3907_, 0, v___x_3982_);
v___x_3985_ = v___x_3907_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v___x_3982_);
lean_ctor_set(v_reuseFailAlloc_3988_, 1, v___x_3983_);
v___x_3985_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v_a_3975_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
v___x_3987_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2964_, v_hasTrace_2986_, v___x_3071_, v_options_2985_, v___x_3074_, v___y_3974_, v___f_3970_, v___x_3986_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
return v___x_3987_;
}
}
v___jp_3989_:
{
lean_object* v___x_3993_; 
v___x_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3993_, 0, v_a_3992_);
v___y_3973_ = v___y_3990_;
v___y_3974_ = v___y_3991_;
v_a_3975_ = v___x_3993_;
goto v___jp_3972_;
}
v___jp_3994_:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = l_List_appendTR___redArg(v___x_3909_, v_fst_3904_);
v___x_3999_ = l_List_appendTR___redArg(v___x_3998_, v_a_3997_);
v___y_3990_ = v___y_3995_;
v___y_3991_ = v___y_3996_;
v_a_3992_ = v___x_3999_;
goto v___jp_3989_;
}
v___jp_4000_:
{
lean_object* v___x_4004_; 
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v_a_4003_);
v___y_3973_ = v___y_4001_;
v___y_3974_ = v___y_4002_;
v_a_3975_ = v___x_4004_;
goto v___jp_3972_;
}
v___jp_4005_:
{
if (lean_obj_tag(v___y_4008_) == 0)
{
lean_object* v_a_4009_; 
v_a_4009_ = lean_ctor_get(v___y_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___y_4008_, 1);
v___y_3990_ = v___y_4006_;
v___y_3991_ = v___y_4007_;
v_a_3992_ = v_a_4009_;
goto v___jp_3989_;
}
else
{
lean_object* v_a_4010_; 
v_a_4010_ = lean_ctor_get(v___y_4008_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___y_4008_, 1);
v___y_4001_ = v___y_4006_;
v___y_4002_ = v___y_4007_;
v_a_4003_ = v_a_4010_;
goto v___jp_4000_;
}
}
v___jp_4011_:
{
if (lean_obj_tag(v___y_4014_) == 0)
{
lean_object* v_a_4015_; 
v_a_4015_ = lean_ctor_get(v___y_4014_, 0);
lean_inc(v_a_4015_);
lean_dec_ref_known(v___y_4014_, 1);
v___y_3995_ = v___y_4012_;
v___y_3996_ = v___y_4013_;
v_a_3997_ = v_a_4015_;
goto v___jp_3994_;
}
else
{
lean_object* v_a_4016_; 
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
v_a_4016_ = lean_ctor_get(v___y_4014_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___y_4014_, 1);
v___y_4001_ = v___y_4012_;
v___y_4002_ = v___y_4013_;
v_a_4003_ = v_a_4016_;
goto v___jp_4000_;
}
}
v___jp_4017_:
{
if (v___y_4022_ == 0)
{
lean_object* v___x_4023_; 
lean_dec_ref(v___y_4020_);
v___x_4023_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4019_, v_a_2970_, v_a_2972_);
lean_dec_ref(v___y_4019_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_dec_ref_known(v___x_4023_, 1);
v___y_3995_ = v___y_4018_;
v___y_3996_ = v___y_4021_;
v_a_3997_ = v_snd_2979_;
goto v___jp_3994_;
}
else
{
lean_object* v_a_4024_; 
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
lean_dec(v_snd_2979_);
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4023_, 1);
v___y_4001_ = v___y_4018_;
v___y_4002_ = v___y_4021_;
v_a_4003_ = v_a_4024_;
goto v___jp_4000_;
}
}
else
{
lean_dec_ref(v___y_4019_);
lean_dec(v_snd_2979_);
v___y_4012_ = v___y_4018_;
v___y_4013_ = v___y_4021_;
v___y_4014_ = v___y_4020_;
goto v___jp_4011_;
}
}
v___jp_4025_:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Lean_Meta_saveState___redArg(v_a_2970_, v_a_2972_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4031_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4029_, 1);
lean_inc(v_snd_2979_);
lean_inc(v_trace_2964_);
v___x_4031_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_4027_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_dec(v_a_4030_);
lean_dec(v_snd_2979_);
v___y_4012_ = v___y_4026_;
v___y_4013_ = v___y_4028_;
v___y_4014_ = v___x_4031_;
goto v___jp_4011_;
}
else
{
lean_object* v_a_4032_; uint8_t v___x_4033_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
v___x_4033_ = l_Lean_Exception_isInterrupt(v_a_4032_);
if (v___x_4033_ == 0)
{
uint8_t v___x_4034_; 
v___x_4034_ = l_Lean_Exception_isRuntime(v_a_4032_);
v___y_4018_ = v___y_4026_;
v___y_4019_ = v_a_4030_;
v___y_4020_ = v___x_4031_;
v___y_4021_ = v___y_4028_;
v___y_4022_ = v___x_4034_;
goto v___jp_4017_;
}
else
{
lean_dec(v_a_4032_);
v___y_4018_ = v___y_4026_;
v___y_4019_ = v_a_4030_;
v___y_4020_ = v___x_4031_;
v___y_4021_ = v___y_4028_;
v___y_4022_ = v___x_4033_;
goto v___jp_4017_;
}
}
}
else
{
lean_object* v_a_4035_; 
lean_dec(v___y_4027_);
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_4035_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4029_, 1);
v___y_4001_ = v___y_4026_;
v___y_4002_ = v___y_4028_;
v_a_4003_ = v_a_4035_;
goto v___jp_4000_;
}
}
v___jp_4036_:
{
if (v___y_4040_ == 0)
{
uint8_t v___x_4041_; 
v___x_4041_ = l_List_isEmpty___redArg(v_fst_3904_);
lean_dec(v_fst_3904_);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
lean_dec(v___y_4038_);
lean_dec(v___x_3909_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v___x_4042_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4043_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4042_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_4006_ = v___y_4037_;
v___y_4007_ = v___y_4039_;
v___y_4008_ = v___x_4043_;
goto v___jp_4005_;
}
else
{
lean_object* v___x_4044_; 
lean_inc(v_trace_2964_);
v___x_4044_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_4038_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_4044_) == 0)
{
lean_object* v_a_4045_; lean_object* v___x_4046_; 
v_a_4045_ = lean_ctor_get(v___x_4044_, 0);
lean_inc(v_a_4045_);
lean_dec_ref_known(v___x_4044_, 1);
v___x_4046_ = l_List_appendTR___redArg(v___x_3909_, v_a_4045_);
v___y_3990_ = v___y_4037_;
v___y_3991_ = v___y_4039_;
v_a_3992_ = v___x_4046_;
goto v___jp_3989_;
}
else
{
lean_dec(v___x_3909_);
v___y_4006_ = v___y_4037_;
v___y_4007_ = v___y_4039_;
v___y_4008_ = v___x_4044_;
goto v___jp_4005_;
}
}
}
else
{
v___y_4026_ = v___y_4037_;
v___y_4027_ = v___y_4038_;
v___y_4028_ = v___y_4039_;
goto v___jp_4025_;
}
}
v___jp_4047_:
{
uint8_t v_commitIndependentGoals_4051_; lean_object* v___x_4052_; 
v_commitIndependentGoals_4051_ = lean_ctor_get_uint8(v_cfg_2963_, sizeof(void*)*4);
lean_inc(v___x_3909_);
v___x_4052_ = l_List_appendTR___redArg(v_a_4050_, v___x_3909_);
if (v_commitIndependentGoals_4051_ == 0)
{
v___y_4037_ = v___y_4048_;
v___y_4038_ = v___x_4052_;
v___y_4039_ = v___y_4049_;
v___y_4040_ = v___x_2983_;
goto v___jp_4036_;
}
else
{
uint8_t v___x_4053_; 
v___x_4053_ = l_List_isEmpty___redArg(v___x_3909_);
if (v___x_4053_ == 0)
{
v___y_4026_ = v___y_4048_;
v___y_4027_ = v___x_4052_;
v___y_4028_ = v___y_4049_;
goto v___jp_4025_;
}
else
{
v___y_4037_ = v___y_4048_;
v___y_4038_ = v___x_4052_;
v___y_4039_ = v___y_4049_;
v___y_4040_ = v___x_2983_;
goto v___jp_4036_;
}
}
}
v___jp_4054_:
{
lean_object* v___x_4058_; double v___x_4059_; double v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4058_ = lean_io_get_num_heartbeats();
v___x_4059_ = lean_float_of_nat(v___y_4055_);
v___x_4060_ = lean_float_of_nat(v___x_4058_);
v___x_4061_ = lean_box_float(v___x_4059_);
v___x_4062_ = lean_box_float(v___x_4060_);
v___x_4063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4061_);
lean_ctor_set(v___x_4063_, 1, v___x_4062_);
v___x_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4064_, 0, v_a_4057_);
lean_ctor_set(v___x_4064_, 1, v___x_4063_);
v___x_4065_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2964_, v_hasTrace_2986_, v___x_3071_, v_options_2985_, v___x_3074_, v___y_4056_, v___f_3970_, v___x_4064_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
return v___x_4065_;
}
v___jp_4066_:
{
lean_object* v___x_4070_; 
v___x_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4070_, 0, v_a_4069_);
v___y_4055_ = v___y_4067_;
v___y_4056_ = v___y_4068_;
v_a_4057_ = v___x_4070_;
goto v___jp_4054_;
}
v___jp_4071_:
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4075_, 0, v_a_4074_);
v___y_4055_ = v___y_4072_;
v___y_4056_ = v___y_4073_;
v_a_4057_ = v___x_4075_;
goto v___jp_4054_;
}
v___jp_4076_:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = l_List_appendTR___redArg(v___x_3909_, v_fst_3904_);
v___x_4081_ = l_List_appendTR___redArg(v___x_4080_, v_a_4079_);
v___y_4072_ = v___y_4077_;
v___y_4073_ = v___y_4078_;
v_a_4074_ = v___x_4081_;
goto v___jp_4071_;
}
v___jp_4082_:
{
if (lean_obj_tag(v___y_4085_) == 0)
{
lean_object* v_a_4086_; 
v_a_4086_ = lean_ctor_get(v___y_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref_known(v___y_4085_, 1);
v___y_4077_ = v___y_4083_;
v___y_4078_ = v___y_4084_;
v_a_4079_ = v_a_4086_;
goto v___jp_4076_;
}
else
{
lean_object* v_a_4087_; 
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
v_a_4087_ = lean_ctor_get(v___y_4085_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v___y_4085_, 1);
v___y_4067_ = v___y_4083_;
v___y_4068_ = v___y_4084_;
v_a_4069_ = v_a_4087_;
goto v___jp_4066_;
}
}
v___jp_4088_:
{
if (v___y_4093_ == 0)
{
lean_object* v___x_4094_; 
lean_dec_ref(v___y_4091_);
v___x_4094_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4090_, v_a_2970_, v_a_2972_);
lean_dec_ref(v___y_4090_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_dec_ref_known(v___x_4094_, 1);
v___y_4077_ = v___y_4089_;
v___y_4078_ = v___y_4092_;
v_a_4079_ = v_snd_2979_;
goto v___jp_4076_;
}
else
{
lean_object* v_a_4095_; 
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
lean_dec(v_snd_2979_);
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4094_, 1);
v___y_4067_ = v___y_4089_;
v___y_4068_ = v___y_4092_;
v_a_4069_ = v_a_4095_;
goto v___jp_4066_;
}
}
else
{
lean_dec_ref(v___y_4090_);
lean_dec(v_snd_2979_);
v___y_4083_ = v___y_4089_;
v___y_4084_ = v___y_4092_;
v___y_4085_ = v___y_4091_;
goto v___jp_4082_;
}
}
v___jp_4096_:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Lean_Meta_saveState___redArg(v_a_2970_, v_a_2972_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4102_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v___x_4100_, 1);
lean_inc(v_snd_2979_);
lean_inc(v_trace_2964_);
v___x_4102_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_4097_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_dec(v_a_4101_);
lean_dec(v_snd_2979_);
v___y_4083_ = v___y_4098_;
v___y_4084_ = v___y_4099_;
v___y_4085_ = v___x_4102_;
goto v___jp_4082_;
}
else
{
lean_object* v_a_4103_; uint8_t v___x_4104_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
v___x_4104_ = l_Lean_Exception_isInterrupt(v_a_4103_);
if (v___x_4104_ == 0)
{
uint8_t v___x_4105_; 
v___x_4105_ = l_Lean_Exception_isRuntime(v_a_4103_);
v___y_4089_ = v___y_4098_;
v___y_4090_ = v_a_4101_;
v___y_4091_ = v___x_4102_;
v___y_4092_ = v___y_4099_;
v___y_4093_ = v___x_4105_;
goto v___jp_4088_;
}
else
{
lean_dec(v_a_4103_);
v___y_4089_ = v___y_4098_;
v___y_4090_ = v_a_4101_;
v___y_4091_ = v___x_4102_;
v___y_4092_ = v___y_4099_;
v___y_4093_ = v___x_4104_;
goto v___jp_4088_;
}
}
}
else
{
lean_object* v_a_4106_; 
lean_dec(v___y_4097_);
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_4106_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4106_);
lean_dec_ref_known(v___x_4100_, 1);
v___y_4067_ = v___y_4098_;
v___y_4068_ = v___y_4099_;
v_a_4069_ = v_a_4106_;
goto v___jp_4066_;
}
}
v___jp_4107_:
{
if (lean_obj_tag(v___y_4110_) == 0)
{
lean_object* v_a_4111_; 
v_a_4111_ = lean_ctor_get(v___y_4110_, 0);
lean_inc(v_a_4111_);
lean_dec_ref_known(v___y_4110_, 1);
v___y_4072_ = v___y_4108_;
v___y_4073_ = v___y_4109_;
v_a_4074_ = v_a_4111_;
goto v___jp_4071_;
}
else
{
lean_object* v_a_4112_; 
v_a_4112_ = lean_ctor_get(v___y_4110_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___y_4110_, 1);
v___y_4067_ = v___y_4108_;
v___y_4068_ = v___y_4109_;
v_a_4069_ = v_a_4112_;
goto v___jp_4066_;
}
}
v___jp_4113_:
{
lean_object* v___x_4117_; 
lean_inc(v_trace_2964_);
v___x_4117_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_4114_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4119_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_a_4118_);
lean_dec_ref_known(v___x_4117_, 1);
v___x_4119_ = l_List_appendTR___redArg(v___x_3909_, v_a_4118_);
v___y_4072_ = v___y_4115_;
v___y_4073_ = v___y_4116_;
v_a_4074_ = v___x_4119_;
goto v___jp_4071_;
}
else
{
lean_dec(v___x_3909_);
v___y_4108_ = v___y_4115_;
v___y_4109_ = v___y_4116_;
v___y_4110_ = v___x_4117_;
goto v___jp_4107_;
}
}
v___jp_4120_:
{
if (v___y_4125_ == 0)
{
uint8_t v___x_4126_; 
v___x_4126_ = l_List_isEmpty___redArg(v_fst_3904_);
lean_dec(v_fst_3904_);
if (v___x_4126_ == 0)
{
if (v___y_4124_ == 0)
{
v___y_4114_ = v___y_4121_;
v___y_4115_ = v___y_4122_;
v___y_4116_ = v___y_4123_;
goto v___jp_4113_;
}
else
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
lean_dec(v___y_4121_);
lean_dec(v___x_3909_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v___x_4127_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4128_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4127_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_4108_ = v___y_4122_;
v___y_4109_ = v___y_4123_;
v___y_4110_ = v___x_4128_;
goto v___jp_4107_;
}
}
else
{
v___y_4114_ = v___y_4121_;
v___y_4115_ = v___y_4122_;
v___y_4116_ = v___y_4123_;
goto v___jp_4113_;
}
}
else
{
v___y_4097_ = v___y_4121_;
v___y_4098_ = v___y_4122_;
v___y_4099_ = v___y_4123_;
goto v___jp_4096_;
}
}
v___jp_4129_:
{
uint8_t v_commitIndependentGoals_4134_; lean_object* v___x_4135_; 
v_commitIndependentGoals_4134_ = lean_ctor_get_uint8(v_cfg_2963_, sizeof(void*)*4);
lean_inc(v___x_3909_);
v___x_4135_ = l_List_appendTR___redArg(v_a_4133_, v___x_3909_);
if (v_commitIndependentGoals_4134_ == 0)
{
v___y_4121_ = v___x_4135_;
v___y_4122_ = v___y_4130_;
v___y_4123_ = v___y_4131_;
v___y_4124_ = v___y_4132_;
v___y_4125_ = v___x_2983_;
goto v___jp_4120_;
}
else
{
uint8_t v___x_4136_; 
v___x_4136_ = l_List_isEmpty___redArg(v___x_3909_);
if (v___x_4136_ == 0)
{
v___y_4097_ = v___x_4135_;
v___y_4098_ = v___y_4130_;
v___y_4099_ = v___y_4131_;
goto v___jp_4096_;
}
else
{
v___y_4121_ = v___x_4135_;
v___y_4122_ = v___y_4130_;
v___y_4123_ = v___y_4131_;
v___y_4124_ = v___y_4132_;
v___y_4125_ = v___x_2983_;
goto v___jp_4120_;
}
}
}
v___jp_4137_:
{
lean_object* v___x_4138_; 
v___x_4138_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2972_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v___x_4140_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4141_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2985_, v___x_4140_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = lean_io_mono_nanos_now();
v___x_4143_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2986_, v___x_2983_, v_goals_2967_, v___x_3971_, v_a_2970_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4145_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___x_4143_, 1);
v___x_4145_ = l_List_reverse___redArg(v_a_4144_);
v___y_4048_ = v___x_4142_;
v___y_4049_ = v_a_4139_;
v_a_4050_ = v___x_4145_;
goto v___jp_4047_;
}
else
{
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4146_; 
v_a_4146_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4143_, 1);
v___y_4048_ = v___x_4142_;
v___y_4049_ = v_a_4139_;
v_a_4050_ = v_a_4146_;
goto v___jp_4047_;
}
else
{
lean_object* v_a_4147_; 
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_4147_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4143_, 1);
v___y_4001_ = v___x_4142_;
v___y_4002_ = v_a_4139_;
v_a_4003_ = v_a_4147_;
goto v___jp_4000_;
}
}
}
else
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
lean_del_object(v___x_3907_);
v___x_4148_ = lean_io_get_num_heartbeats();
v___x_4149_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2986_, v___x_2983_, v_goals_2967_, v___x_3971_, v_a_2970_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4151_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref_known(v___x_4149_, 1);
v___x_4151_ = l_List_reverse___redArg(v_a_4150_);
v___y_4130_ = v___x_4148_;
v___y_4131_ = v_a_4139_;
v___y_4132_ = v___x_4141_;
v_a_4133_ = v___x_4151_;
goto v___jp_4129_;
}
else
{
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4152_; 
v_a_4152_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4149_, 1);
v___y_4130_ = v___x_4148_;
v___y_4131_ = v_a_4139_;
v___y_4132_ = v___x_4141_;
v_a_4133_ = v_a_4152_;
goto v___jp_4129_;
}
else
{
lean_object* v_a_4153_; 
lean_dec(v___x_3909_);
lean_dec(v_fst_3904_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_4153_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4149_, 1);
v___y_4067_ = v___x_4148_;
v___y_4068_ = v_a_4139_;
v_a_4069_ = v_a_4153_;
goto v___jp_4066_;
}
}
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
lean_dec_ref(v___f_3970_);
lean_dec(v___x_3909_);
lean_del_object(v___x_3907_);
lean_dec(v_fst_3904_);
lean_dec(v_snd_2979_);
lean_dec(v_goals_2967_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec(v_trace_2964_);
lean_dec_ref(v_cfg_2963_);
v_a_4154_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4138_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4138_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_snd_2979_);
lean_dec(v_goals_2967_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec(v_trace_2964_);
lean_dec_ref(v_cfg_2963_);
v_a_4168_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_3899_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_3899_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
else
{
goto v___jp_3852_;
}
}
else
{
goto v___jp_3852_;
}
v___jp_3075_:
{
lean_object* v___x_3079_; double v___x_3080_; double v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3079_ = lean_io_get_num_heartbeats();
v___x_3080_ = lean_float_of_nat(v___y_3077_);
v___x_3081_ = lean_float_of_nat(v___x_3079_);
v___x_3082_ = lean_box_float(v___x_3080_);
v___x_3083_ = lean_box_float(v___x_3081_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 1, v___x_3083_);
lean_ctor_set(v___x_2981_, 0, v___x_3082_);
v___x_3085_ = v___x_2981_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3086_, 0, v_a_3078_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2964_, v_hasTrace_2986_, v___x_3071_, v_options_2985_, v___x_3074_, v___y_3076_, v___f_3070_, v___x_3086_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
return v___x_3087_;
}
}
v___jp_3089_:
{
lean_object* v___x_3093_; 
v___x_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3093_, 0, v_a_3092_);
v___y_3076_ = v___y_3090_;
v___y_3077_ = v___y_3091_;
v_a_3078_ = v___x_3093_;
goto v___jp_3075_;
}
v___jp_3094_:
{
lean_object* v___x_3098_; 
v___x_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_a_3097_);
v___y_3076_ = v___y_3095_;
v___y_3077_ = v___y_3096_;
v_a_3078_ = v___x_3098_;
goto v___jp_3075_;
}
v___jp_3099_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = l_List_appendTR___redArg(v___y_3100_, v___y_3103_);
v___x_3106_ = l_List_appendTR___redArg(v___x_3105_, v_a_3104_);
v___y_3095_ = v___y_3101_;
v___y_3096_ = v___y_3102_;
v_a_3097_ = v___x_3106_;
goto v___jp_3094_;
}
v___jp_3107_:
{
if (lean_obj_tag(v___y_3112_) == 0)
{
lean_object* v_a_3113_; 
v_a_3113_ = lean_ctor_get(v___y_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___y_3112_, 1);
v___y_3100_ = v___y_3108_;
v___y_3101_ = v___y_3109_;
v___y_3102_ = v___y_3110_;
v___y_3103_ = v___y_3111_;
v_a_3104_ = v_a_3113_;
goto v___jp_3099_;
}
else
{
lean_object* v_a_3114_; 
lean_dec(v___y_3111_);
lean_dec(v___y_3108_);
v_a_3114_ = lean_ctor_get(v___y_3112_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___y_3112_, 1);
v___y_3090_ = v___y_3109_;
v___y_3091_ = v___y_3110_;
v_a_3092_ = v_a_3114_;
goto v___jp_3089_;
}
}
v___jp_3115_:
{
if (v___y_3122_ == 0)
{
lean_object* v___x_3123_; 
lean_dec_ref(v___y_3118_);
v___x_3123_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3116_, v_a_2970_, v_a_2972_);
lean_dec_ref(v___y_3116_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_dec_ref_known(v___x_3123_, 1);
v___y_3100_ = v___y_3117_;
v___y_3101_ = v___y_3119_;
v___y_3102_ = v___y_3120_;
v___y_3103_ = v___y_3121_;
v_a_3104_ = v_snd_2979_;
goto v___jp_3099_;
}
else
{
lean_object* v_a_3124_; 
lean_dec(v___y_3121_);
lean_dec(v___y_3117_);
lean_dec(v_snd_2979_);
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
v___y_3090_ = v___y_3119_;
v___y_3091_ = v___y_3120_;
v_a_3092_ = v_a_3124_;
goto v___jp_3089_;
}
}
else
{
lean_dec_ref(v___y_3116_);
lean_dec(v_snd_2979_);
v___y_3108_ = v___y_3117_;
v___y_3109_ = v___y_3119_;
v___y_3110_ = v___y_3120_;
v___y_3111_ = v___y_3121_;
v___y_3112_ = v___y_3118_;
goto v___jp_3107_;
}
}
v___jp_3125_:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Meta_saveState___redArg(v_a_2970_, v_a_2972_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3133_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3131_, 1);
lean_inc(v_snd_2979_);
lean_inc(v_trace_2964_);
v___x_3133_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3126_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_dec(v_a_3132_);
lean_dec(v_snd_2979_);
v___y_3108_ = v___y_3127_;
v___y_3109_ = v___y_3128_;
v___y_3110_ = v___y_3129_;
v___y_3111_ = v___y_3130_;
v___y_3112_ = v___x_3133_;
goto v___jp_3107_;
}
else
{
lean_object* v_a_3134_; uint8_t v___x_3135_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3134_);
v___x_3135_ = l_Lean_Exception_isInterrupt(v_a_3134_);
if (v___x_3135_ == 0)
{
uint8_t v___x_3136_; 
v___x_3136_ = l_Lean_Exception_isRuntime(v_a_3134_);
v___y_3116_ = v_a_3132_;
v___y_3117_ = v___y_3127_;
v___y_3118_ = v___x_3133_;
v___y_3119_ = v___y_3128_;
v___y_3120_ = v___y_3129_;
v___y_3121_ = v___y_3130_;
v___y_3122_ = v___x_3136_;
goto v___jp_3115_;
}
else
{
lean_dec(v_a_3134_);
v___y_3116_ = v_a_3132_;
v___y_3117_ = v___y_3127_;
v___y_3118_ = v___x_3133_;
v___y_3119_ = v___y_3128_;
v___y_3120_ = v___y_3129_;
v___y_3121_ = v___y_3130_;
v___y_3122_ = v___x_3135_;
goto v___jp_3115_;
}
}
}
else
{
lean_object* v_a_3137_; 
lean_dec(v___y_3130_);
lean_dec(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3137_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___x_3131_, 1);
v___y_3090_ = v___y_3128_;
v___y_3091_ = v___y_3129_;
v_a_3092_ = v_a_3137_;
goto v___jp_3089_;
}
}
v___jp_3138_:
{
if (lean_obj_tag(v___y_3141_) == 0)
{
lean_object* v_a_3142_; 
v_a_3142_ = lean_ctor_get(v___y_3141_, 0);
lean_inc(v_a_3142_);
lean_dec_ref_known(v___y_3141_, 1);
v___y_3095_ = v___y_3139_;
v___y_3096_ = v___y_3140_;
v_a_3097_ = v_a_3142_;
goto v___jp_3094_;
}
else
{
lean_object* v_a_3143_; 
v_a_3143_ = lean_ctor_get(v___y_3141_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___y_3141_, 1);
v___y_3090_ = v___y_3139_;
v___y_3091_ = v___y_3140_;
v_a_3092_ = v_a_3143_;
goto v___jp_3089_;
}
}
v___jp_3144_:
{
lean_object* v___x_3152_; double v___x_3153_; double v___x_3154_; double v___x_3155_; double v___x_3156_; double v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3152_ = lean_io_mono_nanos_now();
v___x_3153_ = lean_float_of_nat(v___y_3147_);
v___x_3154_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3155_ = lean_float_div(v___x_3153_, v___x_3154_);
v___x_3156_ = lean_float_of_nat(v___x_3152_);
v___x_3157_ = lean_float_div(v___x_3156_, v___x_3154_);
v___x_3158_ = lean_box_float(v___x_3155_);
v___x_3159_ = lean_box_float(v___x_3157_);
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3158_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v_a_3151_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
lean_inc(v_trace_2964_);
v___x_3162_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2964_, v_hasTrace_2986_, v___x_3071_, v_options_2985_, v___y_3145_, v___y_3149_, v___y_3150_, v___x_3161_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_3139_ = v___y_3146_;
v___y_3140_ = v___y_3148_;
v___y_3141_ = v___x_3162_;
goto v___jp_3138_;
}
v___jp_3163_:
{
lean_object* v___x_3171_; 
v___x_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3171_, 0, v_a_3170_);
v___y_3145_ = v___y_3164_;
v___y_3146_ = v___y_3166_;
v___y_3147_ = v___y_3165_;
v___y_3148_ = v___y_3168_;
v___y_3149_ = v___y_3167_;
v___y_3150_ = v___y_3169_;
v_a_3151_ = v___x_3171_;
goto v___jp_3144_;
}
v___jp_3172_:
{
lean_object* v___x_3180_; 
v___x_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3180_, 0, v_a_3179_);
v___y_3145_ = v___y_3173_;
v___y_3146_ = v___y_3175_;
v___y_3147_ = v___y_3174_;
v___y_3148_ = v___y_3177_;
v___y_3149_ = v___y_3176_;
v___y_3150_ = v___y_3178_;
v_a_3151_ = v___x_3180_;
goto v___jp_3144_;
}
v___jp_3181_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = l_List_appendTR___redArg(v___y_3182_, v___y_3189_);
v___x_3192_ = l_List_appendTR___redArg(v___x_3191_, v_a_3190_);
v___y_3173_ = v___y_3183_;
v___y_3174_ = v___y_3185_;
v___y_3175_ = v___y_3184_;
v___y_3176_ = v___y_3187_;
v___y_3177_ = v___y_3186_;
v___y_3178_ = v___y_3188_;
v_a_3179_ = v___x_3192_;
goto v___jp_3172_;
}
v___jp_3193_:
{
if (lean_obj_tag(v___y_3202_) == 0)
{
lean_object* v_a_3203_; 
v_a_3203_ = lean_ctor_get(v___y_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref_known(v___y_3202_, 1);
v___y_3182_ = v___y_3194_;
v___y_3183_ = v___y_3195_;
v___y_3184_ = v___y_3197_;
v___y_3185_ = v___y_3196_;
v___y_3186_ = v___y_3199_;
v___y_3187_ = v___y_3198_;
v___y_3188_ = v___y_3200_;
v___y_3189_ = v___y_3201_;
v_a_3190_ = v_a_3203_;
goto v___jp_3181_;
}
else
{
lean_object* v_a_3204_; 
lean_dec(v___y_3201_);
lean_dec(v___y_3194_);
v_a_3204_ = lean_ctor_get(v___y_3202_, 0);
lean_inc(v_a_3204_);
lean_dec_ref_known(v___y_3202_, 1);
v___y_3164_ = v___y_3195_;
v___y_3165_ = v___y_3196_;
v___y_3166_ = v___y_3197_;
v___y_3167_ = v___y_3198_;
v___y_3168_ = v___y_3199_;
v___y_3169_ = v___y_3200_;
v_a_3170_ = v_a_3204_;
goto v___jp_3163_;
}
}
v___jp_3205_:
{
if (v___y_3216_ == 0)
{
lean_object* v___x_3217_; 
lean_dec_ref(v___y_3211_);
v___x_3217_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3206_, v_a_2970_, v_a_2972_);
lean_dec_ref(v___y_3206_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_dec_ref_known(v___x_3217_, 1);
v___y_3182_ = v___y_3207_;
v___y_3183_ = v___y_3208_;
v___y_3184_ = v___y_3210_;
v___y_3185_ = v___y_3209_;
v___y_3186_ = v___y_3213_;
v___y_3187_ = v___y_3212_;
v___y_3188_ = v___y_3214_;
v___y_3189_ = v___y_3215_;
v_a_3190_ = v_snd_2979_;
goto v___jp_3181_;
}
else
{
lean_object* v_a_3218_; 
lean_dec(v___y_3215_);
lean_dec(v___y_3207_);
lean_dec(v_snd_2979_);
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___y_3164_ = v___y_3208_;
v___y_3165_ = v___y_3209_;
v___y_3166_ = v___y_3210_;
v___y_3167_ = v___y_3212_;
v___y_3168_ = v___y_3213_;
v___y_3169_ = v___y_3214_;
v_a_3170_ = v_a_3218_;
goto v___jp_3163_;
}
}
else
{
lean_dec_ref(v___y_3206_);
lean_dec(v_snd_2979_);
v___y_3194_ = v___y_3207_;
v___y_3195_ = v___y_3208_;
v___y_3196_ = v___y_3209_;
v___y_3197_ = v___y_3210_;
v___y_3198_ = v___y_3212_;
v___y_3199_ = v___y_3213_;
v___y_3200_ = v___y_3214_;
v___y_3201_ = v___y_3215_;
v___y_3202_ = v___y_3211_;
goto v___jp_3193_;
}
}
v___jp_3219_:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_Meta_saveState___redArg(v_a_2970_, v_a_2972_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3231_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref_known(v___x_3229_, 1);
lean_inc(v_snd_2979_);
lean_inc(v_trace_2964_);
v___x_3231_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3226_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_dec(v_a_3230_);
lean_dec(v_snd_2979_);
v___y_3194_ = v___y_3220_;
v___y_3195_ = v___y_3221_;
v___y_3196_ = v___y_3223_;
v___y_3197_ = v___y_3222_;
v___y_3198_ = v___y_3225_;
v___y_3199_ = v___y_3224_;
v___y_3200_ = v___y_3227_;
v___y_3201_ = v___y_3228_;
v___y_3202_ = v___x_3231_;
goto v___jp_3193_;
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
v___y_3206_ = v_a_3230_;
v___y_3207_ = v___y_3220_;
v___y_3208_ = v___y_3221_;
v___y_3209_ = v___y_3223_;
v___y_3210_ = v___y_3222_;
v___y_3211_ = v___x_3231_;
v___y_3212_ = v___y_3225_;
v___y_3213_ = v___y_3224_;
v___y_3214_ = v___y_3227_;
v___y_3215_ = v___y_3228_;
v___y_3216_ = v___x_3234_;
goto v___jp_3205_;
}
else
{
lean_dec(v_a_3232_);
v___y_3206_ = v_a_3230_;
v___y_3207_ = v___y_3220_;
v___y_3208_ = v___y_3221_;
v___y_3209_ = v___y_3223_;
v___y_3210_ = v___y_3222_;
v___y_3211_ = v___x_3231_;
v___y_3212_ = v___y_3225_;
v___y_3213_ = v___y_3224_;
v___y_3214_ = v___y_3227_;
v___y_3215_ = v___y_3228_;
v___y_3216_ = v___x_3233_;
goto v___jp_3205_;
}
}
}
else
{
lean_object* v_a_3235_; 
lean_dec(v___y_3228_);
lean_dec(v___y_3226_);
lean_dec(v___y_3220_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3235_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3229_, 1);
v___y_3164_ = v___y_3221_;
v___y_3165_ = v___y_3223_;
v___y_3166_ = v___y_3222_;
v___y_3167_ = v___y_3225_;
v___y_3168_ = v___y_3224_;
v___y_3169_ = v___y_3227_;
v_a_3170_ = v_a_3235_;
goto v___jp_3163_;
}
}
v___jp_3236_:
{
if (lean_obj_tag(v___y_3243_) == 0)
{
lean_object* v_a_3244_; 
v_a_3244_ = lean_ctor_get(v___y_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref_known(v___y_3243_, 1);
v___y_3173_ = v___y_3237_;
v___y_3174_ = v___y_3239_;
v___y_3175_ = v___y_3238_;
v___y_3176_ = v___y_3241_;
v___y_3177_ = v___y_3240_;
v___y_3178_ = v___y_3242_;
v_a_3179_ = v_a_3244_;
goto v___jp_3172_;
}
else
{
lean_object* v_a_3245_; 
v_a_3245_ = lean_ctor_get(v___y_3243_, 0);
lean_inc(v_a_3245_);
lean_dec_ref_known(v___y_3243_, 1);
v___y_3164_ = v___y_3237_;
v___y_3165_ = v___y_3239_;
v___y_3166_ = v___y_3238_;
v___y_3167_ = v___y_3241_;
v___y_3168_ = v___y_3240_;
v___y_3169_ = v___y_3242_;
v_a_3170_ = v_a_3245_;
goto v___jp_3163_;
}
}
v___jp_3246_:
{
if (v___y_3256_ == 0)
{
uint8_t v___x_3257_; 
v___x_3257_ = l_List_isEmpty___redArg(v___y_3255_);
lean_dec(v___y_3255_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_dec(v___y_3251_);
lean_dec(v___y_3247_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v___x_3258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3259_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3258_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_3237_ = v___y_3248_;
v___y_3238_ = v___y_3250_;
v___y_3239_ = v___y_3249_;
v___y_3240_ = v___y_3253_;
v___y_3241_ = v___y_3252_;
v___y_3242_ = v___y_3254_;
v___y_3243_ = v___x_3259_;
goto v___jp_3236_;
}
else
{
lean_object* v___x_3260_; 
lean_inc(v_trace_2964_);
v___x_3260_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3251_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3262_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v___x_3262_ = l_List_appendTR___redArg(v___y_3247_, v_a_3261_);
v___y_3173_ = v___y_3248_;
v___y_3174_ = v___y_3249_;
v___y_3175_ = v___y_3250_;
v___y_3176_ = v___y_3252_;
v___y_3177_ = v___y_3253_;
v___y_3178_ = v___y_3254_;
v_a_3179_ = v___x_3262_;
goto v___jp_3172_;
}
else
{
lean_dec(v___y_3247_);
v___y_3237_ = v___y_3248_;
v___y_3238_ = v___y_3250_;
v___y_3239_ = v___y_3249_;
v___y_3240_ = v___y_3253_;
v___y_3241_ = v___y_3252_;
v___y_3242_ = v___y_3254_;
v___y_3243_ = v___x_3260_;
goto v___jp_3236_;
}
}
}
else
{
v___y_3220_ = v___y_3247_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3250_;
v___y_3223_ = v___y_3249_;
v___y_3224_ = v___y_3253_;
v___y_3225_ = v___y_3252_;
v___y_3226_ = v___y_3251_;
v___y_3227_ = v___y_3254_;
v___y_3228_ = v___y_3255_;
goto v___jp_3219_;
}
}
v___jp_3263_:
{
uint8_t v_commitIndependentGoals_3273_; lean_object* v___x_3274_; 
v_commitIndependentGoals_3273_ = lean_ctor_get_uint8(v_cfg_2963_, sizeof(void*)*4);
lean_inc(v___y_3264_);
v___x_3274_ = l_List_appendTR___redArg(v_a_3272_, v___y_3264_);
if (v_commitIndependentGoals_3273_ == 0)
{
v___y_3247_ = v___y_3264_;
v___y_3248_ = v___y_3265_;
v___y_3249_ = v___y_3266_;
v___y_3250_ = v___y_3267_;
v___y_3251_ = v___x_3274_;
v___y_3252_ = v___y_3268_;
v___y_3253_ = v___y_3269_;
v___y_3254_ = v___y_3270_;
v___y_3255_ = v___y_3271_;
v___y_3256_ = v___x_2983_;
goto v___jp_3246_;
}
else
{
uint8_t v___x_3275_; 
v___x_3275_ = l_List_isEmpty___redArg(v___y_3264_);
if (v___x_3275_ == 0)
{
v___y_3220_ = v___y_3264_;
v___y_3221_ = v___y_3265_;
v___y_3222_ = v___y_3267_;
v___y_3223_ = v___y_3266_;
v___y_3224_ = v___y_3269_;
v___y_3225_ = v___y_3268_;
v___y_3226_ = v___x_3274_;
v___y_3227_ = v___y_3270_;
v___y_3228_ = v___y_3271_;
goto v___jp_3219_;
}
else
{
v___y_3247_ = v___y_3264_;
v___y_3248_ = v___y_3265_;
v___y_3249_ = v___y_3266_;
v___y_3250_ = v___y_3267_;
v___y_3251_ = v___x_3274_;
v___y_3252_ = v___y_3268_;
v___y_3253_ = v___y_3269_;
v___y_3254_ = v___y_3270_;
v___y_3255_ = v___y_3271_;
v___y_3256_ = v___x_2983_;
goto v___jp_3246_;
}
}
}
v___jp_3276_:
{
lean_object* v___x_3284_; double v___x_3285_; double v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3284_ = lean_io_get_num_heartbeats();
v___x_3285_ = lean_float_of_nat(v___y_3277_);
v___x_3286_ = lean_float_of_nat(v___x_3284_);
v___x_3287_ = lean_box_float(v___x_3285_);
v___x_3288_ = lean_box_float(v___x_3286_);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v_a_3283_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
lean_inc(v_trace_2964_);
v___x_3291_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2964_, v_hasTrace_2986_, v___x_3071_, v_options_2985_, v___y_3278_, v___y_3281_, v___y_3282_, v___x_3290_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_3139_ = v___y_3279_;
v___y_3140_ = v___y_3280_;
v___y_3141_ = v___x_3291_;
goto v___jp_3138_;
}
v___jp_3292_:
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v_a_3299_);
v___y_3277_ = v___y_3293_;
v___y_3278_ = v___y_3294_;
v___y_3279_ = v___y_3295_;
v___y_3280_ = v___y_3297_;
v___y_3281_ = v___y_3296_;
v___y_3282_ = v___y_3298_;
v_a_3283_ = v___x_3300_;
goto v___jp_3276_;
}
v___jp_3301_:
{
lean_object* v___x_3309_; 
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v_a_3308_);
v___y_3277_ = v___y_3302_;
v___y_3278_ = v___y_3303_;
v___y_3279_ = v___y_3304_;
v___y_3280_ = v___y_3306_;
v___y_3281_ = v___y_3305_;
v___y_3282_ = v___y_3307_;
v_a_3283_ = v___x_3309_;
goto v___jp_3276_;
}
v___jp_3310_:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = l_List_appendTR___redArg(v___y_3312_, v___y_3318_);
v___x_3321_ = l_List_appendTR___redArg(v___x_3320_, v_a_3319_);
v___y_3302_ = v___y_3311_;
v___y_3303_ = v___y_3313_;
v___y_3304_ = v___y_3314_;
v___y_3305_ = v___y_3316_;
v___y_3306_ = v___y_3315_;
v___y_3307_ = v___y_3317_;
v_a_3308_ = v___x_3321_;
goto v___jp_3301_;
}
v___jp_3322_:
{
if (lean_obj_tag(v___y_3331_) == 0)
{
lean_object* v_a_3332_; 
v_a_3332_ = lean_ctor_get(v___y_3331_, 0);
lean_inc(v_a_3332_);
lean_dec_ref_known(v___y_3331_, 1);
v___y_3311_ = v___y_3323_;
v___y_3312_ = v___y_3324_;
v___y_3313_ = v___y_3325_;
v___y_3314_ = v___y_3326_;
v___y_3315_ = v___y_3328_;
v___y_3316_ = v___y_3327_;
v___y_3317_ = v___y_3329_;
v___y_3318_ = v___y_3330_;
v_a_3319_ = v_a_3332_;
goto v___jp_3310_;
}
else
{
lean_object* v_a_3333_; 
lean_dec(v___y_3330_);
lean_dec(v___y_3324_);
v_a_3333_ = lean_ctor_get(v___y_3331_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___y_3331_, 1);
v___y_3293_ = v___y_3323_;
v___y_3294_ = v___y_3325_;
v___y_3295_ = v___y_3326_;
v___y_3296_ = v___y_3327_;
v___y_3297_ = v___y_3328_;
v___y_3298_ = v___y_3329_;
v_a_3299_ = v_a_3333_;
goto v___jp_3292_;
}
}
v___jp_3334_:
{
if (v___y_3345_ == 0)
{
lean_object* v___x_3346_; 
lean_dec_ref(v___y_3337_);
v___x_3346_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3335_, v_a_2970_, v_a_2972_);
lean_dec_ref(v___y_3335_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_dec_ref_known(v___x_3346_, 1);
v___y_3311_ = v___y_3336_;
v___y_3312_ = v___y_3338_;
v___y_3313_ = v___y_3339_;
v___y_3314_ = v___y_3340_;
v___y_3315_ = v___y_3342_;
v___y_3316_ = v___y_3341_;
v___y_3317_ = v___y_3343_;
v___y_3318_ = v___y_3344_;
v_a_3319_ = v_snd_2979_;
goto v___jp_3310_;
}
else
{
lean_object* v_a_3347_; 
lean_dec(v___y_3344_);
lean_dec(v___y_3338_);
lean_dec(v_snd_2979_);
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v___x_3346_, 1);
v___y_3293_ = v___y_3336_;
v___y_3294_ = v___y_3339_;
v___y_3295_ = v___y_3340_;
v___y_3296_ = v___y_3341_;
v___y_3297_ = v___y_3342_;
v___y_3298_ = v___y_3343_;
v_a_3299_ = v_a_3347_;
goto v___jp_3292_;
}
}
else
{
lean_dec_ref(v___y_3335_);
lean_dec(v_snd_2979_);
v___y_3323_ = v___y_3336_;
v___y_3324_ = v___y_3338_;
v___y_3325_ = v___y_3339_;
v___y_3326_ = v___y_3340_;
v___y_3327_ = v___y_3341_;
v___y_3328_ = v___y_3342_;
v___y_3329_ = v___y_3343_;
v___y_3330_ = v___y_3344_;
v___y_3331_ = v___y_3337_;
goto v___jp_3322_;
}
}
v___jp_3348_:
{
lean_object* v___x_3358_; 
v___x_3358_ = l_Lean_Meta_saveState___redArg(v_a_2970_, v_a_2972_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3360_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_a_3359_);
lean_dec_ref_known(v___x_3358_, 1);
lean_inc(v_snd_2979_);
lean_inc(v_trace_2964_);
v___x_3360_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3350_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_dec(v_a_3359_);
lean_dec(v_snd_2979_);
v___y_3323_ = v___y_3349_;
v___y_3324_ = v___y_3351_;
v___y_3325_ = v___y_3352_;
v___y_3326_ = v___y_3353_;
v___y_3327_ = v___y_3355_;
v___y_3328_ = v___y_3354_;
v___y_3329_ = v___y_3356_;
v___y_3330_ = v___y_3357_;
v___y_3331_ = v___x_3360_;
goto v___jp_3322_;
}
else
{
lean_object* v_a_3361_; uint8_t v___x_3362_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
v___x_3362_ = l_Lean_Exception_isInterrupt(v_a_3361_);
if (v___x_3362_ == 0)
{
uint8_t v___x_3363_; 
v___x_3363_ = l_Lean_Exception_isRuntime(v_a_3361_);
v___y_3335_ = v_a_3359_;
v___y_3336_ = v___y_3349_;
v___y_3337_ = v___x_3360_;
v___y_3338_ = v___y_3351_;
v___y_3339_ = v___y_3352_;
v___y_3340_ = v___y_3353_;
v___y_3341_ = v___y_3355_;
v___y_3342_ = v___y_3354_;
v___y_3343_ = v___y_3356_;
v___y_3344_ = v___y_3357_;
v___y_3345_ = v___x_3363_;
goto v___jp_3334_;
}
else
{
lean_dec(v_a_3361_);
v___y_3335_ = v_a_3359_;
v___y_3336_ = v___y_3349_;
v___y_3337_ = v___x_3360_;
v___y_3338_ = v___y_3351_;
v___y_3339_ = v___y_3352_;
v___y_3340_ = v___y_3353_;
v___y_3341_ = v___y_3355_;
v___y_3342_ = v___y_3354_;
v___y_3343_ = v___y_3356_;
v___y_3344_ = v___y_3357_;
v___y_3345_ = v___x_3362_;
goto v___jp_3334_;
}
}
}
else
{
lean_object* v_a_3364_; 
lean_dec(v___y_3357_);
lean_dec(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3364_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3358_, 1);
v___y_3293_ = v___y_3349_;
v___y_3294_ = v___y_3352_;
v___y_3295_ = v___y_3353_;
v___y_3296_ = v___y_3355_;
v___y_3297_ = v___y_3354_;
v___y_3298_ = v___y_3356_;
v_a_3299_ = v_a_3364_;
goto v___jp_3292_;
}
}
v___jp_3365_:
{
if (lean_obj_tag(v___y_3372_) == 0)
{
lean_object* v_a_3373_; 
v_a_3373_ = lean_ctor_get(v___y_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___y_3372_, 1);
v___y_3302_ = v___y_3366_;
v___y_3303_ = v___y_3367_;
v___y_3304_ = v___y_3368_;
v___y_3305_ = v___y_3370_;
v___y_3306_ = v___y_3369_;
v___y_3307_ = v___y_3371_;
v_a_3308_ = v_a_3373_;
goto v___jp_3301_;
}
else
{
lean_object* v_a_3374_; 
v_a_3374_ = lean_ctor_get(v___y_3372_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___y_3372_, 1);
v___y_3293_ = v___y_3366_;
v___y_3294_ = v___y_3367_;
v___y_3295_ = v___y_3368_;
v___y_3296_ = v___y_3370_;
v___y_3297_ = v___y_3369_;
v___y_3298_ = v___y_3371_;
v_a_3299_ = v_a_3374_;
goto v___jp_3292_;
}
}
v___jp_3375_:
{
lean_object* v___x_3384_; 
lean_inc(v_trace_2964_);
v___x_3384_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3377_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3386_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = l_List_appendTR___redArg(v___y_3378_, v_a_3385_);
v___y_3302_ = v___y_3376_;
v___y_3303_ = v___y_3379_;
v___y_3304_ = v___y_3380_;
v___y_3305_ = v___y_3382_;
v___y_3306_ = v___y_3381_;
v___y_3307_ = v___y_3383_;
v_a_3308_ = v___x_3386_;
goto v___jp_3301_;
}
else
{
lean_dec(v___y_3378_);
v___y_3366_ = v___y_3376_;
v___y_3367_ = v___y_3379_;
v___y_3368_ = v___y_3380_;
v___y_3369_ = v___y_3381_;
v___y_3370_ = v___y_3382_;
v___y_3371_ = v___y_3383_;
v___y_3372_ = v___x_3384_;
goto v___jp_3365_;
}
}
v___jp_3387_:
{
if (v___y_3398_ == 0)
{
uint8_t v___x_3399_; 
v___x_3399_ = l_List_isEmpty___redArg(v___y_3397_);
lean_dec(v___y_3397_);
if (v___x_3399_ == 0)
{
if (v___y_3391_ == 0)
{
v___y_3376_ = v___y_3389_;
v___y_3377_ = v___y_3388_;
v___y_3378_ = v___y_3390_;
v___y_3379_ = v___y_3392_;
v___y_3380_ = v___y_3393_;
v___y_3381_ = v___y_3395_;
v___y_3382_ = v___y_3394_;
v___y_3383_ = v___y_3396_;
goto v___jp_3375_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
lean_dec(v___y_3390_);
lean_dec(v___y_3388_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v___x_3400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3401_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3400_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_3366_ = v___y_3389_;
v___y_3367_ = v___y_3392_;
v___y_3368_ = v___y_3393_;
v___y_3369_ = v___y_3395_;
v___y_3370_ = v___y_3394_;
v___y_3371_ = v___y_3396_;
v___y_3372_ = v___x_3401_;
goto v___jp_3365_;
}
}
else
{
v___y_3376_ = v___y_3389_;
v___y_3377_ = v___y_3388_;
v___y_3378_ = v___y_3390_;
v___y_3379_ = v___y_3392_;
v___y_3380_ = v___y_3393_;
v___y_3381_ = v___y_3395_;
v___y_3382_ = v___y_3394_;
v___y_3383_ = v___y_3396_;
goto v___jp_3375_;
}
}
else
{
v___y_3349_ = v___y_3389_;
v___y_3350_ = v___y_3388_;
v___y_3351_ = v___y_3390_;
v___y_3352_ = v___y_3392_;
v___y_3353_ = v___y_3393_;
v___y_3354_ = v___y_3395_;
v___y_3355_ = v___y_3394_;
v___y_3356_ = v___y_3396_;
v___y_3357_ = v___y_3397_;
goto v___jp_3348_;
}
}
v___jp_3402_:
{
uint8_t v_commitIndependentGoals_3413_; lean_object* v___x_3414_; 
v_commitIndependentGoals_3413_ = lean_ctor_get_uint8(v_cfg_2963_, sizeof(void*)*4);
lean_inc(v___y_3405_);
v___x_3414_ = l_List_appendTR___redArg(v_a_3412_, v___y_3405_);
if (v_commitIndependentGoals_3413_ == 0)
{
v___y_3388_ = v___x_3414_;
v___y_3389_ = v___y_3403_;
v___y_3390_ = v___y_3405_;
v___y_3391_ = v___y_3404_;
v___y_3392_ = v___y_3406_;
v___y_3393_ = v___y_3407_;
v___y_3394_ = v___y_3408_;
v___y_3395_ = v___y_3409_;
v___y_3396_ = v___y_3410_;
v___y_3397_ = v___y_3411_;
v___y_3398_ = v___x_2983_;
goto v___jp_3387_;
}
else
{
uint8_t v___x_3415_; 
v___x_3415_ = l_List_isEmpty___redArg(v___y_3405_);
if (v___x_3415_ == 0)
{
v___y_3349_ = v___y_3403_;
v___y_3350_ = v___x_3414_;
v___y_3351_ = v___y_3405_;
v___y_3352_ = v___y_3406_;
v___y_3353_ = v___y_3407_;
v___y_3354_ = v___y_3409_;
v___y_3355_ = v___y_3408_;
v___y_3356_ = v___y_3410_;
v___y_3357_ = v___y_3411_;
goto v___jp_3348_;
}
else
{
v___y_3388_ = v___x_3414_;
v___y_3389_ = v___y_3403_;
v___y_3390_ = v___y_3405_;
v___y_3391_ = v___y_3404_;
v___y_3392_ = v___y_3406_;
v___y_3393_ = v___y_3407_;
v___y_3394_ = v___y_3408_;
v___y_3395_ = v___y_3409_;
v___y_3396_ = v___y_3410_;
v___y_3397_ = v___y_3411_;
v___y_3398_ = v___x_2983_;
goto v___jp_3387_;
}
}
}
v___jp_3416_:
{
lean_object* v___x_3425_; 
v___x_3425_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2972_);
if (lean_obj_tag(v___x_3425_) == 0)
{
if (v___y_3419_ == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3427_ = lean_io_mono_nanos_now();
v___x_3428_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3419_, v___x_2983_, v_goals_2967_, v___y_3417_, v_a_2970_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3430_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3428_, 1);
v___x_3430_ = l_List_reverse___redArg(v_a_3429_);
v___y_3264_ = v___y_3418_;
v___y_3265_ = v___y_3420_;
v___y_3266_ = v___x_3427_;
v___y_3267_ = v___y_3421_;
v___y_3268_ = v_a_3426_;
v___y_3269_ = v___y_3422_;
v___y_3270_ = v___y_3423_;
v___y_3271_ = v___y_3424_;
v_a_3272_ = v___x_3430_;
goto v___jp_3263_;
}
else
{
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3431_; 
v_a_3431_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3428_, 1);
v___y_3264_ = v___y_3418_;
v___y_3265_ = v___y_3420_;
v___y_3266_ = v___x_3427_;
v___y_3267_ = v___y_3421_;
v___y_3268_ = v_a_3426_;
v___y_3269_ = v___y_3422_;
v___y_3270_ = v___y_3423_;
v___y_3271_ = v___y_3424_;
v_a_3272_ = v_a_3431_;
goto v___jp_3263_;
}
else
{
lean_object* v_a_3432_; 
lean_dec(v___y_3424_);
lean_dec(v___y_3418_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3432_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3428_, 1);
v___y_3164_ = v___y_3420_;
v___y_3165_ = v___x_3427_;
v___y_3166_ = v___y_3421_;
v___y_3167_ = v_a_3426_;
v___y_3168_ = v___y_3422_;
v___y_3169_ = v___y_3423_;
v_a_3170_ = v_a_3432_;
goto v___jp_3163_;
}
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v_a_3433_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3434_ = lean_io_get_num_heartbeats();
v___x_3435_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3419_, v___x_2983_, v_goals_2967_, v___y_3417_, v_a_2970_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3437_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3436_);
lean_dec_ref_known(v___x_3435_, 1);
v___x_3437_ = l_List_reverse___redArg(v_a_3436_);
v___y_3403_ = v___x_3434_;
v___y_3404_ = v___y_3419_;
v___y_3405_ = v___y_3418_;
v___y_3406_ = v___y_3420_;
v___y_3407_ = v___y_3421_;
v___y_3408_ = v_a_3433_;
v___y_3409_ = v___y_3422_;
v___y_3410_ = v___y_3423_;
v___y_3411_ = v___y_3424_;
v_a_3412_ = v___x_3437_;
goto v___jp_3402_;
}
else
{
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3438_; 
v_a_3438_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3435_, 1);
v___y_3403_ = v___x_3434_;
v___y_3404_ = v___y_3419_;
v___y_3405_ = v___y_3418_;
v___y_3406_ = v___y_3420_;
v___y_3407_ = v___y_3421_;
v___y_3408_ = v_a_3433_;
v___y_3409_ = v___y_3422_;
v___y_3410_ = v___y_3423_;
v___y_3411_ = v___y_3424_;
v_a_3412_ = v_a_3438_;
goto v___jp_3402_;
}
else
{
lean_object* v_a_3439_; 
lean_dec(v___y_3424_);
lean_dec(v___y_3418_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3439_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3439_);
lean_dec_ref_known(v___x_3435_, 1);
v___y_3293_ = v___x_3434_;
v___y_3294_ = v___y_3420_;
v___y_3295_ = v___y_3421_;
v___y_3296_ = v_a_3433_;
v___y_3297_ = v___y_3422_;
v___y_3298_ = v___y_3423_;
v_a_3299_ = v_a_3439_;
goto v___jp_3292_;
}
}
}
}
else
{
lean_object* v_a_3440_; 
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec(v_snd_2979_);
lean_dec(v_goals_2967_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3440_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3425_, 1);
v___y_3090_ = v___y_3421_;
v___y_3091_ = v___y_3422_;
v_a_3092_ = v_a_3440_;
goto v___jp_3089_;
}
}
v___jp_3441_:
{
if (v___y_3447_ == 0)
{
uint8_t v___x_3448_; 
v___x_3448_ = l_List_isEmpty___redArg(v___y_3446_);
lean_dec(v___y_3446_);
if (v___x_3448_ == 0)
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v___x_3449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3450_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3449_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_3139_ = v___y_3444_;
v___y_3140_ = v___y_3445_;
v___y_3141_ = v___x_3450_;
goto v___jp_3138_;
}
else
{
lean_object* v___x_3451_; 
lean_inc(v_trace_2964_);
v___x_3451_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3442_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3453_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v___x_3453_ = l_List_appendTR___redArg(v___y_3443_, v_a_3452_);
v___y_3095_ = v___y_3444_;
v___y_3096_ = v___y_3445_;
v_a_3097_ = v___x_3453_;
goto v___jp_3094_;
}
else
{
lean_dec(v___y_3443_);
v___y_3139_ = v___y_3444_;
v___y_3140_ = v___y_3445_;
v___y_3141_ = v___x_3451_;
goto v___jp_3138_;
}
}
}
else
{
v___y_3126_ = v___y_3442_;
v___y_3127_ = v___y_3443_;
v___y_3128_ = v___y_3444_;
v___y_3129_ = v___y_3445_;
v___y_3130_ = v___y_3446_;
goto v___jp_3125_;
}
}
v___jp_3454_:
{
uint8_t v_commitIndependentGoals_3460_; lean_object* v___x_3461_; 
v_commitIndependentGoals_3460_ = lean_ctor_get_uint8(v_cfg_2963_, sizeof(void*)*4);
lean_inc(v___y_3455_);
v___x_3461_ = l_List_appendTR___redArg(v_a_3459_, v___y_3455_);
if (v_commitIndependentGoals_3460_ == 0)
{
v___y_3442_ = v___x_3461_;
v___y_3443_ = v___y_3455_;
v___y_3444_ = v___y_3456_;
v___y_3445_ = v___y_3457_;
v___y_3446_ = v___y_3458_;
v___y_3447_ = v___x_2983_;
goto v___jp_3441_;
}
else
{
uint8_t v___x_3462_; 
v___x_3462_ = l_List_isEmpty___redArg(v___y_3455_);
if (v___x_3462_ == 0)
{
v___y_3126_ = v___x_3461_;
v___y_3127_ = v___y_3455_;
v___y_3128_ = v___y_3456_;
v___y_3129_ = v___y_3457_;
v___y_3130_ = v___y_3458_;
goto v___jp_3125_;
}
else
{
v___y_3442_ = v___x_3461_;
v___y_3443_ = v___y_3455_;
v___y_3444_ = v___y_3456_;
v___y_3445_ = v___y_3457_;
v___y_3446_ = v___y_3458_;
v___y_3447_ = v___x_2983_;
goto v___jp_3441_;
}
}
}
v___jp_3463_:
{
lean_object* v___x_3467_; double v___x_3468_; double v___x_3469_; double v___x_3470_; double v___x_3471_; double v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3467_ = lean_io_mono_nanos_now();
v___x_3468_ = lean_float_of_nat(v___y_3464_);
v___x_3469_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3470_ = lean_float_div(v___x_3468_, v___x_3469_);
v___x_3471_ = lean_float_of_nat(v___x_3467_);
v___x_3472_ = lean_float_div(v___x_3471_, v___x_3469_);
v___x_3473_ = lean_box_float(v___x_3470_);
v___x_3474_ = lean_box_float(v___x_3472_);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3473_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3476_, 0, v_a_3466_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2964_, v_hasTrace_2986_, v___x_3071_, v_options_2985_, v___x_3074_, v___y_3465_, v___f_3070_, v___x_3476_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
return v___x_3477_;
}
v___jp_3478_:
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3482_, 0, v_a_3481_);
v___y_3464_ = v___y_3479_;
v___y_3465_ = v___y_3480_;
v_a_3466_ = v___x_3482_;
goto v___jp_3463_;
}
v___jp_3483_:
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3487_, 0, v_a_3486_);
v___y_3464_ = v___y_3484_;
v___y_3465_ = v___y_3485_;
v_a_3466_ = v___x_3487_;
goto v___jp_3463_;
}
v___jp_3488_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = l_List_appendTR___redArg(v___y_3492_, v___y_3490_);
v___x_3495_ = l_List_appendTR___redArg(v___x_3494_, v_a_3493_);
v___y_3484_ = v___y_3489_;
v___y_3485_ = v___y_3491_;
v_a_3486_ = v___x_3495_;
goto v___jp_3483_;
}
v___jp_3496_:
{
if (lean_obj_tag(v___y_3501_) == 0)
{
lean_object* v_a_3502_; 
v_a_3502_ = lean_ctor_get(v___y_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___y_3501_, 1);
v___y_3489_ = v___y_3497_;
v___y_3490_ = v___y_3498_;
v___y_3491_ = v___y_3499_;
v___y_3492_ = v___y_3500_;
v_a_3493_ = v_a_3502_;
goto v___jp_3488_;
}
else
{
lean_object* v_a_3503_; 
lean_dec(v___y_3500_);
lean_dec(v___y_3498_);
v_a_3503_ = lean_ctor_get(v___y_3501_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___y_3501_, 1);
v___y_3479_ = v___y_3497_;
v___y_3480_ = v___y_3499_;
v_a_3481_ = v_a_3503_;
goto v___jp_3478_;
}
}
v___jp_3504_:
{
if (v___y_3511_ == 0)
{
lean_object* v___x_3512_; 
lean_dec_ref(v___y_3508_);
v___x_3512_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3507_, v_a_2970_, v_a_2972_);
lean_dec_ref(v___y_3507_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_dec_ref_known(v___x_3512_, 1);
v___y_3489_ = v___y_3505_;
v___y_3490_ = v___y_3506_;
v___y_3491_ = v___y_3509_;
v___y_3492_ = v___y_3510_;
v_a_3493_ = v_snd_2979_;
goto v___jp_3488_;
}
else
{
lean_object* v_a_3513_; 
lean_dec(v___y_3510_);
lean_dec(v___y_3506_);
lean_dec(v_snd_2979_);
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v___y_3479_ = v___y_3505_;
v___y_3480_ = v___y_3509_;
v_a_3481_ = v_a_3513_;
goto v___jp_3478_;
}
}
else
{
lean_dec_ref(v___y_3507_);
lean_dec(v_snd_2979_);
v___y_3497_ = v___y_3505_;
v___y_3498_ = v___y_3506_;
v___y_3499_ = v___y_3509_;
v___y_3500_ = v___y_3510_;
v___y_3501_ = v___y_3508_;
goto v___jp_3496_;
}
}
v___jp_3514_:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_Lean_Meta_saveState___redArg(v_a_2970_, v_a_2972_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
lean_inc(v_snd_2979_);
lean_inc(v_trace_2964_);
v___x_3522_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3517_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_dec(v_a_3521_);
lean_dec(v_snd_2979_);
v___y_3497_ = v___y_3515_;
v___y_3498_ = v___y_3516_;
v___y_3499_ = v___y_3518_;
v___y_3500_ = v___y_3519_;
v___y_3501_ = v___x_3522_;
goto v___jp_3496_;
}
else
{
lean_object* v_a_3523_; uint8_t v___x_3524_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
v___x_3524_ = l_Lean_Exception_isInterrupt(v_a_3523_);
if (v___x_3524_ == 0)
{
uint8_t v___x_3525_; 
v___x_3525_ = l_Lean_Exception_isRuntime(v_a_3523_);
v___y_3505_ = v___y_3515_;
v___y_3506_ = v___y_3516_;
v___y_3507_ = v_a_3521_;
v___y_3508_ = v___x_3522_;
v___y_3509_ = v___y_3518_;
v___y_3510_ = v___y_3519_;
v___y_3511_ = v___x_3525_;
goto v___jp_3504_;
}
else
{
lean_dec(v_a_3523_);
v___y_3505_ = v___y_3515_;
v___y_3506_ = v___y_3516_;
v___y_3507_ = v_a_3521_;
v___y_3508_ = v___x_3522_;
v___y_3509_ = v___y_3518_;
v___y_3510_ = v___y_3519_;
v___y_3511_ = v___x_3524_;
goto v___jp_3504_;
}
}
}
else
{
lean_object* v_a_3526_; 
lean_dec(v___y_3519_);
lean_dec(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3526_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3526_);
lean_dec_ref_known(v___x_3520_, 1);
v___y_3479_ = v___y_3515_;
v___y_3480_ = v___y_3518_;
v_a_3481_ = v_a_3526_;
goto v___jp_3478_;
}
}
v___jp_3527_:
{
if (lean_obj_tag(v___y_3530_) == 0)
{
lean_object* v_a_3531_; 
v_a_3531_ = lean_ctor_get(v___y_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___y_3530_, 1);
v___y_3484_ = v___y_3528_;
v___y_3485_ = v___y_3529_;
v_a_3486_ = v_a_3531_;
goto v___jp_3483_;
}
else
{
lean_object* v_a_3532_; 
v_a_3532_ = lean_ctor_get(v___y_3530_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___y_3530_, 1);
v___y_3479_ = v___y_3528_;
v___y_3480_ = v___y_3529_;
v_a_3481_ = v_a_3532_;
goto v___jp_3478_;
}
}
v___jp_3533_:
{
lean_object* v___x_3541_; double v___x_3542_; double v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3541_ = lean_io_get_num_heartbeats();
v___x_3542_ = lean_float_of_nat(v___y_3538_);
v___x_3543_ = lean_float_of_nat(v___x_3541_);
v___x_3544_ = lean_box_float(v___x_3542_);
v___x_3545_ = lean_box_float(v___x_3543_);
v___x_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3544_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3547_, 0, v_a_3540_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
lean_inc(v_trace_2964_);
v___x_3548_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2964_, v_hasTrace_2986_, v___x_3071_, v_options_2985_, v___y_3537_, v___y_3535_, v___y_3536_, v___x_3547_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_3528_ = v___y_3534_;
v___y_3529_ = v___y_3539_;
v___y_3530_ = v___x_3548_;
goto v___jp_3527_;
}
v___jp_3549_:
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3557_, 0, v_a_3556_);
v___y_3534_ = v___y_3550_;
v___y_3535_ = v___y_3551_;
v___y_3536_ = v___y_3553_;
v___y_3537_ = v___y_3552_;
v___y_3538_ = v___y_3554_;
v___y_3539_ = v___y_3555_;
v_a_3540_ = v___x_3557_;
goto v___jp_3533_;
}
v___jp_3558_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = l_List_appendTR___redArg(v___y_3566_, v___y_3561_);
v___x_3569_ = l_List_appendTR___redArg(v___x_3568_, v_a_3567_);
v___y_3550_ = v___y_3559_;
v___y_3551_ = v___y_3560_;
v___y_3552_ = v___y_3563_;
v___y_3553_ = v___y_3562_;
v___y_3554_ = v___y_3564_;
v___y_3555_ = v___y_3565_;
v_a_3556_ = v___x_3569_;
goto v___jp_3549_;
}
v___jp_3570_:
{
lean_object* v___x_3578_; 
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v_a_3577_);
v___y_3534_ = v___y_3571_;
v___y_3535_ = v___y_3572_;
v___y_3536_ = v___y_3574_;
v___y_3537_ = v___y_3573_;
v___y_3538_ = v___y_3575_;
v___y_3539_ = v___y_3576_;
v_a_3540_ = v___x_3578_;
goto v___jp_3533_;
}
v___jp_3579_:
{
if (lean_obj_tag(v___y_3586_) == 0)
{
lean_object* v_a_3587_; 
v_a_3587_ = lean_ctor_get(v___y_3586_, 0);
lean_inc(v_a_3587_);
lean_dec_ref_known(v___y_3586_, 1);
v___y_3550_ = v___y_3580_;
v___y_3551_ = v___y_3581_;
v___y_3552_ = v___y_3583_;
v___y_3553_ = v___y_3582_;
v___y_3554_ = v___y_3584_;
v___y_3555_ = v___y_3585_;
v_a_3556_ = v_a_3587_;
goto v___jp_3549_;
}
else
{
lean_object* v_a_3588_; 
v_a_3588_ = lean_ctor_get(v___y_3586_, 0);
lean_inc(v_a_3588_);
lean_dec_ref_known(v___y_3586_, 1);
v___y_3571_ = v___y_3580_;
v___y_3572_ = v___y_3581_;
v___y_3573_ = v___y_3583_;
v___y_3574_ = v___y_3582_;
v___y_3575_ = v___y_3584_;
v___y_3576_ = v___y_3585_;
v_a_3577_ = v_a_3588_;
goto v___jp_3570_;
}
}
v___jp_3589_:
{
lean_object* v___x_3598_; 
lean_inc(v_trace_2964_);
v___x_3598_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3595_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3600_ = l_List_appendTR___redArg(v___y_3597_, v_a_3599_);
v___y_3550_ = v___y_3590_;
v___y_3551_ = v___y_3591_;
v___y_3552_ = v___y_3593_;
v___y_3553_ = v___y_3592_;
v___y_3554_ = v___y_3594_;
v___y_3555_ = v___y_3596_;
v_a_3556_ = v___x_3600_;
goto v___jp_3549_;
}
else
{
lean_dec(v___y_3597_);
v___y_3580_ = v___y_3590_;
v___y_3581_ = v___y_3591_;
v___y_3582_ = v___y_3592_;
v___y_3583_ = v___y_3593_;
v___y_3584_ = v___y_3594_;
v___y_3585_ = v___y_3596_;
v___y_3586_ = v___x_3598_;
goto v___jp_3579_;
}
}
v___jp_3601_:
{
if (lean_obj_tag(v___y_3610_) == 0)
{
lean_object* v_a_3611_; 
v_a_3611_ = lean_ctor_get(v___y_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___y_3610_, 1);
v___y_3559_ = v___y_3602_;
v___y_3560_ = v___y_3604_;
v___y_3561_ = v___y_3603_;
v___y_3562_ = v___y_3606_;
v___y_3563_ = v___y_3605_;
v___y_3564_ = v___y_3607_;
v___y_3565_ = v___y_3608_;
v___y_3566_ = v___y_3609_;
v_a_3567_ = v_a_3611_;
goto v___jp_3558_;
}
else
{
lean_object* v_a_3612_; 
lean_dec(v___y_3609_);
lean_dec(v___y_3603_);
v_a_3612_ = lean_ctor_get(v___y_3610_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___y_3610_, 1);
v___y_3571_ = v___y_3602_;
v___y_3572_ = v___y_3604_;
v___y_3573_ = v___y_3605_;
v___y_3574_ = v___y_3606_;
v___y_3575_ = v___y_3607_;
v___y_3576_ = v___y_3608_;
v_a_3577_ = v_a_3612_;
goto v___jp_3570_;
}
}
v___jp_3613_:
{
if (v___y_3624_ == 0)
{
lean_object* v___x_3625_; 
lean_dec_ref(v___y_3623_);
v___x_3625_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3620_, v_a_2970_, v_a_2972_);
lean_dec_ref(v___y_3620_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_dec_ref_known(v___x_3625_, 1);
v___y_3559_ = v___y_3614_;
v___y_3560_ = v___y_3616_;
v___y_3561_ = v___y_3615_;
v___y_3562_ = v___y_3618_;
v___y_3563_ = v___y_3617_;
v___y_3564_ = v___y_3619_;
v___y_3565_ = v___y_3621_;
v___y_3566_ = v___y_3622_;
v_a_3567_ = v_snd_2979_;
goto v___jp_3558_;
}
else
{
lean_object* v_a_3626_; 
lean_dec(v___y_3622_);
lean_dec(v___y_3615_);
lean_dec(v_snd_2979_);
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3625_, 1);
v___y_3571_ = v___y_3614_;
v___y_3572_ = v___y_3616_;
v___y_3573_ = v___y_3617_;
v___y_3574_ = v___y_3618_;
v___y_3575_ = v___y_3619_;
v___y_3576_ = v___y_3621_;
v_a_3577_ = v_a_3626_;
goto v___jp_3570_;
}
}
else
{
lean_dec_ref(v___y_3620_);
lean_dec(v_snd_2979_);
v___y_3602_ = v___y_3614_;
v___y_3603_ = v___y_3615_;
v___y_3604_ = v___y_3616_;
v___y_3605_ = v___y_3617_;
v___y_3606_ = v___y_3618_;
v___y_3607_ = v___y_3619_;
v___y_3608_ = v___y_3621_;
v___y_3609_ = v___y_3622_;
v___y_3610_ = v___y_3623_;
goto v___jp_3601_;
}
}
v___jp_3627_:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_Meta_saveState___redArg(v_a_2970_, v_a_2972_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3639_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
lean_inc(v_snd_2979_);
lean_inc(v_trace_2964_);
v___x_3639_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3634_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_dec(v_a_3638_);
lean_dec(v_snd_2979_);
v___y_3602_ = v___y_3628_;
v___y_3603_ = v___y_3630_;
v___y_3604_ = v___y_3629_;
v___y_3605_ = v___y_3632_;
v___y_3606_ = v___y_3631_;
v___y_3607_ = v___y_3633_;
v___y_3608_ = v___y_3635_;
v___y_3609_ = v___y_3636_;
v___y_3610_ = v___x_3639_;
goto v___jp_3601_;
}
else
{
lean_object* v_a_3640_; uint8_t v___x_3641_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
v___x_3641_ = l_Lean_Exception_isInterrupt(v_a_3640_);
if (v___x_3641_ == 0)
{
uint8_t v___x_3642_; 
v___x_3642_ = l_Lean_Exception_isRuntime(v_a_3640_);
v___y_3614_ = v___y_3628_;
v___y_3615_ = v___y_3630_;
v___y_3616_ = v___y_3629_;
v___y_3617_ = v___y_3632_;
v___y_3618_ = v___y_3631_;
v___y_3619_ = v___y_3633_;
v___y_3620_ = v_a_3638_;
v___y_3621_ = v___y_3635_;
v___y_3622_ = v___y_3636_;
v___y_3623_ = v___x_3639_;
v___y_3624_ = v___x_3642_;
goto v___jp_3613_;
}
else
{
lean_dec(v_a_3640_);
v___y_3614_ = v___y_3628_;
v___y_3615_ = v___y_3630_;
v___y_3616_ = v___y_3629_;
v___y_3617_ = v___y_3632_;
v___y_3618_ = v___y_3631_;
v___y_3619_ = v___y_3633_;
v___y_3620_ = v_a_3638_;
v___y_3621_ = v___y_3635_;
v___y_3622_ = v___y_3636_;
v___y_3623_ = v___x_3639_;
v___y_3624_ = v___x_3641_;
goto v___jp_3613_;
}
}
}
else
{
lean_object* v_a_3643_; 
lean_dec(v___y_3636_);
lean_dec(v___y_3634_);
lean_dec(v___y_3630_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3643_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3643_);
lean_dec_ref_known(v___x_3637_, 1);
v___y_3571_ = v___y_3628_;
v___y_3572_ = v___y_3629_;
v___y_3573_ = v___y_3632_;
v___y_3574_ = v___y_3631_;
v___y_3575_ = v___y_3633_;
v___y_3576_ = v___y_3635_;
v_a_3577_ = v_a_3643_;
goto v___jp_3570_;
}
}
v___jp_3644_:
{
if (v___y_3655_ == 0)
{
uint8_t v___x_3656_; 
v___x_3656_ = l_List_isEmpty___redArg(v___y_3647_);
lean_dec(v___y_3647_);
if (v___x_3656_ == 0)
{
if (v___y_3651_ == 0)
{
v___y_3590_ = v___y_3645_;
v___y_3591_ = v___y_3646_;
v___y_3592_ = v___y_3649_;
v___y_3593_ = v___y_3648_;
v___y_3594_ = v___y_3650_;
v___y_3595_ = v___y_3652_;
v___y_3596_ = v___y_3653_;
v___y_3597_ = v___y_3654_;
goto v___jp_3589_;
}
else
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
lean_dec(v___y_3654_);
lean_dec(v___y_3652_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v___x_3657_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3658_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3657_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_3580_ = v___y_3645_;
v___y_3581_ = v___y_3646_;
v___y_3582_ = v___y_3649_;
v___y_3583_ = v___y_3648_;
v___y_3584_ = v___y_3650_;
v___y_3585_ = v___y_3653_;
v___y_3586_ = v___x_3658_;
goto v___jp_3579_;
}
}
else
{
v___y_3590_ = v___y_3645_;
v___y_3591_ = v___y_3646_;
v___y_3592_ = v___y_3649_;
v___y_3593_ = v___y_3648_;
v___y_3594_ = v___y_3650_;
v___y_3595_ = v___y_3652_;
v___y_3596_ = v___y_3653_;
v___y_3597_ = v___y_3654_;
goto v___jp_3589_;
}
}
else
{
v___y_3628_ = v___y_3645_;
v___y_3629_ = v___y_3646_;
v___y_3630_ = v___y_3647_;
v___y_3631_ = v___y_3649_;
v___y_3632_ = v___y_3648_;
v___y_3633_ = v___y_3650_;
v___y_3634_ = v___y_3652_;
v___y_3635_ = v___y_3653_;
v___y_3636_ = v___y_3654_;
goto v___jp_3627_;
}
}
v___jp_3659_:
{
uint8_t v_commitIndependentGoals_3670_; lean_object* v___x_3671_; 
v_commitIndependentGoals_3670_ = lean_ctor_get_uint8(v_cfg_2963_, sizeof(void*)*4);
lean_inc(v___y_3668_);
v___x_3671_ = l_List_appendTR___redArg(v_a_3669_, v___y_3668_);
if (v_commitIndependentGoals_3670_ == 0)
{
v___y_3645_ = v___y_3660_;
v___y_3646_ = v___y_3662_;
v___y_3647_ = v___y_3661_;
v___y_3648_ = v___y_3663_;
v___y_3649_ = v___y_3664_;
v___y_3650_ = v___y_3666_;
v___y_3651_ = v___y_3665_;
v___y_3652_ = v___x_3671_;
v___y_3653_ = v___y_3667_;
v___y_3654_ = v___y_3668_;
v___y_3655_ = v___x_2983_;
goto v___jp_3644_;
}
else
{
uint8_t v___x_3672_; 
v___x_3672_ = l_List_isEmpty___redArg(v___y_3668_);
if (v___x_3672_ == 0)
{
v___y_3628_ = v___y_3660_;
v___y_3629_ = v___y_3662_;
v___y_3630_ = v___y_3661_;
v___y_3631_ = v___y_3664_;
v___y_3632_ = v___y_3663_;
v___y_3633_ = v___y_3666_;
v___y_3634_ = v___x_3671_;
v___y_3635_ = v___y_3667_;
v___y_3636_ = v___y_3668_;
goto v___jp_3627_;
}
else
{
v___y_3645_ = v___y_3660_;
v___y_3646_ = v___y_3662_;
v___y_3647_ = v___y_3661_;
v___y_3648_ = v___y_3663_;
v___y_3649_ = v___y_3664_;
v___y_3650_ = v___y_3666_;
v___y_3651_ = v___y_3665_;
v___y_3652_ = v___x_3671_;
v___y_3653_ = v___y_3667_;
v___y_3654_ = v___y_3668_;
v___y_3655_ = v___x_2983_;
goto v___jp_3644_;
}
}
}
v___jp_3673_:
{
lean_object* v___x_3681_; double v___x_3682_; double v___x_3683_; double v___x_3684_; double v___x_3685_; double v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3681_ = lean_io_mono_nanos_now();
v___x_3682_ = lean_float_of_nat(v___y_3678_);
v___x_3683_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3684_ = lean_float_div(v___x_3682_, v___x_3683_);
v___x_3685_ = lean_float_of_nat(v___x_3681_);
v___x_3686_ = lean_float_div(v___x_3685_, v___x_3683_);
v___x_3687_ = lean_box_float(v___x_3684_);
v___x_3688_ = lean_box_float(v___x_3686_);
v___x_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3687_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v_a_3680_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
lean_inc(v_trace_2964_);
v___x_3691_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2964_, v_hasTrace_2986_, v___x_3071_, v_options_2985_, v___y_3677_, v___y_3675_, v___y_3676_, v___x_3690_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_3528_ = v___y_3674_;
v___y_3529_ = v___y_3679_;
v___y_3530_ = v___x_3691_;
goto v___jp_3527_;
}
v___jp_3692_:
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3700_, 0, v_a_3699_);
v___y_3674_ = v___y_3693_;
v___y_3675_ = v___y_3694_;
v___y_3676_ = v___y_3696_;
v___y_3677_ = v___y_3695_;
v___y_3678_ = v___y_3697_;
v___y_3679_ = v___y_3698_;
v_a_3680_ = v___x_3700_;
goto v___jp_3673_;
}
v___jp_3701_:
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3709_, 0, v_a_3708_);
v___y_3674_ = v___y_3702_;
v___y_3675_ = v___y_3703_;
v___y_3676_ = v___y_3705_;
v___y_3677_ = v___y_3704_;
v___y_3678_ = v___y_3706_;
v___y_3679_ = v___y_3707_;
v_a_3680_ = v___x_3709_;
goto v___jp_3673_;
}
v___jp_3710_:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = l_List_appendTR___redArg(v___y_3718_, v___y_3713_);
v___x_3721_ = l_List_appendTR___redArg(v___x_3720_, v_a_3719_);
v___y_3702_ = v___y_3711_;
v___y_3703_ = v___y_3712_;
v___y_3704_ = v___y_3715_;
v___y_3705_ = v___y_3714_;
v___y_3706_ = v___y_3716_;
v___y_3707_ = v___y_3717_;
v_a_3708_ = v___x_3721_;
goto v___jp_3701_;
}
v___jp_3722_:
{
if (lean_obj_tag(v___y_3731_) == 0)
{
lean_object* v_a_3732_; 
v_a_3732_ = lean_ctor_get(v___y_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___y_3731_, 1);
v___y_3711_ = v___y_3723_;
v___y_3712_ = v___y_3725_;
v___y_3713_ = v___y_3724_;
v___y_3714_ = v___y_3727_;
v___y_3715_ = v___y_3726_;
v___y_3716_ = v___y_3728_;
v___y_3717_ = v___y_3729_;
v___y_3718_ = v___y_3730_;
v_a_3719_ = v_a_3732_;
goto v___jp_3710_;
}
else
{
lean_object* v_a_3733_; 
lean_dec(v___y_3730_);
lean_dec(v___y_3724_);
v_a_3733_ = lean_ctor_get(v___y_3731_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v___y_3731_, 1);
v___y_3693_ = v___y_3723_;
v___y_3694_ = v___y_3725_;
v___y_3695_ = v___y_3726_;
v___y_3696_ = v___y_3727_;
v___y_3697_ = v___y_3728_;
v___y_3698_ = v___y_3729_;
v_a_3699_ = v_a_3733_;
goto v___jp_3692_;
}
}
v___jp_3734_:
{
if (v___y_3745_ == 0)
{
lean_object* v___x_3746_; 
lean_dec_ref(v___y_3743_);
v___x_3746_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3740_, v_a_2970_, v_a_2972_);
lean_dec_ref(v___y_3740_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_dec_ref_known(v___x_3746_, 1);
v___y_3711_ = v___y_3735_;
v___y_3712_ = v___y_3737_;
v___y_3713_ = v___y_3736_;
v___y_3714_ = v___y_3739_;
v___y_3715_ = v___y_3738_;
v___y_3716_ = v___y_3741_;
v___y_3717_ = v___y_3742_;
v___y_3718_ = v___y_3744_;
v_a_3719_ = v_snd_2979_;
goto v___jp_3710_;
}
else
{
lean_object* v_a_3747_; 
lean_dec(v___y_3744_);
lean_dec(v___y_3736_);
lean_dec(v_snd_2979_);
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3746_, 1);
v___y_3693_ = v___y_3735_;
v___y_3694_ = v___y_3737_;
v___y_3695_ = v___y_3738_;
v___y_3696_ = v___y_3739_;
v___y_3697_ = v___y_3741_;
v___y_3698_ = v___y_3742_;
v_a_3699_ = v_a_3747_;
goto v___jp_3692_;
}
}
else
{
lean_dec_ref(v___y_3740_);
lean_dec(v_snd_2979_);
v___y_3723_ = v___y_3735_;
v___y_3724_ = v___y_3736_;
v___y_3725_ = v___y_3737_;
v___y_3726_ = v___y_3738_;
v___y_3727_ = v___y_3739_;
v___y_3728_ = v___y_3741_;
v___y_3729_ = v___y_3742_;
v___y_3730_ = v___y_3744_;
v___y_3731_ = v___y_3743_;
goto v___jp_3722_;
}
}
v___jp_3748_:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_Meta_saveState___redArg(v_a_2970_, v_a_2972_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v___x_3760_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref_known(v___x_3758_, 1);
lean_inc(v_snd_2979_);
lean_inc(v_trace_2964_);
v___x_3760_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3755_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_dec(v_a_3759_);
lean_dec(v_snd_2979_);
v___y_3723_ = v___y_3749_;
v___y_3724_ = v___y_3751_;
v___y_3725_ = v___y_3750_;
v___y_3726_ = v___y_3753_;
v___y_3727_ = v___y_3752_;
v___y_3728_ = v___y_3754_;
v___y_3729_ = v___y_3756_;
v___y_3730_ = v___y_3757_;
v___y_3731_ = v___x_3760_;
goto v___jp_3722_;
}
else
{
lean_object* v_a_3761_; uint8_t v___x_3762_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3761_);
v___x_3762_ = l_Lean_Exception_isInterrupt(v_a_3761_);
if (v___x_3762_ == 0)
{
uint8_t v___x_3763_; 
v___x_3763_ = l_Lean_Exception_isRuntime(v_a_3761_);
v___y_3735_ = v___y_3749_;
v___y_3736_ = v___y_3751_;
v___y_3737_ = v___y_3750_;
v___y_3738_ = v___y_3753_;
v___y_3739_ = v___y_3752_;
v___y_3740_ = v_a_3759_;
v___y_3741_ = v___y_3754_;
v___y_3742_ = v___y_3756_;
v___y_3743_ = v___x_3760_;
v___y_3744_ = v___y_3757_;
v___y_3745_ = v___x_3763_;
goto v___jp_3734_;
}
else
{
lean_dec(v_a_3761_);
v___y_3735_ = v___y_3749_;
v___y_3736_ = v___y_3751_;
v___y_3737_ = v___y_3750_;
v___y_3738_ = v___y_3753_;
v___y_3739_ = v___y_3752_;
v___y_3740_ = v_a_3759_;
v___y_3741_ = v___y_3754_;
v___y_3742_ = v___y_3756_;
v___y_3743_ = v___x_3760_;
v___y_3744_ = v___y_3757_;
v___y_3745_ = v___x_3762_;
goto v___jp_3734_;
}
}
}
else
{
lean_object* v_a_3764_; 
lean_dec(v___y_3757_);
lean_dec(v___y_3755_);
lean_dec(v___y_3751_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3764_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3758_, 1);
v___y_3693_ = v___y_3749_;
v___y_3694_ = v___y_3750_;
v___y_3695_ = v___y_3753_;
v___y_3696_ = v___y_3752_;
v___y_3697_ = v___y_3754_;
v___y_3698_ = v___y_3756_;
v_a_3699_ = v_a_3764_;
goto v___jp_3692_;
}
}
v___jp_3765_:
{
if (lean_obj_tag(v___y_3772_) == 0)
{
lean_object* v_a_3773_; 
v_a_3773_ = lean_ctor_get(v___y_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref_known(v___y_3772_, 1);
v___y_3702_ = v___y_3766_;
v___y_3703_ = v___y_3767_;
v___y_3704_ = v___y_3769_;
v___y_3705_ = v___y_3768_;
v___y_3706_ = v___y_3770_;
v___y_3707_ = v___y_3771_;
v_a_3708_ = v_a_3773_;
goto v___jp_3701_;
}
else
{
lean_object* v_a_3774_; 
v_a_3774_ = lean_ctor_get(v___y_3772_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___y_3772_, 1);
v___y_3693_ = v___y_3766_;
v___y_3694_ = v___y_3767_;
v___y_3695_ = v___y_3769_;
v___y_3696_ = v___y_3768_;
v___y_3697_ = v___y_3770_;
v___y_3698_ = v___y_3771_;
v_a_3699_ = v_a_3774_;
goto v___jp_3692_;
}
}
v___jp_3775_:
{
if (v___y_3785_ == 0)
{
uint8_t v___x_3786_; 
v___x_3786_ = l_List_isEmpty___redArg(v___y_3778_);
lean_dec(v___y_3778_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
lean_dec(v___y_3784_);
lean_dec(v___y_3782_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v___x_3787_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3788_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3787_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_3766_ = v___y_3776_;
v___y_3767_ = v___y_3777_;
v___y_3768_ = v___y_3780_;
v___y_3769_ = v___y_3779_;
v___y_3770_ = v___y_3781_;
v___y_3771_ = v___y_3783_;
v___y_3772_ = v___x_3788_;
goto v___jp_3765_;
}
else
{
lean_object* v___x_3789_; 
lean_inc(v_trace_2964_);
v___x_3789_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3782_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3791_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3789_, 1);
v___x_3791_ = l_List_appendTR___redArg(v___y_3784_, v_a_3790_);
v___y_3702_ = v___y_3776_;
v___y_3703_ = v___y_3777_;
v___y_3704_ = v___y_3779_;
v___y_3705_ = v___y_3780_;
v___y_3706_ = v___y_3781_;
v___y_3707_ = v___y_3783_;
v_a_3708_ = v___x_3791_;
goto v___jp_3701_;
}
else
{
lean_dec(v___y_3784_);
v___y_3766_ = v___y_3776_;
v___y_3767_ = v___y_3777_;
v___y_3768_ = v___y_3780_;
v___y_3769_ = v___y_3779_;
v___y_3770_ = v___y_3781_;
v___y_3771_ = v___y_3783_;
v___y_3772_ = v___x_3789_;
goto v___jp_3765_;
}
}
}
else
{
v___y_3749_ = v___y_3776_;
v___y_3750_ = v___y_3777_;
v___y_3751_ = v___y_3778_;
v___y_3752_ = v___y_3780_;
v___y_3753_ = v___y_3779_;
v___y_3754_ = v___y_3781_;
v___y_3755_ = v___y_3782_;
v___y_3756_ = v___y_3783_;
v___y_3757_ = v___y_3784_;
goto v___jp_3748_;
}
}
v___jp_3792_:
{
uint8_t v_commitIndependentGoals_3802_; lean_object* v___x_3803_; 
v_commitIndependentGoals_3802_ = lean_ctor_get_uint8(v_cfg_2963_, sizeof(void*)*4);
lean_inc(v___y_3800_);
v___x_3803_ = l_List_appendTR___redArg(v_a_3801_, v___y_3800_);
if (v_commitIndependentGoals_3802_ == 0)
{
v___y_3776_ = v___y_3793_;
v___y_3777_ = v___y_3795_;
v___y_3778_ = v___y_3794_;
v___y_3779_ = v___y_3796_;
v___y_3780_ = v___y_3797_;
v___y_3781_ = v___y_3798_;
v___y_3782_ = v___x_3803_;
v___y_3783_ = v___y_3799_;
v___y_3784_ = v___y_3800_;
v___y_3785_ = v___x_2983_;
goto v___jp_3775_;
}
else
{
uint8_t v___x_3804_; 
v___x_3804_ = l_List_isEmpty___redArg(v___y_3800_);
if (v___x_3804_ == 0)
{
v___y_3749_ = v___y_3793_;
v___y_3750_ = v___y_3795_;
v___y_3751_ = v___y_3794_;
v___y_3752_ = v___y_3797_;
v___y_3753_ = v___y_3796_;
v___y_3754_ = v___y_3798_;
v___y_3755_ = v___x_3803_;
v___y_3756_ = v___y_3799_;
v___y_3757_ = v___y_3800_;
goto v___jp_3748_;
}
else
{
v___y_3776_ = v___y_3793_;
v___y_3777_ = v___y_3795_;
v___y_3778_ = v___y_3794_;
v___y_3779_ = v___y_3796_;
v___y_3780_ = v___y_3797_;
v___y_3781_ = v___y_3798_;
v___y_3782_ = v___x_3803_;
v___y_3783_ = v___y_3799_;
v___y_3784_ = v___y_3800_;
v___y_3785_ = v___x_2983_;
goto v___jp_3775_;
}
}
}
v___jp_3805_:
{
lean_object* v___x_3814_; 
v___x_3814_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2972_);
if (lean_obj_tag(v___x_3814_) == 0)
{
if (v___y_3810_ == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v___x_3814_, 1);
v___x_3816_ = lean_io_mono_nanos_now();
v___x_3817_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2986_, v___x_2983_, v_goals_2967_, v___y_3813_, v_a_2970_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3819_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3817_, 1);
v___x_3819_ = l_List_reverse___redArg(v_a_3818_);
v___y_3793_ = v___y_3806_;
v___y_3794_ = v___y_3807_;
v___y_3795_ = v_a_3815_;
v___y_3796_ = v___y_3808_;
v___y_3797_ = v___y_3809_;
v___y_3798_ = v___x_3816_;
v___y_3799_ = v___y_3811_;
v___y_3800_ = v___y_3812_;
v_a_3801_ = v___x_3819_;
goto v___jp_3792_;
}
else
{
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3820_; 
v_a_3820_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3817_, 1);
v___y_3793_ = v___y_3806_;
v___y_3794_ = v___y_3807_;
v___y_3795_ = v_a_3815_;
v___y_3796_ = v___y_3808_;
v___y_3797_ = v___y_3809_;
v___y_3798_ = v___x_3816_;
v___y_3799_ = v___y_3811_;
v___y_3800_ = v___y_3812_;
v_a_3801_ = v_a_3820_;
goto v___jp_3792_;
}
else
{
lean_object* v_a_3821_; 
lean_dec(v___y_3812_);
lean_dec(v___y_3807_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3821_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3817_, 1);
v___y_3693_ = v___y_3806_;
v___y_3694_ = v_a_3815_;
v___y_3695_ = v___y_3808_;
v___y_3696_ = v___y_3809_;
v___y_3697_ = v___x_3816_;
v___y_3698_ = v___y_3811_;
v_a_3699_ = v_a_3821_;
goto v___jp_3692_;
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v_a_3822_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3814_, 1);
v___x_3823_ = lean_io_get_num_heartbeats();
v___x_3824_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2986_, v___x_2983_, v_goals_2967_, v___y_3813_, v_a_2970_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3826_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v___x_3826_ = l_List_reverse___redArg(v_a_3825_);
v___y_3660_ = v___y_3806_;
v___y_3661_ = v___y_3807_;
v___y_3662_ = v_a_3822_;
v___y_3663_ = v___y_3808_;
v___y_3664_ = v___y_3809_;
v___y_3665_ = v___y_3810_;
v___y_3666_ = v___x_3823_;
v___y_3667_ = v___y_3811_;
v___y_3668_ = v___y_3812_;
v_a_3669_ = v___x_3826_;
goto v___jp_3659_;
}
else
{
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3827_; 
v_a_3827_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3824_, 1);
v___y_3660_ = v___y_3806_;
v___y_3661_ = v___y_3807_;
v___y_3662_ = v_a_3822_;
v___y_3663_ = v___y_3808_;
v___y_3664_ = v___y_3809_;
v___y_3665_ = v___y_3810_;
v___y_3666_ = v___x_3823_;
v___y_3667_ = v___y_3811_;
v___y_3668_ = v___y_3812_;
v_a_3669_ = v_a_3827_;
goto v___jp_3659_;
}
else
{
lean_object* v_a_3828_; 
lean_dec(v___y_3812_);
lean_dec(v___y_3807_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3828_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3828_);
lean_dec_ref_known(v___x_3824_, 1);
v___y_3571_ = v___y_3806_;
v___y_3572_ = v_a_3822_;
v___y_3573_ = v___y_3808_;
v___y_3574_ = v___y_3809_;
v___y_3575_ = v___x_3823_;
v___y_3576_ = v___y_3811_;
v_a_3577_ = v_a_3828_;
goto v___jp_3570_;
}
}
}
}
else
{
lean_object* v_a_3829_; 
lean_dec(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3807_);
lean_dec(v_snd_2979_);
lean_dec(v_goals_2967_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3829_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___x_3814_, 1);
v___y_3479_ = v___y_3806_;
v___y_3480_ = v___y_3811_;
v_a_3481_ = v_a_3829_;
goto v___jp_3478_;
}
}
v___jp_3830_:
{
if (v___y_3836_ == 0)
{
uint8_t v___x_3837_; 
v___x_3837_ = l_List_isEmpty___redArg(v___y_3832_);
lean_dec(v___y_3832_);
if (v___x_3837_ == 0)
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
lean_dec(v___y_3835_);
lean_dec(v___y_3833_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v___x_3838_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3839_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3838_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
v___y_3528_ = v___y_3831_;
v___y_3529_ = v___y_3834_;
v___y_3530_ = v___x_3839_;
goto v___jp_3527_;
}
else
{
lean_object* v___x_3840_; 
lean_inc(v_trace_2964_);
v___x_3840_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v___y_3833_, v_snd_2979_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3842_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
v___x_3842_ = l_List_appendTR___redArg(v___y_3835_, v_a_3841_);
v___y_3484_ = v___y_3831_;
v___y_3485_ = v___y_3834_;
v_a_3486_ = v___x_3842_;
goto v___jp_3483_;
}
else
{
lean_dec(v___y_3835_);
v___y_3528_ = v___y_3831_;
v___y_3529_ = v___y_3834_;
v___y_3530_ = v___x_3840_;
goto v___jp_3527_;
}
}
}
else
{
v___y_3515_ = v___y_3831_;
v___y_3516_ = v___y_3832_;
v___y_3517_ = v___y_3833_;
v___y_3518_ = v___y_3834_;
v___y_3519_ = v___y_3835_;
goto v___jp_3514_;
}
}
v___jp_3843_:
{
uint8_t v_commitIndependentGoals_3849_; lean_object* v___x_3850_; 
v_commitIndependentGoals_3849_ = lean_ctor_get_uint8(v_cfg_2963_, sizeof(void*)*4);
lean_inc(v___y_3847_);
v___x_3850_ = l_List_appendTR___redArg(v_a_3848_, v___y_3847_);
if (v_commitIndependentGoals_3849_ == 0)
{
v___y_3831_ = v___y_3844_;
v___y_3832_ = v___y_3845_;
v___y_3833_ = v___x_3850_;
v___y_3834_ = v___y_3846_;
v___y_3835_ = v___y_3847_;
v___y_3836_ = v___x_2983_;
goto v___jp_3830_;
}
else
{
uint8_t v___x_3851_; 
v___x_3851_ = l_List_isEmpty___redArg(v___y_3847_);
if (v___x_3851_ == 0)
{
v___y_3515_ = v___y_3844_;
v___y_3516_ = v___y_3845_;
v___y_3517_ = v___x_3850_;
v___y_3518_ = v___y_3846_;
v___y_3519_ = v___y_3847_;
goto v___jp_3514_;
}
else
{
v___y_3831_ = v___y_3844_;
v___y_3832_ = v___y_3845_;
v___y_3833_ = v___x_3850_;
v___y_3834_ = v___y_3846_;
v___y_3835_ = v___y_3847_;
v___y_3836_ = v___x_2983_;
goto v___jp_3830_;
}
}
}
v___jp_3852_:
{
lean_object* v___x_3853_; 
v___x_3853_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2972_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3853_, 1);
v___x_3855_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3856_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2985_, v___x_3855_);
if (v___x_3856_ == 0)
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
lean_del_object(v___x_2981_);
v___x_3857_ = lean_io_mono_nanos_now();
v___x_3858_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2978_, v___f_2974_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; lean_object* v_fst_3860_; lean_object* v_snd_3861_; lean_object* v___x_3862_; lean_object* v___f_3863_; lean_object* v___x_3864_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v___x_3858_, 1);
v_fst_3860_ = lean_ctor_get(v_a_3859_, 0);
lean_inc_n(v_fst_3860_, 2);
v_snd_3861_ = lean_ctor_get(v_a_3859_, 1);
lean_inc(v_snd_3861_);
lean_dec(v_a_3859_);
v___x_3862_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3861_, v___x_2975_);
lean_inc(v___x_3862_);
v___f_3863_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3863_, 0, v_fst_3860_);
lean_closure_set(v___f_3863_, 1, v___x_3862_);
v___x_3864_ = lean_box(0);
if (v___x_3074_ == 0)
{
lean_object* v___x_3865_; uint8_t v___x_3866_; 
v___x_3865_ = l_Lean_trace_profiler;
v___x_3866_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2985_, v___x_3865_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; 
lean_dec_ref(v___f_3863_);
v___x_3867_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2986_, v___x_2983_, v_goals_2967_, v___x_3864_, v_a_2970_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3869_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___x_3867_, 1);
v___x_3869_ = l_List_reverse___redArg(v_a_3868_);
v___y_3844_ = v___x_3857_;
v___y_3845_ = v_fst_3860_;
v___y_3846_ = v_a_3854_;
v___y_3847_ = v___x_3862_;
v_a_3848_ = v___x_3869_;
goto v___jp_3843_;
}
else
{
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3870_; 
v_a_3870_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3867_, 1);
v___y_3844_ = v___x_3857_;
v___y_3845_ = v_fst_3860_;
v___y_3846_ = v_a_3854_;
v___y_3847_ = v___x_3862_;
v_a_3848_ = v_a_3870_;
goto v___jp_3843_;
}
else
{
lean_object* v_a_3871_; 
lean_dec(v___x_3862_);
lean_dec(v_fst_3860_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3871_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3867_, 1);
v___y_3479_ = v___x_3857_;
v___y_3480_ = v_a_3854_;
v_a_3481_ = v_a_3871_;
goto v___jp_3478_;
}
}
}
else
{
v___y_3806_ = v___x_3857_;
v___y_3807_ = v_fst_3860_;
v___y_3808_ = v___x_3074_;
v___y_3809_ = v___f_3863_;
v___y_3810_ = v___x_3856_;
v___y_3811_ = v_a_3854_;
v___y_3812_ = v___x_3862_;
v___y_3813_ = v___x_3864_;
goto v___jp_3805_;
}
}
else
{
v___y_3806_ = v___x_3857_;
v___y_3807_ = v_fst_3860_;
v___y_3808_ = v___x_3074_;
v___y_3809_ = v___f_3863_;
v___y_3810_ = v___x_3856_;
v___y_3811_ = v_a_3854_;
v___y_3812_ = v___x_3862_;
v___y_3813_ = v___x_3864_;
goto v___jp_3805_;
}
}
else
{
lean_object* v_a_3872_; 
lean_dec(v_snd_2979_);
lean_dec(v_goals_2967_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3872_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3858_, 1);
v___y_3479_ = v___x_3857_;
v___y_3480_ = v_a_3854_;
v_a_3481_ = v_a_3872_;
goto v___jp_3478_;
}
}
else
{
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = lean_io_get_num_heartbeats();
v___x_3874_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2978_, v___f_2974_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v_fst_3876_; lean_object* v_snd_3877_; lean_object* v___x_3878_; lean_object* v___f_3879_; lean_object* v___x_3880_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3874_, 1);
v_fst_3876_ = lean_ctor_get(v_a_3875_, 0);
lean_inc_n(v_fst_3876_, 2);
v_snd_3877_ = lean_ctor_get(v_a_3875_, 1);
lean_inc(v_snd_3877_);
lean_dec(v_a_3875_);
v___x_3878_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3877_, v___x_2975_);
lean_inc(v___x_3878_);
v___f_3879_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3879_, 0, v_fst_3876_);
lean_closure_set(v___f_3879_, 1, v___x_3878_);
v___x_3880_ = lean_box(0);
if (v___x_3074_ == 0)
{
lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3881_ = l_Lean_trace_profiler;
v___x_3882_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2985_, v___x_3881_);
if (v___x_3882_ == 0)
{
lean_object* v___x_3883_; 
lean_dec_ref(v___f_3879_);
v___x_3883_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3856_, v___x_2983_, v_goals_2967_, v___x_3880_, v_a_2970_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3885_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
v___x_3885_ = l_List_reverse___redArg(v_a_3884_);
v___y_3455_ = v___x_3878_;
v___y_3456_ = v_a_3854_;
v___y_3457_ = v___x_3873_;
v___y_3458_ = v_fst_3876_;
v_a_3459_ = v___x_3885_;
goto v___jp_3454_;
}
else
{
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3886_; 
v_a_3886_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3883_, 1);
v___y_3455_ = v___x_3878_;
v___y_3456_ = v_a_3854_;
v___y_3457_ = v___x_3873_;
v___y_3458_ = v_fst_3876_;
v_a_3459_ = v_a_3886_;
goto v___jp_3454_;
}
else
{
lean_object* v_a_3887_; 
lean_dec(v___x_3878_);
lean_dec(v_fst_3876_);
lean_dec(v_snd_2979_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3887_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3883_, 1);
v___y_3090_ = v_a_3854_;
v___y_3091_ = v___x_3873_;
v_a_3092_ = v_a_3887_;
goto v___jp_3089_;
}
}
}
else
{
v___y_3417_ = v___x_3880_;
v___y_3418_ = v___x_3878_;
v___y_3419_ = v___x_3856_;
v___y_3420_ = v___x_3074_;
v___y_3421_ = v_a_3854_;
v___y_3422_ = v___x_3873_;
v___y_3423_ = v___f_3879_;
v___y_3424_ = v_fst_3876_;
goto v___jp_3416_;
}
}
else
{
v___y_3417_ = v___x_3880_;
v___y_3418_ = v___x_3878_;
v___y_3419_ = v___x_3856_;
v___y_3420_ = v___x_3074_;
v___y_3421_ = v_a_3854_;
v___y_3422_ = v___x_3873_;
v___y_3423_ = v___f_3879_;
v___y_3424_ = v_fst_3876_;
goto v___jp_3416_;
}
}
else
{
lean_object* v_a_3888_; 
lean_dec(v_snd_2979_);
lean_dec(v_goals_2967_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec_ref(v_cfg_2963_);
v_a_3888_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3874_, 1);
v___y_3090_ = v_a_3854_;
v___y_3091_ = v___x_3873_;
v_a_3092_ = v_a_3888_;
goto v___jp_3089_;
}
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec_ref(v___f_3070_);
lean_del_object(v___x_2981_);
lean_dec(v_snd_2979_);
lean_dec(v_fst_2978_);
lean_dec_ref(v___f_2974_);
lean_dec(v_goals_2967_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec(v_trace_2964_);
lean_dec_ref(v_cfg_2963_);
v_a_3889_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3853_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3853_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
}
}
else
{
lean_object* v_maxDepth_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_del_object(v___x_2981_);
lean_dec(v_snd_2979_);
lean_dec(v_fst_2978_);
lean_dec_ref(v___f_2974_);
lean_dec(v_goals_2967_);
v_maxDepth_4176_ = lean_ctor_get(v_cfg_2963_, 0);
lean_inc(v_maxDepth_4176_);
v___x_4177_ = lean_box(0);
v___x_4178_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2963_, v_trace_2964_, v_next_2965_, v_orig_2966_, v_maxDepth_4176_, v_remaining_2968_, v___x_4177_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_);
return v___x_4178_;
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec_ref(v___f_2974_);
lean_dec(v_remaining_2968_);
lean_dec(v_goals_2967_);
lean_dec(v_orig_2966_);
lean_dec_ref(v_next_2965_);
lean_dec(v_trace_2964_);
lean_dec_ref(v_cfg_2963_);
v_a_4180_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_2976_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_2976_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_4188_, lean_object* v_trace_4189_, lean_object* v_next_4190_, lean_object* v_orig_4191_, lean_object* v_goals_4192_, lean_object* v_remaining_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4188_, v_trace_4189_, v_next_4190_, v_orig_4191_, v_goals_4192_, v_remaining_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
return v_res_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_4200_, lean_object* v_00_u03b2_4201_, lean_object* v_L_4202_, lean_object* v_f_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_4202_, v_f_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_4210_, lean_object* v_00_u03b2_4211_, lean_object* v_L_4212_, lean_object* v_f_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_4210_, v_00_u03b2_4211_, v_L_4212_, v_f_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_4220_, lean_object* v_x_4221_, lean_object* v_x_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v___x_4228_; 
v___x_4228_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_4220_, v_x_4221_, v_x_4222_, v___y_4224_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_4229_, lean_object* v_x_4230_, lean_object* v_x_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
uint8_t v___x_48625__boxed_4237_; lean_object* v_res_4238_; 
v___x_48625__boxed_4237_ = lean_unbox(v___x_4229_);
v_res_4238_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_48625__boxed_4237_, v_x_4230_, v_x_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_4239_, uint8_t v___x_4240_, lean_object* v_x_4241_, lean_object* v_x_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v___x_4248_; 
v___x_4248_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_4239_, v___x_4240_, v_x_4241_, v_x_4242_, v___y_4244_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_4249_, lean_object* v___x_4250_, lean_object* v_x_4251_, lean_object* v_x_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
uint8_t v___x_48651__boxed_4258_; uint8_t v___x_48652__boxed_4259_; lean_object* v_res_4260_; 
v___x_48651__boxed_4258_ = lean_unbox(v___x_4249_);
v___x_48652__boxed_4259_ = lean_unbox(v___x_4250_);
v_res_4260_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_48651__boxed_4258_, v___x_48652__boxed_4259_, v_x_4251_, v_x_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_4261_, lean_object* v_00_u03b2_4262_, lean_object* v_f_4263_, lean_object* v_x_4264_, lean_object* v_x_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_4263_, v_x_4264_, v_x_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4272_, lean_object* v_00_u03b2_4273_, lean_object* v_f_4274_, lean_object* v_x_4275_, lean_object* v_x_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_4272_, v_00_u03b2_4273_, v_f_4274_, v_x_4275_, v_x_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_4283_, lean_object* v_00_u03b2_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_4285_, v_a_4286_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_4288_, lean_object* v_00_u03b2_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_4290_, v_a_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_4293_, lean_object* v_g_4294_, lean_object* v_f_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v___x_4301_; 
lean_inc(v___y_4299_);
lean_inc_ref(v___y_4298_);
lean_inc(v___y_4297_);
lean_inc_ref(v___y_4296_);
v___x_4301_ = lean_apply_6(v_next_4293_, v_g_4294_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, lean_box(0));
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4303_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4302_);
lean_dec_ref_known(v___x_4301_, 1);
v___x_4303_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_4302_, v_f_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4303_;
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec_ref(v_f_4295_);
v_a_4304_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4301_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4301_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_4312_, lean_object* v_g_4313_, lean_object* v_f_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_4312_, v_g_4313_, v_f_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_4321_, lean_object* v_trace_4322_, lean_object* v_next_4323_, lean_object* v_goals_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_){
_start:
{
lean_object* v_resolve_4330_; lean_object* v___x_4331_; 
v_resolve_4330_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_4330_, 0, v_next_4323_);
lean_inc_n(v_goals_4324_, 2);
v___x_4331_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4321_, v_trace_4322_, v_resolve_4330_, v_goals_4324_, v_goals_4324_, v_goals_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_4332_, lean_object* v_trace_4333_, lean_object* v_next_4334_, lean_object* v_goals_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_4332_, v_trace_4333_, v_next_4334_, v_goals_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
lean_dec(v_a_4339_);
lean_dec_ref(v_a_4338_);
lean_dec(v_a_4337_);
lean_dec_ref(v_a_4336_);
return v_res_4341_;
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

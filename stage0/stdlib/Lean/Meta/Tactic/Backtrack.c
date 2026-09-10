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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object*);
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
v___x_190_ = lean_st_ref_put(v___y_163_, v___x_189_);
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
lean_object* v___x_311_; lean_object* v_env_312_; lean_object* v___x_313_; lean_object* v_toCold_314_; lean_object* v_mctx_315_; lean_object* v_lctx_316_; lean_object* v_options_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_311_ = lean_st_ref_get(v___y_309_);
v_env_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref(v_env_312_);
lean_dec(v___x_311_);
v___x_313_ = lean_st_ref_get(v___y_307_);
v_toCold_314_ = lean_ctor_get(v___y_308_, 0);
v_mctx_315_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_mctx_315_);
lean_dec(v___x_313_);
v_lctx_316_ = lean_ctor_get(v___y_306_, 2);
v_options_317_ = lean_ctor_get(v_toCold_314_, 2);
lean_inc_ref(v_options_317_);
lean_inc_ref(v_lctx_316_);
v___x_318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_318_, 0, v_env_312_);
lean_ctor_set(v___x_318_, 1, v_mctx_315_);
lean_ctor_set(v___x_318_, 2, v_lctx_316_);
lean_ctor_set(v___x_318_, 3, v_options_317_);
v___x_319_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_msgData_305_);
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
lean_dec_ref_known(v___x_405_, 1);
if (lean_obj_tag(v_val_406_) == 3)
{
lean_object* v_v_407_; 
v_v_407_ = lean_ctor_get(v_val_406_, 0);
lean_inc(v_v_407_);
lean_dec_ref_known(v_val_406_, 1);
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object* v_e_411_){
_start:
{
if (lean_obj_tag(v_e_411_) == 0)
{
uint8_t v___x_412_; 
v___x_412_ = 2;
return v___x_412_;
}
else
{
lean_object* v_a_413_; 
v_a_413_ = lean_ctor_get(v_e_411_, 0);
if (lean_obj_tag(v_a_413_) == 0)
{
uint8_t v___x_414_; 
v___x_414_ = 1;
return v___x_414_;
}
else
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object* v_e_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_e_416_);
lean_dec_ref(v_e_416_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
v_a_421_ = lean_ctor_get(v_x_419_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v_x_419_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v_x_419_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v_x_419_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 1);
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
v_a_429_ = lean_ctor_get(v_x_419_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_x_419_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v_x_419_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v_x_419_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set_tag(v___x_431_, 0);
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg___boxed(lean_object* v_x_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(size_t v_sz_440_, size_t v_i_441_, lean_object* v_bs_442_){
_start:
{
uint8_t v___x_443_; 
v___x_443_ = lean_usize_dec_lt(v_i_441_, v_sz_440_);
if (v___x_443_ == 0)
{
return v_bs_442_;
}
else
{
lean_object* v_v_444_; lean_object* v_msg_445_; lean_object* v___x_446_; lean_object* v_bs_x27_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v_v_444_ = lean_array_uget_borrowed(v_bs_442_, v_i_441_);
v_msg_445_ = lean_ctor_get(v_v_444_, 1);
lean_inc_ref(v_msg_445_);
v___x_446_ = lean_unsigned_to_nat(0u);
v_bs_x27_447_ = lean_array_uset(v_bs_442_, v_i_441_, v___x_446_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_441_, v___x_448_);
v___x_450_ = lean_array_uset(v_bs_x27_447_, v_i_441_, v_msg_445_);
v_i_441_ = v___x_449_;
v_bs_442_ = v___x_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6___boxed(lean_object* v_sz_452_, lean_object* v_i_453_, lean_object* v_bs_454_){
_start:
{
size_t v_sz_boxed_455_; size_t v_i_boxed_456_; lean_object* v_res_457_; 
v_sz_boxed_455_ = lean_unbox_usize(v_sz_452_);
lean_dec(v_sz_452_);
v_i_boxed_456_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_boxed_455_, v_i_boxed_456_, v_bs_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object* v_oldTraces_458_, lean_object* v_data_459_, lean_object* v_ref_460_, lean_object* v_msg_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_toCold_467_; lean_object* v_currRecDepth_468_; lean_object* v_ref_469_; uint8_t v_diag_470_; uint8_t v_suppressElabErrors_471_; lean_object* v___x_472_; lean_object* v_traceState_473_; lean_object* v_traces_474_; lean_object* v_ref_475_; lean_object* v___x_476_; lean_object* v___x_477_; size_t v_sz_478_; size_t v___x_479_; lean_object* v___x_480_; lean_object* v_msg_481_; lean_object* v___x_482_; lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_520_; 
v_toCold_467_ = lean_ctor_get(v___y_464_, 0);
v_currRecDepth_468_ = lean_ctor_get(v___y_464_, 1);
v_ref_469_ = lean_ctor_get(v___y_464_, 2);
v_diag_470_ = lean_ctor_get_uint8(v___y_464_, sizeof(void*)*3);
v_suppressElabErrors_471_ = lean_ctor_get_uint8(v___y_464_, sizeof(void*)*3 + 1);
v___x_472_ = lean_st_ref_get(v___y_465_);
v_traceState_473_ = lean_ctor_get(v___x_472_, 4);
lean_inc_ref(v_traceState_473_);
lean_dec(v___x_472_);
v_traces_474_ = lean_ctor_get(v_traceState_473_, 0);
lean_inc_ref(v_traces_474_);
lean_dec_ref(v_traceState_473_);
v_ref_475_ = l_Lean_replaceRef(v_ref_460_, v_ref_469_);
lean_inc(v_currRecDepth_468_);
lean_inc_ref(v_toCold_467_);
v___x_476_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_476_, 0, v_toCold_467_);
lean_ctor_set(v___x_476_, 1, v_currRecDepth_468_);
lean_ctor_set(v___x_476_, 2, v_ref_475_);
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*3, v_diag_470_);
lean_ctor_set_uint8(v___x_476_, sizeof(void*)*3 + 1, v_suppressElabErrors_471_);
v___x_477_ = l_Lean_PersistentArray_toArray___redArg(v_traces_474_);
lean_dec_ref(v_traces_474_);
v_sz_478_ = lean_array_size(v___x_477_);
v___x_479_ = ((size_t)0ULL);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_478_, v___x_479_, v___x_477_);
v_msg_481_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_481_, 0, v_data_459_);
lean_ctor_set(v_msg_481_, 1, v_msg_461_);
lean_ctor_set(v_msg_481_, 2, v___x_480_);
v___x_482_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_481_, v___y_462_, v___y_463_, v___x_476_, v___y_465_);
lean_dec_ref_known(v___x_476_, 3);
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_520_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_520_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_520_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v_traceState_488_; lean_object* v_env_489_; lean_object* v_nextMacroScope_490_; lean_object* v_ngen_491_; lean_object* v_auxDeclNGen_492_; lean_object* v_cache_493_; lean_object* v_messages_494_; lean_object* v_infoState_495_; lean_object* v_snapshotTasks_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_519_; 
v___x_487_ = lean_st_ref_take(v___y_465_);
v_traceState_488_ = lean_ctor_get(v___x_487_, 4);
v_env_489_ = lean_ctor_get(v___x_487_, 0);
v_nextMacroScope_490_ = lean_ctor_get(v___x_487_, 1);
v_ngen_491_ = lean_ctor_get(v___x_487_, 2);
v_auxDeclNGen_492_ = lean_ctor_get(v___x_487_, 3);
v_cache_493_ = lean_ctor_get(v___x_487_, 5);
v_messages_494_ = lean_ctor_get(v___x_487_, 6);
v_infoState_495_ = lean_ctor_get(v___x_487_, 7);
v_snapshotTasks_496_ = lean_ctor_get(v___x_487_, 8);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_519_ == 0)
{
v___x_498_ = v___x_487_;
v_isShared_499_ = v_isSharedCheck_519_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_snapshotTasks_496_);
lean_inc(v_infoState_495_);
lean_inc(v_messages_494_);
lean_inc(v_cache_493_);
lean_inc(v_traceState_488_);
lean_inc(v_auxDeclNGen_492_);
lean_inc(v_ngen_491_);
lean_inc(v_nextMacroScope_490_);
lean_inc(v_env_489_);
lean_dec(v___x_487_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_519_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
uint64_t v_tid_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_517_; 
v_tid_500_ = lean_ctor_get_uint64(v_traceState_488_, sizeof(void*)*1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_traceState_488_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_traceState_488_, 0);
lean_dec(v_unused_518_);
v___x_502_ = v_traceState_488_;
v_isShared_503_ = v_isSharedCheck_517_;
goto v_resetjp_501_;
}
else
{
lean_dec(v_traceState_488_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_517_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_ref_460_);
lean_ctor_set(v___x_504_, 1, v_a_483_);
v___x_505_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_458_, v___x_504_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_505_);
lean_ctor_set_uint64(v_reuseFailAlloc_516_, sizeof(void*)*1, v_tid_500_);
v___x_507_ = v_reuseFailAlloc_516_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 4, v___x_507_);
v___x_509_ = v___x_498_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_env_489_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_nextMacroScope_490_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_ngen_491_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_auxDeclNGen_492_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_515_, 5, v_cache_493_);
lean_ctor_set(v_reuseFailAlloc_515_, 6, v_messages_494_);
lean_ctor_set(v_reuseFailAlloc_515_, 7, v_infoState_495_);
lean_ctor_set(v_reuseFailAlloc_515_, 8, v_snapshotTasks_496_);
v___x_509_ = v_reuseFailAlloc_515_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = lean_st_ref_put(v___y_465_, v___x_509_);
v___x_511_ = lean_box(0);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_511_);
v___x_513_ = v___x_485_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object* v_oldTraces_521_, lean_object* v_data_522_, lean_object* v_ref_523_, lean_object* v_msg_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_521_, v_data_522_, v_ref_523_, v_msg_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_530_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0(void){
_start:
{
lean_object* v___x_531_; double v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_float_of_nat(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3(void){
_start:
{
lean_object* v___x_536_; double v___x_537_; 
v___x_536_ = lean_unsigned_to_nat(1000u);
v___x_537_ = lean_float_of_nat(v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_cls_538_, uint8_t v_collapsed_539_, lean_object* v_tag_540_, lean_object* v_opts_541_, uint8_t v_clsEnabled_542_, lean_object* v_oldTraces_543_, lean_object* v_msg_544_, lean_object* v_resStartStop_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_fst_551_; lean_object* v_snd_552_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v_data_556_; lean_object* v_fst_567_; lean_object* v_snd_568_; lean_object* v___x_569_; uint8_t v___x_570_; lean_object* v___y_572_; lean_object* v_a_573_; uint8_t v___y_588_; double v___y_619_; 
v_fst_551_ = lean_ctor_get(v_resStartStop_545_, 0);
lean_inc(v_fst_551_);
v_snd_552_ = lean_ctor_get(v_resStartStop_545_, 1);
lean_inc(v_snd_552_);
lean_dec_ref(v_resStartStop_545_);
v_fst_567_ = lean_ctor_get(v_snd_552_, 0);
lean_inc(v_fst_567_);
v_snd_568_ = lean_ctor_get(v_snd_552_, 1);
lean_inc(v_snd_568_);
lean_dec(v_snd_552_);
v___x_569_ = l_Lean_trace_profiler;
v___x_570_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_541_, v___x_569_);
if (v___x_570_ == 0)
{
v___y_588_ = v___x_570_;
goto v___jp_587_;
}
else
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = l_Lean_trace_profiler_useHeartbeats;
v___x_625_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_541_, v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; double v___x_628_; double v___x_629_; double v___x_630_; 
v___x_626_ = l_Lean_trace_profiler_threshold;
v___x_627_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_541_, v___x_626_);
v___x_628_ = lean_float_of_nat(v___x_627_);
v___x_629_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_630_ = lean_float_div(v___x_628_, v___x_629_);
v___y_619_ = v___x_630_;
goto v___jp_618_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; double v___x_633_; 
v___x_631_ = l_Lean_trace_profiler_threshold;
v___x_632_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_541_, v___x_631_);
v___x_633_ = lean_float_of_nat(v___x_632_);
v___y_619_ = v___x_633_;
goto v___jp_618_;
}
}
v___jp_553_:
{
lean_object* v___x_557_; 
lean_inc(v___y_555_);
v___x_557_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_543_, v_data_556_, v___y_555_, v___y_554_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_558_; 
lean_dec_ref_known(v___x_557_, 1);
v___x_558_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_551_);
return v___x_558_;
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec(v_fst_551_);
v_a_559_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_557_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
v___jp_571_:
{
uint8_t v_result_574_; lean_object* v___x_575_; lean_object* v___x_576_; double v___x_577_; lean_object* v_data_578_; 
v_result_574_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_fst_551_);
v___x_575_ = lean_box(v_result_574_);
v___x_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
v___x_577_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_540_);
lean_inc_ref(v___x_576_);
lean_inc(v_cls_538_);
v_data_578_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_578_, 0, v_cls_538_);
lean_ctor_set(v_data_578_, 1, v___x_576_);
lean_ctor_set(v_data_578_, 2, v_tag_540_);
lean_ctor_set_float(v_data_578_, sizeof(void*)*3, v___x_577_);
lean_ctor_set_float(v_data_578_, sizeof(void*)*3 + 8, v___x_577_);
lean_ctor_set_uint8(v_data_578_, sizeof(void*)*3 + 16, v_collapsed_539_);
if (v___x_570_ == 0)
{
lean_dec_ref_known(v___x_576_, 1);
lean_dec(v_snd_568_);
lean_dec(v_fst_567_);
lean_dec_ref(v_tag_540_);
lean_dec(v_cls_538_);
v___y_554_ = v_a_573_;
v___y_555_ = v___y_572_;
v_data_556_ = v_data_578_;
goto v___jp_553_;
}
else
{
lean_object* v_data_579_; double v___x_580_; double v___x_581_; 
lean_dec_ref_known(v_data_578_, 3);
v_data_579_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_579_, 0, v_cls_538_);
lean_ctor_set(v_data_579_, 1, v___x_576_);
lean_ctor_set(v_data_579_, 2, v_tag_540_);
v___x_580_ = lean_unbox_float(v_fst_567_);
lean_dec(v_fst_567_);
lean_ctor_set_float(v_data_579_, sizeof(void*)*3, v___x_580_);
v___x_581_ = lean_unbox_float(v_snd_568_);
lean_dec(v_snd_568_);
lean_ctor_set_float(v_data_579_, sizeof(void*)*3 + 8, v___x_581_);
lean_ctor_set_uint8(v_data_579_, sizeof(void*)*3 + 16, v_collapsed_539_);
v___y_554_ = v_a_573_;
v___y_555_ = v___y_572_;
v_data_556_ = v_data_579_;
goto v___jp_553_;
}
}
v___jp_582_:
{
lean_object* v_ref_583_; lean_object* v___x_584_; 
v_ref_583_ = lean_ctor_get(v___y_548_, 2);
lean_inc(v___y_549_);
lean_inc_ref(v___y_548_);
lean_inc(v___y_547_);
lean_inc_ref(v___y_546_);
lean_inc(v_fst_551_);
v___x_584_ = lean_apply_6(v_msg_544_, v_fst_551_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, lean_box(0));
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___y_572_ = v_ref_583_;
v_a_573_ = v_a_585_;
goto v___jp_571_;
}
else
{
lean_object* v___x_586_; 
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_572_ = v_ref_583_;
v_a_573_ = v___x_586_;
goto v___jp_571_;
}
}
v___jp_587_:
{
if (v_clsEnabled_542_ == 0)
{
if (v___y_588_ == 0)
{
lean_object* v___x_589_; lean_object* v_traceState_590_; lean_object* v_env_591_; lean_object* v_nextMacroScope_592_; lean_object* v_ngen_593_; lean_object* v_auxDeclNGen_594_; lean_object* v_cache_595_; lean_object* v_messages_596_; lean_object* v_infoState_597_; lean_object* v_snapshotTasks_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_617_; 
lean_dec(v_snd_568_);
lean_dec(v_fst_567_);
lean_dec_ref(v_msg_544_);
lean_dec_ref(v_tag_540_);
lean_dec(v_cls_538_);
v___x_589_ = lean_st_ref_take(v___y_549_);
v_traceState_590_ = lean_ctor_get(v___x_589_, 4);
v_env_591_ = lean_ctor_get(v___x_589_, 0);
v_nextMacroScope_592_ = lean_ctor_get(v___x_589_, 1);
v_ngen_593_ = lean_ctor_get(v___x_589_, 2);
v_auxDeclNGen_594_ = lean_ctor_get(v___x_589_, 3);
v_cache_595_ = lean_ctor_get(v___x_589_, 5);
v_messages_596_ = lean_ctor_get(v___x_589_, 6);
v_infoState_597_ = lean_ctor_get(v___x_589_, 7);
v_snapshotTasks_598_ = lean_ctor_get(v___x_589_, 8);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_617_ == 0)
{
v___x_600_ = v___x_589_;
v_isShared_601_ = v_isSharedCheck_617_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_snapshotTasks_598_);
lean_inc(v_infoState_597_);
lean_inc(v_messages_596_);
lean_inc(v_cache_595_);
lean_inc(v_traceState_590_);
lean_inc(v_auxDeclNGen_594_);
lean_inc(v_ngen_593_);
lean_inc(v_nextMacroScope_592_);
lean_inc(v_env_591_);
lean_dec(v___x_589_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_617_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
uint64_t v_tid_602_; lean_object* v_traces_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_616_; 
v_tid_602_ = lean_ctor_get_uint64(v_traceState_590_, sizeof(void*)*1);
v_traces_603_ = lean_ctor_get(v_traceState_590_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v_traceState_590_);
if (v_isSharedCheck_616_ == 0)
{
v___x_605_ = v_traceState_590_;
v_isShared_606_ = v_isSharedCheck_616_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_traces_603_);
lean_dec(v_traceState_590_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_616_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_607_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_543_, v_traces_603_);
lean_dec_ref(v_traces_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_607_);
lean_ctor_set_uint64(v_reuseFailAlloc_615_, sizeof(void*)*1, v_tid_602_);
v___x_609_ = v_reuseFailAlloc_615_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 4, v___x_609_);
v___x_611_ = v___x_600_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_env_591_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_nextMacroScope_592_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_ngen_593_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_auxDeclNGen_594_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_614_, 5, v_cache_595_);
lean_ctor_set(v_reuseFailAlloc_614_, 6, v_messages_596_);
lean_ctor_set(v_reuseFailAlloc_614_, 7, v_infoState_597_);
lean_ctor_set(v_reuseFailAlloc_614_, 8, v_snapshotTasks_598_);
v___x_611_ = v_reuseFailAlloc_614_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_st_ref_put(v___y_549_, v___x_611_);
v___x_613_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_551_);
return v___x_613_;
}
}
}
}
}
else
{
goto v___jp_582_;
}
}
else
{
goto v___jp_582_;
}
}
v___jp_618_:
{
double v___x_620_; double v___x_621_; double v___x_622_; uint8_t v___x_623_; 
v___x_620_ = lean_unbox_float(v_snd_568_);
v___x_621_ = lean_unbox_float(v_fst_567_);
v___x_622_ = lean_float_sub(v___x_620_, v___x_621_);
v___x_623_ = lean_float_decLt(v___y_619_, v___x_622_);
v___y_588_ = v___x_623_;
goto v___jp_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_cls_634_, lean_object* v_collapsed_635_, lean_object* v_tag_636_, lean_object* v_opts_637_, lean_object* v_clsEnabled_638_, lean_object* v_oldTraces_639_, lean_object* v_msg_640_, lean_object* v_resStartStop_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
uint8_t v_collapsed_boxed_647_; uint8_t v_clsEnabled_boxed_648_; lean_object* v_res_649_; 
v_collapsed_boxed_647_ = lean_unbox(v_collapsed_635_);
v_clsEnabled_boxed_648_ = lean_unbox(v_clsEnabled_638_);
v_res_649_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_cls_634_, v_collapsed_boxed_647_, v_tag_636_, v_opts_637_, v_clsEnabled_boxed_648_, v_oldTraces_639_, v_msg_640_, v_resStartStop_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v_opts_637_);
return v_res_649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* v_a_653_, lean_object* v_x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
v___x_661_ = l_Lean_Exception_toMessageData(v_a_653_);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* v_a_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_a_664_, v_x_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec_ref(v_x_665_);
return v_res_671_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object* v_keys_672_, lean_object* v_i_673_, lean_object* v_k_674_){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_array_get_size(v_keys_672_);
v___x_676_ = lean_nat_dec_lt(v_i_673_, v___x_675_);
if (v___x_676_ == 0)
{
lean_dec(v_i_673_);
return v___x_676_;
}
else
{
lean_object* v_k_x27_677_; uint8_t v___x_678_; 
v_k_x27_677_ = lean_array_fget_borrowed(v_keys_672_, v_i_673_);
v___x_678_ = l_Lean_instBEqMVarId_beq(v_k_674_, v_k_x27_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_unsigned_to_nat(1u);
v___x_680_ = lean_nat_add(v_i_673_, v___x_679_);
lean_dec(v_i_673_);
v_i_673_ = v___x_680_;
goto _start;
}
else
{
lean_dec(v_i_673_);
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object* v_keys_682_, lean_object* v_i_683_, lean_object* v_k_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_682_, v_i_683_, v_k_684_);
lean_dec(v_k_684_);
lean_dec_ref(v_keys_682_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_687_, size_t v_x_688_, lean_object* v_x_689_){
_start:
{
if (lean_obj_tag(v_x_687_) == 0)
{
lean_object* v_es_690_; lean_object* v___x_691_; size_t v___x_692_; size_t v___x_693_; lean_object* v_j_694_; lean_object* v___x_695_; 
v_es_690_ = lean_ctor_get(v_x_687_, 0);
v___x_691_ = lean_box(2);
v___x_692_ = ((size_t)31ULL);
v___x_693_ = lean_usize_land(v_x_688_, v___x_692_);
v_j_694_ = lean_usize_to_nat(v___x_693_);
v___x_695_ = lean_array_get_borrowed(v___x_691_, v_es_690_, v_j_694_);
lean_dec(v_j_694_);
switch(lean_obj_tag(v___x_695_))
{
case 0:
{
lean_object* v_key_696_; uint8_t v___x_697_; 
v_key_696_ = lean_ctor_get(v___x_695_, 0);
v___x_697_ = l_Lean_instBEqMVarId_beq(v_x_689_, v_key_696_);
return v___x_697_;
}
case 1:
{
lean_object* v_node_698_; size_t v___x_699_; size_t v___x_700_; 
v_node_698_ = lean_ctor_get(v___x_695_, 0);
v___x_699_ = ((size_t)5ULL);
v___x_700_ = lean_usize_shift_right(v_x_688_, v___x_699_);
v_x_687_ = v_node_698_;
v_x_688_ = v___x_700_;
goto _start;
}
default: 
{
uint8_t v___x_702_; 
v___x_702_ = 0;
return v___x_702_;
}
}
}
else
{
lean_object* v_ks_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_ks_703_ = lean_ctor_get(v_x_687_, 0);
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_ks_703_, v___x_704_, v_x_689_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_x_706_, lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
size_t v_x_74279__boxed_709_; uint8_t v_res_710_; lean_object* v_r_711_; 
v_x_74279__boxed_709_ = lean_unbox_usize(v_x_707_);
lean_dec(v_x_707_);
v_res_710_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_706_, v_x_74279__boxed_709_, v_x_708_);
lean_dec(v_x_708_);
lean_dec_ref(v_x_706_);
v_r_711_ = lean_box(v_res_710_);
return v_r_711_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
uint64_t v___x_714_; size_t v___x_715_; uint8_t v___x_716_; 
v___x_714_ = l_Lean_instHashableMVarId_hash(v_x_713_);
v___x_715_ = lean_uint64_to_usize(v___x_714_);
v___x_716_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_712_, v___x_715_, v_x_713_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
uint8_t v_res_719_; lean_object* v_r_720_; 
v_res_719_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_717_, v_x_718_);
lean_dec(v_x_718_);
lean_dec_ref(v_x_717_);
v_r_720_ = lean_box(v_res_719_);
return v_r_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object* v_mvarId_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; lean_object* v_mctx_725_; lean_object* v_eAssignment_726_; uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_724_ = lean_st_ref_get(v___y_722_);
v_mctx_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_mctx_725_);
lean_dec(v___x_724_);
v_eAssignment_726_ = lean_ctor_get(v_mctx_725_, 8);
lean_inc_ref(v_eAssignment_726_);
lean_dec_ref(v_mctx_725_);
v___x_727_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_eAssignment_726_, v_mvarId_721_);
lean_dec_ref(v_eAssignment_726_);
v___x_728_ = lean_box(v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object* v_mvarId_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec(v_mvarId_730_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_ref_740_; lean_object* v___x_741_; lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_750_; 
v_ref_740_ = lean_ctor_get(v___y_737_, 2);
v___x_741_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_750_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
lean_inc(v_ref_740_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v_ref_740_);
lean_ctor_set(v___x_746_, 1, v_a_742_);
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 1);
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
return v_res_757_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_e_758_){
_start:
{
if (lean_obj_tag(v_e_758_) == 0)
{
uint8_t v___x_759_; 
v___x_759_ = 2;
return v___x_759_;
}
else
{
uint8_t v___x_760_; 
v___x_760_ = 0;
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_e_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_e_761_);
lean_dec_ref(v_e_761_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_764_, uint8_t v_collapsed_765_, lean_object* v_tag_766_, lean_object* v_opts_767_, uint8_t v_clsEnabled_768_, lean_object* v_oldTraces_769_, lean_object* v_msg_770_, lean_object* v_resStartStop_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v_data_782_; lean_object* v_fst_793_; lean_object* v_snd_794_; lean_object* v___x_795_; uint8_t v___x_796_; lean_object* v___y_798_; lean_object* v_a_799_; uint8_t v___y_814_; double v___y_845_; 
v_fst_777_ = lean_ctor_get(v_resStartStop_771_, 0);
lean_inc(v_fst_777_);
v_snd_778_ = lean_ctor_get(v_resStartStop_771_, 1);
lean_inc(v_snd_778_);
lean_dec_ref(v_resStartStop_771_);
v_fst_793_ = lean_ctor_get(v_snd_778_, 0);
lean_inc(v_fst_793_);
v_snd_794_ = lean_ctor_get(v_snd_778_, 1);
lean_inc(v_snd_794_);
lean_dec(v_snd_778_);
v___x_795_ = l_Lean_trace_profiler;
v___x_796_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_767_, v___x_795_);
if (v___x_796_ == 0)
{
v___y_814_ = v___x_796_;
goto v___jp_813_;
}
else
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = l_Lean_trace_profiler_useHeartbeats;
v___x_851_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_767_, v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; double v___x_854_; double v___x_855_; double v___x_856_; 
v___x_852_ = l_Lean_trace_profiler_threshold;
v___x_853_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_767_, v___x_852_);
v___x_854_ = lean_float_of_nat(v___x_853_);
v___x_855_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_856_ = lean_float_div(v___x_854_, v___x_855_);
v___y_845_ = v___x_856_;
goto v___jp_844_;
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; double v___x_859_; 
v___x_857_ = l_Lean_trace_profiler_threshold;
v___x_858_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_767_, v___x_857_);
v___x_859_ = lean_float_of_nat(v___x_858_);
v___y_845_ = v___x_859_;
goto v___jp_844_;
}
}
v___jp_779_:
{
lean_object* v___x_783_; 
lean_inc(v___y_781_);
v___x_783_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_769_, v_data_782_, v___y_781_, v___y_780_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v___x_784_; 
lean_dec_ref_known(v___x_783_, 1);
v___x_784_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_777_);
return v___x_784_;
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec(v_fst_777_);
v_a_785_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_783_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_783_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
v___jp_797_:
{
uint8_t v_result_800_; lean_object* v___x_801_; lean_object* v___x_802_; double v___x_803_; lean_object* v_data_804_; 
v_result_800_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_fst_777_);
v___x_801_ = lean_box(v_result_800_);
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
v___x_803_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_766_);
lean_inc_ref(v___x_802_);
lean_inc(v_cls_764_);
v_data_804_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_804_, 0, v_cls_764_);
lean_ctor_set(v_data_804_, 1, v___x_802_);
lean_ctor_set(v_data_804_, 2, v_tag_766_);
lean_ctor_set_float(v_data_804_, sizeof(void*)*3, v___x_803_);
lean_ctor_set_float(v_data_804_, sizeof(void*)*3 + 8, v___x_803_);
lean_ctor_set_uint8(v_data_804_, sizeof(void*)*3 + 16, v_collapsed_765_);
if (v___x_796_ == 0)
{
lean_dec_ref_known(v___x_802_, 1);
lean_dec(v_snd_794_);
lean_dec(v_fst_793_);
lean_dec_ref(v_tag_766_);
lean_dec(v_cls_764_);
v___y_780_ = v_a_799_;
v___y_781_ = v___y_798_;
v_data_782_ = v_data_804_;
goto v___jp_779_;
}
else
{
lean_object* v_data_805_; double v___x_806_; double v___x_807_; 
lean_dec_ref_known(v_data_804_, 3);
v_data_805_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_805_, 0, v_cls_764_);
lean_ctor_set(v_data_805_, 1, v___x_802_);
lean_ctor_set(v_data_805_, 2, v_tag_766_);
v___x_806_ = lean_unbox_float(v_fst_793_);
lean_dec(v_fst_793_);
lean_ctor_set_float(v_data_805_, sizeof(void*)*3, v___x_806_);
v___x_807_ = lean_unbox_float(v_snd_794_);
lean_dec(v_snd_794_);
lean_ctor_set_float(v_data_805_, sizeof(void*)*3 + 8, v___x_807_);
lean_ctor_set_uint8(v_data_805_, sizeof(void*)*3 + 16, v_collapsed_765_);
v___y_780_ = v_a_799_;
v___y_781_ = v___y_798_;
v_data_782_ = v_data_805_;
goto v___jp_779_;
}
}
v___jp_808_:
{
lean_object* v_ref_809_; lean_object* v___x_810_; 
v_ref_809_ = lean_ctor_get(v___y_774_, 2);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_773_);
lean_inc_ref(v___y_772_);
lean_inc(v_fst_777_);
v___x_810_ = lean_apply_6(v_msg_770_, v_fst_777_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, lean_box(0));
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v___y_798_ = v_ref_809_;
v_a_799_ = v_a_811_;
goto v___jp_797_;
}
else
{
lean_object* v___x_812_; 
lean_dec_ref_known(v___x_810_, 1);
v___x_812_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_798_ = v_ref_809_;
v_a_799_ = v___x_812_;
goto v___jp_797_;
}
}
v___jp_813_:
{
if (v_clsEnabled_768_ == 0)
{
if (v___y_814_ == 0)
{
lean_object* v___x_815_; lean_object* v_traceState_816_; lean_object* v_env_817_; lean_object* v_nextMacroScope_818_; lean_object* v_ngen_819_; lean_object* v_auxDeclNGen_820_; lean_object* v_cache_821_; lean_object* v_messages_822_; lean_object* v_infoState_823_; lean_object* v_snapshotTasks_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_843_; 
lean_dec(v_snd_794_);
lean_dec(v_fst_793_);
lean_dec_ref(v_msg_770_);
lean_dec_ref(v_tag_766_);
lean_dec(v_cls_764_);
v___x_815_ = lean_st_ref_take(v___y_775_);
v_traceState_816_ = lean_ctor_get(v___x_815_, 4);
v_env_817_ = lean_ctor_get(v___x_815_, 0);
v_nextMacroScope_818_ = lean_ctor_get(v___x_815_, 1);
v_ngen_819_ = lean_ctor_get(v___x_815_, 2);
v_auxDeclNGen_820_ = lean_ctor_get(v___x_815_, 3);
v_cache_821_ = lean_ctor_get(v___x_815_, 5);
v_messages_822_ = lean_ctor_get(v___x_815_, 6);
v_infoState_823_ = lean_ctor_get(v___x_815_, 7);
v_snapshotTasks_824_ = lean_ctor_get(v___x_815_, 8);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_843_ == 0)
{
v___x_826_ = v___x_815_;
v_isShared_827_ = v_isSharedCheck_843_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_snapshotTasks_824_);
lean_inc(v_infoState_823_);
lean_inc(v_messages_822_);
lean_inc(v_cache_821_);
lean_inc(v_traceState_816_);
lean_inc(v_auxDeclNGen_820_);
lean_inc(v_ngen_819_);
lean_inc(v_nextMacroScope_818_);
lean_inc(v_env_817_);
lean_dec(v___x_815_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_843_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
uint64_t v_tid_828_; lean_object* v_traces_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_842_; 
v_tid_828_ = lean_ctor_get_uint64(v_traceState_816_, sizeof(void*)*1);
v_traces_829_ = lean_ctor_get(v_traceState_816_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_traceState_816_);
if (v_isSharedCheck_842_ == 0)
{
v___x_831_ = v_traceState_816_;
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_traces_829_);
lean_dec(v_traceState_816_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_769_, v_traces_829_);
lean_dec_ref(v_traces_829_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_833_);
v___x_835_ = v___x_831_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_833_);
lean_ctor_set_uint64(v_reuseFailAlloc_841_, sizeof(void*)*1, v_tid_828_);
v___x_835_ = v_reuseFailAlloc_841_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_837_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 4, v___x_835_);
v___x_837_ = v___x_826_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_env_817_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_nextMacroScope_818_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_ngen_819_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_auxDeclNGen_820_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_840_, 5, v_cache_821_);
lean_ctor_set(v_reuseFailAlloc_840_, 6, v_messages_822_);
lean_ctor_set(v_reuseFailAlloc_840_, 7, v_infoState_823_);
lean_ctor_set(v_reuseFailAlloc_840_, 8, v_snapshotTasks_824_);
v___x_837_ = v_reuseFailAlloc_840_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_st_ref_put(v___y_775_, v___x_837_);
v___x_839_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_777_);
return v___x_839_;
}
}
}
}
}
else
{
goto v___jp_808_;
}
}
else
{
goto v___jp_808_;
}
}
v___jp_844_:
{
double v___x_846_; double v___x_847_; double v___x_848_; uint8_t v___x_849_; 
v___x_846_ = lean_unbox_float(v_snd_794_);
v___x_847_ = lean_unbox_float(v_fst_793_);
v___x_848_ = lean_float_sub(v___x_846_, v___x_847_);
v___x_849_ = lean_float_decLt(v___y_845_, v___x_848_);
v___y_814_ = v___x_849_;
goto v___jp_813_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_860_, lean_object* v_collapsed_861_, lean_object* v_tag_862_, lean_object* v_opts_863_, lean_object* v_clsEnabled_864_, lean_object* v_oldTraces_865_, lean_object* v_msg_866_, lean_object* v_resStartStop_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
uint8_t v_collapsed_boxed_873_; uint8_t v_clsEnabled_boxed_874_; lean_object* v_res_875_; 
v_collapsed_boxed_873_ = lean_unbox(v_collapsed_861_);
v_clsEnabled_boxed_874_ = lean_unbox(v_clsEnabled_864_);
v_res_875_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_860_, v_collapsed_boxed_873_, v_tag_862_, v_opts_863_, v_clsEnabled_boxed_874_, v_oldTraces_865_, v_msg_866_, v_resStartStop_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec_ref(v_opts_863_);
return v_res_875_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_head_879_, lean_object* v_x_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_886_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_head_879_);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_head_890_, lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_head_890_, v_x_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v_x_891_);
return v_res_897_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object* v_head_901_, lean_object* v_x_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_919_; 
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v_head_901_);
v___x_909_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v___x_908_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_919_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_919_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_919_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_914_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v_a_910_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_915_);
v___x_917_ = v___x_912_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object* v_head_920_, lean_object* v_x_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(v_head_920_, v_x_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec_ref(v_x_921_);
return v_res_927_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_928_; double v___x_929_; 
v___x_928_ = lean_unsigned_to_nat(1000000000u);
v___x_929_ = lean_float_of_nat(v___x_928_);
return v___x_929_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_932_ = l_Lean_stringToMessageData(v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* v_tail_941_, lean_object* v_cfg_942_, lean_object* v_trace_943_, lean_object* v_next_944_, lean_object* v_goals_945_, lean_object* v_n_946_, lean_object* v_acc_947_, lean_object* v_r_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_941_, v_cfg_942_, v_trace_943_, v_next_944_, v_goals_945_, v_n_946_, v_acc_947_, v_r_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_955_, lean_object* v_trace_956_, lean_object* v_next_957_, lean_object* v_goals_958_, lean_object* v_n_959_, lean_object* v_curr_960_, lean_object* v_acc_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___y_968_; uint8_t v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; uint8_t v___y_973_; lean_object* v___y_974_; lean_object* v_a_975_; lean_object* v___y_985_; uint8_t v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; uint8_t v___y_990_; lean_object* v___y_991_; lean_object* v_a_992_; lean_object* v___y_1005_; uint8_t v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; uint8_t v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; uint8_t v___y_1056_; lean_object* v___y_1057_; uint8_t v___y_1058_; lean_object* v___y_1059_; lean_object* v_a_1060_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; uint8_t v___y_1073_; lean_object* v___y_1074_; uint8_t v___y_1075_; lean_object* v___y_1076_; lean_object* v_a_1077_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; uint8_t v___y_1083_; lean_object* v___y_1084_; uint8_t v___y_1085_; lean_object* v___y_1086_; lean_object* v_a_1087_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; uint8_t v___y_1093_; lean_object* v___y_1094_; uint8_t v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1101_; lean_object* v___y_1102_; uint8_t v___y_1103_; lean_object* v___y_1104_; uint8_t v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v_a_1108_; lean_object* v___y_1121_; lean_object* v___y_1122_; uint8_t v___y_1123_; lean_object* v___y_1124_; uint8_t v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v_a_1128_; lean_object* v___y_1131_; lean_object* v___y_1132_; uint8_t v___y_1133_; lean_object* v___y_1134_; uint8_t v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v_a_1138_; lean_object* v___y_1141_; lean_object* v___y_1142_; uint8_t v___y_1143_; lean_object* v___y_1144_; uint8_t v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v_zero_1151_; uint8_t v_isZero_1152_; 
v_zero_1151_ = lean_unsigned_to_nat(0u);
v_isZero_1152_ = lean_nat_dec_eq(v_n_959_, v_zero_1151_);
if (v_isZero_1152_ == 1)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec(v_acc_961_);
lean_dec(v_curr_960_);
lean_dec(v_n_959_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
v___x_1153_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1154_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1153_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1154_;
}
else
{
lean_object* v_proc_1155_; lean_object* v_suspend_1156_; lean_object* v_discharge_1157_; lean_object* v___f_1158_; lean_object* v___y_1160_; uint8_t v___y_1161_; uint8_t v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___f_1200_; lean_object* v___y_1202_; uint8_t v___y_1203_; lean_object* v___y_1204_; uint8_t v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v_a_1208_; lean_object* v___y_1218_; uint8_t v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; uint8_t v___y_1222_; lean_object* v___y_1223_; lean_object* v_a_1224_; lean_object* v___y_1237_; lean_object* v___y_1238_; uint8_t v___y_1239_; lean_object* v___y_1240_; uint8_t v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___f_1284_; uint8_t v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; uint8_t v___y_1290_; lean_object* v___y_1291_; lean_object* v_a_1292_; lean_object* v___y_1305_; uint8_t v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; uint8_t v___y_1309_; lean_object* v___y_1310_; lean_object* v_a_1311_; lean_object* v___f_1320_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; uint8_t v___y_1326_; uint8_t v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; uint8_t v___y_1330_; lean_object* v___y_1331_; lean_object* v_a_1332_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; uint8_t v___y_1348_; uint8_t v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; uint8_t v___y_1353_; lean_object* v___y_1354_; lean_object* v_a_1355_; uint8_t v___y_1365_; lean_object* v___y_1366_; uint8_t v___y_1367_; uint8_t v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; uint8_t v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1417_; lean_object* v___y_1418_; uint8_t v___y_1419_; lean_object* v___y_1420_; uint8_t v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; uint8_t v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v_a_1427_; lean_object* v___y_1440_; uint8_t v___y_1441_; lean_object* v___y_1442_; uint8_t v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; uint8_t v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v_a_1450_; lean_object* v___y_1460_; uint8_t v___y_1461_; uint8_t v___y_1462_; uint8_t v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; uint8_t v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1512_; lean_object* v___y_1513_; uint8_t v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; uint8_t v___y_1517_; uint8_t v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v_a_1522_; lean_object* v___y_1532_; lean_object* v___y_1533_; uint8_t v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; uint8_t v___y_1537_; uint8_t v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v_a_1542_; lean_object* v___y_1555_; uint8_t v___y_1556_; uint8_t v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; uint8_t v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v_a_1565_; lean_object* v___y_1575_; uint8_t v___y_1576_; uint8_t v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; uint8_t v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v_a_1585_; lean_object* v___y_1598_; uint8_t v___y_1599_; uint8_t v___y_1600_; uint8_t v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; uint8_t v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1650_; lean_object* v___y_1651_; uint8_t v___y_1652_; lean_object* v___y_1653_; uint8_t v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v_a_1660_; lean_object* v___y_1673_; lean_object* v___y_1674_; uint8_t v___y_1675_; lean_object* v___y_1676_; uint8_t v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; uint8_t v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v_a_1683_; lean_object* v___y_1693_; uint8_t v___y_1694_; lean_object* v___y_1695_; uint8_t v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; uint8_t v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v_a_1703_; lean_object* v___y_1716_; uint8_t v___y_1717_; lean_object* v___y_1718_; uint8_t v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; uint8_t v___y_1722_; lean_object* v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v_a_1726_; uint8_t v___y_1736_; uint8_t v___y_1737_; uint8_t v___y_1738_; lean_object* v___y_1739_; uint8_t v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1788_; uint8_t v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; uint8_t v___y_1792_; lean_object* v___y_1793_; lean_object* v_a_1794_; uint8_t v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; uint8_t v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v_a_1813_; lean_object* v___y_1823_; uint8_t v___y_1824_; lean_object* v___y_1825_; uint8_t v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v_one_1870_; lean_object* v_n_1871_; uint8_t v___y_1873_; lean_object* v___y_1874_; uint8_t v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; uint8_t v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; uint8_t v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; uint8_t v___y_1928_; lean_object* v___y_1952_; uint8_t v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; uint8_t v___y_1958_; uint8_t v___y_1959_; uint8_t v___y_1960_; lean_object* v___y_1961_; uint8_t v___y_2002_; uint8_t v___y_2003_; uint8_t v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; uint8_t v___y_2015_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; uint8_t v___y_2039_; uint8_t v___y_2040_; uint8_t v___y_2041_; lean_object* v___y_2042_; uint8_t v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; uint8_t v___y_2086_; uint8_t v___y_2087_; uint8_t v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; uint8_t v___y_2099_; lean_object* v___y_2120_; uint8_t v___y_2121_; uint8_t v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; uint8_t v___y_2177_; lean_object* v_a_2195_; lean_object* v___y_2289_; lean_object* v___x_2299_; 
v_proc_1155_ = lean_ctor_get(v_cfg_955_, 1);
v_suspend_1156_ = lean_ctor_get(v_cfg_955_, 2);
v_discharge_1157_ = lean_ctor_get(v_cfg_955_, 3);
v___f_1158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1870_ = lean_unsigned_to_nat(1u);
v_n_1871_ = lean_nat_sub(v_n_959_, v_one_1870_);
lean_dec(v_n_959_);
lean_inc_ref(v_proc_1155_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v_curr_960_);
lean_inc(v_goals_958_);
v___x_2299_ = lean_apply_7(v_proc_1155_, v_goals_958_, v_curr_960_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v_a_2195_ = v_a_2300_;
goto v___jp_2194_;
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2369_; 
v_a_2301_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2303_ = v___x_2299_;
v_isShared_2304_ = v_isSharedCheck_2369_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2299_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2369_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___f_2305_; uint8_t v___y_2307_; uint8_t v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; uint8_t v___y_2347_; uint8_t v___x_2367_; 
lean_inc(v_a_2301_);
v___f_2305_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(v___f_2305_, 0, v_a_2301_);
v___x_2367_ = l_Lean_Exception_isInterrupt(v_a_2301_);
if (v___x_2367_ == 0)
{
uint8_t v___x_2368_; 
lean_inc(v_a_2301_);
v___x_2368_ = l_Lean_Exception_isRuntime(v_a_2301_);
v___y_2347_ = v___x_2368_;
goto v___jp_2346_;
}
else
{
v___y_2347_ = v___x_2367_;
goto v___jp_2346_;
}
v___jp_2306_:
{
lean_object* v___x_2311_; lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2345_; 
v___x_2311_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2345_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2345_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2317_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2310_, v___x_2316_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2318_ = lean_io_mono_nanos_now();
v___x_2319_ = lean_io_mono_nanos_now();
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v_a_2301_);
v___x_2321_ = v___x_2314_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2301_);
v___x_2321_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
double v___x_2322_; double v___x_2323_; double v___x_2324_; double v___x_2325_; double v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2322_ = lean_float_of_nat(v___x_2318_);
v___x_2323_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2324_ = lean_float_div(v___x_2322_, v___x_2323_);
v___x_2325_ = lean_float_of_nat(v___x_2319_);
v___x_2326_ = lean_float_div(v___x_2325_, v___x_2323_);
v___x_2327_ = lean_box_float(v___x_2324_);
v___x_2328_ = lean_box_float(v___x_2326_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2321_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
lean_inc_ref(v___y_2309_);
lean_inc(v_trace_956_);
v___x_2331_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_956_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2307_, v_a_2312_, v___f_2305_, v___x_2330_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_2289_ = v___x_2331_;
goto v___jp_2288_;
}
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2333_ = lean_io_get_num_heartbeats();
v___x_2334_ = lean_io_get_num_heartbeats();
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v_a_2301_);
v___x_2336_ = v___x_2314_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2301_);
v___x_2336_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
double v___x_2337_; double v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2337_ = lean_float_of_nat(v___x_2333_);
v___x_2338_ = lean_float_of_nat(v___x_2334_);
v___x_2339_ = lean_box_float(v___x_2337_);
v___x_2340_ = lean_box_float(v___x_2338_);
v___x_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2336_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
lean_inc_ref(v___y_2309_);
lean_inc(v_trace_956_);
v___x_2343_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_956_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2307_, v_a_2312_, v___f_2305_, v___x_2342_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_2289_ = v___x_2343_;
goto v___jp_2288_;
}
}
}
}
v___jp_2346_:
{
if (v___y_2347_ == 0)
{
lean_object* v_toCold_2348_; lean_object* v_options_2349_; uint8_t v_hasTrace_2350_; 
v_toCold_2348_ = lean_ctor_get(v_a_964_, 0);
v_options_2349_ = lean_ctor_get(v_toCold_2348_, 2);
v_hasTrace_2350_ = lean_ctor_get_uint8(v_options_2349_, sizeof(void*)*1);
if (v_hasTrace_2350_ == 0)
{
lean_object* v___x_2352_; 
lean_dec_ref(v___f_2305_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_curr_960_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
if (v_isShared_2304_ == 0)
{
v___x_2352_ = v___x_2303_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2301_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v_inheritedTraceOptions_2354_ = lean_ctor_get(v_toCold_2348_, 11);
v___x_2355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_956_);
v___x_2357_ = l_Lean_Name_append(v___x_2356_, v_trace_956_);
v___x_2358_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2354_, v_options_2349_, v___x_2357_);
lean_dec(v___x_2357_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = l_Lean_trace_profiler;
v___x_2360_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2349_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2362_; 
lean_dec_ref(v___f_2305_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_curr_960_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
if (v_isShared_2304_ == 0)
{
v___x_2362_ = v___x_2303_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2301_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
else
{
lean_del_object(v___x_2303_);
v___y_2307_ = v___x_2358_;
v___y_2308_ = v_hasTrace_2350_;
v___y_2309_ = v___x_2355_;
v___y_2310_ = v_options_2349_;
goto v___jp_2306_;
}
}
else
{
lean_del_object(v___x_2303_);
v___y_2307_ = v___x_2358_;
v___y_2308_ = v_hasTrace_2350_;
v___y_2309_ = v___x_2355_;
v___y_2310_ = v_options_2349_;
goto v___jp_2306_;
}
}
}
else
{
lean_object* v___x_2365_; 
lean_dec_ref(v___f_2305_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_curr_960_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
if (v_isShared_2304_ == 0)
{
v___x_2365_ = v___x_2303_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2301_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
v___jp_1159_:
{
lean_object* v___x_1165_; lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1199_; 
v___x_1165_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1199_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1199_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1171_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1160_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1172_ = lean_io_mono_nanos_now();
v___x_1173_ = lean_io_mono_nanos_now();
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 1);
lean_ctor_set(v___x_1168_, 0, v___y_1163_);
v___x_1175_ = v___x_1168_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___y_1163_);
v___x_1175_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
double v___x_1176_; double v___x_1177_; double v___x_1178_; double v___x_1179_; double v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1176_ = lean_float_of_nat(v___x_1172_);
v___x_1177_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1178_ = lean_float_div(v___x_1176_, v___x_1177_);
v___x_1179_ = lean_float_of_nat(v___x_1173_);
v___x_1180_ = lean_float_div(v___x_1179_, v___x_1177_);
v___x_1181_ = lean_box_float(v___x_1178_);
v___x_1182_ = lean_box_float(v___x_1180_);
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1175_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
lean_inc_ref(v___y_1164_);
v___x_1185_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1162_, v___y_1164_, v___y_1160_, v___y_1161_, v_a_1166_, v___f_1158_, v___x_1184_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1185_;
}
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1187_ = lean_io_get_num_heartbeats();
v___x_1188_ = lean_io_get_num_heartbeats();
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 1);
lean_ctor_set(v___x_1168_, 0, v___y_1163_);
v___x_1190_ = v___x_1168_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___y_1163_);
v___x_1190_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
double v___x_1191_; double v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1191_ = lean_float_of_nat(v___x_1187_);
v___x_1192_ = lean_float_of_nat(v___x_1188_);
v___x_1193_ = lean_box_float(v___x_1191_);
v___x_1194_ = lean_box_float(v___x_1192_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1193_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1190_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
lean_inc_ref(v___y_1164_);
v___x_1197_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1162_, v___y_1164_, v___y_1160_, v___y_1161_, v_a_1166_, v___f_1158_, v___x_1196_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1197_;
}
}
}
}
v___jp_1201_:
{
lean_object* v___x_1209_; double v___x_1210_; double v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1209_ = lean_io_get_num_heartbeats();
v___x_1210_ = lean_float_of_nat(v___y_1206_);
v___x_1211_ = lean_float_of_nat(v___x_1209_);
v___x_1212_ = lean_box_float(v___x_1210_);
v___x_1213_ = lean_box_float(v___x_1211_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_a_1208_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
lean_inc_ref(v___y_1207_);
v___x_1216_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1205_, v___y_1207_, v___y_1204_, v___y_1203_, v___y_1202_, v___f_1200_, v___x_1215_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1216_;
}
v___jp_1217_:
{
lean_object* v___x_1225_; double v___x_1226_; double v___x_1227_; double v___x_1228_; double v___x_1229_; double v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1225_ = lean_io_mono_nanos_now();
v___x_1226_ = lean_float_of_nat(v___y_1221_);
v___x_1227_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1228_ = lean_float_div(v___x_1226_, v___x_1227_);
v___x_1229_ = lean_float_of_nat(v___x_1225_);
v___x_1230_ = lean_float_div(v___x_1229_, v___x_1227_);
v___x_1231_ = lean_box_float(v___x_1228_);
v___x_1232_ = lean_box_float(v___x_1230_);
v___x_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v_a_1224_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
lean_inc_ref(v___y_1223_);
v___x_1235_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1222_, v___y_1223_, v___y_1220_, v___y_1219_, v___y_1218_, v___f_1200_, v___x_1234_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1235_;
}
v___jp_1236_:
{
lean_object* v___x_1244_; lean_object* v_a_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1244_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1247_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1240_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_io_mono_nanos_now();
lean_inc(v_trace_956_);
v___x_1249_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1237_, v___y_1242_, v___y_1238_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set_tag(v___x_1252_, 1);
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
v___y_1218_ = v_a_1245_;
v___y_1219_ = v___y_1239_;
v___y_1220_ = v___y_1240_;
v___y_1221_ = v___x_1248_;
v___y_1222_ = v___y_1241_;
v___y_1223_ = v___y_1243_;
v_a_1224_ = v___x_1255_;
goto v___jp_1217_;
}
}
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
v_a_1258_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1249_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1249_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 0);
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
v___y_1218_ = v_a_1245_;
v___y_1219_ = v___y_1239_;
v___y_1220_ = v___y_1240_;
v___y_1221_ = v___x_1248_;
v___y_1222_ = v___y_1241_;
v___y_1223_ = v___y_1243_;
v_a_1224_ = v___x_1263_;
goto v___jp_1217_;
}
}
}
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_956_);
v___x_1267_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1237_, v___y_1242_, v___y_1238_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 1);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
v___y_1202_ = v_a_1245_;
v___y_1203_ = v___y_1239_;
v___y_1204_ = v___y_1240_;
v___y_1205_ = v___y_1241_;
v___y_1206_ = v___x_1266_;
v___y_1207_ = v___y_1243_;
v_a_1208_ = v___x_1273_;
goto v___jp_1201_;
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
v_a_1276_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1267_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1267_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set_tag(v___x_1278_, 0);
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
v___y_1202_ = v_a_1245_;
v___y_1203_ = v___y_1239_;
v___y_1204_ = v___y_1240_;
v___y_1205_ = v___y_1241_;
v___y_1206_ = v___x_1266_;
v___y_1207_ = v___y_1243_;
v_a_1208_ = v___x_1281_;
goto v___jp_1201_;
}
}
}
}
}
v___jp_1285_:
{
lean_object* v___x_1293_; double v___x_1294_; double v___x_1295_; double v___x_1296_; double v___x_1297_; double v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1293_ = lean_io_mono_nanos_now();
v___x_1294_ = lean_float_of_nat(v___y_1289_);
v___x_1295_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1296_ = lean_float_div(v___x_1294_, v___x_1295_);
v___x_1297_ = lean_float_of_nat(v___x_1293_);
v___x_1298_ = lean_float_div(v___x_1297_, v___x_1295_);
v___x_1299_ = lean_box_float(v___x_1296_);
v___x_1300_ = lean_box_float(v___x_1298_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v_a_1292_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
lean_inc_ref(v___y_1291_);
v___x_1303_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1290_, v___y_1291_, v___y_1287_, v___y_1286_, v___y_1288_, v___f_1284_, v___x_1302_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1303_;
}
v___jp_1304_:
{
lean_object* v___x_1312_; double v___x_1313_; double v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1312_ = lean_io_get_num_heartbeats();
v___x_1313_ = lean_float_of_nat(v___y_1305_);
v___x_1314_ = lean_float_of_nat(v___x_1312_);
v___x_1315_ = lean_box_float(v___x_1313_);
v___x_1316_ = lean_box_float(v___x_1314_);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v_a_1311_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
lean_inc_ref(v___y_1310_);
v___x_1319_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1309_, v___y_1310_, v___y_1307_, v___y_1306_, v___y_1308_, v___f_1284_, v___x_1318_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1319_;
}
v___jp_1321_:
{
lean_object* v___x_1333_; double v___x_1334_; double v___x_1335_; double v___x_1336_; double v___x_1337_; double v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1333_ = lean_io_mono_nanos_now();
v___x_1334_ = lean_float_of_nat(v___y_1325_);
v___x_1335_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1336_ = lean_float_div(v___x_1334_, v___x_1335_);
v___x_1337_ = lean_float_of_nat(v___x_1333_);
v___x_1338_ = lean_float_div(v___x_1337_, v___x_1335_);
v___x_1339_ = lean_box_float(v___x_1336_);
v___x_1340_ = lean_box_float(v___x_1338_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
v___x_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1342_, 0, v_a_1332_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
lean_inc_ref(v___y_1331_);
lean_inc(v_trace_956_);
v___x_1343_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1330_, v___y_1331_, v___y_1329_, v___y_1326_, v___y_1323_, v___f_1320_, v___x_1342_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1090_ = v___y_1322_;
v___y_1091_ = v___y_1324_;
v___y_1092_ = v___y_1328_;
v___y_1093_ = v___y_1327_;
v___y_1094_ = v___y_1329_;
v___y_1095_ = v___y_1330_;
v___y_1096_ = v___y_1331_;
v___y_1097_ = v___x_1343_;
goto v___jp_1089_;
}
v___jp_1344_:
{
lean_object* v___x_1356_; double v___x_1357_; double v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1356_ = lean_io_get_num_heartbeats();
v___x_1357_ = lean_float_of_nat(v___y_1352_);
v___x_1358_ = lean_float_of_nat(v___x_1356_);
v___x_1359_ = lean_box_float(v___x_1357_);
v___x_1360_ = lean_box_float(v___x_1358_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_a_1355_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
lean_inc_ref(v___y_1354_);
lean_inc(v_trace_956_);
v___x_1363_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1353_, v___y_1354_, v___y_1351_, v___y_1348_, v___y_1346_, v___f_1320_, v___x_1362_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1090_ = v___y_1345_;
v___y_1091_ = v___y_1347_;
v___y_1092_ = v___y_1350_;
v___y_1093_ = v___y_1349_;
v___y_1094_ = v___y_1351_;
v___y_1095_ = v___y_1353_;
v___y_1096_ = v___y_1354_;
v___y_1097_ = v___x_1363_;
goto v___jp_1089_;
}
v___jp_1364_:
{
lean_object* v___x_1377_; 
v___x_1377_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
if (v___y_1368_ == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = lean_io_mono_nanos_now();
lean_inc(v_trace_956_);
v___x_1380_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1366_, v___y_1369_, v___y_1370_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set_tag(v___x_1383_, 1);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
v___y_1322_ = v___y_1371_;
v___y_1323_ = v_a_1378_;
v___y_1324_ = v___y_1372_;
v___y_1325_ = v___x_1379_;
v___y_1326_ = v___y_1373_;
v___y_1327_ = v___y_1365_;
v___y_1328_ = v___y_1374_;
v___y_1329_ = v___y_1375_;
v___y_1330_ = v___y_1367_;
v___y_1331_ = v___y_1376_;
v_a_1332_ = v___x_1386_;
goto v___jp_1321_;
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_a_1389_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1380_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1380_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 0);
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
v___y_1322_ = v___y_1371_;
v___y_1323_ = v_a_1378_;
v___y_1324_ = v___y_1372_;
v___y_1325_ = v___x_1379_;
v___y_1326_ = v___y_1373_;
v___y_1327_ = v___y_1365_;
v___y_1328_ = v___y_1374_;
v___y_1329_ = v___y_1375_;
v___y_1330_ = v___y_1367_;
v___y_1331_ = v___y_1376_;
v_a_1332_ = v___x_1394_;
goto v___jp_1321_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v_a_1397_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1397_);
lean_dec_ref(v___x_1377_);
v___x_1398_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_956_);
v___x_1399_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1366_, v___y_1369_, v___y_1370_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set_tag(v___x_1402_, 1);
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
v___y_1345_ = v___y_1371_;
v___y_1346_ = v_a_1397_;
v___y_1347_ = v___y_1372_;
v___y_1348_ = v___y_1373_;
v___y_1349_ = v___y_1365_;
v___y_1350_ = v___y_1374_;
v___y_1351_ = v___y_1375_;
v___y_1352_ = v___x_1398_;
v___y_1353_ = v___y_1367_;
v___y_1354_ = v___y_1376_;
v_a_1355_ = v___x_1405_;
goto v___jp_1344_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_a_1408_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1399_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1399_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 0);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
v___y_1345_ = v___y_1371_;
v___y_1346_ = v_a_1397_;
v___y_1347_ = v___y_1372_;
v___y_1348_ = v___y_1373_;
v___y_1349_ = v___y_1365_;
v___y_1350_ = v___y_1374_;
v___y_1351_ = v___y_1375_;
v___y_1352_ = v___x_1398_;
v___y_1353_ = v___y_1367_;
v___y_1354_ = v___y_1376_;
v_a_1355_ = v___x_1413_;
goto v___jp_1344_;
}
}
}
}
}
v___jp_1416_:
{
lean_object* v___x_1428_; double v___x_1429_; double v___x_1430_; double v___x_1431_; double v___x_1432_; double v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1428_ = lean_io_mono_nanos_now();
v___x_1429_ = lean_float_of_nat(v___y_1418_);
v___x_1430_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1431_ = lean_float_div(v___x_1429_, v___x_1430_);
v___x_1432_ = lean_float_of_nat(v___x_1428_);
v___x_1433_ = lean_float_div(v___x_1432_, v___x_1430_);
v___x_1434_ = lean_box_float(v___x_1431_);
v___x_1435_ = lean_box_float(v___x_1433_);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1434_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_a_1427_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
lean_inc_ref(v___y_1426_);
lean_inc(v_trace_956_);
v___x_1438_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1424_, v___y_1426_, v___y_1423_, v___y_1419_, v___y_1420_, v___f_1200_, v___x_1437_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1141_ = v___y_1417_;
v___y_1142_ = v___y_1422_;
v___y_1143_ = v___y_1421_;
v___y_1144_ = v___y_1423_;
v___y_1145_ = v___y_1424_;
v___y_1146_ = v___y_1425_;
v___y_1147_ = v___y_1426_;
v___y_1148_ = v___x_1438_;
goto v___jp_1140_;
}
v___jp_1439_:
{
lean_object* v___x_1451_; double v___x_1452_; double v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1451_ = lean_io_get_num_heartbeats();
v___x_1452_ = lean_float_of_nat(v___y_1447_);
v___x_1453_ = lean_float_of_nat(v___x_1451_);
v___x_1454_ = lean_box_float(v___x_1452_);
v___x_1455_ = lean_box_float(v___x_1453_);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_a_1450_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
lean_inc_ref(v___y_1449_);
lean_inc(v_trace_956_);
v___x_1458_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1446_, v___y_1449_, v___y_1445_, v___y_1441_, v___y_1442_, v___f_1200_, v___x_1457_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1141_ = v___y_1440_;
v___y_1142_ = v___y_1444_;
v___y_1143_ = v___y_1443_;
v___y_1144_ = v___y_1445_;
v___y_1145_ = v___y_1446_;
v___y_1146_ = v___y_1448_;
v___y_1147_ = v___y_1449_;
v___y_1148_ = v___x_1458_;
goto v___jp_1140_;
}
v___jp_1459_:
{
lean_object* v___x_1472_; 
v___x_1472_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
if (v___y_1463_ == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref(v___x_1472_);
v___x_1474_ = lean_io_mono_nanos_now();
lean_inc(v_trace_956_);
v___x_1475_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1460_, v___y_1464_, v___y_1468_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
lean_ctor_set_tag(v___x_1478_, 1);
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
v___y_1417_ = v___y_1466_;
v___y_1418_ = v___x_1474_;
v___y_1419_ = v___y_1467_;
v___y_1420_ = v_a_1473_;
v___y_1421_ = v___y_1461_;
v___y_1422_ = v___y_1469_;
v___y_1423_ = v___y_1470_;
v___y_1424_ = v___y_1462_;
v___y_1425_ = v___y_1465_;
v___y_1426_ = v___y_1471_;
v_a_1427_ = v___x_1481_;
goto v___jp_1416_;
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
v_a_1484_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1475_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1475_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set_tag(v___x_1486_, 0);
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
v___y_1417_ = v___y_1466_;
v___y_1418_ = v___x_1474_;
v___y_1419_ = v___y_1467_;
v___y_1420_ = v_a_1473_;
v___y_1421_ = v___y_1461_;
v___y_1422_ = v___y_1469_;
v___y_1423_ = v___y_1470_;
v___y_1424_ = v___y_1462_;
v___y_1425_ = v___y_1465_;
v___y_1426_ = v___y_1471_;
v_a_1427_ = v___x_1489_;
goto v___jp_1416_;
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_a_1492_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1492_);
lean_dec_ref(v___x_1472_);
v___x_1493_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_956_);
v___x_1494_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1460_, v___y_1464_, v___y_1468_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set_tag(v___x_1497_, 1);
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
v___y_1440_ = v___y_1466_;
v___y_1441_ = v___y_1467_;
v___y_1442_ = v_a_1492_;
v___y_1443_ = v___y_1461_;
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___y_1470_;
v___y_1446_ = v___y_1462_;
v___y_1447_ = v___x_1493_;
v___y_1448_ = v___y_1465_;
v___y_1449_ = v___y_1471_;
v_a_1450_ = v___x_1500_;
goto v___jp_1439_;
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_a_1503_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1494_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1494_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set_tag(v___x_1505_, 0);
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
v___y_1440_ = v___y_1466_;
v___y_1441_ = v___y_1467_;
v___y_1442_ = v_a_1492_;
v___y_1443_ = v___y_1461_;
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___y_1470_;
v___y_1446_ = v___y_1462_;
v___y_1447_ = v___x_1493_;
v___y_1448_ = v___y_1465_;
v___y_1449_ = v___y_1471_;
v_a_1450_ = v___x_1508_;
goto v___jp_1439_;
}
}
}
}
}
v___jp_1511_:
{
lean_object* v___x_1523_; double v___x_1524_; double v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1523_ = lean_io_get_num_heartbeats();
v___x_1524_ = lean_float_of_nat(v___y_1513_);
v___x_1525_ = lean_float_of_nat(v___x_1523_);
v___x_1526_ = lean_box_float(v___x_1524_);
v___x_1527_ = lean_box_float(v___x_1525_);
v___x_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_a_1522_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
lean_inc_ref(v___y_1521_);
lean_inc(v_trace_956_);
v___x_1530_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1518_, v___y_1521_, v___y_1516_, v___y_1517_, v___y_1520_, v___f_1284_, v___x_1529_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1141_ = v___y_1512_;
v___y_1142_ = v___y_1515_;
v___y_1143_ = v___y_1514_;
v___y_1144_ = v___y_1516_;
v___y_1145_ = v___y_1518_;
v___y_1146_ = v___y_1519_;
v___y_1147_ = v___y_1521_;
v___y_1148_ = v___x_1530_;
goto v___jp_1140_;
}
v___jp_1531_:
{
lean_object* v___x_1543_; double v___x_1544_; double v___x_1545_; double v___x_1546_; double v___x_1547_; double v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1543_ = lean_io_mono_nanos_now();
v___x_1544_ = lean_float_of_nat(v___y_1533_);
v___x_1545_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1546_ = lean_float_div(v___x_1544_, v___x_1545_);
v___x_1547_ = lean_float_of_nat(v___x_1543_);
v___x_1548_ = lean_float_div(v___x_1547_, v___x_1545_);
v___x_1549_ = lean_box_float(v___x_1546_);
v___x_1550_ = lean_box_float(v___x_1548_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_a_1542_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
lean_inc_ref(v___y_1541_);
lean_inc(v_trace_956_);
v___x_1553_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1538_, v___y_1541_, v___y_1536_, v___y_1537_, v___y_1540_, v___f_1284_, v___x_1552_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1141_ = v___y_1532_;
v___y_1142_ = v___y_1535_;
v___y_1143_ = v___y_1534_;
v___y_1144_ = v___y_1536_;
v___y_1145_ = v___y_1538_;
v___y_1146_ = v___y_1539_;
v___y_1147_ = v___y_1541_;
v___y_1148_ = v___x_1553_;
goto v___jp_1140_;
}
v___jp_1554_:
{
lean_object* v___x_1566_; double v___x_1567_; double v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1566_ = lean_io_get_num_heartbeats();
v___x_1567_ = lean_float_of_nat(v___y_1560_);
v___x_1568_ = lean_float_of_nat(v___x_1566_);
v___x_1569_ = lean_box_float(v___x_1567_);
v___x_1570_ = lean_box_float(v___x_1568_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_a_1565_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
lean_inc_ref(v___y_1564_);
lean_inc(v_trace_956_);
v___x_1573_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1561_, v___y_1564_, v___y_1559_, v___y_1556_, v___y_1562_, v___f_1320_, v___x_1572_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1141_ = v___y_1555_;
v___y_1142_ = v___y_1558_;
v___y_1143_ = v___y_1557_;
v___y_1144_ = v___y_1559_;
v___y_1145_ = v___y_1561_;
v___y_1146_ = v___y_1563_;
v___y_1147_ = v___y_1564_;
v___y_1148_ = v___x_1573_;
goto v___jp_1140_;
}
v___jp_1574_:
{
lean_object* v___x_1586_; double v___x_1587_; double v___x_1588_; double v___x_1589_; double v___x_1590_; double v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1586_ = lean_io_mono_nanos_now();
v___x_1587_ = lean_float_of_nat(v___y_1582_);
v___x_1588_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1589_ = lean_float_div(v___x_1587_, v___x_1588_);
v___x_1590_ = lean_float_of_nat(v___x_1586_);
v___x_1591_ = lean_float_div(v___x_1590_, v___x_1588_);
v___x_1592_ = lean_box_float(v___x_1589_);
v___x_1593_ = lean_box_float(v___x_1591_);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_a_1585_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
lean_inc_ref(v___y_1584_);
lean_inc(v_trace_956_);
v___x_1596_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1580_, v___y_1584_, v___y_1579_, v___y_1576_, v___y_1581_, v___f_1320_, v___x_1595_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1141_ = v___y_1575_;
v___y_1142_ = v___y_1578_;
v___y_1143_ = v___y_1577_;
v___y_1144_ = v___y_1579_;
v___y_1145_ = v___y_1580_;
v___y_1146_ = v___y_1583_;
v___y_1147_ = v___y_1584_;
v___y_1148_ = v___x_1596_;
goto v___jp_1140_;
}
v___jp_1597_:
{
lean_object* v___x_1610_; 
v___x_1610_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
if (v___y_1601_ == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v___x_1610_);
v___x_1612_ = lean_io_mono_nanos_now();
lean_inc(v_trace_956_);
v___x_1613_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1598_, v___y_1602_, v___y_1608_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1613_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1613_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
lean_ctor_set_tag(v___x_1616_, 1);
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
v___y_1575_ = v___y_1604_;
v___y_1576_ = v___y_1605_;
v___y_1577_ = v___y_1599_;
v___y_1578_ = v___y_1606_;
v___y_1579_ = v___y_1607_;
v___y_1580_ = v___y_1600_;
v___y_1581_ = v_a_1611_;
v___y_1582_ = v___x_1612_;
v___y_1583_ = v___y_1603_;
v___y_1584_ = v___y_1609_;
v_a_1585_ = v___x_1619_;
goto v___jp_1574_;
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
v_a_1622_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1613_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1613_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
lean_ctor_set_tag(v___x_1624_, 0);
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
v___y_1575_ = v___y_1604_;
v___y_1576_ = v___y_1605_;
v___y_1577_ = v___y_1599_;
v___y_1578_ = v___y_1606_;
v___y_1579_ = v___y_1607_;
v___y_1580_ = v___y_1600_;
v___y_1581_ = v_a_1611_;
v___y_1582_ = v___x_1612_;
v___y_1583_ = v___y_1603_;
v___y_1584_ = v___y_1609_;
v_a_1585_ = v___x_1627_;
goto v___jp_1574_;
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_a_1630_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1630_);
lean_dec_ref(v___x_1610_);
v___x_1631_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_956_);
v___x_1632_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1598_, v___y_1602_, v___y_1608_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
v___y_1555_ = v___y_1604_;
v___y_1556_ = v___y_1605_;
v___y_1557_ = v___y_1599_;
v___y_1558_ = v___y_1606_;
v___y_1559_ = v___y_1607_;
v___y_1560_ = v___x_1631_;
v___y_1561_ = v___y_1600_;
v___y_1562_ = v_a_1630_;
v___y_1563_ = v___y_1603_;
v___y_1564_ = v___y_1609_;
v_a_1565_ = v___x_1638_;
goto v___jp_1554_;
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
v_a_1641_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1632_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1632_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 0);
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
v___y_1555_ = v___y_1604_;
v___y_1556_ = v___y_1605_;
v___y_1557_ = v___y_1599_;
v___y_1558_ = v___y_1606_;
v___y_1559_ = v___y_1607_;
v___y_1560_ = v___x_1631_;
v___y_1561_ = v___y_1600_;
v___y_1562_ = v_a_1630_;
v___y_1563_ = v___y_1603_;
v___y_1564_ = v___y_1609_;
v_a_1565_ = v___x_1646_;
goto v___jp_1554_;
}
}
}
}
}
v___jp_1649_:
{
lean_object* v___x_1661_; double v___x_1662_; double v___x_1663_; double v___x_1664_; double v___x_1665_; double v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1661_ = lean_io_mono_nanos_now();
v___x_1662_ = lean_float_of_nat(v___y_1651_);
v___x_1663_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1664_ = lean_float_div(v___x_1662_, v___x_1663_);
v___x_1665_ = lean_float_of_nat(v___x_1661_);
v___x_1666_ = lean_float_div(v___x_1665_, v___x_1663_);
v___x_1667_ = lean_box_float(v___x_1664_);
v___x_1668_ = lean_box_float(v___x_1666_);
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v_a_1660_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
lean_inc_ref(v___y_1659_);
lean_inc(v_trace_956_);
v___x_1671_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1657_, v___y_1659_, v___y_1656_, v___y_1652_, v___y_1658_, v___f_1284_, v___x_1670_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1090_ = v___y_1650_;
v___y_1091_ = v___y_1653_;
v___y_1092_ = v___y_1655_;
v___y_1093_ = v___y_1654_;
v___y_1094_ = v___y_1656_;
v___y_1095_ = v___y_1657_;
v___y_1096_ = v___y_1659_;
v___y_1097_ = v___x_1671_;
goto v___jp_1089_;
}
v___jp_1672_:
{
lean_object* v___x_1684_; double v___x_1685_; double v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1684_ = lean_io_get_num_heartbeats();
v___x_1685_ = lean_float_of_nat(v___y_1674_);
v___x_1686_ = lean_float_of_nat(v___x_1684_);
v___x_1687_ = lean_box_float(v___x_1685_);
v___x_1688_ = lean_box_float(v___x_1686_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1687_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v_a_1683_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
lean_inc_ref(v___y_1682_);
lean_inc(v_trace_956_);
v___x_1691_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1680_, v___y_1682_, v___y_1679_, v___y_1675_, v___y_1681_, v___f_1284_, v___x_1690_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1090_ = v___y_1673_;
v___y_1091_ = v___y_1676_;
v___y_1092_ = v___y_1678_;
v___y_1093_ = v___y_1677_;
v___y_1094_ = v___y_1679_;
v___y_1095_ = v___y_1680_;
v___y_1096_ = v___y_1682_;
v___y_1097_ = v___x_1691_;
goto v___jp_1089_;
}
v___jp_1692_:
{
lean_object* v___x_1704_; double v___x_1705_; double v___x_1706_; double v___x_1707_; double v___x_1708_; double v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1704_ = lean_io_mono_nanos_now();
v___x_1705_ = lean_float_of_nat(v___y_1700_);
v___x_1706_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1707_ = lean_float_div(v___x_1705_, v___x_1706_);
v___x_1708_ = lean_float_of_nat(v___x_1704_);
v___x_1709_ = lean_float_div(v___x_1708_, v___x_1706_);
v___x_1710_ = lean_box_float(v___x_1707_);
v___x_1711_ = lean_box_float(v___x_1709_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1710_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_a_1703_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
lean_inc_ref(v___y_1702_);
lean_inc(v_trace_956_);
v___x_1714_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1699_, v___y_1702_, v___y_1698_, v___y_1694_, v___y_1701_, v___f_1200_, v___x_1713_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1090_ = v___y_1693_;
v___y_1091_ = v___y_1695_;
v___y_1092_ = v___y_1697_;
v___y_1093_ = v___y_1696_;
v___y_1094_ = v___y_1698_;
v___y_1095_ = v___y_1699_;
v___y_1096_ = v___y_1702_;
v___y_1097_ = v___x_1714_;
goto v___jp_1089_;
}
v___jp_1715_:
{
lean_object* v___x_1727_; double v___x_1728_; double v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1727_ = lean_io_get_num_heartbeats();
v___x_1728_ = lean_float_of_nat(v___y_1723_);
v___x_1729_ = lean_float_of_nat(v___x_1727_);
v___x_1730_ = lean_box_float(v___x_1728_);
v___x_1731_ = lean_box_float(v___x_1729_);
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v_a_1726_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
lean_inc_ref(v___y_1725_);
lean_inc(v_trace_956_);
v___x_1734_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1722_, v___y_1725_, v___y_1721_, v___y_1717_, v___y_1724_, v___f_1200_, v___x_1733_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1090_ = v___y_1716_;
v___y_1091_ = v___y_1718_;
v___y_1092_ = v___y_1720_;
v___y_1093_ = v___y_1719_;
v___y_1094_ = v___y_1721_;
v___y_1095_ = v___y_1722_;
v___y_1096_ = v___y_1725_;
v___y_1097_ = v___x_1734_;
goto v___jp_1089_;
}
v___jp_1735_:
{
lean_object* v___x_1748_; 
v___x_1748_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
if (v___y_1740_ == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref(v___x_1748_);
v___x_1750_ = lean_io_mono_nanos_now();
lean_inc(v_trace_956_);
v___x_1751_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1739_, v___y_1741_, v___y_1743_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set_tag(v___x_1754_, 1);
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
v___y_1693_ = v___y_1742_;
v___y_1694_ = v___y_1736_;
v___y_1695_ = v___y_1744_;
v___y_1696_ = v___y_1737_;
v___y_1697_ = v___y_1745_;
v___y_1698_ = v___y_1746_;
v___y_1699_ = v___y_1738_;
v___y_1700_ = v___x_1750_;
v___y_1701_ = v_a_1749_;
v___y_1702_ = v___y_1747_;
v_a_1703_ = v___x_1757_;
goto v___jp_1692_;
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
v_a_1760_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1751_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1751_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 0);
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
v___y_1693_ = v___y_1742_;
v___y_1694_ = v___y_1736_;
v___y_1695_ = v___y_1744_;
v___y_1696_ = v___y_1737_;
v___y_1697_ = v___y_1745_;
v___y_1698_ = v___y_1746_;
v___y_1699_ = v___y_1738_;
v___y_1700_ = v___x_1750_;
v___y_1701_ = v_a_1749_;
v___y_1702_ = v___y_1747_;
v_a_1703_ = v___x_1765_;
goto v___jp_1692_;
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_a_1768_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1748_);
v___x_1769_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_956_);
v___x_1770_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1739_, v___y_1741_, v___y_1743_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set_tag(v___x_1773_, 1);
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
v___y_1716_ = v___y_1742_;
v___y_1717_ = v___y_1736_;
v___y_1718_ = v___y_1744_;
v___y_1719_ = v___y_1737_;
v___y_1720_ = v___y_1745_;
v___y_1721_ = v___y_1746_;
v___y_1722_ = v___y_1738_;
v___y_1723_ = v___x_1769_;
v___y_1724_ = v_a_1768_;
v___y_1725_ = v___y_1747_;
v_a_1726_ = v___x_1776_;
goto v___jp_1715_;
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_a_1779_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1770_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1770_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set_tag(v___x_1781_, 0);
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
v___y_1716_ = v___y_1742_;
v___y_1717_ = v___y_1736_;
v___y_1718_ = v___y_1744_;
v___y_1719_ = v___y_1737_;
v___y_1720_ = v___y_1745_;
v___y_1721_ = v___y_1746_;
v___y_1722_ = v___y_1738_;
v___y_1723_ = v___x_1769_;
v___y_1724_ = v_a_1768_;
v___y_1725_ = v___y_1747_;
v_a_1726_ = v___x_1784_;
goto v___jp_1715_;
}
}
}
}
}
v___jp_1787_:
{
lean_object* v___x_1795_; double v___x_1796_; double v___x_1797_; double v___x_1798_; double v___x_1799_; double v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1795_ = lean_io_mono_nanos_now();
v___x_1796_ = lean_float_of_nat(v___y_1788_);
v___x_1797_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1798_ = lean_float_div(v___x_1796_, v___x_1797_);
v___x_1799_ = lean_float_of_nat(v___x_1795_);
v___x_1800_ = lean_float_div(v___x_1799_, v___x_1797_);
v___x_1801_ = lean_box_float(v___x_1798_);
v___x_1802_ = lean_box_float(v___x_1800_);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1801_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v_a_1794_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
lean_inc_ref(v___y_1793_);
v___x_1805_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1792_, v___y_1793_, v___y_1791_, v___y_1789_, v___y_1790_, v___f_1320_, v___x_1804_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1805_;
}
v___jp_1806_:
{
lean_object* v___x_1814_; double v___x_1815_; double v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1814_ = lean_io_get_num_heartbeats();
v___x_1815_ = lean_float_of_nat(v___y_1811_);
v___x_1816_ = lean_float_of_nat(v___x_1814_);
v___x_1817_ = lean_box_float(v___x_1815_);
v___x_1818_ = lean_box_float(v___x_1816_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1817_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1820_, 0, v_a_1813_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
lean_inc_ref(v___y_1812_);
v___x_1821_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1810_, v___y_1812_, v___y_1809_, v___y_1807_, v___y_1808_, v___f_1320_, v___x_1820_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1821_;
}
v___jp_1822_:
{
lean_object* v___x_1830_; lean_object* v_a_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1830_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1830_);
v___x_1832_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1833_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1825_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_io_mono_nanos_now();
lean_inc(v_trace_956_);
v___x_1835_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1823_, v___y_1828_, v___y_1827_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set_tag(v___x_1838_, 1);
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
v___y_1788_ = v___x_1834_;
v___y_1789_ = v___y_1824_;
v___y_1790_ = v_a_1831_;
v___y_1791_ = v___y_1825_;
v___y_1792_ = v___y_1826_;
v___y_1793_ = v___y_1829_;
v_a_1794_ = v___x_1841_;
goto v___jp_1787_;
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
v_a_1844_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1835_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1835_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set_tag(v___x_1846_, 0);
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
v___y_1788_ = v___x_1834_;
v___y_1789_ = v___y_1824_;
v___y_1790_ = v_a_1831_;
v___y_1791_ = v___y_1825_;
v___y_1792_ = v___y_1826_;
v___y_1793_ = v___y_1829_;
v_a_1794_ = v___x_1849_;
goto v___jp_1787_;
}
}
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_956_);
v___x_1853_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1823_, v___y_1828_, v___y_1827_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set_tag(v___x_1856_, 1);
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
v___y_1807_ = v___y_1824_;
v___y_1808_ = v_a_1831_;
v___y_1809_ = v___y_1825_;
v___y_1810_ = v___y_1826_;
v___y_1811_ = v___x_1852_;
v___y_1812_ = v___y_1829_;
v_a_1813_ = v___x_1859_;
goto v___jp_1806_;
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1862_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1853_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1853_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 0);
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
v___y_1807_ = v___y_1824_;
v___y_1808_ = v_a_1831_;
v___y_1809_ = v___y_1825_;
v___y_1810_ = v___y_1826_;
v___y_1811_ = v___x_1852_;
v___y_1812_ = v___y_1829_;
v_a_1813_ = v___x_1867_;
goto v___jp_1806_;
}
}
}
}
}
v___jp_1872_:
{
lean_object* v___x_1878_; lean_object* v_a_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1878_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1881_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1874_, v___x_1880_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_io_mono_nanos_now();
lean_inc(v_trace_956_);
v___x_1883_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v_n_1871_, v___y_1876_, v_acc_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 1);
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
v___y_1286_ = v___y_1873_;
v___y_1287_ = v___y_1874_;
v___y_1288_ = v_a_1879_;
v___y_1289_ = v___x_1882_;
v___y_1290_ = v___y_1875_;
v___y_1291_ = v___y_1877_;
v_a_1292_ = v___x_1889_;
goto v___jp_1285_;
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
v_a_1892_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1883_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1883_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set_tag(v___x_1894_, 0);
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
v___y_1286_ = v___y_1873_;
v___y_1287_ = v___y_1874_;
v___y_1288_ = v_a_1879_;
v___y_1289_ = v___x_1882_;
v___y_1290_ = v___y_1875_;
v___y_1291_ = v___y_1877_;
v_a_1292_ = v___x_1897_;
goto v___jp_1285_;
}
}
}
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_956_);
v___x_1901_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v_n_1871_, v___y_1876_, v_acc_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 1);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v___y_1305_ = v___x_1900_;
v___y_1306_ = v___y_1873_;
v___y_1307_ = v___y_1874_;
v___y_1308_ = v_a_1879_;
v___y_1309_ = v___y_1875_;
v___y_1310_ = v___y_1877_;
v_a_1311_ = v___x_1907_;
goto v___jp_1304_;
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_a_1910_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1901_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1901_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set_tag(v___x_1912_, 0);
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
v___y_1305_ = v___x_1900_;
v___y_1306_ = v___y_1873_;
v___y_1307_ = v___y_1874_;
v___y_1308_ = v_a_1879_;
v___y_1309_ = v___y_1875_;
v___y_1310_ = v___y_1877_;
v_a_1311_ = v___x_1915_;
goto v___jp_1304_;
}
}
}
}
}
v___jp_1918_:
{
if (v___y_1928_ == 0)
{
lean_object* v___x_1929_; 
lean_dec_ref(v___y_1925_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v___y_1920_);
v___x_1929_ = lean_apply_6(v___y_1927_, v___y_1920_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
if (lean_obj_tag(v_a_1930_) == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1931_ = lean_nat_add(v_n_1871_, v_one_1870_);
lean_dec(v_n_1871_);
v___x_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___y_1920_);
lean_ctor_set(v___x_1932_, 1, v_acc_961_);
v___x_1933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_956_);
v___x_1934_ = l_Lean_Name_append(v___x_1933_, v_trace_956_);
v___x_1935_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1924_, v___y_1921_, v___x_1934_);
lean_dec(v___x_1934_);
if (v___x_1935_ == 0)
{
if (v___y_1919_ == 0)
{
v_n_959_ = v___x_1931_;
v_curr_960_ = v___y_1923_;
v_acc_961_ = v___x_1932_;
goto _start;
}
else
{
v___y_1237_ = v___x_1931_;
v___y_1238_ = v___x_1932_;
v___y_1239_ = v___x_1935_;
v___y_1240_ = v___y_1921_;
v___y_1241_ = v___y_1922_;
v___y_1242_ = v___y_1923_;
v___y_1243_ = v___y_1926_;
goto v___jp_1236_;
}
}
else
{
v___y_1237_ = v___x_1931_;
v___y_1238_ = v___x_1932_;
v___y_1239_ = v___x_1935_;
v___y_1240_ = v___y_1921_;
v___y_1241_ = v___y_1922_;
v___y_1242_ = v___y_1923_;
v___y_1243_ = v___y_1926_;
goto v___jp_1236_;
}
}
else
{
lean_object* v_val_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
lean_dec(v___y_1920_);
v_val_1937_ = lean_ctor_get(v_a_1930_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v_a_1930_, 1);
v___x_1938_ = l_List_appendTR___redArg(v_val_1937_, v___y_1923_);
v___x_1939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_956_);
v___x_1940_ = l_Lean_Name_append(v___x_1939_, v_trace_956_);
v___x_1941_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1924_, v___y_1921_, v___x_1940_);
lean_dec(v___x_1940_);
if (v___x_1941_ == 0)
{
if (v___y_1919_ == 0)
{
v_n_959_ = v_n_1871_;
v_curr_960_ = v___x_1938_;
goto _start;
}
else
{
v___y_1873_ = v___x_1941_;
v___y_1874_ = v___y_1921_;
v___y_1875_ = v___y_1922_;
v___y_1876_ = v___x_1938_;
v___y_1877_ = v___y_1926_;
goto v___jp_1872_;
}
}
else
{
v___y_1873_ = v___x_1941_;
v___y_1874_ = v___y_1921_;
v___y_1875_ = v___y_1922_;
v___y_1876_ = v___x_1938_;
v___y_1877_ = v___y_1926_;
goto v___jp_1872_;
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v___y_1923_);
lean_dec(v___y_1920_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
v_a_1943_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1929_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1929_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1923_);
lean_dec(v___y_1920_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
return v___y_1925_;
}
}
v___jp_1951_:
{
lean_object* v___x_1962_; 
v___x_1962_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
if (v___y_1960_ == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref(v___x_1962_);
v___x_1964_ = lean_io_mono_nanos_now();
lean_inc(v_trace_956_);
v___x_1965_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v_n_1871_, v___y_1955_, v_acc_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1965_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1965_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
lean_ctor_set_tag(v___x_1968_, 1);
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
v___y_1650_ = v___y_1952_;
v___y_1651_ = v___x_1964_;
v___y_1652_ = v___y_1953_;
v___y_1653_ = v___y_1954_;
v___y_1654_ = v___y_1958_;
v___y_1655_ = v___y_1957_;
v___y_1656_ = v___y_1956_;
v___y_1657_ = v___y_1959_;
v___y_1658_ = v_a_1963_;
v___y_1659_ = v___y_1961_;
v_a_1660_ = v___x_1971_;
goto v___jp_1649_;
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
v_a_1974_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1965_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1965_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set_tag(v___x_1976_, 0);
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
v___y_1650_ = v___y_1952_;
v___y_1651_ = v___x_1964_;
v___y_1652_ = v___y_1953_;
v___y_1653_ = v___y_1954_;
v___y_1654_ = v___y_1958_;
v___y_1655_ = v___y_1957_;
v___y_1656_ = v___y_1956_;
v___y_1657_ = v___y_1959_;
v___y_1658_ = v_a_1963_;
v___y_1659_ = v___y_1961_;
v_a_1660_ = v___x_1979_;
goto v___jp_1649_;
}
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_a_1982_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1982_);
lean_dec_ref(v___x_1962_);
v___x_1983_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_956_);
v___x_1984_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v_n_1871_, v___y_1955_, v_acc_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1984_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 1);
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
v___y_1673_ = v___y_1952_;
v___y_1674_ = v___x_1983_;
v___y_1675_ = v___y_1953_;
v___y_1676_ = v___y_1954_;
v___y_1677_ = v___y_1958_;
v___y_1678_ = v___y_1957_;
v___y_1679_ = v___y_1956_;
v___y_1680_ = v___y_1959_;
v___y_1681_ = v_a_1982_;
v___y_1682_ = v___y_1961_;
v_a_1683_ = v___x_1990_;
goto v___jp_1672_;
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
v_a_1993_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1984_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1984_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set_tag(v___x_1995_, 0);
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
v___y_1673_ = v___y_1952_;
v___y_1674_ = v___x_1983_;
v___y_1675_ = v___y_1953_;
v___y_1676_ = v___y_1954_;
v___y_1677_ = v___y_1958_;
v___y_1678_ = v___y_1957_;
v___y_1679_ = v___y_1956_;
v___y_1680_ = v___y_1959_;
v___y_1681_ = v_a_1982_;
v___y_1682_ = v___y_1961_;
v_a_1683_ = v___x_1998_;
goto v___jp_1672_;
}
}
}
}
}
v___jp_2001_:
{
if (v___y_2015_ == 0)
{
lean_object* v___x_2016_; 
lean_dec_ref(v___y_2006_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v___y_2009_);
v___x_2016_ = lean_apply_6(v___y_2007_, v___y_2009_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
if (lean_obj_tag(v_a_2017_) == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2018_ = lean_nat_add(v_n_1871_, v_one_1870_);
lean_dec(v_n_1871_);
v___x_2019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___y_2009_);
lean_ctor_set(v___x_2019_, 1, v_acc_961_);
v___x_2020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_956_);
v___x_2021_ = l_Lean_Name_append(v___x_2020_, v_trace_956_);
v___x_2022_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2013_, v___y_2011_, v___x_2021_);
lean_dec(v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = l_Lean_trace_profiler;
v___x_2024_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2011_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; 
lean_inc(v_trace_956_);
v___x_2025_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___x_2018_, v___y_2005_, v___x_2019_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1090_ = v___y_2008_;
v___y_1091_ = v___y_2010_;
v___y_1092_ = v___y_2012_;
v___y_1093_ = v___y_2002_;
v___y_1094_ = v___y_2011_;
v___y_1095_ = v___y_2003_;
v___y_1096_ = v___y_2014_;
v___y_1097_ = v___x_2025_;
goto v___jp_1089_;
}
else
{
v___y_1736_ = v___x_2022_;
v___y_1737_ = v___y_2002_;
v___y_1738_ = v___y_2003_;
v___y_1739_ = v___x_2018_;
v___y_1740_ = v___y_2004_;
v___y_1741_ = v___y_2005_;
v___y_1742_ = v___y_2008_;
v___y_1743_ = v___x_2019_;
v___y_1744_ = v___y_2010_;
v___y_1745_ = v___y_2012_;
v___y_1746_ = v___y_2011_;
v___y_1747_ = v___y_2014_;
goto v___jp_1735_;
}
}
else
{
v___y_1736_ = v___x_2022_;
v___y_1737_ = v___y_2002_;
v___y_1738_ = v___y_2003_;
v___y_1739_ = v___x_2018_;
v___y_1740_ = v___y_2004_;
v___y_1741_ = v___y_2005_;
v___y_1742_ = v___y_2008_;
v___y_1743_ = v___x_2019_;
v___y_1744_ = v___y_2010_;
v___y_1745_ = v___y_2012_;
v___y_1746_ = v___y_2011_;
v___y_1747_ = v___y_2014_;
goto v___jp_1735_;
}
}
else
{
lean_object* v_val_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
lean_dec(v___y_2009_);
v_val_2026_ = lean_ctor_get(v_a_2017_, 0);
lean_inc(v_val_2026_);
lean_dec_ref_known(v_a_2017_, 1);
v___x_2027_ = l_List_appendTR___redArg(v_val_2026_, v___y_2005_);
v___x_2028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_956_);
v___x_2029_ = l_Lean_Name_append(v___x_2028_, v_trace_956_);
v___x_2030_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2013_, v___y_2011_, v___x_2029_);
lean_dec(v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = l_Lean_trace_profiler;
v___x_2032_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2011_, v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; 
lean_inc(v_trace_956_);
v___x_2033_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v_n_1871_, v___x_2027_, v_acc_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1090_ = v___y_2008_;
v___y_1091_ = v___y_2010_;
v___y_1092_ = v___y_2012_;
v___y_1093_ = v___y_2002_;
v___y_1094_ = v___y_2011_;
v___y_1095_ = v___y_2003_;
v___y_1096_ = v___y_2014_;
v___y_1097_ = v___x_2033_;
goto v___jp_1089_;
}
else
{
v___y_1952_ = v___y_2008_;
v___y_1953_ = v___x_2030_;
v___y_1954_ = v___y_2010_;
v___y_1955_ = v___x_2027_;
v___y_1956_ = v___y_2011_;
v___y_1957_ = v___y_2012_;
v___y_1958_ = v___y_2002_;
v___y_1959_ = v___y_2003_;
v___y_1960_ = v___y_2004_;
v___y_1961_ = v___y_2014_;
goto v___jp_1951_;
}
}
else
{
v___y_1952_ = v___y_2008_;
v___y_1953_ = v___x_2030_;
v___y_1954_ = v___y_2010_;
v___y_1955_ = v___x_2027_;
v___y_1956_ = v___y_2011_;
v___y_1957_ = v___y_2012_;
v___y_1958_ = v___y_2002_;
v___y_1959_ = v___y_2003_;
v___y_1960_ = v___y_2004_;
v___y_1961_ = v___y_2014_;
goto v___jp_1951_;
}
}
}
else
{
lean_object* v_a_2034_; 
lean_dec(v___y_2009_);
lean_dec(v___y_2005_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec_ref(v_cfg_955_);
v_a_2034_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2016_, 1);
v___y_1080_ = v___y_2008_;
v___y_1081_ = v___y_2010_;
v___y_1082_ = v___y_2011_;
v___y_1083_ = v___y_2002_;
v___y_1084_ = v___y_2012_;
v___y_1085_ = v___y_2003_;
v___y_1086_ = v___y_2014_;
v_a_1087_ = v_a_2034_;
goto v___jp_1079_;
}
}
else
{
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2005_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec_ref(v_cfg_955_);
v___y_1080_ = v___y_2008_;
v___y_1081_ = v___y_2010_;
v___y_1082_ = v___y_2011_;
v___y_1083_ = v___y_2002_;
v___y_1084_ = v___y_2012_;
v___y_1085_ = v___y_2003_;
v___y_1086_ = v___y_2014_;
v_a_1087_ = v___y_2006_;
goto v___jp_1079_;
}
}
v___jp_2035_:
{
lean_object* v___x_2046_; 
v___x_2046_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
if (v___y_2043_ == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref(v___x_2046_);
v___x_2048_ = lean_io_mono_nanos_now();
lean_inc(v_trace_956_);
v___x_2049_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v_n_1871_, v___y_2042_, v_acc_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set_tag(v___x_2052_, 1);
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
v___y_1532_ = v___y_2036_;
v___y_1533_ = v___x_2048_;
v___y_1534_ = v___y_2039_;
v___y_1535_ = v___y_2038_;
v___y_1536_ = v___y_2037_;
v___y_1537_ = v___y_2041_;
v___y_1538_ = v___y_2040_;
v___y_1539_ = v___y_2044_;
v___y_1540_ = v_a_2047_;
v___y_1541_ = v___y_2045_;
v_a_1542_ = v___x_2055_;
goto v___jp_1531_;
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
v_a_2058_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2049_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2049_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set_tag(v___x_2060_, 0);
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
v___y_1532_ = v___y_2036_;
v___y_1533_ = v___x_2048_;
v___y_1534_ = v___y_2039_;
v___y_1535_ = v___y_2038_;
v___y_1536_ = v___y_2037_;
v___y_1537_ = v___y_2041_;
v___y_1538_ = v___y_2040_;
v___y_1539_ = v___y_2044_;
v___y_1540_ = v_a_2047_;
v___y_1541_ = v___y_2045_;
v_a_1542_ = v___x_2063_;
goto v___jp_1531_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v_a_2066_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2066_);
lean_dec_ref(v___x_2046_);
v___x_2067_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_956_);
v___x_2068_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v_n_1871_, v___y_2042_, v_acc_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set_tag(v___x_2071_, 1);
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
v___y_1512_ = v___y_2036_;
v___y_1513_ = v___x_2067_;
v___y_1514_ = v___y_2039_;
v___y_1515_ = v___y_2038_;
v___y_1516_ = v___y_2037_;
v___y_1517_ = v___y_2041_;
v___y_1518_ = v___y_2040_;
v___y_1519_ = v___y_2044_;
v___y_1520_ = v_a_2066_;
v___y_1521_ = v___y_2045_;
v_a_1522_ = v___x_2074_;
goto v___jp_1511_;
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
v_a_2077_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2068_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2068_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 0);
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
v___y_1512_ = v___y_2036_;
v___y_1513_ = v___x_2067_;
v___y_1514_ = v___y_2039_;
v___y_1515_ = v___y_2038_;
v___y_1516_ = v___y_2037_;
v___y_1517_ = v___y_2041_;
v___y_1518_ = v___y_2040_;
v___y_1519_ = v___y_2044_;
v___y_1520_ = v_a_2066_;
v___y_1521_ = v___y_2045_;
v_a_1522_ = v___x_2082_;
goto v___jp_1511_;
}
}
}
}
}
v___jp_2085_:
{
if (v___y_2099_ == 0)
{
lean_object* v___x_2100_; 
lean_dec_ref(v___y_2090_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v___y_2094_);
v___x_2100_ = lean_apply_6(v___y_2092_, v___y_2094_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
if (lean_obj_tag(v_a_2101_) == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2102_ = lean_nat_add(v_n_1871_, v_one_1870_);
lean_dec(v_n_1871_);
v___x_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___y_2094_);
lean_ctor_set(v___x_2103_, 1, v_acc_961_);
v___x_2104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_956_);
v___x_2105_ = l_Lean_Name_append(v___x_2104_, v_trace_956_);
v___x_2106_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2097_, v___y_2095_, v___x_2105_);
lean_dec(v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = l_Lean_trace_profiler;
v___x_2108_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2095_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; 
lean_inc(v_trace_956_);
v___x_2109_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___x_2102_, v___y_2089_, v___x_2103_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1141_ = v___y_2093_;
v___y_1142_ = v___y_2096_;
v___y_1143_ = v___y_2086_;
v___y_1144_ = v___y_2095_;
v___y_1145_ = v___y_2087_;
v___y_1146_ = v___y_2091_;
v___y_1147_ = v___y_2098_;
v___y_1148_ = v___x_2109_;
goto v___jp_1140_;
}
else
{
v___y_1460_ = v___x_2102_;
v___y_1461_ = v___y_2086_;
v___y_1462_ = v___y_2087_;
v___y_1463_ = v___y_2088_;
v___y_1464_ = v___y_2089_;
v___y_1465_ = v___y_2091_;
v___y_1466_ = v___y_2093_;
v___y_1467_ = v___x_2106_;
v___y_1468_ = v___x_2103_;
v___y_1469_ = v___y_2096_;
v___y_1470_ = v___y_2095_;
v___y_1471_ = v___y_2098_;
goto v___jp_1459_;
}
}
else
{
v___y_1460_ = v___x_2102_;
v___y_1461_ = v___y_2086_;
v___y_1462_ = v___y_2087_;
v___y_1463_ = v___y_2088_;
v___y_1464_ = v___y_2089_;
v___y_1465_ = v___y_2091_;
v___y_1466_ = v___y_2093_;
v___y_1467_ = v___x_2106_;
v___y_1468_ = v___x_2103_;
v___y_1469_ = v___y_2096_;
v___y_1470_ = v___y_2095_;
v___y_1471_ = v___y_2098_;
goto v___jp_1459_;
}
}
else
{
lean_object* v_val_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
lean_dec(v___y_2094_);
v_val_2110_ = lean_ctor_get(v_a_2101_, 0);
lean_inc(v_val_2110_);
lean_dec_ref_known(v_a_2101_, 1);
v___x_2111_ = l_List_appendTR___redArg(v_val_2110_, v___y_2089_);
v___x_2112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_956_);
v___x_2113_ = l_Lean_Name_append(v___x_2112_, v_trace_956_);
v___x_2114_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2097_, v___y_2095_, v___x_2113_);
lean_dec(v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = l_Lean_trace_profiler;
v___x_2116_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2095_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; 
lean_inc(v_trace_956_);
v___x_2117_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v_n_1871_, v___x_2111_, v_acc_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1141_ = v___y_2093_;
v___y_1142_ = v___y_2096_;
v___y_1143_ = v___y_2086_;
v___y_1144_ = v___y_2095_;
v___y_1145_ = v___y_2087_;
v___y_1146_ = v___y_2091_;
v___y_1147_ = v___y_2098_;
v___y_1148_ = v___x_2117_;
goto v___jp_1140_;
}
else
{
v___y_2036_ = v___y_2093_;
v___y_2037_ = v___y_2095_;
v___y_2038_ = v___y_2096_;
v___y_2039_ = v___y_2086_;
v___y_2040_ = v___y_2087_;
v___y_2041_ = v___x_2114_;
v___y_2042_ = v___x_2111_;
v___y_2043_ = v___y_2088_;
v___y_2044_ = v___y_2091_;
v___y_2045_ = v___y_2098_;
goto v___jp_2035_;
}
}
else
{
v___y_2036_ = v___y_2093_;
v___y_2037_ = v___y_2095_;
v___y_2038_ = v___y_2096_;
v___y_2039_ = v___y_2086_;
v___y_2040_ = v___y_2087_;
v___y_2041_ = v___x_2114_;
v___y_2042_ = v___x_2111_;
v___y_2043_ = v___y_2088_;
v___y_2044_ = v___y_2091_;
v___y_2045_ = v___y_2098_;
goto v___jp_2035_;
}
}
}
else
{
lean_object* v_a_2118_; 
lean_dec(v___y_2094_);
lean_dec(v___y_2089_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec_ref(v_cfg_955_);
v_a_2118_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2100_, 1);
v___y_1131_ = v___y_2093_;
v___y_1132_ = v___y_2095_;
v___y_1133_ = v___y_2086_;
v___y_1134_ = v___y_2096_;
v___y_1135_ = v___y_2087_;
v___y_1136_ = v___y_2091_;
v___y_1137_ = v___y_2098_;
v_a_1138_ = v_a_2118_;
goto v___jp_1130_;
}
}
else
{
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2089_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec_ref(v_cfg_955_);
v___y_1131_ = v___y_2093_;
v___y_1132_ = v___y_2095_;
v___y_1133_ = v___y_2086_;
v___y_1134_ = v___y_2096_;
v___y_1135_ = v___y_2087_;
v___y_1136_ = v___y_2091_;
v___y_1137_ = v___y_2098_;
v_a_1138_ = v___y_2090_;
goto v___jp_1130_;
}
}
v___jp_2119_:
{
lean_object* v___x_2132_; lean_object* v_a_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2132_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2132_);
v___x_2134_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2135_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2128_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_dec_ref(v___y_2123_);
v___x_2136_ = lean_io_mono_nanos_now();
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v___y_2127_);
v___x_2137_ = lean_apply_6(v___y_2120_, v___y_2127_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; uint8_t v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = lean_unbox(v_a_2138_);
lean_dec(v_a_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
lean_inc_ref(v_next_957_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v___y_2127_);
v___x_2140_ = lean_apply_7(v_next_957_, v___y_2127_, v___y_2131_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; 
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec_ref(v_cfg_955_);
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___y_1121_ = v___y_2126_;
v___y_1122_ = v___y_2128_;
v___y_1123_ = v___y_2121_;
v___y_1124_ = v_a_2133_;
v___y_1125_ = v___y_2122_;
v___y_1126_ = v___x_2136_;
v___y_1127_ = v___y_2130_;
v_a_1128_ = v_a_2141_;
goto v___jp_1120_;
}
else
{
lean_object* v_a_2142_; uint8_t v___x_2143_; 
v_a_2142_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2143_ = l_Lean_Exception_isInterrupt(v_a_2142_);
if (v___x_2143_ == 0)
{
uint8_t v___x_2144_; 
lean_inc(v_a_2142_);
v___x_2144_ = l_Lean_Exception_isRuntime(v_a_2142_);
v___y_2086_ = v___y_2121_;
v___y_2087_ = v___y_2122_;
v___y_2088_ = v___x_2135_;
v___y_2089_ = v___y_2124_;
v___y_2090_ = v_a_2142_;
v___y_2091_ = v___x_2136_;
v___y_2092_ = v___y_2125_;
v___y_2093_ = v___y_2126_;
v___y_2094_ = v___y_2127_;
v___y_2095_ = v___y_2128_;
v___y_2096_ = v_a_2133_;
v___y_2097_ = v___y_2129_;
v___y_2098_ = v___y_2130_;
v___y_2099_ = v___x_2144_;
goto v___jp_2085_;
}
else
{
v___y_2086_ = v___y_2121_;
v___y_2087_ = v___y_2122_;
v___y_2088_ = v___x_2135_;
v___y_2089_ = v___y_2124_;
v___y_2090_ = v_a_2142_;
v___y_2091_ = v___x_2136_;
v___y_2092_ = v___y_2125_;
v___y_2093_ = v___y_2126_;
v___y_2094_ = v___y_2127_;
v___y_2095_ = v___y_2128_;
v___y_2096_ = v_a_2133_;
v___y_2097_ = v___y_2129_;
v___y_2098_ = v___y_2130_;
v___y_2099_ = v___x_2143_;
goto v___jp_2085_;
}
}
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
lean_dec_ref(v___y_2131_);
lean_dec_ref(v___y_2125_);
v___x_2145_ = lean_nat_add(v_n_1871_, v_one_1870_);
lean_dec(v_n_1871_);
v___x_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___y_2127_);
lean_ctor_set(v___x_2146_, 1, v_acc_961_);
v___x_2147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_956_);
v___x_2148_ = l_Lean_Name_append(v___x_2147_, v_trace_956_);
v___x_2149_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2129_, v___y_2128_, v___x_2148_);
lean_dec(v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = l_Lean_trace_profiler;
v___x_2151_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2128_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; 
lean_inc(v_trace_956_);
v___x_2152_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___x_2145_, v___y_2124_, v___x_2146_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1141_ = v___y_2126_;
v___y_1142_ = v_a_2133_;
v___y_1143_ = v___y_2121_;
v___y_1144_ = v___y_2128_;
v___y_1145_ = v___y_2122_;
v___y_1146_ = v___x_2136_;
v___y_1147_ = v___y_2130_;
v___y_1148_ = v___x_2152_;
goto v___jp_1140_;
}
else
{
v___y_1598_ = v___x_2145_;
v___y_1599_ = v___y_2121_;
v___y_1600_ = v___y_2122_;
v___y_1601_ = v___x_2135_;
v___y_1602_ = v___y_2124_;
v___y_1603_ = v___x_2136_;
v___y_1604_ = v___y_2126_;
v___y_1605_ = v___x_2149_;
v___y_1606_ = v_a_2133_;
v___y_1607_ = v___y_2128_;
v___y_1608_ = v___x_2146_;
v___y_1609_ = v___y_2130_;
goto v___jp_1597_;
}
}
else
{
v___y_1598_ = v___x_2145_;
v___y_1599_ = v___y_2121_;
v___y_1600_ = v___y_2122_;
v___y_1601_ = v___x_2135_;
v___y_1602_ = v___y_2124_;
v___y_1603_ = v___x_2136_;
v___y_1604_ = v___y_2126_;
v___y_1605_ = v___x_2149_;
v___y_1606_ = v_a_2133_;
v___y_1607_ = v___y_2128_;
v___y_1608_ = v___x_2146_;
v___y_1609_ = v___y_2130_;
goto v___jp_1597_;
}
}
}
else
{
lean_object* v_a_2153_; 
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec_ref(v_cfg_955_);
v_a_2153_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2137_, 1);
v___y_1131_ = v___y_2126_;
v___y_1132_ = v___y_2128_;
v___y_1133_ = v___y_2121_;
v___y_1134_ = v_a_2133_;
v___y_1135_ = v___y_2122_;
v___y_1136_ = v___x_2136_;
v___y_1137_ = v___y_2130_;
v_a_1138_ = v_a_2153_;
goto v___jp_1130_;
}
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec_ref(v___y_2131_);
v___x_2154_ = lean_io_get_num_heartbeats();
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v___y_2127_);
v___x_2155_ = lean_apply_6(v___y_2120_, v___y_2127_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; uint8_t v___x_2157_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2155_, 1);
v___x_2157_ = lean_unbox(v_a_2156_);
lean_dec(v_a_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; 
lean_inc_ref(v_next_957_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v___y_2127_);
v___x_2158_ = lean_apply_7(v_next_957_, v___y_2127_, v___y_2123_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; 
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec_ref(v_cfg_955_);
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2158_, 1);
v___y_1070_ = v___y_2126_;
v___y_1071_ = v___x_2154_;
v___y_1072_ = v___y_2128_;
v___y_1073_ = v___y_2121_;
v___y_1074_ = v_a_2133_;
v___y_1075_ = v___y_2122_;
v___y_1076_ = v___y_2130_;
v_a_1077_ = v_a_2159_;
goto v___jp_1069_;
}
else
{
lean_object* v_a_2160_; uint8_t v___x_2161_; 
v_a_2160_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2158_, 1);
v___x_2161_ = l_Lean_Exception_isInterrupt(v_a_2160_);
if (v___x_2161_ == 0)
{
uint8_t v___x_2162_; 
lean_inc(v_a_2160_);
v___x_2162_ = l_Lean_Exception_isRuntime(v_a_2160_);
v___y_2002_ = v___y_2121_;
v___y_2003_ = v___y_2122_;
v___y_2004_ = v___x_2135_;
v___y_2005_ = v___y_2124_;
v___y_2006_ = v_a_2160_;
v___y_2007_ = v___y_2125_;
v___y_2008_ = v___y_2126_;
v___y_2009_ = v___y_2127_;
v___y_2010_ = v___x_2154_;
v___y_2011_ = v___y_2128_;
v___y_2012_ = v_a_2133_;
v___y_2013_ = v___y_2129_;
v___y_2014_ = v___y_2130_;
v___y_2015_ = v___x_2162_;
goto v___jp_2001_;
}
else
{
v___y_2002_ = v___y_2121_;
v___y_2003_ = v___y_2122_;
v___y_2004_ = v___x_2135_;
v___y_2005_ = v___y_2124_;
v___y_2006_ = v_a_2160_;
v___y_2007_ = v___y_2125_;
v___y_2008_ = v___y_2126_;
v___y_2009_ = v___y_2127_;
v___y_2010_ = v___x_2154_;
v___y_2011_ = v___y_2128_;
v___y_2012_ = v_a_2133_;
v___y_2013_ = v___y_2129_;
v___y_2014_ = v___y_2130_;
v___y_2015_ = v___x_2161_;
goto v___jp_2001_;
}
}
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
lean_dec_ref(v___y_2125_);
lean_dec_ref(v___y_2123_);
v___x_2163_ = lean_nat_add(v_n_1871_, v_one_1870_);
lean_dec(v_n_1871_);
v___x_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___y_2127_);
lean_ctor_set(v___x_2164_, 1, v_acc_961_);
v___x_2165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_956_);
v___x_2166_ = l_Lean_Name_append(v___x_2165_, v_trace_956_);
v___x_2167_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2129_, v___y_2128_, v___x_2166_);
lean_dec(v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; uint8_t v___x_2169_; 
v___x_2168_ = l_Lean_trace_profiler;
v___x_2169_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2128_, v___x_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; 
lean_inc(v_trace_956_);
v___x_2170_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___x_2163_, v___y_2124_, v___x_2164_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
v___y_1090_ = v___y_2126_;
v___y_1091_ = v___x_2154_;
v___y_1092_ = v_a_2133_;
v___y_1093_ = v___y_2121_;
v___y_1094_ = v___y_2128_;
v___y_1095_ = v___y_2122_;
v___y_1096_ = v___y_2130_;
v___y_1097_ = v___x_2170_;
goto v___jp_1089_;
}
else
{
v___y_1365_ = v___y_2121_;
v___y_1366_ = v___x_2163_;
v___y_1367_ = v___y_2122_;
v___y_1368_ = v___x_2135_;
v___y_1369_ = v___y_2124_;
v___y_1370_ = v___x_2164_;
v___y_1371_ = v___y_2126_;
v___y_1372_ = v___x_2154_;
v___y_1373_ = v___x_2167_;
v___y_1374_ = v_a_2133_;
v___y_1375_ = v___y_2128_;
v___y_1376_ = v___y_2130_;
goto v___jp_1364_;
}
}
else
{
v___y_1365_ = v___y_2121_;
v___y_1366_ = v___x_2163_;
v___y_1367_ = v___y_2122_;
v___y_1368_ = v___x_2135_;
v___y_1369_ = v___y_2124_;
v___y_1370_ = v___x_2164_;
v___y_1371_ = v___y_2126_;
v___y_1372_ = v___x_2154_;
v___y_1373_ = v___x_2167_;
v___y_1374_ = v_a_2133_;
v___y_1375_ = v___y_2128_;
v___y_1376_ = v___y_2130_;
goto v___jp_1364_;
}
}
}
else
{
lean_object* v_a_2171_; 
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec_ref(v_cfg_955_);
v_a_2171_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2155_, 1);
v___y_1080_ = v___y_2126_;
v___y_1081_ = v___x_2154_;
v___y_1082_ = v___y_2128_;
v___y_1083_ = v___y_2121_;
v___y_1084_ = v_a_2133_;
v___y_1085_ = v___y_2122_;
v___y_1086_ = v___y_2130_;
v_a_1087_ = v_a_2171_;
goto v___jp_1079_;
}
}
}
v___jp_2172_:
{
if (v___y_2177_ == 0)
{
lean_object* v___x_2178_; 
lean_dec_ref(v___y_2173_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v___y_2174_);
v___x_2178_ = lean_apply_6(v___y_2176_, v___y_2174_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
if (lean_obj_tag(v_a_2179_) == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_nat_add(v_n_1871_, v_one_1870_);
lean_dec(v_n_1871_);
v___x_2181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___y_2174_);
lean_ctor_set(v___x_2181_, 1, v_acc_961_);
v_n_959_ = v___x_2180_;
v_curr_960_ = v___y_2175_;
v_acc_961_ = v___x_2181_;
goto _start;
}
else
{
lean_object* v_val_2183_; lean_object* v___x_2184_; 
lean_dec(v___y_2174_);
v_val_2183_ = lean_ctor_get(v_a_2179_, 0);
lean_inc(v_val_2183_);
lean_dec_ref_known(v_a_2179_, 1);
v___x_2184_ = l_List_appendTR___redArg(v_val_2183_, v___y_2175_);
v_n_959_ = v_n_1871_;
v_curr_960_ = v___x_2184_;
goto _start;
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
v_a_2186_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2178_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2178_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
return v___y_2173_;
}
}
v___jp_2194_:
{
if (lean_obj_tag(v_a_2195_) == 0)
{
if (lean_obj_tag(v_curr_960_) == 0)
{
lean_object* v_toCold_2196_; lean_object* v_options_2197_; lean_object* v_inheritedTraceOptions_2198_; uint8_t v_hasTrace_2199_; lean_object* v___x_2200_; 
lean_dec(v_n_1871_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec_ref(v_cfg_955_);
v_toCold_2196_ = lean_ctor_get(v_a_964_, 0);
v_options_2197_ = lean_ctor_get(v_toCold_2196_, 2);
v_inheritedTraceOptions_2198_ = lean_ctor_get(v_toCold_2196_, 11);
v_hasTrace_2199_ = lean_ctor_get_uint8(v_options_2197_, sizeof(void*)*1);
v___x_2200_ = l_List_reverse___redArg(v_acc_961_);
if (v_hasTrace_2199_ == 0)
{
lean_object* v___x_2201_; 
lean_dec(v_trace_956_);
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_956_);
v___x_2204_ = l_Lean_Name_append(v___x_2203_, v_trace_956_);
v___x_2205_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2198_, v_options_2197_, v___x_2204_);
lean_dec(v___x_2204_);
if (v___x_2205_ == 0)
{
lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = l_Lean_trace_profiler;
v___x_2207_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2197_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; 
lean_dec(v_trace_956_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2200_);
return v___x_2208_;
}
else
{
v___y_1160_ = v_options_2197_;
v___y_1161_ = v___x_2205_;
v___y_1162_ = v_hasTrace_2199_;
v___y_1163_ = v___x_2200_;
v___y_1164_ = v___x_2202_;
goto v___jp_1159_;
}
}
else
{
v___y_1160_ = v_options_2197_;
v___y_1161_ = v___x_2205_;
v___y_1162_ = v_hasTrace_2199_;
v___y_1163_ = v___x_2200_;
v___y_1164_ = v___x_2202_;
goto v___jp_1159_;
}
}
}
else
{
lean_object* v_head_2209_; lean_object* v_tail_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2285_; 
v_head_2209_ = lean_ctor_get(v_curr_960_, 0);
v_tail_2210_ = lean_ctor_get(v_curr_960_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_curr_960_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2212_ = v_curr_960_;
v_isShared_2213_ = v_isSharedCheck_2285_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_tail_2210_);
lean_inc(v_head_2209_);
lean_dec(v_curr_960_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2285_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; lean_object* v_a_2215_; uint8_t v___x_2216_; uint8_t v___x_2217_; 
v___x_2214_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2209_, v_a_963_);
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref(v___x_2214_);
v___x_2216_ = 1;
v___x_2217_ = lean_unbox(v_a_2215_);
lean_dec(v_a_2215_);
if (v___x_2217_ == 0)
{
lean_object* v_toCold_2218_; lean_object* v_options_2219_; uint8_t v_hasTrace_2220_; 
v_toCold_2218_ = lean_ctor_get(v_a_964_, 0);
v_options_2219_ = lean_ctor_get(v_toCold_2218_, 2);
v_hasTrace_2220_ = lean_ctor_get_uint8(v_options_2219_, sizeof(void*)*1);
if (v_hasTrace_2220_ == 0)
{
lean_object* v___x_2221_; 
lean_inc_ref(v_suspend_1156_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v_head_2209_);
v___x_2221_ = lean_apply_6(v_suspend_1156_, v_head_2209_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; uint8_t v___x_2223_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v___x_2223_ = lean_unbox(v_a_2222_);
lean_dec(v_a_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___f_2224_; lean_object* v___x_2225_; 
lean_del_object(v___x_2212_);
lean_inc(v_acc_961_);
lean_inc(v_n_1871_);
lean_inc(v_goals_958_);
lean_inc_ref_n(v_next_957_, 2);
lean_inc(v_trace_956_);
lean_inc_ref(v_cfg_955_);
lean_inc(v_tail_2210_);
v___f_2224_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2224_, 0, v_tail_2210_);
lean_closure_set(v___f_2224_, 1, v_cfg_955_);
lean_closure_set(v___f_2224_, 2, v_trace_956_);
lean_closure_set(v___f_2224_, 3, v_next_957_);
lean_closure_set(v___f_2224_, 4, v_goals_958_);
lean_closure_set(v___f_2224_, 5, v_n_1871_);
lean_closure_set(v___f_2224_, 6, v_acc_961_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v_head_2209_);
v___x_2225_ = lean_apply_7(v_next_957_, v_head_2209_, v___f_2224_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_dec(v_tail_2210_);
lean_dec(v_head_2209_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
return v___x_2225_;
}
else
{
lean_object* v_a_2226_; uint8_t v___x_2227_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2226_);
v___x_2227_ = l_Lean_Exception_isInterrupt(v_a_2226_);
if (v___x_2227_ == 0)
{
uint8_t v___x_2228_; 
v___x_2228_ = l_Lean_Exception_isRuntime(v_a_2226_);
lean_inc_ref(v_discharge_1157_);
v___y_2173_ = v___x_2225_;
v___y_2174_ = v_head_2209_;
v___y_2175_ = v_tail_2210_;
v___y_2176_ = v_discharge_1157_;
v___y_2177_ = v___x_2228_;
goto v___jp_2172_;
}
else
{
lean_dec(v_a_2226_);
lean_inc_ref(v_discharge_1157_);
v___y_2173_ = v___x_2225_;
v___y_2174_ = v_head_2209_;
v___y_2175_ = v_tail_2210_;
v___y_2176_ = v_discharge_1157_;
v___y_2177_ = v___x_2227_;
goto v___jp_2172_;
}
}
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_nat_add(v_n_1871_, v_one_1870_);
lean_dec(v_n_1871_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 1, v_acc_961_);
v___x_2231_ = v___x_2212_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_head_2209_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_acc_961_);
v___x_2231_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
v_n_959_ = v___x_2229_;
v_curr_960_ = v_tail_2210_;
v_acc_961_ = v___x_2231_;
goto _start;
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_del_object(v___x_2212_);
lean_dec(v_tail_2210_);
lean_dec(v_head_2209_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
v_a_2234_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2221_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2221_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2242_; lean_object* v___f_2243_; lean_object* v___f_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v_inheritedTraceOptions_2242_ = lean_ctor_get(v_toCold_2218_, 11);
lean_inc(v_acc_961_);
lean_inc(v_n_1871_);
lean_inc(v_goals_958_);
lean_inc_ref(v_next_957_);
lean_inc_n(v_trace_956_, 2);
lean_inc_ref(v_cfg_955_);
lean_inc(v_tail_2210_);
v___f_2243_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2243_, 0, v_tail_2210_);
lean_closure_set(v___f_2243_, 1, v_cfg_955_);
lean_closure_set(v___f_2243_, 2, v_trace_956_);
lean_closure_set(v___f_2243_, 3, v_next_957_);
lean_closure_set(v___f_2243_, 4, v_goals_958_);
lean_closure_set(v___f_2243_, 5, v_n_1871_);
lean_closure_set(v___f_2243_, 6, v_acc_961_);
lean_inc(v_head_2209_);
v___f_2244_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(v___f_2244_, 0, v_head_2209_);
v___x_2245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
v___x_2247_ = l_Lean_Name_append(v___x_2246_, v_trace_956_);
v___x_2248_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2242_, v_options_2219_, v___x_2247_);
lean_dec(v___x_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = l_Lean_trace_profiler;
v___x_2250_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2219_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; 
lean_dec_ref(v___f_2244_);
lean_inc_ref(v_suspend_1156_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v_head_2209_);
v___x_2251_ = lean_apply_6(v_suspend_1156_, v_head_2209_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; uint8_t v___x_2253_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v___x_2253_ = lean_unbox(v_a_2252_);
lean_dec(v_a_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
lean_del_object(v___x_2212_);
lean_inc_ref(v_next_957_);
lean_inc(v_a_965_);
lean_inc_ref(v_a_964_);
lean_inc(v_a_963_);
lean_inc_ref(v_a_962_);
lean_inc(v_head_2209_);
v___x_2254_ = lean_apply_7(v_next_957_, v_head_2209_, v___f_2243_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, lean_box(0));
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_dec(v_tail_2210_);
lean_dec(v_head_2209_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
return v___x_2254_;
}
else
{
lean_object* v_a_2255_; uint8_t v___x_2256_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
v___x_2256_ = l_Lean_Exception_isInterrupt(v_a_2255_);
if (v___x_2256_ == 0)
{
uint8_t v___x_2257_; 
v___x_2257_ = l_Lean_Exception_isRuntime(v_a_2255_);
lean_inc_ref(v_discharge_1157_);
v___y_1919_ = v___x_2250_;
v___y_1920_ = v_head_2209_;
v___y_1921_ = v_options_2219_;
v___y_1922_ = v___x_2216_;
v___y_1923_ = v_tail_2210_;
v___y_1924_ = v_inheritedTraceOptions_2242_;
v___y_1925_ = v___x_2254_;
v___y_1926_ = v___x_2245_;
v___y_1927_ = v_discharge_1157_;
v___y_1928_ = v___x_2257_;
goto v___jp_1918_;
}
else
{
lean_dec(v_a_2255_);
lean_inc_ref(v_discharge_1157_);
v___y_1919_ = v___x_2250_;
v___y_1920_ = v_head_2209_;
v___y_1921_ = v_options_2219_;
v___y_1922_ = v___x_2216_;
v___y_1923_ = v_tail_2210_;
v___y_1924_ = v_inheritedTraceOptions_2242_;
v___y_1925_ = v___x_2254_;
v___y_1926_ = v___x_2245_;
v___y_1927_ = v_discharge_1157_;
v___y_1928_ = v___x_2256_;
goto v___jp_1918_;
}
}
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2260_; 
lean_dec_ref(v___f_2243_);
v___x_2258_ = lean_nat_add(v_n_1871_, v_one_1870_);
lean_dec(v_n_1871_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 1, v_acc_961_);
v___x_2260_ = v___x_2212_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_head_2209_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_acc_961_);
v___x_2260_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
if (v___x_2248_ == 0)
{
if (v___x_2250_ == 0)
{
v_n_959_ = v___x_2258_;
v_curr_960_ = v_tail_2210_;
v_acc_961_ = v___x_2260_;
goto _start;
}
else
{
v___y_1823_ = v___x_2258_;
v___y_1824_ = v___x_2248_;
v___y_1825_ = v_options_2219_;
v___y_1826_ = v___x_2216_;
v___y_1827_ = v___x_2260_;
v___y_1828_ = v_tail_2210_;
v___y_1829_ = v___x_2245_;
goto v___jp_1822_;
}
}
else
{
v___y_1823_ = v___x_2258_;
v___y_1824_ = v___x_2248_;
v___y_1825_ = v_options_2219_;
v___y_1826_ = v___x_2216_;
v___y_1827_ = v___x_2260_;
v___y_1828_ = v_tail_2210_;
v___y_1829_ = v___x_2245_;
goto v___jp_1822_;
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec_ref(v___f_2243_);
lean_del_object(v___x_2212_);
lean_dec(v_tail_2210_);
lean_dec(v_head_2209_);
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
v_a_2263_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2251_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2251_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_del_object(v___x_2212_);
lean_inc_ref(v_discharge_1157_);
lean_inc_ref(v___f_2243_);
lean_inc_ref(v_suspend_1156_);
v___y_2120_ = v_suspend_1156_;
v___y_2121_ = v___x_2248_;
v___y_2122_ = v___x_2216_;
v___y_2123_ = v___f_2243_;
v___y_2124_ = v_tail_2210_;
v___y_2125_ = v_discharge_1157_;
v___y_2126_ = v___f_2244_;
v___y_2127_ = v_head_2209_;
v___y_2128_ = v_options_2219_;
v___y_2129_ = v_inheritedTraceOptions_2242_;
v___y_2130_ = v___x_2245_;
v___y_2131_ = v___f_2243_;
goto v___jp_2119_;
}
}
else
{
lean_del_object(v___x_2212_);
lean_inc_ref(v_discharge_1157_);
lean_inc_ref(v___f_2243_);
lean_inc_ref(v_suspend_1156_);
v___y_2120_ = v_suspend_1156_;
v___y_2121_ = v___x_2248_;
v___y_2122_ = v___x_2216_;
v___y_2123_ = v___f_2243_;
v___y_2124_ = v_tail_2210_;
v___y_2125_ = v_discharge_1157_;
v___y_2126_ = v___f_2244_;
v___y_2127_ = v_head_2209_;
v___y_2128_ = v_options_2219_;
v___y_2129_ = v_inheritedTraceOptions_2242_;
v___y_2130_ = v___x_2245_;
v___y_2131_ = v___f_2243_;
goto v___jp_2119_;
}
}
}
else
{
lean_object* v_toCold_2271_; lean_object* v_options_2272_; lean_object* v_inheritedTraceOptions_2273_; uint8_t v_hasTrace_2274_; lean_object* v___x_2275_; 
lean_del_object(v___x_2212_);
v_toCold_2271_ = lean_ctor_get(v_a_964_, 0);
v_options_2272_ = lean_ctor_get(v_toCold_2271_, 2);
v_inheritedTraceOptions_2273_ = lean_ctor_get(v_toCold_2271_, 11);
v_hasTrace_2274_ = lean_ctor_get_uint8(v_options_2272_, sizeof(void*)*1);
v___x_2275_ = lean_nat_add(v_n_1871_, v_one_1870_);
lean_dec(v_n_1871_);
if (v_hasTrace_2274_ == 0)
{
lean_dec(v_head_2209_);
v_n_959_ = v___x_2275_;
v_curr_960_ = v_tail_2210_;
goto _start;
}
else
{
lean_object* v___f_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v___f_2277_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2277_, 0, v_head_2209_);
v___x_2278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_956_);
v___x_2280_ = l_Lean_Name_append(v___x_2279_, v_trace_956_);
v___x_2281_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2273_, v_options_2272_, v___x_2280_);
lean_dec(v___x_2280_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; uint8_t v___x_2283_; 
v___x_2282_ = l_Lean_trace_profiler;
v___x_2283_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2272_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_dec_ref(v___f_2277_);
v_n_959_ = v___x_2275_;
v_curr_960_ = v_tail_2210_;
goto _start;
}
else
{
v___y_1005_ = v___x_2278_;
v___y_1006_ = v___x_2281_;
v___y_1007_ = v___f_2277_;
v___y_1008_ = v_options_2272_;
v___y_1009_ = v___x_2216_;
v___y_1010_ = v_tail_2210_;
v___y_1011_ = v___x_2275_;
goto v___jp_1004_;
}
}
else
{
v___y_1005_ = v___x_2278_;
v___y_1006_ = v___x_2281_;
v___y_1007_ = v___f_2277_;
v___y_1008_ = v_options_2272_;
v___y_1009_ = v___x_2216_;
v___y_1010_ = v_tail_2210_;
v___y_1011_ = v___x_2275_;
goto v___jp_1004_;
}
}
}
}
}
}
else
{
lean_object* v_val_2286_; 
lean_dec(v_curr_960_);
v_val_2286_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_val_2286_);
lean_dec_ref_known(v_a_2195_, 1);
v_n_959_ = v_n_1871_;
v_curr_960_ = v_val_2286_;
goto _start;
}
}
v___jp_2288_:
{
if (lean_obj_tag(v___y_2289_) == 0)
{
lean_object* v_a_2290_; 
v_a_2290_ = lean_ctor_get(v___y_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___y_2289_, 1);
v_a_2195_ = v_a_2290_;
goto v___jp_2194_;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_n_1871_);
lean_dec(v_acc_961_);
lean_dec(v_curr_960_);
lean_dec(v_goals_958_);
lean_dec_ref(v_next_957_);
lean_dec(v_trace_956_);
lean_dec_ref(v_cfg_955_);
v_a_2291_ = lean_ctor_get(v___y_2289_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___y_2289_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___y_2289_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___y_2289_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
v___jp_967_:
{
lean_object* v___x_976_; double v___x_977_; double v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_976_ = lean_io_get_num_heartbeats();
v___x_977_ = lean_float_of_nat(v___y_972_);
v___x_978_ = lean_float_of_nat(v___x_976_);
v___x_979_ = lean_box_float(v___x_977_);
v___x_980_ = lean_box_float(v___x_978_);
v___x_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_982_, 0, v_a_975_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
lean_inc_ref(v___y_968_);
v___x_983_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_973_, v___y_968_, v___y_971_, v___y_969_, v___y_974_, v___y_970_, v___x_982_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_983_;
}
v___jp_984_:
{
lean_object* v___x_993_; double v___x_994_; double v___x_995_; double v___x_996_; double v___x_997_; double v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_993_ = lean_io_mono_nanos_now();
v___x_994_ = lean_float_of_nat(v___y_989_);
v___x_995_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_996_ = lean_float_div(v___x_994_, v___x_995_);
v___x_997_ = lean_float_of_nat(v___x_993_);
v___x_998_ = lean_float_div(v___x_997_, v___x_995_);
v___x_999_ = lean_box_float(v___x_996_);
v___x_1000_ = lean_box_float(v___x_998_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_a_992_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
lean_inc_ref(v___y_985_);
v___x_1003_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_990_, v___y_985_, v___y_988_, v___y_986_, v___y_991_, v___y_987_, v___x_1002_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1003_;
}
v___jp_1004_:
{
lean_object* v___x_1012_; lean_object* v_a_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1012_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_965_);
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref(v___x_1012_);
v___x_1014_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1015_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1008_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_io_mono_nanos_now();
lean_inc(v_trace_956_);
v___x_1017_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1011_, v___y_1010_, v_acc_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 1);
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
v___y_985_ = v___y_1005_;
v___y_986_ = v___y_1006_;
v___y_987_ = v___y_1007_;
v___y_988_ = v___y_1008_;
v___y_989_ = v___x_1016_;
v___y_990_ = v___y_1009_;
v___y_991_ = v_a_1013_;
v_a_992_ = v___x_1023_;
goto v___jp_984_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1017_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1017_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 0);
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
v___y_985_ = v___y_1005_;
v___y_986_ = v___y_1006_;
v___y_987_ = v___y_1007_;
v___y_988_ = v___y_1008_;
v___y_989_ = v___x_1016_;
v___y_990_ = v___y_1009_;
v___y_991_ = v_a_1013_;
v_a_992_ = v___x_1031_;
goto v___jp_984_;
}
}
}
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_956_);
v___x_1035_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_955_, v_trace_956_, v_next_957_, v_goals_958_, v___y_1011_, v___y_1010_, v_acc_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set_tag(v___x_1038_, 1);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
v___y_968_ = v___y_1005_;
v___y_969_ = v___y_1006_;
v___y_970_ = v___y_1007_;
v___y_971_ = v___y_1008_;
v___y_972_ = v___x_1034_;
v___y_973_ = v___y_1009_;
v___y_974_ = v_a_1013_;
v_a_975_ = v___x_1041_;
goto v___jp_967_;
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_a_1044_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1035_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1035_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 0);
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
v___y_968_ = v___y_1005_;
v___y_969_ = v___y_1006_;
v___y_970_ = v___y_1007_;
v___y_971_ = v___y_1008_;
v___y_972_ = v___x_1034_;
v___y_973_ = v___y_1009_;
v___y_974_ = v_a_1013_;
v_a_975_ = v___x_1049_;
goto v___jp_967_;
}
}
}
}
}
v___jp_1052_:
{
lean_object* v___x_1061_; double v___x_1062_; double v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1061_ = lean_io_get_num_heartbeats();
v___x_1062_ = lean_float_of_nat(v___y_1054_);
v___x_1063_ = lean_float_of_nat(v___x_1061_);
v___x_1064_ = lean_box_float(v___x_1062_);
v___x_1065_ = lean_box_float(v___x_1063_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_a_1060_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
lean_inc_ref(v___y_1059_);
v___x_1068_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1058_, v___y_1059_, v___y_1057_, v___y_1056_, v___y_1055_, v___y_1053_, v___x_1067_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1068_;
}
v___jp_1069_:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_a_1077_);
v___y_1053_ = v___y_1070_;
v___y_1054_ = v___y_1071_;
v___y_1055_ = v___y_1074_;
v___y_1056_ = v___y_1073_;
v___y_1057_ = v___y_1072_;
v___y_1058_ = v___y_1075_;
v___y_1059_ = v___y_1076_;
v_a_1060_ = v___x_1078_;
goto v___jp_1052_;
}
v___jp_1079_:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_a_1087_);
v___y_1053_ = v___y_1080_;
v___y_1054_ = v___y_1081_;
v___y_1055_ = v___y_1084_;
v___y_1056_ = v___y_1083_;
v___y_1057_ = v___y_1082_;
v___y_1058_ = v___y_1085_;
v___y_1059_ = v___y_1086_;
v_a_1060_ = v___x_1088_;
goto v___jp_1052_;
}
v___jp_1089_:
{
if (lean_obj_tag(v___y_1097_) == 0)
{
lean_object* v_a_1098_; 
v_a_1098_ = lean_ctor_get(v___y_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___y_1097_, 1);
v___y_1070_ = v___y_1090_;
v___y_1071_ = v___y_1091_;
v___y_1072_ = v___y_1094_;
v___y_1073_ = v___y_1093_;
v___y_1074_ = v___y_1092_;
v___y_1075_ = v___y_1095_;
v___y_1076_ = v___y_1096_;
v_a_1077_ = v_a_1098_;
goto v___jp_1069_;
}
else
{
lean_object* v_a_1099_; 
v_a_1099_ = lean_ctor_get(v___y_1097_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___y_1097_, 1);
v___y_1080_ = v___y_1090_;
v___y_1081_ = v___y_1091_;
v___y_1082_ = v___y_1094_;
v___y_1083_ = v___y_1093_;
v___y_1084_ = v___y_1092_;
v___y_1085_ = v___y_1095_;
v___y_1086_ = v___y_1096_;
v_a_1087_ = v_a_1099_;
goto v___jp_1079_;
}
}
v___jp_1100_:
{
lean_object* v___x_1109_; double v___x_1110_; double v___x_1111_; double v___x_1112_; double v___x_1113_; double v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1109_ = lean_io_mono_nanos_now();
v___x_1110_ = lean_float_of_nat(v___y_1106_);
v___x_1111_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1112_ = lean_float_div(v___x_1110_, v___x_1111_);
v___x_1113_ = lean_float_of_nat(v___x_1109_);
v___x_1114_ = lean_float_div(v___x_1113_, v___x_1111_);
v___x_1115_ = lean_box_float(v___x_1112_);
v___x_1116_ = lean_box_float(v___x_1114_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_a_1108_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
lean_inc_ref(v___y_1107_);
v___x_1119_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_956_, v___y_1105_, v___y_1107_, v___y_1104_, v___y_1103_, v___y_1102_, v___y_1101_, v___x_1118_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_1119_;
}
v___jp_1120_:
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_a_1128_);
v___y_1101_ = v___y_1121_;
v___y_1102_ = v___y_1124_;
v___y_1103_ = v___y_1123_;
v___y_1104_ = v___y_1122_;
v___y_1105_ = v___y_1125_;
v___y_1106_ = v___y_1126_;
v___y_1107_ = v___y_1127_;
v_a_1108_ = v___x_1129_;
goto v___jp_1100_;
}
v___jp_1130_:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_a_1138_);
v___y_1101_ = v___y_1131_;
v___y_1102_ = v___y_1134_;
v___y_1103_ = v___y_1133_;
v___y_1104_ = v___y_1132_;
v___y_1105_ = v___y_1135_;
v___y_1106_ = v___y_1136_;
v___y_1107_ = v___y_1137_;
v_a_1108_ = v___x_1139_;
goto v___jp_1100_;
}
v___jp_1140_:
{
if (lean_obj_tag(v___y_1148_) == 0)
{
lean_object* v_a_1149_; 
v_a_1149_ = lean_ctor_get(v___y_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___y_1148_, 1);
v___y_1121_ = v___y_1141_;
v___y_1122_ = v___y_1144_;
v___y_1123_ = v___y_1143_;
v___y_1124_ = v___y_1142_;
v___y_1125_ = v___y_1145_;
v___y_1126_ = v___y_1146_;
v___y_1127_ = v___y_1147_;
v_a_1128_ = v_a_1149_;
goto v___jp_1120_;
}
else
{
lean_object* v_a_1150_; 
v_a_1150_ = lean_ctor_get(v___y_1148_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___y_1148_, 1);
v___y_1131_ = v___y_1141_;
v___y_1132_ = v___y_1144_;
v___y_1133_ = v___y_1143_;
v___y_1134_ = v___y_1142_;
v___y_1135_ = v___y_1145_;
v___y_1136_ = v___y_1146_;
v___y_1137_ = v___y_1147_;
v_a_1138_ = v_a_1150_;
goto v___jp_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2370_, lean_object* v_trace_2371_, lean_object* v_next_2372_, lean_object* v_goals_2373_, lean_object* v_n_2374_, lean_object* v_curr_2375_, lean_object* v_acc_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2370_, v_trace_2371_, v_next_2372_, v_goals_2373_, v_n_2374_, v_curr_2375_, v_acc_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object* v_tail_2383_, lean_object* v_cfg_2384_, lean_object* v_trace_2385_, lean_object* v_next_2386_, lean_object* v_goals_2387_, lean_object* v_n_2388_, lean_object* v_acc_2389_, lean_object* v_r_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = l_List_appendTR___redArg(v_r_2390_, v_tail_2383_);
v___x_2397_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2397_, 0, v_cfg_2384_);
lean_closure_set(v___x_2397_, 1, v_trace_2385_);
lean_closure_set(v___x_2397_, 2, v_next_2386_);
lean_closure_set(v___x_2397_, 3, v_goals_2387_);
lean_closure_set(v___x_2397_, 4, v_n_2388_);
lean_closure_set(v___x_2397_, 5, v___x_2396_);
lean_closure_set(v___x_2397_, 6, v_acc_2389_);
v___x_2398_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v___x_2397_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2399_, lean_object* v_msg_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2407_, lean_object* v_msg_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2407_, v_msg_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object* v_00_u03b1_2415_, lean_object* v_x_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_2416_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_x_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_00_u03b1_2423_, v_x_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* v_mvarId_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_2431_, v___y_2433_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* v_mvarId_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_mvarId_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v_mvarId_2438_);
return v_res_2444_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_object* v_00_u03b2_2445_, lean_object* v_x_2446_, lean_object* v_x_2447_){
_start:
{
uint8_t v___x_2448_; 
v___x_2448_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_2446_, v_x_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2449_, lean_object* v_x_2450_, lean_object* v_x_2451_){
_start:
{
uint8_t v_res_2452_; lean_object* v_r_2453_; 
v_res_2452_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(v_00_u03b2_2449_, v_x_2450_, v_x_2451_);
lean_dec(v_x_2451_);
lean_dec_ref(v_x_2450_);
v_r_2453_ = lean_box(v_res_2452_);
return v_r_2453_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_2454_, lean_object* v_x_2455_, size_t v_x_2456_, lean_object* v_x_2457_){
_start:
{
uint8_t v___x_2458_; 
v___x_2458_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_2455_, v_x_2456_, v_x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___boxed(lean_object* v_00_u03b2_2459_, lean_object* v_x_2460_, lean_object* v_x_2461_, lean_object* v_x_2462_){
_start:
{
size_t v_x_77611__boxed_2463_; uint8_t v_res_2464_; lean_object* v_r_2465_; 
v_x_77611__boxed_2463_ = lean_unbox_usize(v_x_2461_);
lean_dec(v_x_2461_);
v_res_2464_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2459_, v_x_2460_, v_x_77611__boxed_2463_, v_x_2462_);
lean_dec(v_x_2462_);
lean_dec_ref(v_x_2460_);
v_r_2465_ = lean_box(v_res_2464_);
return v_r_2465_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_object* v_00_u03b2_2466_, lean_object* v_keys_2467_, lean_object* v_vals_2468_, lean_object* v_heq_2469_, lean_object* v_i_2470_, lean_object* v_k_2471_){
_start:
{
uint8_t v___x_2472_; 
v___x_2472_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_2467_, v_i_2470_, v_k_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2473_, lean_object* v_keys_2474_, lean_object* v_vals_2475_, lean_object* v_heq_2476_, lean_object* v_i_2477_, lean_object* v_k_2478_){
_start:
{
uint8_t v_res_2479_; lean_object* v_r_2480_; 
v_res_2479_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(v_00_u03b2_2473_, v_keys_2474_, v_vals_2475_, v_heq_2476_, v_i_2477_, v_k_2478_);
lean_dec(v_k_2478_);
lean_dec_ref(v_vals_2475_);
lean_dec_ref(v_keys_2474_);
v_r_2480_ = lean_box(v_res_2479_);
return v_r_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2481_, lean_object* v_h__1_2482_, lean_object* v_h__2_2483_){
_start:
{
lean_object* v_zero_2484_; uint8_t v_isZero_2485_; 
v_zero_2484_ = lean_unsigned_to_nat(0u);
v_isZero_2485_ = lean_nat_dec_eq(v_n_2481_, v_zero_2484_);
if (v_isZero_2485_ == 1)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec(v_h__2_2483_);
v___x_2486_ = lean_box(0);
v___x_2487_ = lean_apply_1(v_h__1_2482_, v___x_2486_);
return v___x_2487_;
}
else
{
lean_object* v_one_2488_; lean_object* v_n_2489_; lean_object* v___x_2490_; 
lean_dec(v_h__1_2482_);
v_one_2488_ = lean_unsigned_to_nat(1u);
v_n_2489_ = lean_nat_sub(v_n_2481_, v_one_2488_);
v___x_2490_ = lean_apply_1(v_h__2_2483_, v_n_2489_);
return v___x_2490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2491_, lean_object* v_h__1_2492_, lean_object* v_h__2_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2491_, v_h__1_2492_, v_h__2_2493_);
lean_dec(v_n_2491_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2495_, lean_object* v_n_2496_, lean_object* v_h__1_2497_, lean_object* v_h__2_2498_){
_start:
{
lean_object* v_zero_2499_; uint8_t v_isZero_2500_; 
v_zero_2499_ = lean_unsigned_to_nat(0u);
v_isZero_2500_ = lean_nat_dec_eq(v_n_2496_, v_zero_2499_);
if (v_isZero_2500_ == 1)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_dec(v_h__2_2498_);
v___x_2501_ = lean_box(0);
v___x_2502_ = lean_apply_1(v_h__1_2497_, v___x_2501_);
return v___x_2502_;
}
else
{
lean_object* v_one_2503_; lean_object* v_n_2504_; lean_object* v___x_2505_; 
lean_dec(v_h__1_2497_);
v_one_2503_ = lean_unsigned_to_nat(1u);
v_n_2504_ = lean_nat_sub(v_n_2496_, v_one_2503_);
v___x_2505_ = lean_apply_1(v_h__2_2498_, v_n_2504_);
return v___x_2505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* v_motive_2506_, lean_object* v_n_2507_, lean_object* v_h__1_2508_, lean_object* v_h__2_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(v_motive_2506_, v_n_2507_, v_h__1_2508_, v_h__2_2509_);
lean_dec(v_n_2507_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* v_procResult_x3f_2511_, lean_object* v_h__1_2512_, lean_object* v_h__2_2513_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2511_) == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec(v_h__1_2512_);
v___x_2514_ = lean_box(0);
v___x_2515_ = lean_apply_1(v_h__2_2513_, v___x_2514_);
return v___x_2515_;
}
else
{
lean_object* v_val_2516_; lean_object* v___x_2517_; 
lean_dec(v_h__2_2513_);
v_val_2516_ = lean_ctor_get(v_procResult_x3f_2511_, 0);
lean_inc(v_val_2516_);
lean_dec_ref_known(v_procResult_x3f_2511_, 1);
v___x_2517_ = lean_apply_1(v_h__1_2512_, v_val_2516_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* v_motive_2518_, lean_object* v_procResult_x3f_2519_, lean_object* v_h__1_2520_, lean_object* v_h__2_2521_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2519_) == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec(v_h__1_2520_);
v___x_2522_ = lean_box(0);
v___x_2523_ = lean_apply_1(v_h__2_2521_, v___x_2522_);
return v___x_2523_;
}
else
{
lean_object* v_val_2524_; lean_object* v___x_2525_; 
lean_dec(v_h__2_2521_);
v_val_2524_ = lean_ctor_get(v_procResult_x3f_2519_, 0);
lean_inc(v_val_2524_);
lean_dec_ref_known(v_procResult_x3f_2519_, 1);
v___x_2525_ = lean_apply_1(v_h__1_2520_, v_val_2524_);
return v___x_2525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2526_, lean_object* v_h__1_2527_, lean_object* v_h__2_2528_){
_start:
{
if (lean_obj_tag(v_curr_2526_) == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec(v_h__2_2528_);
v___x_2529_ = lean_box(0);
v___x_2530_ = lean_apply_1(v_h__1_2527_, v___x_2529_);
return v___x_2530_;
}
else
{
lean_object* v_head_2531_; lean_object* v_tail_2532_; lean_object* v___x_2533_; 
lean_dec(v_h__1_2527_);
v_head_2531_ = lean_ctor_get(v_curr_2526_, 0);
lean_inc(v_head_2531_);
v_tail_2532_ = lean_ctor_get(v_curr_2526_, 1);
lean_inc(v_tail_2532_);
lean_dec_ref_known(v_curr_2526_, 2);
v___x_2533_ = lean_apply_2(v_h__2_2528_, v_head_2531_, v_tail_2532_);
return v___x_2533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2534_, lean_object* v_curr_2535_, lean_object* v_h__1_2536_, lean_object* v_h__2_2537_){
_start:
{
if (lean_obj_tag(v_curr_2535_) == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec(v_h__2_2537_);
v___x_2538_ = lean_box(0);
v___x_2539_ = lean_apply_1(v_h__1_2536_, v___x_2538_);
return v___x_2539_;
}
else
{
lean_object* v_head_2540_; lean_object* v_tail_2541_; lean_object* v___x_2542_; 
lean_dec(v_h__1_2536_);
v_head_2540_ = lean_ctor_get(v_curr_2535_, 0);
lean_inc(v_head_2540_);
v_tail_2541_ = lean_ctor_get(v_curr_2535_, 1);
lean_inc(v_tail_2541_);
lean_dec_ref_known(v_curr_2535_, 2);
v___x_2542_ = lean_apply_2(v_h__2_2537_, v_head_2540_, v_tail_2541_);
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2543_, lean_object* v_h__1_2544_, lean_object* v_h__2_2545_){
_start:
{
if (lean_obj_tag(v_____do__lift_2543_) == 0)
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
lean_dec(v_h__2_2545_);
v___x_2546_ = lean_box(0);
v___x_2547_ = lean_apply_1(v_h__1_2544_, v___x_2546_);
return v___x_2547_;
}
else
{
lean_object* v_val_2548_; lean_object* v___x_2549_; 
lean_dec(v_h__1_2544_);
v_val_2548_ = lean_ctor_get(v_____do__lift_2543_, 0);
lean_inc(v_val_2548_);
lean_dec_ref_known(v_____do__lift_2543_, 1);
v___x_2549_ = lean_apply_1(v_h__2_2545_, v_val_2548_);
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_2550_, lean_object* v_____do__lift_2551_, lean_object* v_h__1_2552_, lean_object* v_h__2_2553_){
_start:
{
if (lean_obj_tag(v_____do__lift_2551_) == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec(v_h__2_2553_);
v___x_2554_ = lean_box(0);
v___x_2555_ = lean_apply_1(v_h__1_2552_, v___x_2554_);
return v___x_2555_;
}
else
{
lean_object* v_val_2556_; lean_object* v___x_2557_; 
lean_dec(v_h__1_2552_);
v_val_2556_ = lean_ctor_get(v_____do__lift_2551_, 0);
lean_inc(v_val_2556_);
lean_dec_ref_known(v_____do__lift_2551_, 1);
v___x_2557_ = lean_apply_1(v_h__2_2553_, v_val_2556_);
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_2558_, lean_object* v_trace_2559_, lean_object* v_next_2560_, lean_object* v_orig_2561_, lean_object* v_g_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_maxDepth_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v_maxDepth_2568_ = lean_ctor_get(v_cfg_2558_, 0);
lean_inc(v_maxDepth_2568_);
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2570_, 0, v_g_2562_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2558_, v_trace_2559_, v_next_2560_, v_orig_2561_, v_maxDepth_2568_, v___x_2570_, v___x_2569_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_2572_, lean_object* v_trace_2573_, lean_object* v_next_2574_, lean_object* v_orig_2575_, lean_object* v_g_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2572_, v_trace_2573_, v_next_2574_, v_orig_2575_, v_g_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
if (lean_obj_tag(v_a_2583_) == 0)
{
lean_object* v___x_2585_; 
v___x_2585_ = l_List_reverse___redArg(v_a_2584_);
return v___x_2585_;
}
else
{
lean_object* v_head_2586_; lean_object* v_tail_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2596_; 
v_head_2586_ = lean_ctor_get(v_a_2583_, 0);
v_tail_2587_ = lean_ctor_get(v_a_2583_, 1);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_a_2583_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2589_ = v_a_2583_;
v_isShared_2590_ = v_isSharedCheck_2596_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_tail_2587_);
lean_inc(v_head_2586_);
lean_dec(v_a_2583_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2596_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = l_Lean_MessageData_ofFormat(v_head_2586_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v_a_2584_);
lean_ctor_set(v___x_2589_, 0, v___x_2591_);
v___x_2593_ = v___x_2589_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_a_2584_);
v___x_2593_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
v_a_2583_ = v_tail_2587_;
v_a_2584_ = v___x_2593_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_2599_ = l_Lean_stringToMessageData(v___x_2598_);
return v___x_2599_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_2602_ = l_Lean_stringToMessageData(v___x_2601_);
return v___x_2602_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_2605_ = l_Lean_stringToMessageData(v___x_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_2606_, lean_object* v_snd_2607_, lean_object* v_x_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2606_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2616_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2616_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_2607_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2636_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2619_ = v___x_2616_;
v_isShared_2620_ = v_isSharedCheck_2636_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2636_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2621_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_2622_ = lean_box(0);
v___x_2623_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2615_, v___x_2622_);
v___x_2624_ = l_Lean_MessageData_ofList(v___x_2623_);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2621_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_2629_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2617_, v___x_2622_);
v___x_2630_ = l_Lean_MessageData_ofList(v___x_2629_);
v___x_2631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2628_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2627_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2632_);
v___x_2634_ = v___x_2619_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v_a_2615_);
v_a_2637_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2616_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2616_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_snd_2607_);
v_a_2645_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2614_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2614_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_2653_, lean_object* v_snd_2654_, lean_object* v_x_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2653_, v_snd_2654_, v_x_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec_ref(v_x_2655_);
return v_res_2661_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_2664_ = l_Lean_stringToMessageData(v___x_2663_);
return v___x_2664_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_2667_ = l_Lean_stringToMessageData(v___x_2666_);
return v___x_2667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_2668_, lean_object* v___x_2669_, lean_object* v_x_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2668_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2678_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_2669_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2696_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2696_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2696_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2683_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_2684_ = lean_box(0);
v___x_2685_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2677_, v___x_2684_);
v___x_2686_ = l_Lean_MessageData_ofList(v___x_2685_);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2683_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_2689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2679_, v___x_2684_);
v___x_2691_ = l_Lean_MessageData_ofList(v___x_2690_);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2689_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2692_);
v___x_2694_ = v___x_2681_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec(v_a_2677_);
v_a_2697_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2678_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2678_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec(v___x_2669_);
v_a_2705_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2676_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2676_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_2713_, lean_object* v___x_2714_, lean_object* v_x_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2713_, v___x_2714_, v_x_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec_ref(v_x_2715_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t v___x_2722_, lean_object* v_x_2723_, lean_object* v_x_2724_, lean_object* v___y_2725_){
_start:
{
if (lean_obj_tag(v_x_2723_) == 0)
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v_x_2724_);
return v___x_2727_;
}
else
{
lean_object* v_head_2728_; lean_object* v_tail_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2744_; 
v_head_2728_ = lean_ctor_get(v_x_2723_, 0);
v_tail_2729_ = lean_ctor_get(v_x_2723_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_x_2723_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2731_ = v_x_2723_;
v_isShared_2732_ = v_isSharedCheck_2744_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_tail_2729_);
lean_inc(v_head_2728_);
lean_dec(v_x_2723_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2744_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
uint8_t v_a_2739_; lean_object* v___x_2741_; lean_object* v_a_2742_; uint8_t v___x_2743_; 
v___x_2741_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2728_, v___y_2725_);
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2742_);
lean_dec_ref(v___x_2741_);
v___x_2743_ = lean_unbox(v_a_2742_);
lean_dec(v_a_2742_);
if (v___x_2743_ == 0)
{
goto v___jp_2733_;
}
else
{
v_a_2739_ = v___x_2722_;
goto v___jp_2738_;
}
v___jp_2733_:
{
lean_object* v___x_2735_; 
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 1, v_x_2724_);
v___x_2735_ = v___x_2731_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_head_2728_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_x_2724_);
v___x_2735_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
v_x_2723_ = v_tail_2729_;
v_x_2724_ = v___x_2735_;
goto _start;
}
}
v___jp_2738_:
{
if (v_a_2739_ == 0)
{
lean_del_object(v___x_2731_);
lean_dec(v_head_2728_);
v_x_2723_ = v_tail_2729_;
goto _start;
}
else
{
goto v___jp_2733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v___x_2745_, lean_object* v_x_2746_, lean_object* v_x_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v___x_45531__boxed_2750_; lean_object* v_res_2751_; 
v___x_45531__boxed_2750_ = lean_unbox(v___x_2745_);
v_res_2751_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_45531__boxed_2750_, v_x_2746_, v_x_2747_, v___y_2748_);
lean_dec(v___y_2748_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
if (lean_obj_tag(v_a_2752_) == 0)
{
lean_object* v___x_2754_; 
v___x_2754_ = lean_array_to_list(v_a_2753_);
return v___x_2754_;
}
else
{
lean_object* v_head_2755_; lean_object* v_tail_2756_; lean_object* v___x_2757_; 
v_head_2755_ = lean_ctor_get(v_a_2752_, 0);
lean_inc(v_head_2755_);
v_tail_2756_ = lean_ctor_get(v_a_2752_, 1);
lean_inc(v_tail_2756_);
lean_dec_ref_known(v_a_2752_, 2);
v___x_2757_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2753_, v_head_2755_);
v_a_2752_ = v_tail_2756_;
v_a_2753_ = v___x_2757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
if (lean_obj_tag(v_a_2760_) == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_dec(v_goals_2759_);
v___x_2768_ = lean_array_to_list(v_a_2761_);
v___x_2769_ = lean_array_to_list(v_a_2762_);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2768_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
return v___x_2771_;
}
else
{
lean_object* v_head_2772_; lean_object* v_tail_2773_; lean_object* v___x_2774_; 
v_head_2772_ = lean_ctor_get(v_a_2760_, 0);
lean_inc_n(v_head_2772_, 2);
v_tail_2773_ = lean_ctor_get(v_a_2760_, 1);
lean_inc(v_tail_2773_);
lean_dec_ref_known(v_a_2760_, 2);
lean_inc(v_goals_2759_);
v___x_2774_ = l_Lean_MVarId_isIndependentOf(v_goals_2759_, v_head_2772_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; uint8_t v___x_2776_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
v___x_2776_ = lean_unbox(v_a_2775_);
lean_dec(v_a_2775_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_array_push(v_a_2762_, v_head_2772_);
v_a_2760_ = v_tail_2773_;
v_a_2762_ = v___x_2777_;
goto _start;
}
else
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_array_push(v_a_2761_, v_head_2772_);
v_a_2760_ = v_tail_2773_;
v_a_2761_ = v___x_2779_;
goto _start;
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec(v_tail_2773_);
lean_dec(v_head_2772_);
lean_dec_ref(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_goals_2759_);
v_a_2781_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2774_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2774_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
if (lean_obj_tag(v_a_2799_) == 0)
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_array_to_list(v_a_2800_);
return v___x_2801_;
}
else
{
lean_object* v_head_2802_; 
v_head_2802_ = lean_ctor_get(v_a_2799_, 0);
if (lean_obj_tag(v_head_2802_) == 0)
{
lean_object* v_tail_2803_; lean_object* v_val_2804_; lean_object* v___x_2805_; 
lean_inc_ref(v_head_2802_);
v_tail_2803_ = lean_ctor_get(v_a_2799_, 1);
lean_inc(v_tail_2803_);
lean_dec_ref_known(v_a_2799_, 2);
v_val_2804_ = lean_ctor_get(v_head_2802_, 0);
lean_inc(v_val_2804_);
lean_dec_ref_known(v_head_2802_, 1);
v___x_2805_ = lean_array_push(v_a_2800_, v_val_2804_);
v_a_2799_ = v_tail_2803_;
v_a_2800_ = v___x_2805_;
goto _start;
}
else
{
lean_object* v_tail_2807_; 
v_tail_2807_ = lean_ctor_get(v_a_2799_, 1);
lean_inc(v_tail_2807_);
lean_dec_ref_known(v_a_2799_, 2);
v_a_2799_ = v_tail_2807_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
if (lean_obj_tag(v_x_2810_) == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec_ref(v_f_2809_);
v___x_2817_ = l_List_reverse___redArg(v_x_2811_);
v___x_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
return v___x_2818_;
}
else
{
lean_object* v_head_2819_; lean_object* v_tail_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2865_; 
v_head_2819_ = lean_ctor_get(v_x_2810_, 0);
v_tail_2820_ = lean_ctor_get(v_x_2810_, 1);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_x_2810_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2822_ = v_x_2810_;
v_isShared_2823_ = v_isSharedCheck_2865_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_tail_2820_);
lean_inc(v_head_2819_);
lean_dec(v_x_2810_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2865_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v_a_2825_; lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_Meta_saveState___redArg(v___y_2813_, v___y_2815_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
lean_inc_ref(v_f_2809_);
lean_inc(v___y_2815_);
lean_inc_ref(v___y_2814_);
lean_inc(v___y_2813_);
lean_inc_ref(v___y_2812_);
lean_inc(v_head_2819_);
v___x_2832_ = lean_apply_6(v_f_2809_, v_head_2819_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, lean_box(0));
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2834_; 
lean_dec(v_a_2831_);
lean_dec(v_head_2819_);
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_a_2833_);
v_a_2825_ = v___x_2834_;
goto v___jp_2824_;
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2856_; 
v_a_2835_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2837_ = v___x_2832_;
v_isShared_2838_ = v_isSharedCheck_2856_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2832_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2856_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
uint8_t v___y_2840_; uint8_t v___x_2854_; 
v___x_2854_ = l_Lean_Exception_isInterrupt(v_a_2835_);
if (v___x_2854_ == 0)
{
uint8_t v___x_2855_; 
lean_inc(v_a_2835_);
v___x_2855_ = l_Lean_Exception_isRuntime(v_a_2835_);
v___y_2840_ = v___x_2855_;
goto v___jp_2839_;
}
else
{
v___y_2840_ = v___x_2854_;
goto v___jp_2839_;
}
v___jp_2839_:
{
if (v___y_2840_ == 0)
{
lean_object* v___x_2841_; 
lean_del_object(v___x_2837_);
lean_dec(v_a_2835_);
v___x_2841_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2831_, v___y_2813_, v___y_2815_);
lean_dec(v_a_2831_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v___x_2842_; 
lean_dec_ref_known(v___x_2841_, 1);
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_head_2819_);
v_a_2825_ = v___x_2842_;
goto v___jp_2824_;
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_del_object(v___x_2822_);
lean_dec(v_tail_2820_);
lean_dec(v_head_2819_);
lean_dec(v_x_2811_);
lean_dec_ref(v_f_2809_);
v_a_2843_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2841_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2841_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
else
{
lean_object* v___x_2852_; 
lean_dec(v_a_2831_);
lean_del_object(v___x_2822_);
lean_dec(v_tail_2820_);
lean_dec(v_head_2819_);
lean_dec(v_x_2811_);
lean_dec_ref(v_f_2809_);
if (v_isShared_2838_ == 0)
{
v___x_2852_ = v___x_2837_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2835_);
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
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_del_object(v___x_2822_);
lean_dec(v_tail_2820_);
lean_dec(v_head_2819_);
lean_dec(v_x_2811_);
lean_dec_ref(v_f_2809_);
v_a_2857_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2830_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2830_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
v___jp_2824_:
{
lean_object* v___x_2827_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 1, v_x_2811_);
lean_ctor_set(v___x_2822_, 0, v_a_2825_);
v___x_2827_ = v___x_2822_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2825_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_x_2811_);
v___x_2827_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
v_x_2810_ = v_tail_2820_;
v_x_2811_ = v___x_2827_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_2866_, lean_object* v_x_2867_, lean_object* v_x_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2866_, v_x_2867_, v_x_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_2875_, lean_object* v_a_2876_){
_start:
{
if (lean_obj_tag(v_a_2875_) == 0)
{
lean_object* v___x_2877_; 
v___x_2877_ = lean_array_to_list(v_a_2876_);
return v___x_2877_;
}
else
{
lean_object* v_head_2878_; 
v_head_2878_ = lean_ctor_get(v_a_2875_, 0);
if (lean_obj_tag(v_head_2878_) == 1)
{
lean_object* v_tail_2879_; lean_object* v_val_2880_; lean_object* v___x_2881_; 
lean_inc_ref(v_head_2878_);
v_tail_2879_ = lean_ctor_get(v_a_2875_, 1);
lean_inc(v_tail_2879_);
lean_dec_ref_known(v_a_2875_, 2);
v_val_2880_ = lean_ctor_get(v_head_2878_, 0);
lean_inc(v_val_2880_);
lean_dec_ref_known(v_head_2878_, 1);
v___x_2881_ = lean_array_push(v_a_2876_, v_val_2880_);
v_a_2875_ = v_tail_2879_;
v_a_2876_ = v___x_2881_;
goto _start;
}
else
{
lean_object* v_tail_2883_; 
v_tail_2883_ = lean_ctor_get(v_a_2875_, 1);
lean_inc(v_tail_2883_);
lean_dec_ref_known(v_a_2875_, 2);
v_a_2875_ = v_tail_2883_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_2885_, lean_object* v_f_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_box(0);
v___x_2893_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2886_, v_L_2885_, v___x_2892_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2905_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2905_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2905_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2898_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_2894_);
v___x_2899_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_2894_, v___x_2898_);
v___x_2900_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_2894_, v___x_2898_);
v___x_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2901_);
v___x_2903_ = v___x_2896_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_a_2906_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2893_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2893_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* v_L_2914_, lean_object* v_f_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_2914_, v_f_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t v___x_2922_, uint8_t v___x_2923_, lean_object* v_x_2924_, lean_object* v_x_2925_, lean_object* v___y_2926_){
_start:
{
if (lean_obj_tag(v_x_2924_) == 0)
{
lean_object* v___x_2928_; 
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v_x_2925_);
return v___x_2928_;
}
else
{
lean_object* v_head_2929_; lean_object* v_tail_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2944_; 
v_head_2929_ = lean_ctor_get(v_x_2924_, 0);
v_tail_2930_ = lean_ctor_get(v_x_2924_, 1);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_x_2924_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2932_ = v_x_2924_;
v_isShared_2933_ = v_isSharedCheck_2944_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_tail_2930_);
lean_inc(v_head_2929_);
lean_dec(v_x_2924_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2944_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
uint8_t v_a_2935_; lean_object* v___x_2941_; lean_object* v_a_2942_; uint8_t v___x_2943_; 
v___x_2941_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2929_, v___y_2926_);
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref(v___x_2941_);
v___x_2943_ = lean_unbox(v_a_2942_);
lean_dec(v_a_2942_);
if (v___x_2943_ == 0)
{
v_a_2935_ = v___x_2922_;
goto v___jp_2934_;
}
else
{
v_a_2935_ = v___x_2923_;
goto v___jp_2934_;
}
v___jp_2934_:
{
if (v_a_2935_ == 0)
{
lean_del_object(v___x_2932_);
lean_dec(v_head_2929_);
v_x_2924_ = v_tail_2930_;
goto _start;
}
else
{
lean_object* v___x_2938_; 
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 1, v_x_2925_);
v___x_2938_ = v___x_2932_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_head_2929_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_x_2925_);
v___x_2938_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
v_x_2924_ = v_tail_2930_;
v_x_2925_ = v___x_2938_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* v___x_2945_, lean_object* v___x_2946_, lean_object* v_x_2947_, lean_object* v_x_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
uint8_t v___x_45885__boxed_2951_; uint8_t v___x_45886__boxed_2952_; lean_object* v_res_2953_; 
v___x_45885__boxed_2951_ = lean_unbox(v___x_2945_);
v___x_45886__boxed_2952_ = lean_unbox(v___x_2946_);
v_res_2953_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_45885__boxed_2951_, v___x_45886__boxed_2952_, v_x_2947_, v_x_2948_, v___y_2949_);
lean_dec(v___y_2949_);
return v_res_2953_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2(void){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1));
v___x_2958_ = l_Lean_stringToMessageData(v___x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_2959_, lean_object* v_trace_2960_, lean_object* v_next_2961_, lean_object* v_orig_2962_, lean_object* v_goals_2963_, lean_object* v_remaining_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
lean_inc(v_remaining_2964_);
lean_inc(v_goals_2963_);
v___x_2971_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2963_, v_remaining_2964_, v___x_2970_, v___x_2970_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v_fst_2973_; lean_object* v_snd_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_4175_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2971_, 1);
v_fst_2973_ = lean_ctor_get(v_a_2972_, 0);
v_snd_2974_ = lean_ctor_get(v_a_2972_, 1);
v_isSharedCheck_4175_ = !lean_is_exclusive(v_a_2972_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_2976_ = v_a_2972_;
v_isShared_2977_ = v_isSharedCheck_4175_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_snd_2974_);
lean_inc(v_fst_2973_);
lean_dec(v_a_2972_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_4175_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
uint8_t v___x_2978_; 
v___x_2978_ = l_List_isEmpty___redArg(v_fst_2973_);
if (v___x_2978_ == 0)
{
lean_object* v_toCold_2979_; lean_object* v_options_2980_; lean_object* v_inheritedTraceOptions_2981_; uint8_t v_hasTrace_2982_; lean_object* v___f_2983_; 
lean_dec(v_remaining_2964_);
v_toCold_2979_ = lean_ctor_get(v_a_2967_, 0);
v_options_2980_ = lean_ctor_get(v_toCold_2979_, 2);
v_inheritedTraceOptions_2981_ = lean_ctor_get(v_toCold_2979_, 11);
v_hasTrace_2982_ = lean_ctor_get_uint8(v_options_2980_, sizeof(void*)*1);
lean_inc(v_orig_2962_);
lean_inc_ref(v_next_2961_);
lean_inc(v_trace_2960_);
lean_inc_ref(v_cfg_2959_);
v___f_2983_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2983_, 0, v_cfg_2959_);
lean_closure_set(v___f_2983_, 1, v_trace_2960_);
lean_closure_set(v___f_2983_, 2, v_next_2961_);
lean_closure_set(v___f_2983_, 3, v_orig_2962_);
if (v_hasTrace_2982_ == 0)
{
lean_object* v___x_2984_; 
lean_del_object(v___x_2976_);
v___x_2984_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2973_, v___f_2983_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3057_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_2987_ = v___x_2984_;
v_isShared_2988_ = v_isSharedCheck_3057_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2984_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3057_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v_fst_2989_; lean_object* v_snd_2990_; lean_object* v___x_2991_; lean_object* v_a_2993_; lean_object* v___y_3000_; lean_object* v___y_3003_; lean_object* v___y_3004_; uint8_t v___y_3005_; lean_object* v___y_3016_; lean_object* v___y_3032_; uint8_t v___y_3033_; lean_object* v_a_3048_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_fst_2989_ = lean_ctor_get(v_a_2985_, 0);
lean_inc(v_fst_2989_);
v_snd_2990_ = lean_ctor_get(v_a_2985_, 1);
lean_inc(v_snd_2990_);
lean_dec(v_a_2985_);
v___x_2991_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_2990_, v___x_2970_);
v___x_3052_ = lean_box(0);
v___x_3053_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_2978_, v_goals_2963_, v___x_3052_, v_a_2966_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3055_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3053_, 1);
v___x_3055_ = l_List_reverse___redArg(v_a_3054_);
v_a_3048_ = v___x_3055_;
goto v___jp_3047_;
}
else
{
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3056_; 
v_a_3056_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3053_, 1);
v_a_3048_ = v_a_3056_;
goto v___jp_3047_;
}
else
{
lean_dec(v___x_2991_);
lean_dec(v_fst_2989_);
lean_del_object(v___x_2987_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec(v_trace_2960_);
lean_dec_ref(v_cfg_2959_);
return v___x_3053_;
}
}
v___jp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2994_ = l_List_appendTR___redArg(v___x_2991_, v_fst_2989_);
v___x_2995_ = l_List_appendTR___redArg(v___x_2994_, v_a_2993_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v___x_2995_);
v___x_2997_ = v___x_2987_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
v___jp_2999_:
{
if (lean_obj_tag(v___y_3000_) == 0)
{
lean_object* v_a_3001_; 
v_a_3001_ = lean_ctor_get(v___y_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___y_3000_, 1);
v_a_2993_ = v_a_3001_;
goto v___jp_2992_;
}
else
{
lean_dec(v___x_2991_);
lean_dec(v_fst_2989_);
lean_del_object(v___x_2987_);
return v___y_3000_;
}
}
v___jp_3002_:
{
if (v___y_3005_ == 0)
{
lean_object* v___x_3006_; 
lean_dec_ref(v___y_3004_);
v___x_3006_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3003_, v_a_2966_, v_a_2968_);
lean_dec_ref(v___y_3003_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_dec_ref_known(v___x_3006_, 1);
v_a_2993_ = v_snd_2974_;
goto v___jp_2992_;
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec(v___x_2991_);
lean_dec(v_fst_2989_);
lean_del_object(v___x_2987_);
lean_dec(v_snd_2974_);
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_3006_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3006_);
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
else
{
lean_dec_ref(v___y_3003_);
lean_dec(v_snd_2974_);
v___y_3000_ = v___y_3004_;
goto v___jp_2999_;
}
}
v___jp_3015_:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_Meta_saveState___redArg(v_a_2966_, v_a_2968_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
lean_inc(v_snd_2974_);
v___x_3019_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3016_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_dec(v_a_3018_);
lean_dec(v_snd_2974_);
v___y_3000_ = v___x_3019_;
goto v___jp_2999_;
}
else
{
lean_object* v_a_3020_; uint8_t v___x_3021_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
v___x_3021_ = l_Lean_Exception_isInterrupt(v_a_3020_);
if (v___x_3021_ == 0)
{
uint8_t v___x_3022_; 
v___x_3022_ = l_Lean_Exception_isRuntime(v_a_3020_);
v___y_3003_ = v_a_3018_;
v___y_3004_ = v___x_3019_;
v___y_3005_ = v___x_3022_;
goto v___jp_3002_;
}
else
{
lean_dec(v_a_3020_);
v___y_3003_ = v_a_3018_;
v___y_3004_ = v___x_3019_;
v___y_3005_ = v___x_3021_;
goto v___jp_3002_;
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec(v___y_3016_);
lean_dec(v___x_2991_);
lean_dec(v_fst_2989_);
lean_del_object(v___x_2987_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec(v_trace_2960_);
lean_dec_ref(v_cfg_2959_);
v_a_3023_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3017_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3017_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
v___jp_3031_:
{
if (v___y_3033_ == 0)
{
uint8_t v___x_3034_; 
lean_del_object(v___x_2987_);
v___x_3034_ = l_List_isEmpty___redArg(v_fst_2989_);
lean_dec(v_fst_2989_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_dec(v___y_3032_);
lean_dec(v___x_2991_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec(v_trace_2960_);
lean_dec_ref(v_cfg_2959_);
v___x_3035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3036_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3035_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
return v___x_3036_;
}
else
{
lean_object* v___x_3037_; 
v___x_3037_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3032_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3046_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3046_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3046_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; lean_object* v___x_3044_; 
v___x_3042_ = l_List_appendTR___redArg(v___x_2991_, v_a_3038_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3042_);
v___x_3044_ = v___x_3040_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
else
{
lean_dec(v___x_2991_);
return v___x_3037_;
}
}
}
else
{
v___y_3016_ = v___y_3032_;
goto v___jp_3015_;
}
}
v___jp_3047_:
{
uint8_t v_commitIndependentGoals_3049_; lean_object* v___x_3050_; 
v_commitIndependentGoals_3049_ = lean_ctor_get_uint8(v_cfg_2959_, sizeof(void*)*4);
lean_inc(v___x_2991_);
v___x_3050_ = l_List_appendTR___redArg(v_a_3048_, v___x_2991_);
if (v_commitIndependentGoals_3049_ == 0)
{
v___y_3032_ = v___x_3050_;
v___y_3033_ = v___x_2978_;
goto v___jp_3031_;
}
else
{
uint8_t v___x_3051_; 
v___x_3051_ = l_List_isEmpty___redArg(v___x_2991_);
if (v___x_3051_ == 0)
{
v___y_3016_ = v___x_3050_;
goto v___jp_3015_;
}
else
{
v___y_3032_ = v___x_3050_;
v___y_3033_ = v___x_2978_;
goto v___jp_3031_;
}
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec(v_snd_2974_);
lean_dec(v_goals_2963_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec(v_trace_2960_);
lean_dec_ref(v_cfg_2959_);
v_a_3058_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_2984_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_2984_);
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
lean_object* v___f_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v_a_3074_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v_a_3088_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v_a_3093_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v_a_3100_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; uint8_t v___y_3118_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3141_; lean_object* v___y_3142_; uint8_t v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v_a_3147_; lean_object* v___y_3160_; uint8_t v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v_a_3166_; lean_object* v___y_3169_; uint8_t v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v_a_3175_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; uint8_t v___y_3181_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v_a_3186_; lean_object* v___y_3190_; lean_object* v___y_3191_; uint8_t v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3202_; lean_object* v___y_3203_; uint8_t v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; uint8_t v___y_3212_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; uint8_t v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3233_; lean_object* v___y_3234_; uint8_t v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; uint8_t v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; uint8_t v___y_3252_; lean_object* v___y_3260_; lean_object* v___y_3261_; uint8_t v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v_a_3268_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; uint8_t v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v_a_3279_; lean_object* v___y_3289_; lean_object* v___y_3290_; uint8_t v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v_a_3295_; lean_object* v___y_3298_; lean_object* v___y_3299_; uint8_t v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v_a_3304_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; uint8_t v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v_a_3315_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; uint8_t v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; uint8_t v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; uint8_t v___y_3341_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; uint8_t v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; uint8_t v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; uint8_t v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; uint8_t v___y_3388_; uint8_t v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; uint8_t v___y_3394_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; uint8_t v___y_3402_; uint8_t v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v_a_3408_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; uint8_t v___y_3416_; uint8_t v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; uint8_t v___y_3443_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v_a_3455_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v_a_3462_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v_a_3477_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v_a_3482_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v_a_3489_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; uint8_t v___y_3507_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3530_; lean_object* v___y_3531_; uint8_t v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v_a_3536_; lean_object* v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v_a_3552_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; uint8_t v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v_a_3563_; lean_object* v___y_3567_; lean_object* v___y_3568_; uint8_t v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v_a_3573_; lean_object* v___y_3576_; lean_object* v___y_3577_; uint8_t v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3586_; lean_object* v___y_3587_; uint8_t v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; uint8_t v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; uint8_t v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; lean_object* v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; uint8_t v___y_3620_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; uint8_t v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; uint8_t v___y_3644_; uint8_t v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; uint8_t v___y_3651_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; uint8_t v___y_3659_; uint8_t v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v_a_3665_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; uint8_t v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v_a_3676_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; uint8_t v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v_a_3695_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; uint8_t v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v_a_3704_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; uint8_t v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v_a_3715_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; uint8_t v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; uint8_t v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; uint8_t v___y_3741_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; uint8_t v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; uint8_t v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; uint8_t v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; uint8_t v___y_3781_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; uint8_t v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v_a_3797_; lean_object* v___y_3802_; lean_object* v___y_3803_; uint8_t v___y_3804_; uint8_t v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; uint8_t v___y_3832_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v_a_3844_; 
lean_inc(v_snd_2974_);
lean_inc(v_fst_2973_);
v___f_3066_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3066_, 0, v_fst_2973_);
lean_closure_set(v___f_3066_, 1, v_snd_2974_);
v___x_3067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_3068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_2960_);
v___x_3069_ = l_Lean_Name_append(v___x_3068_, v_trace_2960_);
v___x_3070_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2981_, v_options_2980_, v___x_3069_);
lean_dec(v___x_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3893_ = l_Lean_trace_profiler;
v___x_3894_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2980_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; 
lean_dec_ref(v___f_3066_);
lean_del_object(v___x_2976_);
v___x_3895_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2973_, v___f_2983_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_4163_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_3898_ = v___x_3895_;
v_isShared_3899_ = v_isSharedCheck_4163_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3895_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_4163_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v_fst_3900_; lean_object* v_snd_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_4162_; 
v_fst_3900_ = lean_ctor_get(v_a_3896_, 0);
v_snd_3901_ = lean_ctor_get(v_a_3896_, 1);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_a_3896_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_3903_ = v_a_3896_;
v_isShared_3904_ = v_isSharedCheck_4162_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_snd_3901_);
lean_inc(v_fst_3900_);
lean_dec(v_a_3896_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_4162_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v_a_3907_; lean_object* v___y_3914_; lean_object* v___y_3917_; lean_object* v___y_3918_; uint8_t v___y_3919_; lean_object* v___y_3930_; lean_object* v___y_3946_; uint8_t v___y_3947_; lean_object* v_a_3962_; lean_object* v___f_3966_; lean_object* v___x_3967_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v_a_3971_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v_a_3988_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v_a_3993_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v_a_3999_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; uint8_t v___y_4018_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; uint8_t v___y_4036_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v_a_4046_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v_a_4053_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v_a_4065_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v_a_4070_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v_a_4075_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; uint8_t v___y_4089_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4117_; uint8_t v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; uint8_t v___y_4121_; lean_object* v___y_4126_; uint8_t v___y_4127_; lean_object* v___y_4128_; lean_object* v_a_4129_; 
v___x_3905_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3901_, v___x_2970_);
lean_inc(v___x_3905_);
lean_inc(v_fst_3900_);
v___f_3966_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3966_, 0, v_fst_3900_);
lean_closure_set(v___f_3966_, 1, v___x_3905_);
v___x_3967_ = lean_box(0);
if (v___x_3070_ == 0)
{
if (v___x_3894_ == 0)
{
lean_object* v___x_4158_; 
lean_dec_ref(v___f_3966_);
lean_del_object(v___x_3903_);
v___x_4158_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2982_, v___x_2978_, v_goals_2963_, v___x_3967_, v_a_2966_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4160_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref_known(v___x_4158_, 1);
v___x_4160_ = l_List_reverse___redArg(v_a_4159_);
v_a_3962_ = v___x_4160_;
goto v___jp_3961_;
}
else
{
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4161_; 
v_a_4161_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4158_, 1);
v_a_3962_ = v_a_4161_;
goto v___jp_3961_;
}
else
{
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
lean_del_object(v___x_3898_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec(v_trace_2960_);
lean_dec_ref(v_cfg_2959_);
return v___x_4158_;
}
}
}
else
{
lean_del_object(v___x_3898_);
goto v___jp_4133_;
}
}
else
{
lean_del_object(v___x_3898_);
goto v___jp_4133_;
}
v___jp_3906_:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3908_ = l_List_appendTR___redArg(v___x_3905_, v_fst_3900_);
v___x_3909_ = l_List_appendTR___redArg(v___x_3908_, v_a_3907_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 0, v___x_3909_);
v___x_3911_ = v___x_3898_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
v___jp_3913_:
{
if (lean_obj_tag(v___y_3914_) == 0)
{
lean_object* v_a_3915_; 
v_a_3915_ = lean_ctor_get(v___y_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___y_3914_, 1);
v_a_3907_ = v_a_3915_;
goto v___jp_3906_;
}
else
{
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
lean_del_object(v___x_3898_);
return v___y_3914_;
}
}
v___jp_3916_:
{
if (v___y_3919_ == 0)
{
lean_object* v___x_3920_; 
lean_dec_ref(v___y_3917_);
v___x_3920_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3918_, v_a_2966_, v_a_2968_);
lean_dec_ref(v___y_3918_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_dec_ref_known(v___x_3920_, 1);
v_a_3907_ = v_snd_2974_;
goto v___jp_3906_;
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
lean_del_object(v___x_3898_);
lean_dec(v_snd_2974_);
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3920_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3920_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
else
{
lean_dec_ref(v___y_3918_);
lean_dec(v_snd_2974_);
v___y_3914_ = v___y_3917_;
goto v___jp_3913_;
}
}
v___jp_3929_:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_Meta_saveState___redArg(v_a_2966_, v_a_2968_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3933_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
lean_inc(v_snd_2974_);
v___x_3933_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3930_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_dec(v_a_3932_);
lean_dec(v_snd_2974_);
v___y_3914_ = v___x_3933_;
goto v___jp_3913_;
}
else
{
lean_object* v_a_3934_; uint8_t v___x_3935_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
v___x_3935_ = l_Lean_Exception_isInterrupt(v_a_3934_);
if (v___x_3935_ == 0)
{
uint8_t v___x_3936_; 
v___x_3936_ = l_Lean_Exception_isRuntime(v_a_3934_);
v___y_3917_ = v___x_3933_;
v___y_3918_ = v_a_3932_;
v___y_3919_ = v___x_3936_;
goto v___jp_3916_;
}
else
{
lean_dec(v_a_3934_);
v___y_3917_ = v___x_3933_;
v___y_3918_ = v_a_3932_;
v___y_3919_ = v___x_3935_;
goto v___jp_3916_;
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v___y_3930_);
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
lean_del_object(v___x_3898_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec(v_trace_2960_);
lean_dec_ref(v_cfg_2959_);
v_a_3937_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3931_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3931_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
v___jp_3945_:
{
if (v___y_3947_ == 0)
{
uint8_t v___x_3948_; 
lean_del_object(v___x_3898_);
v___x_3948_ = l_List_isEmpty___redArg(v_fst_3900_);
lean_dec(v_fst_3900_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
lean_dec(v___y_3946_);
lean_dec(v___x_3905_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec(v_trace_2960_);
lean_dec_ref(v_cfg_2959_);
v___x_3949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3950_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3949_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
return v___x_3950_;
}
else
{
lean_object* v___x_3951_; 
v___x_3951_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3946_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3960_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3954_ = v___x_3951_;
v_isShared_3955_ = v_isSharedCheck_3960_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3960_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3958_; 
v___x_3956_ = l_List_appendTR___redArg(v___x_3905_, v_a_3952_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v___x_3956_);
v___x_3958_ = v___x_3954_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
else
{
lean_dec(v___x_3905_);
return v___x_3951_;
}
}
}
else
{
v___y_3930_ = v___y_3946_;
goto v___jp_3929_;
}
}
v___jp_3961_:
{
uint8_t v_commitIndependentGoals_3963_; lean_object* v___x_3964_; 
v_commitIndependentGoals_3963_ = lean_ctor_get_uint8(v_cfg_2959_, sizeof(void*)*4);
lean_inc(v___x_3905_);
v___x_3964_ = l_List_appendTR___redArg(v_a_3962_, v___x_3905_);
if (v_commitIndependentGoals_3963_ == 0)
{
v___y_3946_ = v___x_3964_;
v___y_3947_ = v___x_2978_;
goto v___jp_3945_;
}
else
{
uint8_t v___x_3965_; 
v___x_3965_ = l_List_isEmpty___redArg(v___x_3905_);
if (v___x_3965_ == 0)
{
v___y_3930_ = v___x_3964_;
goto v___jp_3929_;
}
else
{
v___y_3946_ = v___x_3964_;
v___y_3947_ = v___x_2978_;
goto v___jp_3945_;
}
}
}
v___jp_3968_:
{
lean_object* v___x_3972_; double v___x_3973_; double v___x_3974_; double v___x_3975_; double v___x_3976_; double v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3981_; 
v___x_3972_ = lean_io_mono_nanos_now();
v___x_3973_ = lean_float_of_nat(v___y_3969_);
v___x_3974_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3975_ = lean_float_div(v___x_3973_, v___x_3974_);
v___x_3976_ = lean_float_of_nat(v___x_3972_);
v___x_3977_ = lean_float_div(v___x_3976_, v___x_3974_);
v___x_3978_ = lean_box_float(v___x_3975_);
v___x_3979_ = lean_box_float(v___x_3977_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 1, v___x_3979_);
lean_ctor_set(v___x_3903_, 0, v___x_3978_);
v___x_3981_ = v___x_3903_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3978_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v___x_3979_);
v___x_3981_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3982_, 0, v_a_3971_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2960_, v_hasTrace_2982_, v___x_3067_, v_options_2980_, v___x_3070_, v___y_3970_, v___f_3966_, v___x_3982_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
return v___x_3983_;
}
}
v___jp_3985_:
{
lean_object* v___x_3989_; 
v___x_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3989_, 0, v_a_3988_);
v___y_3969_ = v___y_3986_;
v___y_3970_ = v___y_3987_;
v_a_3971_ = v___x_3989_;
goto v___jp_3968_;
}
v___jp_3990_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3994_ = l_List_appendTR___redArg(v___x_3905_, v_fst_3900_);
v___x_3995_ = l_List_appendTR___redArg(v___x_3994_, v_a_3993_);
v___y_3986_ = v___y_3991_;
v___y_3987_ = v___y_3992_;
v_a_3988_ = v___x_3995_;
goto v___jp_3985_;
}
v___jp_3996_:
{
lean_object* v___x_4000_; 
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v_a_3999_);
v___y_3969_ = v___y_3997_;
v___y_3970_ = v___y_3998_;
v_a_3971_ = v___x_4000_;
goto v___jp_3968_;
}
v___jp_4001_:
{
if (lean_obj_tag(v___y_4004_) == 0)
{
lean_object* v_a_4005_; 
v_a_4005_ = lean_ctor_get(v___y_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___y_4004_, 1);
v___y_3986_ = v___y_4002_;
v___y_3987_ = v___y_4003_;
v_a_3988_ = v_a_4005_;
goto v___jp_3985_;
}
else
{
lean_object* v_a_4006_; 
v_a_4006_ = lean_ctor_get(v___y_4004_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___y_4004_, 1);
v___y_3997_ = v___y_4002_;
v___y_3998_ = v___y_4003_;
v_a_3999_ = v_a_4006_;
goto v___jp_3996_;
}
}
v___jp_4007_:
{
if (lean_obj_tag(v___y_4010_) == 0)
{
lean_object* v_a_4011_; 
v_a_4011_ = lean_ctor_get(v___y_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___y_4010_, 1);
v___y_3991_ = v___y_4008_;
v___y_3992_ = v___y_4009_;
v_a_3993_ = v_a_4011_;
goto v___jp_3990_;
}
else
{
lean_object* v_a_4012_; 
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
v_a_4012_ = lean_ctor_get(v___y_4010_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v___y_4010_, 1);
v___y_3997_ = v___y_4008_;
v___y_3998_ = v___y_4009_;
v_a_3999_ = v_a_4012_;
goto v___jp_3996_;
}
}
v___jp_4013_:
{
if (v___y_4018_ == 0)
{
lean_object* v___x_4019_; 
lean_dec_ref(v___y_4017_);
v___x_4019_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4014_, v_a_2966_, v_a_2968_);
lean_dec_ref(v___y_4014_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_dec_ref_known(v___x_4019_, 1);
v___y_3991_ = v___y_4015_;
v___y_3992_ = v___y_4016_;
v_a_3993_ = v_snd_2974_;
goto v___jp_3990_;
}
else
{
lean_object* v_a_4020_; 
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
lean_dec(v_snd_2974_);
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref_known(v___x_4019_, 1);
v___y_3997_ = v___y_4015_;
v___y_3998_ = v___y_4016_;
v_a_3999_ = v_a_4020_;
goto v___jp_3996_;
}
}
else
{
lean_dec_ref(v___y_4014_);
lean_dec(v_snd_2974_);
v___y_4008_ = v___y_4015_;
v___y_4009_ = v___y_4016_;
v___y_4010_ = v___y_4017_;
goto v___jp_4007_;
}
}
v___jp_4021_:
{
lean_object* v___x_4025_; 
v___x_4025_ = l_Lean_Meta_saveState___redArg(v_a_2966_, v_a_2968_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4027_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4025_, 1);
lean_inc(v_snd_2974_);
lean_inc(v_trace_2960_);
v___x_4027_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_4022_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_dec(v_a_4026_);
lean_dec(v_snd_2974_);
v___y_4008_ = v___y_4023_;
v___y_4009_ = v___y_4024_;
v___y_4010_ = v___x_4027_;
goto v___jp_4007_;
}
else
{
lean_object* v_a_4028_; uint8_t v___x_4029_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
v___x_4029_ = l_Lean_Exception_isInterrupt(v_a_4028_);
if (v___x_4029_ == 0)
{
uint8_t v___x_4030_; 
v___x_4030_ = l_Lean_Exception_isRuntime(v_a_4028_);
v___y_4014_ = v_a_4026_;
v___y_4015_ = v___y_4023_;
v___y_4016_ = v___y_4024_;
v___y_4017_ = v___x_4027_;
v___y_4018_ = v___x_4030_;
goto v___jp_4013_;
}
else
{
lean_dec(v_a_4028_);
v___y_4014_ = v_a_4026_;
v___y_4015_ = v___y_4023_;
v___y_4016_ = v___y_4024_;
v___y_4017_ = v___x_4027_;
v___y_4018_ = v___x_4029_;
goto v___jp_4013_;
}
}
}
else
{
lean_object* v_a_4031_; 
lean_dec(v___y_4022_);
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_4031_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4031_);
lean_dec_ref_known(v___x_4025_, 1);
v___y_3997_ = v___y_4023_;
v___y_3998_ = v___y_4024_;
v_a_3999_ = v_a_4031_;
goto v___jp_3996_;
}
}
v___jp_4032_:
{
if (v___y_4036_ == 0)
{
uint8_t v___x_4037_; 
v___x_4037_ = l_List_isEmpty___redArg(v_fst_3900_);
lean_dec(v_fst_3900_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
lean_dec(v___y_4033_);
lean_dec(v___x_3905_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v___x_4038_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4039_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4038_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_4002_ = v___y_4034_;
v___y_4003_ = v___y_4035_;
v___y_4004_ = v___x_4039_;
goto v___jp_4001_;
}
else
{
lean_object* v___x_4040_; 
lean_inc(v_trace_2960_);
v___x_4040_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_4033_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___x_4040_, 1);
v___x_4042_ = l_List_appendTR___redArg(v___x_3905_, v_a_4041_);
v___y_3986_ = v___y_4034_;
v___y_3987_ = v___y_4035_;
v_a_3988_ = v___x_4042_;
goto v___jp_3985_;
}
else
{
lean_dec(v___x_3905_);
v___y_4002_ = v___y_4034_;
v___y_4003_ = v___y_4035_;
v___y_4004_ = v___x_4040_;
goto v___jp_4001_;
}
}
}
else
{
v___y_4022_ = v___y_4033_;
v___y_4023_ = v___y_4034_;
v___y_4024_ = v___y_4035_;
goto v___jp_4021_;
}
}
v___jp_4043_:
{
uint8_t v_commitIndependentGoals_4047_; lean_object* v___x_4048_; 
v_commitIndependentGoals_4047_ = lean_ctor_get_uint8(v_cfg_2959_, sizeof(void*)*4);
lean_inc(v___x_3905_);
v___x_4048_ = l_List_appendTR___redArg(v_a_4046_, v___x_3905_);
if (v_commitIndependentGoals_4047_ == 0)
{
v___y_4033_ = v___x_4048_;
v___y_4034_ = v___y_4044_;
v___y_4035_ = v___y_4045_;
v___y_4036_ = v___x_2978_;
goto v___jp_4032_;
}
else
{
uint8_t v___x_4049_; 
v___x_4049_ = l_List_isEmpty___redArg(v___x_3905_);
if (v___x_4049_ == 0)
{
v___y_4022_ = v___x_4048_;
v___y_4023_ = v___y_4044_;
v___y_4024_ = v___y_4045_;
goto v___jp_4021_;
}
else
{
v___y_4033_ = v___x_4048_;
v___y_4034_ = v___y_4044_;
v___y_4035_ = v___y_4045_;
v___y_4036_ = v___x_2978_;
goto v___jp_4032_;
}
}
}
v___jp_4050_:
{
lean_object* v___x_4054_; double v___x_4055_; double v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4054_ = lean_io_get_num_heartbeats();
v___x_4055_ = lean_float_of_nat(v___y_4051_);
v___x_4056_ = lean_float_of_nat(v___x_4054_);
v___x_4057_ = lean_box_float(v___x_4055_);
v___x_4058_ = lean_box_float(v___x_4056_);
v___x_4059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4057_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
v___x_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4060_, 0, v_a_4053_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
v___x_4061_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2960_, v_hasTrace_2982_, v___x_3067_, v_options_2980_, v___x_3070_, v___y_4052_, v___f_3966_, v___x_4060_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
return v___x_4061_;
}
v___jp_4062_:
{
lean_object* v___x_4066_; 
v___x_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4066_, 0, v_a_4065_);
v___y_4051_ = v___y_4063_;
v___y_4052_ = v___y_4064_;
v_a_4053_ = v___x_4066_;
goto v___jp_4050_;
}
v___jp_4067_:
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4071_, 0, v_a_4070_);
v___y_4051_ = v___y_4068_;
v___y_4052_ = v___y_4069_;
v_a_4053_ = v___x_4071_;
goto v___jp_4050_;
}
v___jp_4072_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = l_List_appendTR___redArg(v___x_3905_, v_fst_3900_);
v___x_4077_ = l_List_appendTR___redArg(v___x_4076_, v_a_4075_);
v___y_4068_ = v___y_4073_;
v___y_4069_ = v___y_4074_;
v_a_4070_ = v___x_4077_;
goto v___jp_4067_;
}
v___jp_4078_:
{
if (lean_obj_tag(v___y_4081_) == 0)
{
lean_object* v_a_4082_; 
v_a_4082_ = lean_ctor_get(v___y_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v___y_4081_, 1);
v___y_4073_ = v___y_4079_;
v___y_4074_ = v___y_4080_;
v_a_4075_ = v_a_4082_;
goto v___jp_4072_;
}
else
{
lean_object* v_a_4083_; 
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
v_a_4083_ = lean_ctor_get(v___y_4081_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___y_4081_, 1);
v___y_4063_ = v___y_4079_;
v___y_4064_ = v___y_4080_;
v_a_4065_ = v_a_4083_;
goto v___jp_4062_;
}
}
v___jp_4084_:
{
if (v___y_4089_ == 0)
{
lean_object* v___x_4090_; 
lean_dec_ref(v___y_4088_);
v___x_4090_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4085_, v_a_2966_, v_a_2968_);
lean_dec_ref(v___y_4085_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_dec_ref_known(v___x_4090_, 1);
v___y_4073_ = v___y_4086_;
v___y_4074_ = v___y_4087_;
v_a_4075_ = v_snd_2974_;
goto v___jp_4072_;
}
else
{
lean_object* v_a_4091_; 
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
lean_dec(v_snd_2974_);
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref_known(v___x_4090_, 1);
v___y_4063_ = v___y_4086_;
v___y_4064_ = v___y_4087_;
v_a_4065_ = v_a_4091_;
goto v___jp_4062_;
}
}
else
{
lean_dec_ref(v___y_4085_);
lean_dec(v_snd_2974_);
v___y_4079_ = v___y_4086_;
v___y_4080_ = v___y_4087_;
v___y_4081_ = v___y_4088_;
goto v___jp_4078_;
}
}
v___jp_4092_:
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Lean_Meta_saveState___redArg(v_a_2966_, v_a_2968_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v_a_4097_; lean_object* v___x_4098_; 
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4096_, 1);
lean_inc(v_snd_2974_);
lean_inc(v_trace_2960_);
v___x_4098_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_4094_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_dec(v_a_4097_);
lean_dec(v_snd_2974_);
v___y_4079_ = v___y_4093_;
v___y_4080_ = v___y_4095_;
v___y_4081_ = v___x_4098_;
goto v___jp_4078_;
}
else
{
lean_object* v_a_4099_; uint8_t v___x_4100_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
v___x_4100_ = l_Lean_Exception_isInterrupt(v_a_4099_);
if (v___x_4100_ == 0)
{
uint8_t v___x_4101_; 
v___x_4101_ = l_Lean_Exception_isRuntime(v_a_4099_);
v___y_4085_ = v_a_4097_;
v___y_4086_ = v___y_4093_;
v___y_4087_ = v___y_4095_;
v___y_4088_ = v___x_4098_;
v___y_4089_ = v___x_4101_;
goto v___jp_4084_;
}
else
{
lean_dec(v_a_4099_);
v___y_4085_ = v_a_4097_;
v___y_4086_ = v___y_4093_;
v___y_4087_ = v___y_4095_;
v___y_4088_ = v___x_4098_;
v___y_4089_ = v___x_4100_;
goto v___jp_4084_;
}
}
}
else
{
lean_object* v_a_4102_; 
lean_dec(v___y_4094_);
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_4102_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4096_, 1);
v___y_4063_ = v___y_4093_;
v___y_4064_ = v___y_4095_;
v_a_4065_ = v_a_4102_;
goto v___jp_4062_;
}
}
v___jp_4103_:
{
if (lean_obj_tag(v___y_4106_) == 0)
{
lean_object* v_a_4107_; 
v_a_4107_ = lean_ctor_get(v___y_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v___y_4106_, 1);
v___y_4068_ = v___y_4104_;
v___y_4069_ = v___y_4105_;
v_a_4070_ = v_a_4107_;
goto v___jp_4067_;
}
else
{
lean_object* v_a_4108_; 
v_a_4108_ = lean_ctor_get(v___y_4106_, 0);
lean_inc(v_a_4108_);
lean_dec_ref_known(v___y_4106_, 1);
v___y_4063_ = v___y_4104_;
v___y_4064_ = v___y_4105_;
v_a_4065_ = v_a_4108_;
goto v___jp_4062_;
}
}
v___jp_4109_:
{
lean_object* v___x_4113_; 
lean_inc(v_trace_2960_);
v___x_4113_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_4111_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4115_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___x_4113_, 1);
v___x_4115_ = l_List_appendTR___redArg(v___x_3905_, v_a_4114_);
v___y_4068_ = v___y_4110_;
v___y_4069_ = v___y_4112_;
v_a_4070_ = v___x_4115_;
goto v___jp_4067_;
}
else
{
lean_dec(v___x_3905_);
v___y_4104_ = v___y_4110_;
v___y_4105_ = v___y_4112_;
v___y_4106_ = v___x_4113_;
goto v___jp_4103_;
}
}
v___jp_4116_:
{
if (v___y_4121_ == 0)
{
uint8_t v___x_4122_; 
v___x_4122_ = l_List_isEmpty___redArg(v_fst_3900_);
lean_dec(v_fst_3900_);
if (v___x_4122_ == 0)
{
if (v___y_4118_ == 0)
{
v___y_4110_ = v___y_4117_;
v___y_4111_ = v___y_4119_;
v___y_4112_ = v___y_4120_;
goto v___jp_4109_;
}
else
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
lean_dec(v___y_4119_);
lean_dec(v___x_3905_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v___x_4123_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4124_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4123_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_4104_ = v___y_4117_;
v___y_4105_ = v___y_4120_;
v___y_4106_ = v___x_4124_;
goto v___jp_4103_;
}
}
else
{
v___y_4110_ = v___y_4117_;
v___y_4111_ = v___y_4119_;
v___y_4112_ = v___y_4120_;
goto v___jp_4109_;
}
}
else
{
v___y_4093_ = v___y_4117_;
v___y_4094_ = v___y_4119_;
v___y_4095_ = v___y_4120_;
goto v___jp_4092_;
}
}
v___jp_4125_:
{
uint8_t v_commitIndependentGoals_4130_; lean_object* v___x_4131_; 
v_commitIndependentGoals_4130_ = lean_ctor_get_uint8(v_cfg_2959_, sizeof(void*)*4);
lean_inc(v___x_3905_);
v___x_4131_ = l_List_appendTR___redArg(v_a_4129_, v___x_3905_);
if (v_commitIndependentGoals_4130_ == 0)
{
v___y_4117_ = v___y_4126_;
v___y_4118_ = v___y_4127_;
v___y_4119_ = v___x_4131_;
v___y_4120_ = v___y_4128_;
v___y_4121_ = v___x_2978_;
goto v___jp_4116_;
}
else
{
uint8_t v___x_4132_; 
v___x_4132_ = l_List_isEmpty___redArg(v___x_3905_);
if (v___x_4132_ == 0)
{
v___y_4093_ = v___y_4126_;
v___y_4094_ = v___x_4131_;
v___y_4095_ = v___y_4128_;
goto v___jp_4092_;
}
else
{
v___y_4117_ = v___y_4126_;
v___y_4118_ = v___y_4127_;
v___y_4119_ = v___x_4131_;
v___y_4120_ = v___y_4128_;
v___y_4121_ = v___x_2978_;
goto v___jp_4116_;
}
}
}
v___jp_4133_:
{
lean_object* v___x_4134_; 
v___x_4134_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2968_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4136_; uint8_t v___x_4137_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4134_, 1);
v___x_4136_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4137_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2980_, v___x_4136_);
if (v___x_4137_ == 0)
{
lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4138_ = lean_io_mono_nanos_now();
v___x_4139_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2982_, v___x_2978_, v_goals_2963_, v___x_3967_, v_a_2966_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v___x_4141_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4139_, 1);
v___x_4141_ = l_List_reverse___redArg(v_a_4140_);
v___y_4044_ = v___x_4138_;
v___y_4045_ = v_a_4135_;
v_a_4046_ = v___x_4141_;
goto v___jp_4043_;
}
else
{
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4142_; 
v_a_4142_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4139_, 1);
v___y_4044_ = v___x_4138_;
v___y_4045_ = v_a_4135_;
v_a_4046_ = v_a_4142_;
goto v___jp_4043_;
}
else
{
lean_object* v_a_4143_; 
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_4143_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4139_, 1);
v___y_3997_ = v___x_4138_;
v___y_3998_ = v_a_4135_;
v_a_3999_ = v_a_4143_;
goto v___jp_3996_;
}
}
}
else
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
lean_del_object(v___x_3903_);
v___x_4144_ = lean_io_get_num_heartbeats();
v___x_4145_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2982_, v___x_2978_, v_goals_2963_, v___x_3967_, v_a_2966_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4147_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4145_, 1);
v___x_4147_ = l_List_reverse___redArg(v_a_4146_);
v___y_4126_ = v___x_4144_;
v___y_4127_ = v___x_4137_;
v___y_4128_ = v_a_4135_;
v_a_4129_ = v___x_4147_;
goto v___jp_4125_;
}
else
{
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4148_; 
v_a_4148_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4145_, 1);
v___y_4126_ = v___x_4144_;
v___y_4127_ = v___x_4137_;
v___y_4128_ = v_a_4135_;
v_a_4129_ = v_a_4148_;
goto v___jp_4125_;
}
else
{
lean_object* v_a_4149_; 
lean_dec(v___x_3905_);
lean_dec(v_fst_3900_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_4149_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4145_, 1);
v___y_4063_ = v___x_4144_;
v___y_4064_ = v_a_4135_;
v_a_4065_ = v_a_4149_;
goto v___jp_4062_;
}
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec_ref(v___f_3966_);
lean_dec(v___x_3905_);
lean_del_object(v___x_3903_);
lean_dec(v_fst_3900_);
lean_dec(v_snd_2974_);
lean_dec(v_goals_2963_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec(v_trace_2960_);
lean_dec_ref(v_cfg_2959_);
v_a_4150_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4134_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4134_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec(v_snd_2974_);
lean_dec(v_goals_2963_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec(v_trace_2960_);
lean_dec_ref(v_cfg_2959_);
v_a_4164_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_3895_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_3895_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
else
{
goto v___jp_3848_;
}
}
else
{
goto v___jp_3848_;
}
v___jp_3071_:
{
lean_object* v___x_3075_; double v___x_3076_; double v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3075_ = lean_io_get_num_heartbeats();
v___x_3076_ = lean_float_of_nat(v___y_3072_);
v___x_3077_ = lean_float_of_nat(v___x_3075_);
v___x_3078_ = lean_box_float(v___x_3076_);
v___x_3079_ = lean_box_float(v___x_3077_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 1, v___x_3079_);
lean_ctor_set(v___x_2976_, 0, v___x_3078_);
v___x_3081_ = v___x_2976_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v_a_3074_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2960_, v_hasTrace_2982_, v___x_3067_, v_options_2980_, v___x_3070_, v___y_3073_, v___f_3066_, v___x_3082_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
return v___x_3083_;
}
}
v___jp_3085_:
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v_a_3088_);
v___y_3072_ = v___y_3086_;
v___y_3073_ = v___y_3087_;
v_a_3074_ = v___x_3089_;
goto v___jp_3071_;
}
v___jp_3090_:
{
lean_object* v___x_3094_; 
v___x_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3094_, 0, v_a_3093_);
v___y_3072_ = v___y_3091_;
v___y_3073_ = v___y_3092_;
v_a_3074_ = v___x_3094_;
goto v___jp_3071_;
}
v___jp_3095_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = l_List_appendTR___redArg(v___y_3099_, v___y_3096_);
v___x_3102_ = l_List_appendTR___redArg(v___x_3101_, v_a_3100_);
v___y_3091_ = v___y_3097_;
v___y_3092_ = v___y_3098_;
v_a_3093_ = v___x_3102_;
goto v___jp_3090_;
}
v___jp_3103_:
{
if (lean_obj_tag(v___y_3108_) == 0)
{
lean_object* v_a_3109_; 
v_a_3109_ = lean_ctor_get(v___y_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___y_3108_, 1);
v___y_3096_ = v___y_3104_;
v___y_3097_ = v___y_3105_;
v___y_3098_ = v___y_3106_;
v___y_3099_ = v___y_3107_;
v_a_3100_ = v_a_3109_;
goto v___jp_3095_;
}
else
{
lean_object* v_a_3110_; 
lean_dec(v___y_3107_);
lean_dec(v___y_3104_);
v_a_3110_ = lean_ctor_get(v___y_3108_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___y_3108_, 1);
v___y_3086_ = v___y_3105_;
v___y_3087_ = v___y_3106_;
v_a_3088_ = v_a_3110_;
goto v___jp_3085_;
}
}
v___jp_3111_:
{
if (v___y_3118_ == 0)
{
lean_object* v___x_3119_; 
lean_dec_ref(v___y_3112_);
v___x_3119_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3115_, v_a_2966_, v_a_2968_);
lean_dec_ref(v___y_3115_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_dec_ref_known(v___x_3119_, 1);
v___y_3096_ = v___y_3113_;
v___y_3097_ = v___y_3114_;
v___y_3098_ = v___y_3116_;
v___y_3099_ = v___y_3117_;
v_a_3100_ = v_snd_2974_;
goto v___jp_3095_;
}
else
{
lean_object* v_a_3120_; 
lean_dec(v___y_3117_);
lean_dec(v___y_3113_);
lean_dec(v_snd_2974_);
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v___y_3086_ = v___y_3114_;
v___y_3087_ = v___y_3116_;
v_a_3088_ = v_a_3120_;
goto v___jp_3085_;
}
}
else
{
lean_dec_ref(v___y_3115_);
lean_dec(v_snd_2974_);
v___y_3104_ = v___y_3113_;
v___y_3105_ = v___y_3114_;
v___y_3106_ = v___y_3116_;
v___y_3107_ = v___y_3117_;
v___y_3108_ = v___y_3112_;
goto v___jp_3103_;
}
}
v___jp_3121_:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_Meta_saveState___redArg(v_a_2966_, v_a_2968_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3129_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3127_, 1);
lean_inc(v_snd_2974_);
lean_inc(v_trace_2960_);
v___x_3129_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3124_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_dec(v_a_3128_);
lean_dec(v_snd_2974_);
v___y_3104_ = v___y_3122_;
v___y_3105_ = v___y_3123_;
v___y_3106_ = v___y_3125_;
v___y_3107_ = v___y_3126_;
v___y_3108_ = v___x_3129_;
goto v___jp_3103_;
}
else
{
lean_object* v_a_3130_; uint8_t v___x_3131_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
v___x_3131_ = l_Lean_Exception_isInterrupt(v_a_3130_);
if (v___x_3131_ == 0)
{
uint8_t v___x_3132_; 
v___x_3132_ = l_Lean_Exception_isRuntime(v_a_3130_);
v___y_3112_ = v___x_3129_;
v___y_3113_ = v___y_3122_;
v___y_3114_ = v___y_3123_;
v___y_3115_ = v_a_3128_;
v___y_3116_ = v___y_3125_;
v___y_3117_ = v___y_3126_;
v___y_3118_ = v___x_3132_;
goto v___jp_3111_;
}
else
{
lean_dec(v_a_3130_);
v___y_3112_ = v___x_3129_;
v___y_3113_ = v___y_3122_;
v___y_3114_ = v___y_3123_;
v___y_3115_ = v_a_3128_;
v___y_3116_ = v___y_3125_;
v___y_3117_ = v___y_3126_;
v___y_3118_ = v___x_3131_;
goto v___jp_3111_;
}
}
}
else
{
lean_object* v_a_3133_; 
lean_dec(v___y_3126_);
lean_dec(v___y_3124_);
lean_dec(v___y_3122_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3133_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3127_, 1);
v___y_3086_ = v___y_3123_;
v___y_3087_ = v___y_3125_;
v_a_3088_ = v_a_3133_;
goto v___jp_3085_;
}
}
v___jp_3134_:
{
if (lean_obj_tag(v___y_3137_) == 0)
{
lean_object* v_a_3138_; 
v_a_3138_ = lean_ctor_get(v___y_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___y_3137_, 1);
v___y_3091_ = v___y_3135_;
v___y_3092_ = v___y_3136_;
v_a_3093_ = v_a_3138_;
goto v___jp_3090_;
}
else
{
lean_object* v_a_3139_; 
v_a_3139_ = lean_ctor_get(v___y_3137_, 0);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___y_3137_, 1);
v___y_3086_ = v___y_3135_;
v___y_3087_ = v___y_3136_;
v_a_3088_ = v_a_3139_;
goto v___jp_3085_;
}
}
v___jp_3140_:
{
lean_object* v___x_3148_; double v___x_3149_; double v___x_3150_; double v___x_3151_; double v___x_3152_; double v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3148_ = lean_io_mono_nanos_now();
v___x_3149_ = lean_float_of_nat(v___y_3144_);
v___x_3150_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3151_ = lean_float_div(v___x_3149_, v___x_3150_);
v___x_3152_ = lean_float_of_nat(v___x_3148_);
v___x_3153_ = lean_float_div(v___x_3152_, v___x_3150_);
v___x_3154_ = lean_box_float(v___x_3151_);
v___x_3155_ = lean_box_float(v___x_3153_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3154_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v_a_3147_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
lean_inc(v_trace_2960_);
v___x_3158_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2960_, v_hasTrace_2982_, v___x_3067_, v_options_2980_, v___y_3143_, v___y_3146_, v___y_3141_, v___x_3157_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_3135_ = v___y_3142_;
v___y_3136_ = v___y_3145_;
v___y_3137_ = v___x_3158_;
goto v___jp_3134_;
}
v___jp_3159_:
{
lean_object* v___x_3167_; 
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v_a_3166_);
v___y_3141_ = v___y_3160_;
v___y_3142_ = v___y_3162_;
v___y_3143_ = v___y_3161_;
v___y_3144_ = v___y_3163_;
v___y_3145_ = v___y_3164_;
v___y_3146_ = v___y_3165_;
v_a_3147_ = v___x_3167_;
goto v___jp_3140_;
}
v___jp_3168_:
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_a_3175_);
v___y_3141_ = v___y_3169_;
v___y_3142_ = v___y_3171_;
v___y_3143_ = v___y_3170_;
v___y_3144_ = v___y_3172_;
v___y_3145_ = v___y_3173_;
v___y_3146_ = v___y_3174_;
v_a_3147_ = v___x_3176_;
goto v___jp_3140_;
}
v___jp_3177_:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = l_List_appendTR___redArg(v___y_3185_, v___y_3178_);
v___x_3188_ = l_List_appendTR___redArg(v___x_3187_, v_a_3186_);
v___y_3169_ = v___y_3179_;
v___y_3170_ = v___y_3181_;
v___y_3171_ = v___y_3180_;
v___y_3172_ = v___y_3182_;
v___y_3173_ = v___y_3183_;
v___y_3174_ = v___y_3184_;
v_a_3175_ = v___x_3188_;
goto v___jp_3168_;
}
v___jp_3189_:
{
if (lean_obj_tag(v___y_3198_) == 0)
{
lean_object* v_a_3199_; 
v_a_3199_ = lean_ctor_get(v___y_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___y_3198_, 1);
v___y_3178_ = v___y_3190_;
v___y_3179_ = v___y_3191_;
v___y_3180_ = v___y_3193_;
v___y_3181_ = v___y_3192_;
v___y_3182_ = v___y_3194_;
v___y_3183_ = v___y_3195_;
v___y_3184_ = v___y_3197_;
v___y_3185_ = v___y_3196_;
v_a_3186_ = v_a_3199_;
goto v___jp_3177_;
}
else
{
lean_object* v_a_3200_; 
lean_dec(v___y_3196_);
lean_dec(v___y_3190_);
v_a_3200_ = lean_ctor_get(v___y_3198_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___y_3198_, 1);
v___y_3160_ = v___y_3191_;
v___y_3161_ = v___y_3192_;
v___y_3162_ = v___y_3193_;
v___y_3163_ = v___y_3194_;
v___y_3164_ = v___y_3195_;
v___y_3165_ = v___y_3197_;
v_a_3166_ = v_a_3200_;
goto v___jp_3159_;
}
}
v___jp_3201_:
{
if (v___y_3212_ == 0)
{
lean_object* v___x_3213_; 
lean_dec_ref(v___y_3210_);
v___x_3213_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3211_, v_a_2966_, v_a_2968_);
lean_dec_ref(v___y_3211_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_dec_ref_known(v___x_3213_, 1);
v___y_3178_ = v___y_3202_;
v___y_3179_ = v___y_3203_;
v___y_3180_ = v___y_3205_;
v___y_3181_ = v___y_3204_;
v___y_3182_ = v___y_3206_;
v___y_3183_ = v___y_3207_;
v___y_3184_ = v___y_3209_;
v___y_3185_ = v___y_3208_;
v_a_3186_ = v_snd_2974_;
goto v___jp_3177_;
}
else
{
lean_object* v_a_3214_; 
lean_dec(v___y_3208_);
lean_dec(v___y_3202_);
lean_dec(v_snd_2974_);
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v___y_3160_ = v___y_3203_;
v___y_3161_ = v___y_3204_;
v___y_3162_ = v___y_3205_;
v___y_3163_ = v___y_3206_;
v___y_3164_ = v___y_3207_;
v___y_3165_ = v___y_3209_;
v_a_3166_ = v_a_3214_;
goto v___jp_3159_;
}
}
else
{
lean_dec_ref(v___y_3211_);
lean_dec(v_snd_2974_);
v___y_3190_ = v___y_3202_;
v___y_3191_ = v___y_3203_;
v___y_3192_ = v___y_3204_;
v___y_3193_ = v___y_3205_;
v___y_3194_ = v___y_3206_;
v___y_3195_ = v___y_3207_;
v___y_3196_ = v___y_3208_;
v___y_3197_ = v___y_3209_;
v___y_3198_ = v___y_3210_;
goto v___jp_3189_;
}
}
v___jp_3215_:
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_Meta_saveState___redArg(v_a_2966_, v_a_2968_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3227_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3225_, 1);
lean_inc(v_snd_2974_);
lean_inc(v_trace_2960_);
v___x_3227_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3218_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_dec(v_a_3226_);
lean_dec(v_snd_2974_);
v___y_3190_ = v___y_3216_;
v___y_3191_ = v___y_3217_;
v___y_3192_ = v___y_3220_;
v___y_3193_ = v___y_3219_;
v___y_3194_ = v___y_3221_;
v___y_3195_ = v___y_3222_;
v___y_3196_ = v___y_3224_;
v___y_3197_ = v___y_3223_;
v___y_3198_ = v___x_3227_;
goto v___jp_3189_;
}
else
{
lean_object* v_a_3228_; uint8_t v___x_3229_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
v___x_3229_ = l_Lean_Exception_isInterrupt(v_a_3228_);
if (v___x_3229_ == 0)
{
uint8_t v___x_3230_; 
v___x_3230_ = l_Lean_Exception_isRuntime(v_a_3228_);
v___y_3202_ = v___y_3216_;
v___y_3203_ = v___y_3217_;
v___y_3204_ = v___y_3220_;
v___y_3205_ = v___y_3219_;
v___y_3206_ = v___y_3221_;
v___y_3207_ = v___y_3222_;
v___y_3208_ = v___y_3224_;
v___y_3209_ = v___y_3223_;
v___y_3210_ = v___x_3227_;
v___y_3211_ = v_a_3226_;
v___y_3212_ = v___x_3230_;
goto v___jp_3201_;
}
else
{
lean_dec(v_a_3228_);
v___y_3202_ = v___y_3216_;
v___y_3203_ = v___y_3217_;
v___y_3204_ = v___y_3220_;
v___y_3205_ = v___y_3219_;
v___y_3206_ = v___y_3221_;
v___y_3207_ = v___y_3222_;
v___y_3208_ = v___y_3224_;
v___y_3209_ = v___y_3223_;
v___y_3210_ = v___x_3227_;
v___y_3211_ = v_a_3226_;
v___y_3212_ = v___x_3229_;
goto v___jp_3201_;
}
}
}
else
{
lean_object* v_a_3231_; 
lean_dec(v___y_3224_);
lean_dec(v___y_3218_);
lean_dec(v___y_3216_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3231_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3225_, 1);
v___y_3160_ = v___y_3217_;
v___y_3161_ = v___y_3220_;
v___y_3162_ = v___y_3219_;
v___y_3163_ = v___y_3221_;
v___y_3164_ = v___y_3222_;
v___y_3165_ = v___y_3223_;
v_a_3166_ = v_a_3231_;
goto v___jp_3159_;
}
}
v___jp_3232_:
{
if (lean_obj_tag(v___y_3239_) == 0)
{
lean_object* v_a_3240_; 
v_a_3240_ = lean_ctor_get(v___y_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___y_3239_, 1);
v___y_3169_ = v___y_3233_;
v___y_3170_ = v___y_3235_;
v___y_3171_ = v___y_3234_;
v___y_3172_ = v___y_3236_;
v___y_3173_ = v___y_3237_;
v___y_3174_ = v___y_3238_;
v_a_3175_ = v_a_3240_;
goto v___jp_3168_;
}
else
{
lean_object* v_a_3241_; 
v_a_3241_ = lean_ctor_get(v___y_3239_, 0);
lean_inc(v_a_3241_);
lean_dec_ref_known(v___y_3239_, 1);
v___y_3160_ = v___y_3233_;
v___y_3161_ = v___y_3235_;
v___y_3162_ = v___y_3234_;
v___y_3163_ = v___y_3236_;
v___y_3164_ = v___y_3237_;
v___y_3165_ = v___y_3238_;
v_a_3166_ = v_a_3241_;
goto v___jp_3159_;
}
}
v___jp_3242_:
{
if (v___y_3252_ == 0)
{
uint8_t v___x_3253_; 
v___x_3253_ = l_List_isEmpty___redArg(v___y_3243_);
lean_dec(v___y_3243_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
lean_dec(v___y_3250_);
lean_dec(v___y_3245_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v___x_3254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3255_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3254_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_3233_ = v___y_3244_;
v___y_3234_ = v___y_3247_;
v___y_3235_ = v___y_3246_;
v___y_3236_ = v___y_3248_;
v___y_3237_ = v___y_3249_;
v___y_3238_ = v___y_3251_;
v___y_3239_ = v___x_3255_;
goto v___jp_3232_;
}
else
{
lean_object* v___x_3256_; 
lean_inc(v_trace_2960_);
v___x_3256_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3245_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3258_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref_known(v___x_3256_, 1);
v___x_3258_ = l_List_appendTR___redArg(v___y_3250_, v_a_3257_);
v___y_3169_ = v___y_3244_;
v___y_3170_ = v___y_3246_;
v___y_3171_ = v___y_3247_;
v___y_3172_ = v___y_3248_;
v___y_3173_ = v___y_3249_;
v___y_3174_ = v___y_3251_;
v_a_3175_ = v___x_3258_;
goto v___jp_3168_;
}
else
{
lean_dec(v___y_3250_);
v___y_3233_ = v___y_3244_;
v___y_3234_ = v___y_3247_;
v___y_3235_ = v___y_3246_;
v___y_3236_ = v___y_3248_;
v___y_3237_ = v___y_3249_;
v___y_3238_ = v___y_3251_;
v___y_3239_ = v___x_3256_;
goto v___jp_3232_;
}
}
}
else
{
v___y_3216_ = v___y_3243_;
v___y_3217_ = v___y_3244_;
v___y_3218_ = v___y_3245_;
v___y_3219_ = v___y_3247_;
v___y_3220_ = v___y_3246_;
v___y_3221_ = v___y_3248_;
v___y_3222_ = v___y_3249_;
v___y_3223_ = v___y_3251_;
v___y_3224_ = v___y_3250_;
goto v___jp_3215_;
}
}
v___jp_3259_:
{
uint8_t v_commitIndependentGoals_3269_; lean_object* v___x_3270_; 
v_commitIndependentGoals_3269_ = lean_ctor_get_uint8(v_cfg_2959_, sizeof(void*)*4);
lean_inc(v___y_3267_);
v___x_3270_ = l_List_appendTR___redArg(v_a_3268_, v___y_3267_);
if (v_commitIndependentGoals_3269_ == 0)
{
v___y_3243_ = v___y_3260_;
v___y_3244_ = v___y_3261_;
v___y_3245_ = v___x_3270_;
v___y_3246_ = v___y_3262_;
v___y_3247_ = v___y_3263_;
v___y_3248_ = v___y_3264_;
v___y_3249_ = v___y_3265_;
v___y_3250_ = v___y_3267_;
v___y_3251_ = v___y_3266_;
v___y_3252_ = v___x_2978_;
goto v___jp_3242_;
}
else
{
uint8_t v___x_3271_; 
v___x_3271_ = l_List_isEmpty___redArg(v___y_3267_);
if (v___x_3271_ == 0)
{
v___y_3216_ = v___y_3260_;
v___y_3217_ = v___y_3261_;
v___y_3218_ = v___x_3270_;
v___y_3219_ = v___y_3263_;
v___y_3220_ = v___y_3262_;
v___y_3221_ = v___y_3264_;
v___y_3222_ = v___y_3265_;
v___y_3223_ = v___y_3266_;
v___y_3224_ = v___y_3267_;
goto v___jp_3215_;
}
else
{
v___y_3243_ = v___y_3260_;
v___y_3244_ = v___y_3261_;
v___y_3245_ = v___x_3270_;
v___y_3246_ = v___y_3262_;
v___y_3247_ = v___y_3263_;
v___y_3248_ = v___y_3264_;
v___y_3249_ = v___y_3265_;
v___y_3250_ = v___y_3267_;
v___y_3251_ = v___y_3266_;
v___y_3252_ = v___x_2978_;
goto v___jp_3242_;
}
}
}
v___jp_3272_:
{
lean_object* v___x_3280_; double v___x_3281_; double v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3280_ = lean_io_get_num_heartbeats();
v___x_3281_ = lean_float_of_nat(v___y_3274_);
v___x_3282_ = lean_float_of_nat(v___x_3280_);
v___x_3283_ = lean_box_float(v___x_3281_);
v___x_3284_ = lean_box_float(v___x_3282_);
v___x_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v_a_3279_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
lean_inc(v_trace_2960_);
v___x_3287_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2960_, v_hasTrace_2982_, v___x_3067_, v_options_2980_, v___y_3276_, v___y_3278_, v___y_3273_, v___x_3286_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_3135_ = v___y_3275_;
v___y_3136_ = v___y_3277_;
v___y_3137_ = v___x_3287_;
goto v___jp_3134_;
}
v___jp_3288_:
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3296_, 0, v_a_3295_);
v___y_3273_ = v___y_3289_;
v___y_3274_ = v___y_3290_;
v___y_3275_ = v___y_3292_;
v___y_3276_ = v___y_3291_;
v___y_3277_ = v___y_3293_;
v___y_3278_ = v___y_3294_;
v_a_3279_ = v___x_3296_;
goto v___jp_3272_;
}
v___jp_3297_:
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3305_, 0, v_a_3304_);
v___y_3273_ = v___y_3298_;
v___y_3274_ = v___y_3299_;
v___y_3275_ = v___y_3301_;
v___y_3276_ = v___y_3300_;
v___y_3277_ = v___y_3302_;
v___y_3278_ = v___y_3303_;
v_a_3279_ = v___x_3305_;
goto v___jp_3272_;
}
v___jp_3306_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = l_List_appendTR___redArg(v___y_3314_, v___y_3307_);
v___x_3317_ = l_List_appendTR___redArg(v___x_3316_, v_a_3315_);
v___y_3298_ = v___y_3308_;
v___y_3299_ = v___y_3309_;
v___y_3300_ = v___y_3311_;
v___y_3301_ = v___y_3310_;
v___y_3302_ = v___y_3312_;
v___y_3303_ = v___y_3313_;
v_a_3304_ = v___x_3317_;
goto v___jp_3297_;
}
v___jp_3318_:
{
if (lean_obj_tag(v___y_3327_) == 0)
{
lean_object* v_a_3328_; 
v_a_3328_ = lean_ctor_get(v___y_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___y_3327_, 1);
v___y_3307_ = v___y_3319_;
v___y_3308_ = v___y_3320_;
v___y_3309_ = v___y_3321_;
v___y_3310_ = v___y_3323_;
v___y_3311_ = v___y_3322_;
v___y_3312_ = v___y_3324_;
v___y_3313_ = v___y_3326_;
v___y_3314_ = v___y_3325_;
v_a_3315_ = v_a_3328_;
goto v___jp_3306_;
}
else
{
lean_object* v_a_3329_; 
lean_dec(v___y_3325_);
lean_dec(v___y_3319_);
v_a_3329_ = lean_ctor_get(v___y_3327_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v___y_3327_, 1);
v___y_3289_ = v___y_3320_;
v___y_3290_ = v___y_3321_;
v___y_3291_ = v___y_3322_;
v___y_3292_ = v___y_3323_;
v___y_3293_ = v___y_3324_;
v___y_3294_ = v___y_3326_;
v_a_3295_ = v_a_3329_;
goto v___jp_3288_;
}
}
v___jp_3330_:
{
if (v___y_3341_ == 0)
{
lean_object* v___x_3342_; 
lean_dec_ref(v___y_3331_);
v___x_3342_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3338_, v_a_2966_, v_a_2968_);
lean_dec_ref(v___y_3338_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_dec_ref_known(v___x_3342_, 1);
v___y_3307_ = v___y_3332_;
v___y_3308_ = v___y_3333_;
v___y_3309_ = v___y_3334_;
v___y_3310_ = v___y_3336_;
v___y_3311_ = v___y_3335_;
v___y_3312_ = v___y_3337_;
v___y_3313_ = v___y_3340_;
v___y_3314_ = v___y_3339_;
v_a_3315_ = v_snd_2974_;
goto v___jp_3306_;
}
else
{
lean_object* v_a_3343_; 
lean_dec(v___y_3339_);
lean_dec(v___y_3332_);
lean_dec(v_snd_2974_);
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v___y_3289_ = v___y_3333_;
v___y_3290_ = v___y_3334_;
v___y_3291_ = v___y_3335_;
v___y_3292_ = v___y_3336_;
v___y_3293_ = v___y_3337_;
v___y_3294_ = v___y_3340_;
v_a_3295_ = v_a_3343_;
goto v___jp_3288_;
}
}
else
{
lean_dec_ref(v___y_3338_);
lean_dec(v_snd_2974_);
v___y_3319_ = v___y_3332_;
v___y_3320_ = v___y_3333_;
v___y_3321_ = v___y_3334_;
v___y_3322_ = v___y_3335_;
v___y_3323_ = v___y_3336_;
v___y_3324_ = v___y_3337_;
v___y_3325_ = v___y_3339_;
v___y_3326_ = v___y_3340_;
v___y_3327_ = v___y_3331_;
goto v___jp_3318_;
}
}
v___jp_3344_:
{
lean_object* v___x_3354_; 
v___x_3354_ = l_Lean_Meta_saveState___redArg(v_a_2966_, v_a_2968_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref_known(v___x_3354_, 1);
lean_inc(v_snd_2974_);
lean_inc(v_trace_2960_);
v___x_3356_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3347_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_dec(v_a_3355_);
lean_dec(v_snd_2974_);
v___y_3319_ = v___y_3345_;
v___y_3320_ = v___y_3346_;
v___y_3321_ = v___y_3348_;
v___y_3322_ = v___y_3350_;
v___y_3323_ = v___y_3349_;
v___y_3324_ = v___y_3351_;
v___y_3325_ = v___y_3353_;
v___y_3326_ = v___y_3352_;
v___y_3327_ = v___x_3356_;
goto v___jp_3318_;
}
else
{
lean_object* v_a_3357_; uint8_t v___x_3358_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
v___x_3358_ = l_Lean_Exception_isInterrupt(v_a_3357_);
if (v___x_3358_ == 0)
{
uint8_t v___x_3359_; 
v___x_3359_ = l_Lean_Exception_isRuntime(v_a_3357_);
v___y_3331_ = v___x_3356_;
v___y_3332_ = v___y_3345_;
v___y_3333_ = v___y_3346_;
v___y_3334_ = v___y_3348_;
v___y_3335_ = v___y_3350_;
v___y_3336_ = v___y_3349_;
v___y_3337_ = v___y_3351_;
v___y_3338_ = v_a_3355_;
v___y_3339_ = v___y_3353_;
v___y_3340_ = v___y_3352_;
v___y_3341_ = v___x_3359_;
goto v___jp_3330_;
}
else
{
lean_dec(v_a_3357_);
v___y_3331_ = v___x_3356_;
v___y_3332_ = v___y_3345_;
v___y_3333_ = v___y_3346_;
v___y_3334_ = v___y_3348_;
v___y_3335_ = v___y_3350_;
v___y_3336_ = v___y_3349_;
v___y_3337_ = v___y_3351_;
v___y_3338_ = v_a_3355_;
v___y_3339_ = v___y_3353_;
v___y_3340_ = v___y_3352_;
v___y_3341_ = v___x_3358_;
goto v___jp_3330_;
}
}
}
else
{
lean_object* v_a_3360_; 
lean_dec(v___y_3353_);
lean_dec(v___y_3347_);
lean_dec(v___y_3345_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3360_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3354_, 1);
v___y_3289_ = v___y_3346_;
v___y_3290_ = v___y_3348_;
v___y_3291_ = v___y_3350_;
v___y_3292_ = v___y_3349_;
v___y_3293_ = v___y_3351_;
v___y_3294_ = v___y_3352_;
v_a_3295_ = v_a_3360_;
goto v___jp_3288_;
}
}
v___jp_3361_:
{
if (lean_obj_tag(v___y_3368_) == 0)
{
lean_object* v_a_3369_; 
v_a_3369_ = lean_ctor_get(v___y_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref_known(v___y_3368_, 1);
v___y_3298_ = v___y_3362_;
v___y_3299_ = v___y_3363_;
v___y_3300_ = v___y_3365_;
v___y_3301_ = v___y_3364_;
v___y_3302_ = v___y_3366_;
v___y_3303_ = v___y_3367_;
v_a_3304_ = v_a_3369_;
goto v___jp_3297_;
}
else
{
lean_object* v_a_3370_; 
v_a_3370_ = lean_ctor_get(v___y_3368_, 0);
lean_inc(v_a_3370_);
lean_dec_ref_known(v___y_3368_, 1);
v___y_3289_ = v___y_3362_;
v___y_3290_ = v___y_3363_;
v___y_3291_ = v___y_3365_;
v___y_3292_ = v___y_3364_;
v___y_3293_ = v___y_3366_;
v___y_3294_ = v___y_3367_;
v_a_3295_ = v_a_3370_;
goto v___jp_3288_;
}
}
v___jp_3371_:
{
lean_object* v___x_3380_; 
lean_inc(v_trace_2960_);
v___x_3380_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3373_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3382_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref_known(v___x_3380_, 1);
v___x_3382_ = l_List_appendTR___redArg(v___y_3379_, v_a_3381_);
v___y_3298_ = v___y_3372_;
v___y_3299_ = v___y_3374_;
v___y_3300_ = v___y_3376_;
v___y_3301_ = v___y_3375_;
v___y_3302_ = v___y_3377_;
v___y_3303_ = v___y_3378_;
v_a_3304_ = v___x_3382_;
goto v___jp_3297_;
}
else
{
lean_dec(v___y_3379_);
v___y_3362_ = v___y_3372_;
v___y_3363_ = v___y_3374_;
v___y_3364_ = v___y_3375_;
v___y_3365_ = v___y_3376_;
v___y_3366_ = v___y_3377_;
v___y_3367_ = v___y_3378_;
v___y_3368_ = v___x_3380_;
goto v___jp_3361_;
}
}
v___jp_3383_:
{
if (v___y_3394_ == 0)
{
uint8_t v___x_3395_; 
v___x_3395_ = l_List_isEmpty___redArg(v___y_3384_);
lean_dec(v___y_3384_);
if (v___x_3395_ == 0)
{
if (v___y_3388_ == 0)
{
v___y_3372_ = v___y_3385_;
v___y_3373_ = v___y_3386_;
v___y_3374_ = v___y_3387_;
v___y_3375_ = v___y_3390_;
v___y_3376_ = v___y_3389_;
v___y_3377_ = v___y_3391_;
v___y_3378_ = v___y_3393_;
v___y_3379_ = v___y_3392_;
goto v___jp_3371_;
}
else
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_dec(v___y_3392_);
lean_dec(v___y_3386_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v___x_3396_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3397_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3396_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_3362_ = v___y_3385_;
v___y_3363_ = v___y_3387_;
v___y_3364_ = v___y_3390_;
v___y_3365_ = v___y_3389_;
v___y_3366_ = v___y_3391_;
v___y_3367_ = v___y_3393_;
v___y_3368_ = v___x_3397_;
goto v___jp_3361_;
}
}
else
{
v___y_3372_ = v___y_3385_;
v___y_3373_ = v___y_3386_;
v___y_3374_ = v___y_3387_;
v___y_3375_ = v___y_3390_;
v___y_3376_ = v___y_3389_;
v___y_3377_ = v___y_3391_;
v___y_3378_ = v___y_3393_;
v___y_3379_ = v___y_3392_;
goto v___jp_3371_;
}
}
else
{
v___y_3345_ = v___y_3384_;
v___y_3346_ = v___y_3385_;
v___y_3347_ = v___y_3386_;
v___y_3348_ = v___y_3387_;
v___y_3349_ = v___y_3390_;
v___y_3350_ = v___y_3389_;
v___y_3351_ = v___y_3391_;
v___y_3352_ = v___y_3393_;
v___y_3353_ = v___y_3392_;
goto v___jp_3344_;
}
}
v___jp_3398_:
{
uint8_t v_commitIndependentGoals_3409_; lean_object* v___x_3410_; 
v_commitIndependentGoals_3409_ = lean_ctor_get_uint8(v_cfg_2959_, sizeof(void*)*4);
lean_inc(v___y_3407_);
v___x_3410_ = l_List_appendTR___redArg(v_a_3408_, v___y_3407_);
if (v_commitIndependentGoals_3409_ == 0)
{
v___y_3384_ = v___y_3399_;
v___y_3385_ = v___y_3400_;
v___y_3386_ = v___x_3410_;
v___y_3387_ = v___y_3401_;
v___y_3388_ = v___y_3402_;
v___y_3389_ = v___y_3403_;
v___y_3390_ = v___y_3404_;
v___y_3391_ = v___y_3405_;
v___y_3392_ = v___y_3407_;
v___y_3393_ = v___y_3406_;
v___y_3394_ = v___x_2978_;
goto v___jp_3383_;
}
else
{
uint8_t v___x_3411_; 
v___x_3411_ = l_List_isEmpty___redArg(v___y_3407_);
if (v___x_3411_ == 0)
{
v___y_3345_ = v___y_3399_;
v___y_3346_ = v___y_3400_;
v___y_3347_ = v___x_3410_;
v___y_3348_ = v___y_3401_;
v___y_3349_ = v___y_3404_;
v___y_3350_ = v___y_3403_;
v___y_3351_ = v___y_3405_;
v___y_3352_ = v___y_3406_;
v___y_3353_ = v___y_3407_;
goto v___jp_3344_;
}
else
{
v___y_3384_ = v___y_3399_;
v___y_3385_ = v___y_3400_;
v___y_3386_ = v___x_3410_;
v___y_3387_ = v___y_3401_;
v___y_3388_ = v___y_3402_;
v___y_3389_ = v___y_3403_;
v___y_3390_ = v___y_3404_;
v___y_3391_ = v___y_3405_;
v___y_3392_ = v___y_3407_;
v___y_3393_ = v___y_3406_;
v___y_3394_ = v___x_2978_;
goto v___jp_3383_;
}
}
}
v___jp_3412_:
{
lean_object* v___x_3421_; 
v___x_3421_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2968_);
if (lean_obj_tag(v___x_3421_) == 0)
{
if (v___y_3416_ == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref_known(v___x_3421_, 1);
v___x_3423_ = lean_io_mono_nanos_now();
v___x_3424_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3416_, v___x_2978_, v_goals_2963_, v___y_3413_, v_a_2966_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___x_3426_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
v___x_3426_ = l_List_reverse___redArg(v_a_3425_);
v___y_3260_ = v___y_3414_;
v___y_3261_ = v___y_3415_;
v___y_3262_ = v___y_3417_;
v___y_3263_ = v___y_3418_;
v___y_3264_ = v___x_3423_;
v___y_3265_ = v___y_3419_;
v___y_3266_ = v_a_3422_;
v___y_3267_ = v___y_3420_;
v_a_3268_ = v___x_3426_;
goto v___jp_3259_;
}
else
{
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3427_; 
v_a_3427_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3427_);
lean_dec_ref_known(v___x_3424_, 1);
v___y_3260_ = v___y_3414_;
v___y_3261_ = v___y_3415_;
v___y_3262_ = v___y_3417_;
v___y_3263_ = v___y_3418_;
v___y_3264_ = v___x_3423_;
v___y_3265_ = v___y_3419_;
v___y_3266_ = v_a_3422_;
v___y_3267_ = v___y_3420_;
v_a_3268_ = v_a_3427_;
goto v___jp_3259_;
}
else
{
lean_object* v_a_3428_; 
lean_dec(v___y_3420_);
lean_dec(v___y_3414_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3428_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3424_, 1);
v___y_3160_ = v___y_3415_;
v___y_3161_ = v___y_3417_;
v___y_3162_ = v___y_3418_;
v___y_3163_ = v___x_3423_;
v___y_3164_ = v___y_3419_;
v___y_3165_ = v_a_3422_;
v_a_3166_ = v_a_3428_;
goto v___jp_3159_;
}
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v_a_3429_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3421_, 1);
v___x_3430_ = lean_io_get_num_heartbeats();
v___x_3431_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3416_, v___x_2978_, v_goals_2963_, v___y_3413_, v_a_2966_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3433_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
v___x_3433_ = l_List_reverse___redArg(v_a_3432_);
v___y_3399_ = v___y_3414_;
v___y_3400_ = v___y_3415_;
v___y_3401_ = v___x_3430_;
v___y_3402_ = v___y_3416_;
v___y_3403_ = v___y_3417_;
v___y_3404_ = v___y_3418_;
v___y_3405_ = v___y_3419_;
v___y_3406_ = v_a_3429_;
v___y_3407_ = v___y_3420_;
v_a_3408_ = v___x_3433_;
goto v___jp_3398_;
}
else
{
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3434_; 
v_a_3434_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3431_, 1);
v___y_3399_ = v___y_3414_;
v___y_3400_ = v___y_3415_;
v___y_3401_ = v___x_3430_;
v___y_3402_ = v___y_3416_;
v___y_3403_ = v___y_3417_;
v___y_3404_ = v___y_3418_;
v___y_3405_ = v___y_3419_;
v___y_3406_ = v_a_3429_;
v___y_3407_ = v___y_3420_;
v_a_3408_ = v_a_3434_;
goto v___jp_3398_;
}
else
{
lean_object* v_a_3435_; 
lean_dec(v___y_3420_);
lean_dec(v___y_3414_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3435_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3431_, 1);
v___y_3289_ = v___y_3415_;
v___y_3290_ = v___x_3430_;
v___y_3291_ = v___y_3417_;
v___y_3292_ = v___y_3418_;
v___y_3293_ = v___y_3419_;
v___y_3294_ = v_a_3429_;
v_a_3295_ = v_a_3435_;
goto v___jp_3288_;
}
}
}
}
else
{
lean_object* v_a_3436_; 
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec(v_snd_2974_);
lean_dec(v_goals_2963_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3436_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3436_);
lean_dec_ref_known(v___x_3421_, 1);
v___y_3086_ = v___y_3418_;
v___y_3087_ = v___y_3419_;
v_a_3088_ = v_a_3436_;
goto v___jp_3085_;
}
}
v___jp_3437_:
{
if (v___y_3443_ == 0)
{
uint8_t v___x_3444_; 
v___x_3444_ = l_List_isEmpty___redArg(v___y_3438_);
lean_dec(v___y_3438_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
lean_dec(v___y_3442_);
lean_dec(v___y_3439_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v___x_3445_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3446_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3445_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_3135_ = v___y_3440_;
v___y_3136_ = v___y_3441_;
v___y_3137_ = v___x_3446_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3447_; 
lean_inc(v_trace_2960_);
v___x_3447_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3439_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3449_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref_known(v___x_3447_, 1);
v___x_3449_ = l_List_appendTR___redArg(v___y_3442_, v_a_3448_);
v___y_3091_ = v___y_3440_;
v___y_3092_ = v___y_3441_;
v_a_3093_ = v___x_3449_;
goto v___jp_3090_;
}
else
{
lean_dec(v___y_3442_);
v___y_3135_ = v___y_3440_;
v___y_3136_ = v___y_3441_;
v___y_3137_ = v___x_3447_;
goto v___jp_3134_;
}
}
}
else
{
v___y_3122_ = v___y_3438_;
v___y_3123_ = v___y_3440_;
v___y_3124_ = v___y_3439_;
v___y_3125_ = v___y_3441_;
v___y_3126_ = v___y_3442_;
goto v___jp_3121_;
}
}
v___jp_3450_:
{
uint8_t v_commitIndependentGoals_3456_; lean_object* v___x_3457_; 
v_commitIndependentGoals_3456_ = lean_ctor_get_uint8(v_cfg_2959_, sizeof(void*)*4);
lean_inc(v___y_3454_);
v___x_3457_ = l_List_appendTR___redArg(v_a_3455_, v___y_3454_);
if (v_commitIndependentGoals_3456_ == 0)
{
v___y_3438_ = v___y_3451_;
v___y_3439_ = v___x_3457_;
v___y_3440_ = v___y_3452_;
v___y_3441_ = v___y_3453_;
v___y_3442_ = v___y_3454_;
v___y_3443_ = v___x_2978_;
goto v___jp_3437_;
}
else
{
uint8_t v___x_3458_; 
v___x_3458_ = l_List_isEmpty___redArg(v___y_3454_);
if (v___x_3458_ == 0)
{
v___y_3122_ = v___y_3451_;
v___y_3123_ = v___y_3452_;
v___y_3124_ = v___x_3457_;
v___y_3125_ = v___y_3453_;
v___y_3126_ = v___y_3454_;
goto v___jp_3121_;
}
else
{
v___y_3438_ = v___y_3451_;
v___y_3439_ = v___x_3457_;
v___y_3440_ = v___y_3452_;
v___y_3441_ = v___y_3453_;
v___y_3442_ = v___y_3454_;
v___y_3443_ = v___x_2978_;
goto v___jp_3437_;
}
}
}
v___jp_3459_:
{
lean_object* v___x_3463_; double v___x_3464_; double v___x_3465_; double v___x_3466_; double v___x_3467_; double v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3463_ = lean_io_mono_nanos_now();
v___x_3464_ = lean_float_of_nat(v___y_3460_);
v___x_3465_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3466_ = lean_float_div(v___x_3464_, v___x_3465_);
v___x_3467_ = lean_float_of_nat(v___x_3463_);
v___x_3468_ = lean_float_div(v___x_3467_, v___x_3465_);
v___x_3469_ = lean_box_float(v___x_3466_);
v___x_3470_ = lean_box_float(v___x_3468_);
v___x_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3469_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3472_, 0, v_a_3462_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2960_, v_hasTrace_2982_, v___x_3067_, v_options_2980_, v___x_3070_, v___y_3461_, v___f_3066_, v___x_3472_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
return v___x_3473_;
}
v___jp_3474_:
{
lean_object* v___x_3478_; 
v___x_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3478_, 0, v_a_3477_);
v___y_3460_ = v___y_3475_;
v___y_3461_ = v___y_3476_;
v_a_3462_ = v___x_3478_;
goto v___jp_3459_;
}
v___jp_3479_:
{
lean_object* v___x_3483_; 
v___x_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3483_, 0, v_a_3482_);
v___y_3460_ = v___y_3480_;
v___y_3461_ = v___y_3481_;
v_a_3462_ = v___x_3483_;
goto v___jp_3459_;
}
v___jp_3484_:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = l_List_appendTR___redArg(v___y_3488_, v___y_3485_);
v___x_3491_ = l_List_appendTR___redArg(v___x_3490_, v_a_3489_);
v___y_3480_ = v___y_3486_;
v___y_3481_ = v___y_3487_;
v_a_3482_ = v___x_3491_;
goto v___jp_3479_;
}
v___jp_3492_:
{
if (lean_obj_tag(v___y_3497_) == 0)
{
lean_object* v_a_3498_; 
v_a_3498_ = lean_ctor_get(v___y_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___y_3497_, 1);
v___y_3485_ = v___y_3493_;
v___y_3486_ = v___y_3494_;
v___y_3487_ = v___y_3495_;
v___y_3488_ = v___y_3496_;
v_a_3489_ = v_a_3498_;
goto v___jp_3484_;
}
else
{
lean_object* v_a_3499_; 
lean_dec(v___y_3496_);
lean_dec(v___y_3493_);
v_a_3499_ = lean_ctor_get(v___y_3497_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___y_3497_, 1);
v___y_3475_ = v___y_3494_;
v___y_3476_ = v___y_3495_;
v_a_3477_ = v_a_3499_;
goto v___jp_3474_;
}
}
v___jp_3500_:
{
if (v___y_3507_ == 0)
{
lean_object* v___x_3508_; 
lean_dec_ref(v___y_3503_);
v___x_3508_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3506_, v_a_2966_, v_a_2968_);
lean_dec_ref(v___y_3506_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_dec_ref_known(v___x_3508_, 1);
v___y_3485_ = v___y_3501_;
v___y_3486_ = v___y_3502_;
v___y_3487_ = v___y_3504_;
v___y_3488_ = v___y_3505_;
v_a_3489_ = v_snd_2974_;
goto v___jp_3484_;
}
else
{
lean_object* v_a_3509_; 
lean_dec(v___y_3505_);
lean_dec(v___y_3501_);
lean_dec(v_snd_2974_);
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v___y_3475_ = v___y_3502_;
v___y_3476_ = v___y_3504_;
v_a_3477_ = v_a_3509_;
goto v___jp_3474_;
}
}
else
{
lean_dec_ref(v___y_3506_);
lean_dec(v_snd_2974_);
v___y_3493_ = v___y_3501_;
v___y_3494_ = v___y_3502_;
v___y_3495_ = v___y_3504_;
v___y_3496_ = v___y_3505_;
v___y_3497_ = v___y_3503_;
goto v___jp_3492_;
}
}
v___jp_3510_:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_Meta_saveState___redArg(v_a_2966_, v_a_2968_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3518_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3516_, 1);
lean_inc(v_snd_2974_);
lean_inc(v_trace_2960_);
v___x_3518_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3513_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_dec(v_a_3517_);
lean_dec(v_snd_2974_);
v___y_3493_ = v___y_3511_;
v___y_3494_ = v___y_3512_;
v___y_3495_ = v___y_3514_;
v___y_3496_ = v___y_3515_;
v___y_3497_ = v___x_3518_;
goto v___jp_3492_;
}
else
{
lean_object* v_a_3519_; uint8_t v___x_3520_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
v___x_3520_ = l_Lean_Exception_isInterrupt(v_a_3519_);
if (v___x_3520_ == 0)
{
uint8_t v___x_3521_; 
v___x_3521_ = l_Lean_Exception_isRuntime(v_a_3519_);
v___y_3501_ = v___y_3511_;
v___y_3502_ = v___y_3512_;
v___y_3503_ = v___x_3518_;
v___y_3504_ = v___y_3514_;
v___y_3505_ = v___y_3515_;
v___y_3506_ = v_a_3517_;
v___y_3507_ = v___x_3521_;
goto v___jp_3500_;
}
else
{
lean_dec(v_a_3519_);
v___y_3501_ = v___y_3511_;
v___y_3502_ = v___y_3512_;
v___y_3503_ = v___x_3518_;
v___y_3504_ = v___y_3514_;
v___y_3505_ = v___y_3515_;
v___y_3506_ = v_a_3517_;
v___y_3507_ = v___x_3520_;
goto v___jp_3500_;
}
}
}
else
{
lean_object* v_a_3522_; 
lean_dec(v___y_3515_);
lean_dec(v___y_3513_);
lean_dec(v___y_3511_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3522_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3516_, 1);
v___y_3475_ = v___y_3512_;
v___y_3476_ = v___y_3514_;
v_a_3477_ = v_a_3522_;
goto v___jp_3474_;
}
}
v___jp_3523_:
{
if (lean_obj_tag(v___y_3526_) == 0)
{
lean_object* v_a_3527_; 
v_a_3527_ = lean_ctor_get(v___y_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___y_3526_, 1);
v___y_3480_ = v___y_3524_;
v___y_3481_ = v___y_3525_;
v_a_3482_ = v_a_3527_;
goto v___jp_3479_;
}
else
{
lean_object* v_a_3528_; 
v_a_3528_ = lean_ctor_get(v___y_3526_, 0);
lean_inc(v_a_3528_);
lean_dec_ref_known(v___y_3526_, 1);
v___y_3475_ = v___y_3524_;
v___y_3476_ = v___y_3525_;
v_a_3477_ = v_a_3528_;
goto v___jp_3474_;
}
}
v___jp_3529_:
{
lean_object* v___x_3537_; double v___x_3538_; double v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3537_ = lean_io_get_num_heartbeats();
v___x_3538_ = lean_float_of_nat(v___y_3533_);
v___x_3539_ = lean_float_of_nat(v___x_3537_);
v___x_3540_ = lean_box_float(v___x_3538_);
v___x_3541_ = lean_box_float(v___x_3539_);
v___x_3542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3540_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3543_, 0, v_a_3536_);
lean_ctor_set(v___x_3543_, 1, v___x_3542_);
lean_inc(v_trace_2960_);
v___x_3544_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2960_, v_hasTrace_2982_, v___x_3067_, v_options_2980_, v___y_3532_, v___y_3530_, v___y_3535_, v___x_3543_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_3524_ = v___y_3531_;
v___y_3525_ = v___y_3534_;
v___y_3526_ = v___x_3544_;
goto v___jp_3523_;
}
v___jp_3545_:
{
lean_object* v___x_3553_; 
v___x_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3553_, 0, v_a_3552_);
v___y_3530_ = v___y_3546_;
v___y_3531_ = v___y_3547_;
v___y_3532_ = v___y_3548_;
v___y_3533_ = v___y_3549_;
v___y_3534_ = v___y_3551_;
v___y_3535_ = v___y_3550_;
v_a_3536_ = v___x_3553_;
goto v___jp_3529_;
}
v___jp_3554_:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = l_List_appendTR___redArg(v___y_3562_, v___y_3556_);
v___x_3565_ = l_List_appendTR___redArg(v___x_3564_, v_a_3563_);
v___y_3546_ = v___y_3555_;
v___y_3547_ = v___y_3557_;
v___y_3548_ = v___y_3558_;
v___y_3549_ = v___y_3559_;
v___y_3550_ = v___y_3561_;
v___y_3551_ = v___y_3560_;
v_a_3552_ = v___x_3565_;
goto v___jp_3545_;
}
v___jp_3566_:
{
lean_object* v___x_3574_; 
v___x_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3574_, 0, v_a_3573_);
v___y_3530_ = v___y_3567_;
v___y_3531_ = v___y_3568_;
v___y_3532_ = v___y_3569_;
v___y_3533_ = v___y_3570_;
v___y_3534_ = v___y_3572_;
v___y_3535_ = v___y_3571_;
v_a_3536_ = v___x_3574_;
goto v___jp_3529_;
}
v___jp_3575_:
{
if (lean_obj_tag(v___y_3582_) == 0)
{
lean_object* v_a_3583_; 
v_a_3583_ = lean_ctor_get(v___y_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___y_3582_, 1);
v___y_3546_ = v___y_3576_;
v___y_3547_ = v___y_3577_;
v___y_3548_ = v___y_3578_;
v___y_3549_ = v___y_3579_;
v___y_3550_ = v___y_3581_;
v___y_3551_ = v___y_3580_;
v_a_3552_ = v_a_3583_;
goto v___jp_3545_;
}
else
{
lean_object* v_a_3584_; 
v_a_3584_ = lean_ctor_get(v___y_3582_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___y_3582_, 1);
v___y_3567_ = v___y_3576_;
v___y_3568_ = v___y_3577_;
v___y_3569_ = v___y_3578_;
v___y_3570_ = v___y_3579_;
v___y_3571_ = v___y_3581_;
v___y_3572_ = v___y_3580_;
v_a_3573_ = v_a_3584_;
goto v___jp_3566_;
}
}
v___jp_3585_:
{
lean_object* v___x_3594_; 
lean_inc(v_trace_2960_);
v___x_3594_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3592_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3596_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3594_, 1);
v___x_3596_ = l_List_appendTR___redArg(v___y_3593_, v_a_3595_);
v___y_3546_ = v___y_3586_;
v___y_3547_ = v___y_3587_;
v___y_3548_ = v___y_3588_;
v___y_3549_ = v___y_3589_;
v___y_3550_ = v___y_3591_;
v___y_3551_ = v___y_3590_;
v_a_3552_ = v___x_3596_;
goto v___jp_3545_;
}
else
{
lean_dec(v___y_3593_);
v___y_3576_ = v___y_3586_;
v___y_3577_ = v___y_3587_;
v___y_3578_ = v___y_3588_;
v___y_3579_ = v___y_3589_;
v___y_3580_ = v___y_3590_;
v___y_3581_ = v___y_3591_;
v___y_3582_ = v___x_3594_;
goto v___jp_3575_;
}
}
v___jp_3597_:
{
if (lean_obj_tag(v___y_3606_) == 0)
{
lean_object* v_a_3607_; 
v_a_3607_ = lean_ctor_get(v___y_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___y_3606_, 1);
v___y_3555_ = v___y_3598_;
v___y_3556_ = v___y_3599_;
v___y_3557_ = v___y_3600_;
v___y_3558_ = v___y_3601_;
v___y_3559_ = v___y_3602_;
v___y_3560_ = v___y_3604_;
v___y_3561_ = v___y_3603_;
v___y_3562_ = v___y_3605_;
v_a_3563_ = v_a_3607_;
goto v___jp_3554_;
}
else
{
lean_object* v_a_3608_; 
lean_dec(v___y_3605_);
lean_dec(v___y_3599_);
v_a_3608_ = lean_ctor_get(v___y_3606_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___y_3606_, 1);
v___y_3567_ = v___y_3598_;
v___y_3568_ = v___y_3600_;
v___y_3569_ = v___y_3601_;
v___y_3570_ = v___y_3602_;
v___y_3571_ = v___y_3603_;
v___y_3572_ = v___y_3604_;
v_a_3573_ = v_a_3608_;
goto v___jp_3566_;
}
}
v___jp_3609_:
{
if (v___y_3620_ == 0)
{
lean_object* v___x_3621_; 
lean_dec_ref(v___y_3614_);
v___x_3621_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3615_, v_a_2966_, v_a_2968_);
lean_dec_ref(v___y_3615_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_dec_ref_known(v___x_3621_, 1);
v___y_3555_ = v___y_3610_;
v___y_3556_ = v___y_3611_;
v___y_3557_ = v___y_3612_;
v___y_3558_ = v___y_3613_;
v___y_3559_ = v___y_3616_;
v___y_3560_ = v___y_3618_;
v___y_3561_ = v___y_3617_;
v___y_3562_ = v___y_3619_;
v_a_3563_ = v_snd_2974_;
goto v___jp_3554_;
}
else
{
lean_object* v_a_3622_; 
lean_dec(v___y_3619_);
lean_dec(v___y_3611_);
lean_dec(v_snd_2974_);
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
lean_dec_ref_known(v___x_3621_, 1);
v___y_3567_ = v___y_3610_;
v___y_3568_ = v___y_3612_;
v___y_3569_ = v___y_3613_;
v___y_3570_ = v___y_3616_;
v___y_3571_ = v___y_3617_;
v___y_3572_ = v___y_3618_;
v_a_3573_ = v_a_3622_;
goto v___jp_3566_;
}
}
else
{
lean_dec_ref(v___y_3615_);
lean_dec(v_snd_2974_);
v___y_3598_ = v___y_3610_;
v___y_3599_ = v___y_3611_;
v___y_3600_ = v___y_3612_;
v___y_3601_ = v___y_3613_;
v___y_3602_ = v___y_3616_;
v___y_3603_ = v___y_3617_;
v___y_3604_ = v___y_3618_;
v___y_3605_ = v___y_3619_;
v___y_3606_ = v___y_3614_;
goto v___jp_3597_;
}
}
v___jp_3623_:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Lean_Meta_saveState___redArg(v_a_2966_, v_a_2968_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3635_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
lean_inc(v_snd_2974_);
lean_inc(v_trace_2960_);
v___x_3635_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3631_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_dec(v_a_3634_);
lean_dec(v_snd_2974_);
v___y_3598_ = v___y_3624_;
v___y_3599_ = v___y_3625_;
v___y_3600_ = v___y_3626_;
v___y_3601_ = v___y_3627_;
v___y_3602_ = v___y_3628_;
v___y_3603_ = v___y_3630_;
v___y_3604_ = v___y_3629_;
v___y_3605_ = v___y_3632_;
v___y_3606_ = v___x_3635_;
goto v___jp_3597_;
}
else
{
lean_object* v_a_3636_; uint8_t v___x_3637_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3636_);
v___x_3637_ = l_Lean_Exception_isInterrupt(v_a_3636_);
if (v___x_3637_ == 0)
{
uint8_t v___x_3638_; 
v___x_3638_ = l_Lean_Exception_isRuntime(v_a_3636_);
v___y_3610_ = v___y_3624_;
v___y_3611_ = v___y_3625_;
v___y_3612_ = v___y_3626_;
v___y_3613_ = v___y_3627_;
v___y_3614_ = v___x_3635_;
v___y_3615_ = v_a_3634_;
v___y_3616_ = v___y_3628_;
v___y_3617_ = v___y_3630_;
v___y_3618_ = v___y_3629_;
v___y_3619_ = v___y_3632_;
v___y_3620_ = v___x_3638_;
goto v___jp_3609_;
}
else
{
lean_dec(v_a_3636_);
v___y_3610_ = v___y_3624_;
v___y_3611_ = v___y_3625_;
v___y_3612_ = v___y_3626_;
v___y_3613_ = v___y_3627_;
v___y_3614_ = v___x_3635_;
v___y_3615_ = v_a_3634_;
v___y_3616_ = v___y_3628_;
v___y_3617_ = v___y_3630_;
v___y_3618_ = v___y_3629_;
v___y_3619_ = v___y_3632_;
v___y_3620_ = v___x_3637_;
goto v___jp_3609_;
}
}
}
else
{
lean_object* v_a_3639_; 
lean_dec(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec(v___y_3625_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3639_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3633_, 1);
v___y_3567_ = v___y_3624_;
v___y_3568_ = v___y_3626_;
v___y_3569_ = v___y_3627_;
v___y_3570_ = v___y_3628_;
v___y_3571_ = v___y_3630_;
v___y_3572_ = v___y_3629_;
v_a_3573_ = v_a_3639_;
goto v___jp_3566_;
}
}
v___jp_3640_:
{
if (v___y_3651_ == 0)
{
uint8_t v___x_3652_; 
v___x_3652_ = l_List_isEmpty___redArg(v___y_3642_);
lean_dec(v___y_3642_);
if (v___x_3652_ == 0)
{
if (v___y_3645_ == 0)
{
v___y_3586_ = v___y_3641_;
v___y_3587_ = v___y_3643_;
v___y_3588_ = v___y_3644_;
v___y_3589_ = v___y_3646_;
v___y_3590_ = v___y_3649_;
v___y_3591_ = v___y_3648_;
v___y_3592_ = v___y_3647_;
v___y_3593_ = v___y_3650_;
goto v___jp_3585_;
}
else
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
lean_dec(v___y_3650_);
lean_dec(v___y_3647_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v___x_3653_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3654_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3653_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_3576_ = v___y_3641_;
v___y_3577_ = v___y_3643_;
v___y_3578_ = v___y_3644_;
v___y_3579_ = v___y_3646_;
v___y_3580_ = v___y_3649_;
v___y_3581_ = v___y_3648_;
v___y_3582_ = v___x_3654_;
goto v___jp_3575_;
}
}
else
{
v___y_3586_ = v___y_3641_;
v___y_3587_ = v___y_3643_;
v___y_3588_ = v___y_3644_;
v___y_3589_ = v___y_3646_;
v___y_3590_ = v___y_3649_;
v___y_3591_ = v___y_3648_;
v___y_3592_ = v___y_3647_;
v___y_3593_ = v___y_3650_;
goto v___jp_3585_;
}
}
else
{
v___y_3624_ = v___y_3641_;
v___y_3625_ = v___y_3642_;
v___y_3626_ = v___y_3643_;
v___y_3627_ = v___y_3644_;
v___y_3628_ = v___y_3646_;
v___y_3629_ = v___y_3649_;
v___y_3630_ = v___y_3648_;
v___y_3631_ = v___y_3647_;
v___y_3632_ = v___y_3650_;
goto v___jp_3623_;
}
}
v___jp_3655_:
{
uint8_t v_commitIndependentGoals_3666_; lean_object* v___x_3667_; 
v_commitIndependentGoals_3666_ = lean_ctor_get_uint8(v_cfg_2959_, sizeof(void*)*4);
lean_inc(v___y_3664_);
v___x_3667_ = l_List_appendTR___redArg(v_a_3665_, v___y_3664_);
if (v_commitIndependentGoals_3666_ == 0)
{
v___y_3641_ = v___y_3656_;
v___y_3642_ = v___y_3657_;
v___y_3643_ = v___y_3658_;
v___y_3644_ = v___y_3659_;
v___y_3645_ = v___y_3660_;
v___y_3646_ = v___y_3661_;
v___y_3647_ = v___x_3667_;
v___y_3648_ = v___y_3662_;
v___y_3649_ = v___y_3663_;
v___y_3650_ = v___y_3664_;
v___y_3651_ = v___x_2978_;
goto v___jp_3640_;
}
else
{
uint8_t v___x_3668_; 
v___x_3668_ = l_List_isEmpty___redArg(v___y_3664_);
if (v___x_3668_ == 0)
{
v___y_3624_ = v___y_3656_;
v___y_3625_ = v___y_3657_;
v___y_3626_ = v___y_3658_;
v___y_3627_ = v___y_3659_;
v___y_3628_ = v___y_3661_;
v___y_3629_ = v___y_3663_;
v___y_3630_ = v___y_3662_;
v___y_3631_ = v___x_3667_;
v___y_3632_ = v___y_3664_;
goto v___jp_3623_;
}
else
{
v___y_3641_ = v___y_3656_;
v___y_3642_ = v___y_3657_;
v___y_3643_ = v___y_3658_;
v___y_3644_ = v___y_3659_;
v___y_3645_ = v___y_3660_;
v___y_3646_ = v___y_3661_;
v___y_3647_ = v___x_3667_;
v___y_3648_ = v___y_3662_;
v___y_3649_ = v___y_3663_;
v___y_3650_ = v___y_3664_;
v___y_3651_ = v___x_2978_;
goto v___jp_3640_;
}
}
}
v___jp_3669_:
{
lean_object* v___x_3677_; double v___x_3678_; double v___x_3679_; double v___x_3680_; double v___x_3681_; double v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3677_ = lean_io_mono_nanos_now();
v___x_3678_ = lean_float_of_nat(v___y_3672_);
v___x_3679_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3680_ = lean_float_div(v___x_3678_, v___x_3679_);
v___x_3681_ = lean_float_of_nat(v___x_3677_);
v___x_3682_ = lean_float_div(v___x_3681_, v___x_3679_);
v___x_3683_ = lean_box_float(v___x_3680_);
v___x_3684_ = lean_box_float(v___x_3682_);
v___x_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3683_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3686_, 0, v_a_3676_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
lean_inc(v_trace_2960_);
v___x_3687_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2960_, v_hasTrace_2982_, v___x_3067_, v_options_2980_, v___y_3673_, v___y_3670_, v___y_3675_, v___x_3686_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_3524_ = v___y_3671_;
v___y_3525_ = v___y_3674_;
v___y_3526_ = v___x_3687_;
goto v___jp_3523_;
}
v___jp_3688_:
{
lean_object* v___x_3696_; 
v___x_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3696_, 0, v_a_3695_);
v___y_3670_ = v___y_3689_;
v___y_3671_ = v___y_3690_;
v___y_3672_ = v___y_3691_;
v___y_3673_ = v___y_3692_;
v___y_3674_ = v___y_3694_;
v___y_3675_ = v___y_3693_;
v_a_3676_ = v___x_3696_;
goto v___jp_3669_;
}
v___jp_3697_:
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3705_, 0, v_a_3704_);
v___y_3670_ = v___y_3698_;
v___y_3671_ = v___y_3699_;
v___y_3672_ = v___y_3700_;
v___y_3673_ = v___y_3701_;
v___y_3674_ = v___y_3703_;
v___y_3675_ = v___y_3702_;
v_a_3676_ = v___x_3705_;
goto v___jp_3669_;
}
v___jp_3706_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = l_List_appendTR___redArg(v___y_3714_, v___y_3708_);
v___x_3717_ = l_List_appendTR___redArg(v___x_3716_, v_a_3715_);
v___y_3698_ = v___y_3707_;
v___y_3699_ = v___y_3709_;
v___y_3700_ = v___y_3710_;
v___y_3701_ = v___y_3711_;
v___y_3702_ = v___y_3713_;
v___y_3703_ = v___y_3712_;
v_a_3704_ = v___x_3717_;
goto v___jp_3697_;
}
v___jp_3718_:
{
if (lean_obj_tag(v___y_3727_) == 0)
{
lean_object* v_a_3728_; 
v_a_3728_ = lean_ctor_get(v___y_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___y_3727_, 1);
v___y_3707_ = v___y_3719_;
v___y_3708_ = v___y_3720_;
v___y_3709_ = v___y_3721_;
v___y_3710_ = v___y_3722_;
v___y_3711_ = v___y_3723_;
v___y_3712_ = v___y_3725_;
v___y_3713_ = v___y_3724_;
v___y_3714_ = v___y_3726_;
v_a_3715_ = v_a_3728_;
goto v___jp_3706_;
}
else
{
lean_object* v_a_3729_; 
lean_dec(v___y_3726_);
lean_dec(v___y_3720_);
v_a_3729_ = lean_ctor_get(v___y_3727_, 0);
lean_inc(v_a_3729_);
lean_dec_ref_known(v___y_3727_, 1);
v___y_3689_ = v___y_3719_;
v___y_3690_ = v___y_3721_;
v___y_3691_ = v___y_3722_;
v___y_3692_ = v___y_3723_;
v___y_3693_ = v___y_3724_;
v___y_3694_ = v___y_3725_;
v_a_3695_ = v_a_3729_;
goto v___jp_3688_;
}
}
v___jp_3730_:
{
if (v___y_3741_ == 0)
{
lean_object* v___x_3742_; 
lean_dec_ref(v___y_3732_);
v___x_3742_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3734_, v_a_2966_, v_a_2968_);
lean_dec_ref(v___y_3734_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_dec_ref_known(v___x_3742_, 1);
v___y_3707_ = v___y_3731_;
v___y_3708_ = v___y_3733_;
v___y_3709_ = v___y_3735_;
v___y_3710_ = v___y_3736_;
v___y_3711_ = v___y_3737_;
v___y_3712_ = v___y_3739_;
v___y_3713_ = v___y_3738_;
v___y_3714_ = v___y_3740_;
v_a_3715_ = v_snd_2974_;
goto v___jp_3706_;
}
else
{
lean_object* v_a_3743_; 
lean_dec(v___y_3740_);
lean_dec(v___y_3733_);
lean_dec(v_snd_2974_);
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
v___y_3689_ = v___y_3731_;
v___y_3690_ = v___y_3735_;
v___y_3691_ = v___y_3736_;
v___y_3692_ = v___y_3737_;
v___y_3693_ = v___y_3738_;
v___y_3694_ = v___y_3739_;
v_a_3695_ = v_a_3743_;
goto v___jp_3688_;
}
}
else
{
lean_dec_ref(v___y_3734_);
lean_dec(v_snd_2974_);
v___y_3719_ = v___y_3731_;
v___y_3720_ = v___y_3733_;
v___y_3721_ = v___y_3735_;
v___y_3722_ = v___y_3736_;
v___y_3723_ = v___y_3737_;
v___y_3724_ = v___y_3738_;
v___y_3725_ = v___y_3739_;
v___y_3726_ = v___y_3740_;
v___y_3727_ = v___y_3732_;
goto v___jp_3718_;
}
}
v___jp_3744_:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_Meta_saveState___redArg(v_a_2966_, v_a_2968_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3756_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
lean_inc(v_snd_2974_);
lean_inc(v_trace_2960_);
v___x_3756_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3750_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_dec(v_a_3755_);
lean_dec(v_snd_2974_);
v___y_3719_ = v___y_3745_;
v___y_3720_ = v___y_3746_;
v___y_3721_ = v___y_3747_;
v___y_3722_ = v___y_3748_;
v___y_3723_ = v___y_3749_;
v___y_3724_ = v___y_3752_;
v___y_3725_ = v___y_3751_;
v___y_3726_ = v___y_3753_;
v___y_3727_ = v___x_3756_;
goto v___jp_3718_;
}
else
{
lean_object* v_a_3757_; uint8_t v___x_3758_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
v___x_3758_ = l_Lean_Exception_isInterrupt(v_a_3757_);
if (v___x_3758_ == 0)
{
uint8_t v___x_3759_; 
v___x_3759_ = l_Lean_Exception_isRuntime(v_a_3757_);
v___y_3731_ = v___y_3745_;
v___y_3732_ = v___x_3756_;
v___y_3733_ = v___y_3746_;
v___y_3734_ = v_a_3755_;
v___y_3735_ = v___y_3747_;
v___y_3736_ = v___y_3748_;
v___y_3737_ = v___y_3749_;
v___y_3738_ = v___y_3752_;
v___y_3739_ = v___y_3751_;
v___y_3740_ = v___y_3753_;
v___y_3741_ = v___x_3759_;
goto v___jp_3730_;
}
else
{
lean_dec(v_a_3757_);
v___y_3731_ = v___y_3745_;
v___y_3732_ = v___x_3756_;
v___y_3733_ = v___y_3746_;
v___y_3734_ = v_a_3755_;
v___y_3735_ = v___y_3747_;
v___y_3736_ = v___y_3748_;
v___y_3737_ = v___y_3749_;
v___y_3738_ = v___y_3752_;
v___y_3739_ = v___y_3751_;
v___y_3740_ = v___y_3753_;
v___y_3741_ = v___x_3758_;
goto v___jp_3730_;
}
}
}
else
{
lean_object* v_a_3760_; 
lean_dec(v___y_3753_);
lean_dec(v___y_3750_);
lean_dec(v___y_3746_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3760_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3754_, 1);
v___y_3689_ = v___y_3745_;
v___y_3690_ = v___y_3747_;
v___y_3691_ = v___y_3748_;
v___y_3692_ = v___y_3749_;
v___y_3693_ = v___y_3752_;
v___y_3694_ = v___y_3751_;
v_a_3695_ = v_a_3760_;
goto v___jp_3688_;
}
}
v___jp_3761_:
{
if (lean_obj_tag(v___y_3768_) == 0)
{
lean_object* v_a_3769_; 
v_a_3769_ = lean_ctor_get(v___y_3768_, 0);
lean_inc(v_a_3769_);
lean_dec_ref_known(v___y_3768_, 1);
v___y_3698_ = v___y_3762_;
v___y_3699_ = v___y_3763_;
v___y_3700_ = v___y_3764_;
v___y_3701_ = v___y_3765_;
v___y_3702_ = v___y_3767_;
v___y_3703_ = v___y_3766_;
v_a_3704_ = v_a_3769_;
goto v___jp_3697_;
}
else
{
lean_object* v_a_3770_; 
v_a_3770_ = lean_ctor_get(v___y_3768_, 0);
lean_inc(v_a_3770_);
lean_dec_ref_known(v___y_3768_, 1);
v___y_3689_ = v___y_3762_;
v___y_3690_ = v___y_3763_;
v___y_3691_ = v___y_3764_;
v___y_3692_ = v___y_3765_;
v___y_3693_ = v___y_3767_;
v___y_3694_ = v___y_3766_;
v_a_3695_ = v_a_3770_;
goto v___jp_3688_;
}
}
v___jp_3771_:
{
if (v___y_3781_ == 0)
{
uint8_t v___x_3782_; 
v___x_3782_ = l_List_isEmpty___redArg(v___y_3773_);
lean_dec(v___y_3773_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
lean_dec(v___y_3780_);
lean_dec(v___y_3777_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v___x_3783_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3784_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3783_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_3762_ = v___y_3772_;
v___y_3763_ = v___y_3774_;
v___y_3764_ = v___y_3775_;
v___y_3765_ = v___y_3776_;
v___y_3766_ = v___y_3779_;
v___y_3767_ = v___y_3778_;
v___y_3768_ = v___x_3784_;
goto v___jp_3761_;
}
else
{
lean_object* v___x_3785_; 
lean_inc(v_trace_2960_);
v___x_3785_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3777_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3787_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v___x_3787_ = l_List_appendTR___redArg(v___y_3780_, v_a_3786_);
v___y_3698_ = v___y_3772_;
v___y_3699_ = v___y_3774_;
v___y_3700_ = v___y_3775_;
v___y_3701_ = v___y_3776_;
v___y_3702_ = v___y_3778_;
v___y_3703_ = v___y_3779_;
v_a_3704_ = v___x_3787_;
goto v___jp_3697_;
}
else
{
lean_dec(v___y_3780_);
v___y_3762_ = v___y_3772_;
v___y_3763_ = v___y_3774_;
v___y_3764_ = v___y_3775_;
v___y_3765_ = v___y_3776_;
v___y_3766_ = v___y_3779_;
v___y_3767_ = v___y_3778_;
v___y_3768_ = v___x_3785_;
goto v___jp_3761_;
}
}
}
else
{
v___y_3745_ = v___y_3772_;
v___y_3746_ = v___y_3773_;
v___y_3747_ = v___y_3774_;
v___y_3748_ = v___y_3775_;
v___y_3749_ = v___y_3776_;
v___y_3750_ = v___y_3777_;
v___y_3751_ = v___y_3779_;
v___y_3752_ = v___y_3778_;
v___y_3753_ = v___y_3780_;
goto v___jp_3744_;
}
}
v___jp_3788_:
{
uint8_t v_commitIndependentGoals_3798_; lean_object* v___x_3799_; 
v_commitIndependentGoals_3798_ = lean_ctor_get_uint8(v_cfg_2959_, sizeof(void*)*4);
lean_inc(v___y_3796_);
v___x_3799_ = l_List_appendTR___redArg(v_a_3797_, v___y_3796_);
if (v_commitIndependentGoals_3798_ == 0)
{
v___y_3772_ = v___y_3789_;
v___y_3773_ = v___y_3790_;
v___y_3774_ = v___y_3791_;
v___y_3775_ = v___y_3792_;
v___y_3776_ = v___y_3793_;
v___y_3777_ = v___x_3799_;
v___y_3778_ = v___y_3794_;
v___y_3779_ = v___y_3795_;
v___y_3780_ = v___y_3796_;
v___y_3781_ = v___x_2978_;
goto v___jp_3771_;
}
else
{
uint8_t v___x_3800_; 
v___x_3800_ = l_List_isEmpty___redArg(v___y_3796_);
if (v___x_3800_ == 0)
{
v___y_3745_ = v___y_3789_;
v___y_3746_ = v___y_3790_;
v___y_3747_ = v___y_3791_;
v___y_3748_ = v___y_3792_;
v___y_3749_ = v___y_3793_;
v___y_3750_ = v___x_3799_;
v___y_3751_ = v___y_3795_;
v___y_3752_ = v___y_3794_;
v___y_3753_ = v___y_3796_;
goto v___jp_3744_;
}
else
{
v___y_3772_ = v___y_3789_;
v___y_3773_ = v___y_3790_;
v___y_3774_ = v___y_3791_;
v___y_3775_ = v___y_3792_;
v___y_3776_ = v___y_3793_;
v___y_3777_ = v___x_3799_;
v___y_3778_ = v___y_3794_;
v___y_3779_ = v___y_3795_;
v___y_3780_ = v___y_3796_;
v___y_3781_ = v___x_2978_;
goto v___jp_3771_;
}
}
}
v___jp_3801_:
{
lean_object* v___x_3810_; 
v___x_3810_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2968_);
if (lean_obj_tag(v___x_3810_) == 0)
{
if (v___y_3805_ == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3811_);
lean_dec_ref_known(v___x_3810_, 1);
v___x_3812_ = lean_io_mono_nanos_now();
v___x_3813_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2982_, v___x_2978_, v_goals_2963_, v___y_3806_, v_a_2966_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v___x_3815_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref_known(v___x_3813_, 1);
v___x_3815_ = l_List_reverse___redArg(v_a_3814_);
v___y_3789_ = v_a_3811_;
v___y_3790_ = v___y_3802_;
v___y_3791_ = v___y_3803_;
v___y_3792_ = v___x_3812_;
v___y_3793_ = v___y_3804_;
v___y_3794_ = v___y_3807_;
v___y_3795_ = v___y_3808_;
v___y_3796_ = v___y_3809_;
v_a_3797_ = v___x_3815_;
goto v___jp_3788_;
}
else
{
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3816_; 
v_a_3816_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3813_, 1);
v___y_3789_ = v_a_3811_;
v___y_3790_ = v___y_3802_;
v___y_3791_ = v___y_3803_;
v___y_3792_ = v___x_3812_;
v___y_3793_ = v___y_3804_;
v___y_3794_ = v___y_3807_;
v___y_3795_ = v___y_3808_;
v___y_3796_ = v___y_3809_;
v_a_3797_ = v_a_3816_;
goto v___jp_3788_;
}
else
{
lean_object* v_a_3817_; 
lean_dec(v___y_3809_);
lean_dec(v___y_3802_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3817_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3813_, 1);
v___y_3689_ = v_a_3811_;
v___y_3690_ = v___y_3803_;
v___y_3691_ = v___x_3812_;
v___y_3692_ = v___y_3804_;
v___y_3693_ = v___y_3807_;
v___y_3694_ = v___y_3808_;
v_a_3695_ = v_a_3817_;
goto v___jp_3688_;
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v_a_3818_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3810_, 1);
v___x_3819_ = lean_io_get_num_heartbeats();
v___x_3820_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2982_, v___x_2978_, v_goals_2963_, v___y_3806_, v_a_2966_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; lean_object* v___x_3822_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3820_, 1);
v___x_3822_ = l_List_reverse___redArg(v_a_3821_);
v___y_3656_ = v_a_3818_;
v___y_3657_ = v___y_3802_;
v___y_3658_ = v___y_3803_;
v___y_3659_ = v___y_3804_;
v___y_3660_ = v___y_3805_;
v___y_3661_ = v___x_3819_;
v___y_3662_ = v___y_3807_;
v___y_3663_ = v___y_3808_;
v___y_3664_ = v___y_3809_;
v_a_3665_ = v___x_3822_;
goto v___jp_3655_;
}
else
{
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3823_; 
v_a_3823_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3823_);
lean_dec_ref_known(v___x_3820_, 1);
v___y_3656_ = v_a_3818_;
v___y_3657_ = v___y_3802_;
v___y_3658_ = v___y_3803_;
v___y_3659_ = v___y_3804_;
v___y_3660_ = v___y_3805_;
v___y_3661_ = v___x_3819_;
v___y_3662_ = v___y_3807_;
v___y_3663_ = v___y_3808_;
v___y_3664_ = v___y_3809_;
v_a_3665_ = v_a_3823_;
goto v___jp_3655_;
}
else
{
lean_object* v_a_3824_; 
lean_dec(v___y_3809_);
lean_dec(v___y_3802_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3824_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3824_);
lean_dec_ref_known(v___x_3820_, 1);
v___y_3567_ = v_a_3818_;
v___y_3568_ = v___y_3803_;
v___y_3569_ = v___y_3804_;
v___y_3570_ = v___x_3819_;
v___y_3571_ = v___y_3807_;
v___y_3572_ = v___y_3808_;
v_a_3573_ = v_a_3824_;
goto v___jp_3566_;
}
}
}
}
else
{
lean_object* v_a_3825_; 
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec(v___y_3802_);
lean_dec(v_snd_2974_);
lean_dec(v_goals_2963_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3825_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3810_, 1);
v___y_3475_ = v___y_3803_;
v___y_3476_ = v___y_3808_;
v_a_3477_ = v_a_3825_;
goto v___jp_3474_;
}
}
v___jp_3826_:
{
if (v___y_3832_ == 0)
{
uint8_t v___x_3833_; 
v___x_3833_ = l_List_isEmpty___redArg(v___y_3827_);
lean_dec(v___y_3827_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
lean_dec(v___y_3831_);
lean_dec(v___y_3829_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v___x_3834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3835_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3834_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
v___y_3524_ = v___y_3828_;
v___y_3525_ = v___y_3830_;
v___y_3526_ = v___x_3835_;
goto v___jp_3523_;
}
else
{
lean_object* v___x_3836_; 
lean_inc(v_trace_2960_);
v___x_3836_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v___y_3829_, v_snd_2974_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3838_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref_known(v___x_3836_, 1);
v___x_3838_ = l_List_appendTR___redArg(v___y_3831_, v_a_3837_);
v___y_3480_ = v___y_3828_;
v___y_3481_ = v___y_3830_;
v_a_3482_ = v___x_3838_;
goto v___jp_3479_;
}
else
{
lean_dec(v___y_3831_);
v___y_3524_ = v___y_3828_;
v___y_3525_ = v___y_3830_;
v___y_3526_ = v___x_3836_;
goto v___jp_3523_;
}
}
}
else
{
v___y_3511_ = v___y_3827_;
v___y_3512_ = v___y_3828_;
v___y_3513_ = v___y_3829_;
v___y_3514_ = v___y_3830_;
v___y_3515_ = v___y_3831_;
goto v___jp_3510_;
}
}
v___jp_3839_:
{
uint8_t v_commitIndependentGoals_3845_; lean_object* v___x_3846_; 
v_commitIndependentGoals_3845_ = lean_ctor_get_uint8(v_cfg_2959_, sizeof(void*)*4);
lean_inc(v___y_3843_);
v___x_3846_ = l_List_appendTR___redArg(v_a_3844_, v___y_3843_);
if (v_commitIndependentGoals_3845_ == 0)
{
v___y_3827_ = v___y_3840_;
v___y_3828_ = v___y_3841_;
v___y_3829_ = v___x_3846_;
v___y_3830_ = v___y_3842_;
v___y_3831_ = v___y_3843_;
v___y_3832_ = v___x_2978_;
goto v___jp_3826_;
}
else
{
uint8_t v___x_3847_; 
v___x_3847_ = l_List_isEmpty___redArg(v___y_3843_);
if (v___x_3847_ == 0)
{
v___y_3511_ = v___y_3840_;
v___y_3512_ = v___y_3841_;
v___y_3513_ = v___x_3846_;
v___y_3514_ = v___y_3842_;
v___y_3515_ = v___y_3843_;
goto v___jp_3510_;
}
else
{
v___y_3827_ = v___y_3840_;
v___y_3828_ = v___y_3841_;
v___y_3829_ = v___x_3846_;
v___y_3830_ = v___y_3842_;
v___y_3831_ = v___y_3843_;
v___y_3832_ = v___x_2978_;
goto v___jp_3826_;
}
}
}
v___jp_3848_:
{
lean_object* v___x_3849_; 
v___x_3849_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2968_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; uint8_t v___x_3852_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3849_, 1);
v___x_3851_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3852_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2980_, v___x_3851_);
if (v___x_3852_ == 0)
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
lean_del_object(v___x_2976_);
v___x_3853_ = lean_io_mono_nanos_now();
v___x_3854_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2973_, v___f_2983_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v_fst_3856_; lean_object* v_snd_3857_; lean_object* v___x_3858_; lean_object* v___f_3859_; lean_object* v___x_3860_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref_known(v___x_3854_, 1);
v_fst_3856_ = lean_ctor_get(v_a_3855_, 0);
lean_inc_n(v_fst_3856_, 2);
v_snd_3857_ = lean_ctor_get(v_a_3855_, 1);
lean_inc(v_snd_3857_);
lean_dec(v_a_3855_);
v___x_3858_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3857_, v___x_2970_);
lean_inc(v___x_3858_);
v___f_3859_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3859_, 0, v_fst_3856_);
lean_closure_set(v___f_3859_, 1, v___x_3858_);
v___x_3860_ = lean_box(0);
if (v___x_3070_ == 0)
{
lean_object* v___x_3861_; uint8_t v___x_3862_; 
v___x_3861_ = l_Lean_trace_profiler;
v___x_3862_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2980_, v___x_3861_);
if (v___x_3862_ == 0)
{
lean_object* v___x_3863_; 
lean_dec_ref(v___f_3859_);
v___x_3863_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2982_, v___x_2978_, v_goals_2963_, v___x_3860_, v_a_2966_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3865_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v___x_3863_, 1);
v___x_3865_ = l_List_reverse___redArg(v_a_3864_);
v___y_3840_ = v_fst_3856_;
v___y_3841_ = v___x_3853_;
v___y_3842_ = v_a_3850_;
v___y_3843_ = v___x_3858_;
v_a_3844_ = v___x_3865_;
goto v___jp_3839_;
}
else
{
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3866_; 
v_a_3866_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3866_);
lean_dec_ref_known(v___x_3863_, 1);
v___y_3840_ = v_fst_3856_;
v___y_3841_ = v___x_3853_;
v___y_3842_ = v_a_3850_;
v___y_3843_ = v___x_3858_;
v_a_3844_ = v_a_3866_;
goto v___jp_3839_;
}
else
{
lean_object* v_a_3867_; 
lean_dec(v___x_3858_);
lean_dec(v_fst_3856_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3867_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3863_, 1);
v___y_3475_ = v___x_3853_;
v___y_3476_ = v_a_3850_;
v_a_3477_ = v_a_3867_;
goto v___jp_3474_;
}
}
}
else
{
v___y_3802_ = v_fst_3856_;
v___y_3803_ = v___x_3853_;
v___y_3804_ = v___x_3070_;
v___y_3805_ = v___x_3852_;
v___y_3806_ = v___x_3860_;
v___y_3807_ = v___f_3859_;
v___y_3808_ = v_a_3850_;
v___y_3809_ = v___x_3858_;
goto v___jp_3801_;
}
}
else
{
v___y_3802_ = v_fst_3856_;
v___y_3803_ = v___x_3853_;
v___y_3804_ = v___x_3070_;
v___y_3805_ = v___x_3852_;
v___y_3806_ = v___x_3860_;
v___y_3807_ = v___f_3859_;
v___y_3808_ = v_a_3850_;
v___y_3809_ = v___x_3858_;
goto v___jp_3801_;
}
}
else
{
lean_object* v_a_3868_; 
lean_dec(v_snd_2974_);
lean_dec(v_goals_2963_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3868_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___x_3854_, 1);
v___y_3475_ = v___x_3853_;
v___y_3476_ = v_a_3850_;
v_a_3477_ = v_a_3868_;
goto v___jp_3474_;
}
}
else
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = lean_io_get_num_heartbeats();
v___x_3870_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2973_, v___f_2983_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v_fst_3872_; lean_object* v_snd_3873_; lean_object* v___x_3874_; lean_object* v___f_3875_; lean_object* v___x_3876_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v_fst_3872_ = lean_ctor_get(v_a_3871_, 0);
lean_inc_n(v_fst_3872_, 2);
v_snd_3873_ = lean_ctor_get(v_a_3871_, 1);
lean_inc(v_snd_3873_);
lean_dec(v_a_3871_);
v___x_3874_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3873_, v___x_2970_);
lean_inc(v___x_3874_);
v___f_3875_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3875_, 0, v_fst_3872_);
lean_closure_set(v___f_3875_, 1, v___x_3874_);
v___x_3876_ = lean_box(0);
if (v___x_3070_ == 0)
{
lean_object* v___x_3877_; uint8_t v___x_3878_; 
v___x_3877_ = l_Lean_trace_profiler;
v___x_3878_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2980_, v___x_3877_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; 
lean_dec_ref(v___f_3875_);
v___x_3879_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3852_, v___x_2978_, v_goals_2963_, v___x_3876_, v_a_2966_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3881_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3881_ = l_List_reverse___redArg(v_a_3880_);
v___y_3451_ = v_fst_3872_;
v___y_3452_ = v___x_3869_;
v___y_3453_ = v_a_3850_;
v___y_3454_ = v___x_3874_;
v_a_3455_ = v___x_3881_;
goto v___jp_3450_;
}
else
{
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3882_; 
v_a_3882_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3879_, 1);
v___y_3451_ = v_fst_3872_;
v___y_3452_ = v___x_3869_;
v___y_3453_ = v_a_3850_;
v___y_3454_ = v___x_3874_;
v_a_3455_ = v_a_3882_;
goto v___jp_3450_;
}
else
{
lean_object* v_a_3883_; 
lean_dec(v___x_3874_);
lean_dec(v_fst_3872_);
lean_dec(v_snd_2974_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3883_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3883_);
lean_dec_ref_known(v___x_3879_, 1);
v___y_3086_ = v___x_3869_;
v___y_3087_ = v_a_3850_;
v_a_3088_ = v_a_3883_;
goto v___jp_3085_;
}
}
}
else
{
v___y_3413_ = v___x_3876_;
v___y_3414_ = v_fst_3872_;
v___y_3415_ = v___f_3875_;
v___y_3416_ = v___x_3852_;
v___y_3417_ = v___x_3070_;
v___y_3418_ = v___x_3869_;
v___y_3419_ = v_a_3850_;
v___y_3420_ = v___x_3874_;
goto v___jp_3412_;
}
}
else
{
v___y_3413_ = v___x_3876_;
v___y_3414_ = v_fst_3872_;
v___y_3415_ = v___f_3875_;
v___y_3416_ = v___x_3852_;
v___y_3417_ = v___x_3070_;
v___y_3418_ = v___x_3869_;
v___y_3419_ = v_a_3850_;
v___y_3420_ = v___x_3874_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3884_; 
lean_dec(v_snd_2974_);
lean_dec(v_goals_2963_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec_ref(v_cfg_2959_);
v_a_3884_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3870_, 1);
v___y_3086_ = v___x_3869_;
v___y_3087_ = v_a_3850_;
v_a_3088_ = v_a_3884_;
goto v___jp_3085_;
}
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
lean_dec_ref(v___f_3066_);
lean_dec_ref(v___f_2983_);
lean_del_object(v___x_2976_);
lean_dec(v_snd_2974_);
lean_dec(v_fst_2973_);
lean_dec(v_goals_2963_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec(v_trace_2960_);
lean_dec_ref(v_cfg_2959_);
v_a_3885_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3849_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3849_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
}
}
else
{
lean_object* v_maxDepth_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
lean_del_object(v___x_2976_);
lean_dec(v_snd_2974_);
lean_dec(v_fst_2973_);
lean_dec(v_goals_2963_);
v_maxDepth_4172_ = lean_ctor_get(v_cfg_2959_, 0);
lean_inc(v_maxDepth_4172_);
v___x_4173_ = lean_box(0);
v___x_4174_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2959_, v_trace_2960_, v_next_2961_, v_orig_2962_, v_maxDepth_4172_, v_remaining_2964_, v___x_4173_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
return v___x_4174_;
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_dec(v_remaining_2964_);
lean_dec(v_goals_2963_);
lean_dec(v_orig_2962_);
lean_dec_ref(v_next_2961_);
lean_dec(v_trace_2960_);
lean_dec_ref(v_cfg_2959_);
v_a_4176_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_2971_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_2971_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_4184_, lean_object* v_trace_4185_, lean_object* v_next_4186_, lean_object* v_orig_4187_, lean_object* v_goals_4188_, lean_object* v_remaining_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4184_, v_trace_4185_, v_next_4186_, v_orig_4187_, v_goals_4188_, v_remaining_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_4196_, lean_object* v_00_u03b2_4197_, lean_object* v_L_4198_, lean_object* v_f_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_4198_, v_f_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_4206_, lean_object* v_00_u03b2_4207_, lean_object* v_L_4208_, lean_object* v_f_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_4206_, v_00_u03b2_4207_, v_L_4208_, v_f_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_4216_, lean_object* v_x_4217_, lean_object* v_x_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v___x_4224_; 
v___x_4224_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_4216_, v_x_4217_, v_x_4218_, v___y_4220_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_4225_, lean_object* v_x_4226_, lean_object* v_x_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
uint8_t v___x_48444__boxed_4233_; lean_object* v_res_4234_; 
v___x_48444__boxed_4233_ = lean_unbox(v___x_4225_);
v_res_4234_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_48444__boxed_4233_, v_x_4226_, v_x_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_4235_, uint8_t v___x_4236_, lean_object* v_x_4237_, lean_object* v_x_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_4235_, v___x_4236_, v_x_4237_, v_x_4238_, v___y_4240_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_4245_, lean_object* v___x_4246_, lean_object* v_x_4247_, lean_object* v_x_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
uint8_t v___x_48470__boxed_4254_; uint8_t v___x_48471__boxed_4255_; lean_object* v_res_4256_; 
v___x_48470__boxed_4254_ = lean_unbox(v___x_4245_);
v___x_48471__boxed_4255_ = lean_unbox(v___x_4246_);
v_res_4256_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_48470__boxed_4254_, v___x_48471__boxed_4255_, v_x_4247_, v_x_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_4257_, lean_object* v_00_u03b2_4258_, lean_object* v_f_4259_, lean_object* v_x_4260_, lean_object* v_x_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_4259_, v_x_4260_, v_x_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_4268_, lean_object* v_00_u03b2_4269_, lean_object* v_f_4270_, lean_object* v_x_4271_, lean_object* v_x_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v_res_4278_; 
v_res_4278_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_4268_, v_00_u03b2_4269_, v_f_4270_, v_x_4271_, v_x_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_4279_, lean_object* v_00_u03b2_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_4281_, v_a_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_4284_, lean_object* v_00_u03b2_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_4286_, v_a_4287_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_4289_, lean_object* v_g_4290_, lean_object* v_f_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v___x_4297_; 
lean_inc(v___y_4295_);
lean_inc_ref(v___y_4294_);
lean_inc(v___y_4293_);
lean_inc_ref(v___y_4292_);
v___x_4297_ = lean_apply_6(v_next_4289_, v_g_4290_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_, lean_box(0));
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4299_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
v___x_4299_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_4298_, v_f_4291_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
return v___x_4299_;
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec_ref(v_f_4291_);
v_a_4300_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4297_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4297_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_4308_, lean_object* v_g_4309_, lean_object* v_f_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_4308_, v_g_4309_, v_f_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_4317_, lean_object* v_trace_4318_, lean_object* v_next_4319_, lean_object* v_goals_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v_resolve_4326_; lean_object* v___x_4327_; 
v_resolve_4326_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_4326_, 0, v_next_4319_);
lean_inc_n(v_goals_4320_, 2);
v___x_4327_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_4317_, v_trace_4318_, v_resolve_4326_, v_goals_4320_, v_goals_4320_, v_goals_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_4328_, lean_object* v_trace_4329_, lean_object* v_next_4330_, lean_object* v_goals_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_){
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_4328_, v_trace_4329_, v_next_4330_, v_goals_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_);
lean_dec(v_a_4335_);
lean_dec_ref(v_a_4334_);
lean_dec(v_a_4333_);
lean_dec_ref(v_a_4332_);
return v_res_4337_;
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

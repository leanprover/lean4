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
v_options_316_ = lean_ctor_get(v___y_308_, 1);
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object* v_e_410_){
_start:
{
if (lean_obj_tag(v_e_410_) == 0)
{
uint8_t v___x_411_; 
v___x_411_ = 2;
return v___x_411_;
}
else
{
lean_object* v_a_412_; 
v_a_412_ = lean_ctor_get(v_e_410_, 0);
if (lean_obj_tag(v_a_412_) == 0)
{
uint8_t v___x_413_; 
v___x_413_ = 1;
return v___x_413_;
}
else
{
uint8_t v___x_414_; 
v___x_414_ = 0;
return v___x_414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object* v_e_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_e_415_);
lean_dec_ref(v_e_415_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(lean_object* v_x_418_){
_start:
{
if (lean_obj_tag(v_x_418_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
v_a_420_ = lean_ctor_get(v_x_418_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v_x_418_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v_x_418_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v_x_418_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set_tag(v___x_422_, 1);
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_a_428_ = lean_ctor_get(v_x_418_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_x_418_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v_x_418_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v_x_418_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 0);
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg___boxed(lean_object* v_x_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(size_t v_sz_439_, size_t v_i_440_, lean_object* v_bs_441_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = lean_usize_dec_lt(v_i_440_, v_sz_439_);
if (v___x_442_ == 0)
{
return v_bs_441_;
}
else
{
lean_object* v_v_443_; lean_object* v_msg_444_; lean_object* v___x_445_; lean_object* v_bs_x27_446_; size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
v_v_443_ = lean_array_uget_borrowed(v_bs_441_, v_i_440_);
v_msg_444_ = lean_ctor_get(v_v_443_, 1);
lean_inc_ref(v_msg_444_);
v___x_445_ = lean_unsigned_to_nat(0u);
v_bs_x27_446_ = lean_array_uset(v_bs_441_, v_i_440_, v___x_445_);
v___x_447_ = ((size_t)1ULL);
v___x_448_ = lean_usize_add(v_i_440_, v___x_447_);
v___x_449_ = lean_array_uset(v_bs_x27_446_, v_i_440_, v_msg_444_);
v_i_440_ = v___x_448_;
v_bs_441_ = v___x_449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6___boxed(lean_object* v_sz_451_, lean_object* v_i_452_, lean_object* v_bs_453_){
_start:
{
size_t v_sz_boxed_454_; size_t v_i_boxed_455_; lean_object* v_res_456_; 
v_sz_boxed_454_ = lean_unbox_usize(v_sz_451_);
lean_dec(v_sz_451_);
v_i_boxed_455_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_res_456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_boxed_454_, v_i_boxed_455_, v_bs_453_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object* v_oldTraces_457_, lean_object* v_data_458_, lean_object* v_ref_459_, lean_object* v_msg_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_toCold_466_; lean_object* v_options_467_; lean_object* v_currRecDepth_468_; lean_object* v_maxRecDepth_469_; lean_object* v_ref_470_; lean_object* v_currNamespace_471_; lean_object* v_openDecls_472_; lean_object* v_initHeartbeats_473_; lean_object* v_maxHeartbeats_474_; lean_object* v_currMacroScope_475_; uint8_t v_diag_476_; uint8_t v_suppressElabErrors_477_; lean_object* v___x_478_; lean_object* v_traceState_479_; lean_object* v_traces_480_; lean_object* v_ref_481_; lean_object* v___x_482_; lean_object* v___x_483_; size_t v_sz_484_; size_t v___x_485_; lean_object* v___x_486_; lean_object* v_msg_487_; lean_object* v___x_488_; lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_526_; 
v_toCold_466_ = lean_ctor_get(v___y_463_, 0);
v_options_467_ = lean_ctor_get(v___y_463_, 1);
v_currRecDepth_468_ = lean_ctor_get(v___y_463_, 2);
v_maxRecDepth_469_ = lean_ctor_get(v___y_463_, 3);
v_ref_470_ = lean_ctor_get(v___y_463_, 4);
v_currNamespace_471_ = lean_ctor_get(v___y_463_, 5);
v_openDecls_472_ = lean_ctor_get(v___y_463_, 6);
v_initHeartbeats_473_ = lean_ctor_get(v___y_463_, 7);
v_maxHeartbeats_474_ = lean_ctor_get(v___y_463_, 8);
v_currMacroScope_475_ = lean_ctor_get(v___y_463_, 9);
v_diag_476_ = lean_ctor_get_uint8(v___y_463_, sizeof(void*)*10);
v_suppressElabErrors_477_ = lean_ctor_get_uint8(v___y_463_, sizeof(void*)*10 + 1);
v___x_478_ = lean_st_ref_get(v___y_464_);
v_traceState_479_ = lean_ctor_get(v___x_478_, 4);
lean_inc_ref(v_traceState_479_);
lean_dec(v___x_478_);
v_traces_480_ = lean_ctor_get(v_traceState_479_, 0);
lean_inc_ref(v_traces_480_);
lean_dec_ref(v_traceState_479_);
v_ref_481_ = l_Lean_replaceRef(v_ref_459_, v_ref_470_);
lean_inc(v_currMacroScope_475_);
lean_inc(v_maxHeartbeats_474_);
lean_inc(v_initHeartbeats_473_);
lean_inc(v_openDecls_472_);
lean_inc(v_currNamespace_471_);
lean_inc(v_maxRecDepth_469_);
lean_inc(v_currRecDepth_468_);
lean_inc_ref(v_options_467_);
lean_inc_ref(v_toCold_466_);
v___x_482_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_482_, 0, v_toCold_466_);
lean_ctor_set(v___x_482_, 1, v_options_467_);
lean_ctor_set(v___x_482_, 2, v_currRecDepth_468_);
lean_ctor_set(v___x_482_, 3, v_maxRecDepth_469_);
lean_ctor_set(v___x_482_, 4, v_ref_481_);
lean_ctor_set(v___x_482_, 5, v_currNamespace_471_);
lean_ctor_set(v___x_482_, 6, v_openDecls_472_);
lean_ctor_set(v___x_482_, 7, v_initHeartbeats_473_);
lean_ctor_set(v___x_482_, 8, v_maxHeartbeats_474_);
lean_ctor_set(v___x_482_, 9, v_currMacroScope_475_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*10, v_diag_476_);
lean_ctor_set_uint8(v___x_482_, sizeof(void*)*10 + 1, v_suppressElabErrors_477_);
v___x_483_ = l_Lean_PersistentArray_toArray___redArg(v_traces_480_);
lean_dec_ref(v_traces_480_);
v_sz_484_ = lean_array_size(v___x_483_);
v___x_485_ = ((size_t)0ULL);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_484_, v___x_485_, v___x_483_);
v_msg_487_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_487_, 0, v_data_458_);
lean_ctor_set(v_msg_487_, 1, v_msg_460_);
lean_ctor_set(v_msg_487_, 2, v___x_486_);
v___x_488_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_487_, v___y_461_, v___y_462_, v___x_482_, v___y_464_);
lean_dec_ref_known(v___x_482_, 10);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_526_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_526_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_526_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v_traceState_494_; lean_object* v_env_495_; lean_object* v_nextMacroScope_496_; lean_object* v_ngen_497_; lean_object* v_auxDeclNGen_498_; lean_object* v_cache_499_; lean_object* v_messages_500_; lean_object* v_infoState_501_; lean_object* v_snapshotTasks_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_525_; 
v___x_493_ = lean_st_ref_take(v___y_464_);
v_traceState_494_ = lean_ctor_get(v___x_493_, 4);
v_env_495_ = lean_ctor_get(v___x_493_, 0);
v_nextMacroScope_496_ = lean_ctor_get(v___x_493_, 1);
v_ngen_497_ = lean_ctor_get(v___x_493_, 2);
v_auxDeclNGen_498_ = lean_ctor_get(v___x_493_, 3);
v_cache_499_ = lean_ctor_get(v___x_493_, 5);
v_messages_500_ = lean_ctor_get(v___x_493_, 6);
v_infoState_501_ = lean_ctor_get(v___x_493_, 7);
v_snapshotTasks_502_ = lean_ctor_get(v___x_493_, 8);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_525_ == 0)
{
v___x_504_ = v___x_493_;
v_isShared_505_ = v_isSharedCheck_525_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_snapshotTasks_502_);
lean_inc(v_infoState_501_);
lean_inc(v_messages_500_);
lean_inc(v_cache_499_);
lean_inc(v_traceState_494_);
lean_inc(v_auxDeclNGen_498_);
lean_inc(v_ngen_497_);
lean_inc(v_nextMacroScope_496_);
lean_inc(v_env_495_);
lean_dec(v___x_493_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_525_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint64_t v_tid_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_523_; 
v_tid_506_ = lean_ctor_get_uint64(v_traceState_494_, sizeof(void*)*1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_traceState_494_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v_traceState_494_, 0);
lean_dec(v_unused_524_);
v___x_508_ = v_traceState_494_;
v_isShared_509_ = v_isSharedCheck_523_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_traceState_494_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_523_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v_ref_459_);
lean_ctor_set(v___x_510_, 1, v_a_489_);
v___x_511_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_457_, v___x_510_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_511_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_511_);
lean_ctor_set_uint64(v_reuseFailAlloc_522_, sizeof(void*)*1, v_tid_506_);
v___x_513_ = v_reuseFailAlloc_522_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 4, v___x_513_);
v___x_515_ = v___x_504_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_env_495_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_nextMacroScope_496_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_ngen_497_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_auxDeclNGen_498_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_521_, 5, v_cache_499_);
lean_ctor_set(v_reuseFailAlloc_521_, 6, v_messages_500_);
lean_ctor_set(v_reuseFailAlloc_521_, 7, v_infoState_501_);
lean_ctor_set(v_reuseFailAlloc_521_, 8, v_snapshotTasks_502_);
v___x_515_ = v_reuseFailAlloc_521_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_516_ = lean_st_ref_put(v___y_464_, v___x_515_);
v___x_517_ = lean_box(0);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_517_);
v___x_519_ = v___x_491_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object* v_oldTraces_527_, lean_object* v_data_528_, lean_object* v_ref_529_, lean_object* v_msg_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_527_, v_data_528_, v_ref_529_, v_msg_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_536_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0(void){
_start:
{
lean_object* v___x_537_; double v___x_538_; 
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = lean_float_of_nat(v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1));
v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
return v___x_541_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3(void){
_start:
{
lean_object* v___x_542_; double v___x_543_; 
v___x_542_ = lean_unsigned_to_nat(1000u);
v___x_543_ = lean_float_of_nat(v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_cls_544_, uint8_t v_collapsed_545_, lean_object* v_tag_546_, lean_object* v_opts_547_, uint8_t v_clsEnabled_548_, lean_object* v_oldTraces_549_, lean_object* v_msg_550_, lean_object* v_resStartStop_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_fst_557_; lean_object* v_snd_558_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v_data_562_; lean_object* v_fst_573_; lean_object* v_snd_574_; lean_object* v___x_575_; uint8_t v___x_576_; lean_object* v___y_578_; lean_object* v_a_579_; uint8_t v___y_594_; double v___y_625_; 
v_fst_557_ = lean_ctor_get(v_resStartStop_551_, 0);
lean_inc(v_fst_557_);
v_snd_558_ = lean_ctor_get(v_resStartStop_551_, 1);
lean_inc(v_snd_558_);
lean_dec_ref(v_resStartStop_551_);
v_fst_573_ = lean_ctor_get(v_snd_558_, 0);
lean_inc(v_fst_573_);
v_snd_574_ = lean_ctor_get(v_snd_558_, 1);
lean_inc(v_snd_574_);
lean_dec(v_snd_558_);
v___x_575_ = l_Lean_trace_profiler;
v___x_576_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_547_, v___x_575_);
if (v___x_576_ == 0)
{
v___y_594_ = v___x_576_;
goto v___jp_593_;
}
else
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = l_Lean_trace_profiler_useHeartbeats;
v___x_631_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_547_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; double v___x_634_; double v___x_635_; double v___x_636_; 
v___x_632_ = l_Lean_trace_profiler_threshold;
v___x_633_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_547_, v___x_632_);
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
v___x_638_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_547_, v___x_637_);
v___x_639_ = lean_float_of_nat(v___x_638_);
v___y_625_ = v___x_639_;
goto v___jp_624_;
}
}
v___jp_559_:
{
lean_object* v___x_563_; 
lean_inc(v___y_560_);
v___x_563_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_549_, v_data_562_, v___y_560_, v___y_561_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v___x_564_; 
lean_dec_ref_known(v___x_563_, 1);
v___x_564_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_557_);
return v___x_564_;
}
else
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec(v_fst_557_);
v_a_565_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_563_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_563_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_a_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
v___jp_577_:
{
uint8_t v_result_580_; lean_object* v___x_581_; lean_object* v___x_582_; double v___x_583_; lean_object* v_data_584_; 
v_result_580_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_fst_557_);
v___x_581_ = lean_box(v_result_580_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
v___x_583_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_546_);
lean_inc_ref(v___x_582_);
lean_inc(v_cls_544_);
v_data_584_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_584_, 0, v_cls_544_);
lean_ctor_set(v_data_584_, 1, v___x_582_);
lean_ctor_set(v_data_584_, 2, v_tag_546_);
lean_ctor_set_float(v_data_584_, sizeof(void*)*3, v___x_583_);
lean_ctor_set_float(v_data_584_, sizeof(void*)*3 + 8, v___x_583_);
lean_ctor_set_uint8(v_data_584_, sizeof(void*)*3 + 16, v_collapsed_545_);
if (v___x_576_ == 0)
{
lean_dec_ref_known(v___x_582_, 1);
lean_dec(v_snd_574_);
lean_dec(v_fst_573_);
lean_dec_ref(v_tag_546_);
lean_dec(v_cls_544_);
v___y_560_ = v___y_578_;
v___y_561_ = v_a_579_;
v_data_562_ = v_data_584_;
goto v___jp_559_;
}
else
{
lean_object* v_data_585_; double v___x_586_; double v___x_587_; 
lean_dec_ref_known(v_data_584_, 3);
v_data_585_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_585_, 0, v_cls_544_);
lean_ctor_set(v_data_585_, 1, v___x_582_);
lean_ctor_set(v_data_585_, 2, v_tag_546_);
v___x_586_ = lean_unbox_float(v_fst_573_);
lean_dec(v_fst_573_);
lean_ctor_set_float(v_data_585_, sizeof(void*)*3, v___x_586_);
v___x_587_ = lean_unbox_float(v_snd_574_);
lean_dec(v_snd_574_);
lean_ctor_set_float(v_data_585_, sizeof(void*)*3 + 8, v___x_587_);
lean_ctor_set_uint8(v_data_585_, sizeof(void*)*3 + 16, v_collapsed_545_);
v___y_560_ = v___y_578_;
v___y_561_ = v_a_579_;
v_data_562_ = v_data_585_;
goto v___jp_559_;
}
}
v___jp_588_:
{
lean_object* v_ref_589_; lean_object* v___x_590_; 
v_ref_589_ = lean_ctor_get(v___y_554_, 4);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
lean_inc(v_fst_557_);
v___x_590_ = lean_apply_6(v_msg_550_, v_fst_557_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, lean_box(0));
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___y_578_ = v_ref_589_;
v_a_579_ = v_a_591_;
goto v___jp_577_;
}
else
{
lean_object* v___x_592_; 
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_578_ = v_ref_589_;
v_a_579_ = v___x_592_;
goto v___jp_577_;
}
}
v___jp_593_:
{
if (v_clsEnabled_548_ == 0)
{
if (v___y_594_ == 0)
{
lean_object* v___x_595_; lean_object* v_traceState_596_; lean_object* v_env_597_; lean_object* v_nextMacroScope_598_; lean_object* v_ngen_599_; lean_object* v_auxDeclNGen_600_; lean_object* v_cache_601_; lean_object* v_messages_602_; lean_object* v_infoState_603_; lean_object* v_snapshotTasks_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_snd_574_);
lean_dec(v_fst_573_);
lean_dec_ref(v_msg_550_);
lean_dec_ref(v_tag_546_);
lean_dec(v_cls_544_);
v___x_595_ = lean_st_ref_take(v___y_555_);
v_traceState_596_ = lean_ctor_get(v___x_595_, 4);
v_env_597_ = lean_ctor_get(v___x_595_, 0);
v_nextMacroScope_598_ = lean_ctor_get(v___x_595_, 1);
v_ngen_599_ = lean_ctor_get(v___x_595_, 2);
v_auxDeclNGen_600_ = lean_ctor_get(v___x_595_, 3);
v_cache_601_ = lean_ctor_get(v___x_595_, 5);
v_messages_602_ = lean_ctor_get(v___x_595_, 6);
v_infoState_603_ = lean_ctor_get(v___x_595_, 7);
v_snapshotTasks_604_ = lean_ctor_get(v___x_595_, 8);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_623_ == 0)
{
v___x_606_ = v___x_595_;
v_isShared_607_ = v_isSharedCheck_623_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_snapshotTasks_604_);
lean_inc(v_infoState_603_);
lean_inc(v_messages_602_);
lean_inc(v_cache_601_);
lean_inc(v_traceState_596_);
lean_inc(v_auxDeclNGen_600_);
lean_inc(v_ngen_599_);
lean_inc(v_nextMacroScope_598_);
lean_inc(v_env_597_);
lean_dec(v___x_595_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_623_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
uint64_t v_tid_608_; lean_object* v_traces_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_622_; 
v_tid_608_ = lean_ctor_get_uint64(v_traceState_596_, sizeof(void*)*1);
v_traces_609_ = lean_ctor_get(v_traceState_596_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v_traceState_596_);
if (v_isSharedCheck_622_ == 0)
{
v___x_611_ = v_traceState_596_;
v_isShared_612_ = v_isSharedCheck_622_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_traces_609_);
lean_dec(v_traceState_596_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_622_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_549_, v_traces_609_);
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
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_env_597_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_nextMacroScope_598_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_ngen_599_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_auxDeclNGen_600_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_620_, 5, v_cache_601_);
lean_ctor_set(v_reuseFailAlloc_620_, 6, v_messages_602_);
lean_ctor_set(v_reuseFailAlloc_620_, 7, v_infoState_603_);
lean_ctor_set(v_reuseFailAlloc_620_, 8, v_snapshotTasks_604_);
v___x_617_ = v_reuseFailAlloc_620_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_st_ref_put(v___y_555_, v___x_617_);
v___x_619_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_557_);
return v___x_619_;
}
}
}
}
}
else
{
goto v___jp_588_;
}
}
else
{
goto v___jp_588_;
}
}
v___jp_624_:
{
double v___x_626_; double v___x_627_; double v___x_628_; uint8_t v___x_629_; 
v___x_626_ = lean_unbox_float(v_snd_574_);
v___x_627_ = lean_unbox_float(v_fst_573_);
v___x_628_ = lean_float_sub(v___x_626_, v___x_627_);
v___x_629_ = lean_float_decLt(v___y_625_, v___x_628_);
v___y_594_ = v___x_629_;
goto v___jp_593_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* v_a_659_, lean_object* v_x_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_666_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
v___x_667_ = l_Lean_Exception_toMessageData(v_a_659_);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* v_a_670_, lean_object* v_x_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_a_670_, v_x_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec_ref(v_x_671_);
return v_res_677_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object* v_keys_678_, lean_object* v_i_679_, lean_object* v_k_680_){
_start:
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = lean_array_get_size(v_keys_678_);
v___x_682_ = lean_nat_dec_lt(v_i_679_, v___x_681_);
if (v___x_682_ == 0)
{
lean_dec(v_i_679_);
return v___x_682_;
}
else
{
lean_object* v_k_x27_683_; uint8_t v___x_684_; 
v_k_x27_683_ = lean_array_fget_borrowed(v_keys_678_, v_i_679_);
v___x_684_ = l_Lean_instBEqMVarId_beq(v_k_680_, v_k_x27_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_add(v_i_679_, v___x_685_);
lean_dec(v_i_679_);
v_i_679_ = v___x_686_;
goto _start;
}
else
{
lean_dec(v_i_679_);
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object* v_keys_688_, lean_object* v_i_689_, lean_object* v_k_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_688_, v_i_689_, v_k_690_);
lean_dec(v_k_690_);
lean_dec_ref(v_keys_688_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_693_, size_t v_x_694_, lean_object* v_x_695_){
_start:
{
if (lean_obj_tag(v_x_693_) == 0)
{
lean_object* v_es_696_; lean_object* v___x_697_; size_t v___x_698_; size_t v___x_699_; lean_object* v_j_700_; lean_object* v___x_701_; 
v_es_696_ = lean_ctor_get(v_x_693_, 0);
v___x_697_ = lean_box(2);
v___x_698_ = ((size_t)31ULL);
v___x_699_ = lean_usize_land(v_x_694_, v___x_698_);
v_j_700_ = lean_usize_to_nat(v___x_699_);
v___x_701_ = lean_array_get_borrowed(v___x_697_, v_es_696_, v_j_700_);
lean_dec(v_j_700_);
switch(lean_obj_tag(v___x_701_))
{
case 0:
{
lean_object* v_key_702_; uint8_t v___x_703_; 
v_key_702_ = lean_ctor_get(v___x_701_, 0);
v___x_703_ = l_Lean_instBEqMVarId_beq(v_x_695_, v_key_702_);
return v___x_703_;
}
case 1:
{
lean_object* v_node_704_; size_t v___x_705_; size_t v___x_706_; 
v_node_704_ = lean_ctor_get(v___x_701_, 0);
v___x_705_ = ((size_t)5ULL);
v___x_706_ = lean_usize_shift_right(v_x_694_, v___x_705_);
v_x_693_ = v_node_704_;
v_x_694_ = v___x_706_;
goto _start;
}
default: 
{
uint8_t v___x_708_; 
v___x_708_ = 0;
return v___x_708_;
}
}
}
else
{
lean_object* v_ks_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_ks_709_ = lean_ctor_get(v_x_693_, 0);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_ks_709_, v___x_710_, v_x_695_);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v_x_714_){
_start:
{
size_t v_x_73858__boxed_715_; uint8_t v_res_716_; lean_object* v_r_717_; 
v_x_73858__boxed_715_ = lean_unbox_usize(v_x_713_);
lean_dec(v_x_713_);
v_res_716_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_712_, v_x_73858__boxed_715_, v_x_714_);
lean_dec(v_x_714_);
lean_dec_ref(v_x_712_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
uint64_t v___x_720_; size_t v___x_721_; uint8_t v___x_722_; 
v___x_720_ = l_Lean_instHashableMVarId_hash(v_x_719_);
v___x_721_ = lean_uint64_to_usize(v___x_720_);
v___x_722_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_718_, v___x_721_, v_x_719_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_723_, v_x_724_);
lean_dec(v_x_724_);
lean_dec_ref(v_x_723_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object* v_mvarId_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; lean_object* v_mctx_731_; lean_object* v_eAssignment_732_; uint8_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_730_ = lean_st_ref_get(v___y_728_);
v_mctx_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_ref(v_mctx_731_);
lean_dec(v___x_730_);
v_eAssignment_732_ = lean_ctor_get(v_mctx_731_, 8);
lean_inc_ref(v_eAssignment_732_);
lean_dec_ref(v_mctx_731_);
v___x_733_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_eAssignment_732_, v_mvarId_727_);
lean_dec_ref(v_eAssignment_732_);
v___x_734_ = lean_box(v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object* v_mvarId_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec(v_mvarId_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_ref_746_; lean_object* v___x_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
v_ref_746_ = lean_ctor_get(v___y_743_, 4);
v___x_747_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
lean_inc(v_ref_746_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_ref_746_);
lean_ctor_set(v___x_752_, 1, v_a_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 1);
lean_ctor_set(v___x_750_, 0, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_763_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_e_764_){
_start:
{
if (lean_obj_tag(v_e_764_) == 0)
{
uint8_t v___x_765_; 
v___x_765_ = 2;
return v___x_765_;
}
else
{
uint8_t v___x_766_; 
v___x_766_ = 0;
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_e_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_e_767_);
lean_dec_ref(v_e_767_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_770_, uint8_t v_collapsed_771_, lean_object* v_tag_772_, lean_object* v_opts_773_, uint8_t v_clsEnabled_774_, lean_object* v_oldTraces_775_, lean_object* v_msg_776_, lean_object* v_resStartStop_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_fst_783_; lean_object* v_snd_784_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v_data_788_; lean_object* v_fst_799_; lean_object* v_snd_800_; lean_object* v___x_801_; uint8_t v___x_802_; lean_object* v___y_804_; lean_object* v_a_805_; uint8_t v___y_820_; double v___y_851_; 
v_fst_783_ = lean_ctor_get(v_resStartStop_777_, 0);
lean_inc(v_fst_783_);
v_snd_784_ = lean_ctor_get(v_resStartStop_777_, 1);
lean_inc(v_snd_784_);
lean_dec_ref(v_resStartStop_777_);
v_fst_799_ = lean_ctor_get(v_snd_784_, 0);
lean_inc(v_fst_799_);
v_snd_800_ = lean_ctor_get(v_snd_784_, 1);
lean_inc(v_snd_800_);
lean_dec(v_snd_784_);
v___x_801_ = l_Lean_trace_profiler;
v___x_802_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_773_, v___x_801_);
if (v___x_802_ == 0)
{
v___y_820_ = v___x_802_;
goto v___jp_819_;
}
else
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = l_Lean_trace_profiler_useHeartbeats;
v___x_857_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_773_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; double v___x_860_; double v___x_861_; double v___x_862_; 
v___x_858_ = l_Lean_trace_profiler_threshold;
v___x_859_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_773_, v___x_858_);
v___x_860_ = lean_float_of_nat(v___x_859_);
v___x_861_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_862_ = lean_float_div(v___x_860_, v___x_861_);
v___y_851_ = v___x_862_;
goto v___jp_850_;
}
else
{
lean_object* v___x_863_; lean_object* v___x_864_; double v___x_865_; 
v___x_863_ = l_Lean_trace_profiler_threshold;
v___x_864_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_773_, v___x_863_);
v___x_865_ = lean_float_of_nat(v___x_864_);
v___y_851_ = v___x_865_;
goto v___jp_850_;
}
}
v___jp_785_:
{
lean_object* v___x_789_; 
lean_inc(v___y_786_);
v___x_789_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_775_, v_data_788_, v___y_786_, v___y_787_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_790_; 
lean_dec_ref_known(v___x_789_, 1);
v___x_790_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_783_);
return v___x_790_;
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_fst_783_);
v_a_791_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_789_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
v___jp_803_:
{
uint8_t v_result_806_; lean_object* v___x_807_; lean_object* v___x_808_; double v___x_809_; lean_object* v_data_810_; 
v_result_806_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_fst_783_);
v___x_807_ = lean_box(v_result_806_);
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___x_809_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_772_);
lean_inc_ref(v___x_808_);
lean_inc(v_cls_770_);
v_data_810_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_810_, 0, v_cls_770_);
lean_ctor_set(v_data_810_, 1, v___x_808_);
lean_ctor_set(v_data_810_, 2, v_tag_772_);
lean_ctor_set_float(v_data_810_, sizeof(void*)*3, v___x_809_);
lean_ctor_set_float(v_data_810_, sizeof(void*)*3 + 8, v___x_809_);
lean_ctor_set_uint8(v_data_810_, sizeof(void*)*3 + 16, v_collapsed_771_);
if (v___x_802_ == 0)
{
lean_dec_ref_known(v___x_808_, 1);
lean_dec(v_snd_800_);
lean_dec(v_fst_799_);
lean_dec_ref(v_tag_772_);
lean_dec(v_cls_770_);
v___y_786_ = v___y_804_;
v___y_787_ = v_a_805_;
v_data_788_ = v_data_810_;
goto v___jp_785_;
}
else
{
lean_object* v_data_811_; double v___x_812_; double v___x_813_; 
lean_dec_ref_known(v_data_810_, 3);
v_data_811_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_811_, 0, v_cls_770_);
lean_ctor_set(v_data_811_, 1, v___x_808_);
lean_ctor_set(v_data_811_, 2, v_tag_772_);
v___x_812_ = lean_unbox_float(v_fst_799_);
lean_dec(v_fst_799_);
lean_ctor_set_float(v_data_811_, sizeof(void*)*3, v___x_812_);
v___x_813_ = lean_unbox_float(v_snd_800_);
lean_dec(v_snd_800_);
lean_ctor_set_float(v_data_811_, sizeof(void*)*3 + 8, v___x_813_);
lean_ctor_set_uint8(v_data_811_, sizeof(void*)*3 + 16, v_collapsed_771_);
v___y_786_ = v___y_804_;
v___y_787_ = v_a_805_;
v_data_788_ = v_data_811_;
goto v___jp_785_;
}
}
v___jp_814_:
{
lean_object* v_ref_815_; lean_object* v___x_816_; 
v_ref_815_ = lean_ctor_get(v___y_780_, 4);
lean_inc(v___y_781_);
lean_inc_ref(v___y_780_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc(v_fst_783_);
v___x_816_ = lean_apply_6(v_msg_776_, v_fst_783_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, lean_box(0));
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
v___y_804_ = v_ref_815_;
v_a_805_ = v_a_817_;
goto v___jp_803_;
}
else
{
lean_object* v___x_818_; 
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_804_ = v_ref_815_;
v_a_805_ = v___x_818_;
goto v___jp_803_;
}
}
v___jp_819_:
{
if (v_clsEnabled_774_ == 0)
{
if (v___y_820_ == 0)
{
lean_object* v___x_821_; lean_object* v_traceState_822_; lean_object* v_env_823_; lean_object* v_nextMacroScope_824_; lean_object* v_ngen_825_; lean_object* v_auxDeclNGen_826_; lean_object* v_cache_827_; lean_object* v_messages_828_; lean_object* v_infoState_829_; lean_object* v_snapshotTasks_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_snd_800_);
lean_dec(v_fst_799_);
lean_dec_ref(v_msg_776_);
lean_dec_ref(v_tag_772_);
lean_dec(v_cls_770_);
v___x_821_ = lean_st_ref_take(v___y_781_);
v_traceState_822_ = lean_ctor_get(v___x_821_, 4);
v_env_823_ = lean_ctor_get(v___x_821_, 0);
v_nextMacroScope_824_ = lean_ctor_get(v___x_821_, 1);
v_ngen_825_ = lean_ctor_get(v___x_821_, 2);
v_auxDeclNGen_826_ = lean_ctor_get(v___x_821_, 3);
v_cache_827_ = lean_ctor_get(v___x_821_, 5);
v_messages_828_ = lean_ctor_get(v___x_821_, 6);
v_infoState_829_ = lean_ctor_get(v___x_821_, 7);
v_snapshotTasks_830_ = lean_ctor_get(v___x_821_, 8);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_849_ == 0)
{
v___x_832_ = v___x_821_;
v_isShared_833_ = v_isSharedCheck_849_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_snapshotTasks_830_);
lean_inc(v_infoState_829_);
lean_inc(v_messages_828_);
lean_inc(v_cache_827_);
lean_inc(v_traceState_822_);
lean_inc(v_auxDeclNGen_826_);
lean_inc(v_ngen_825_);
lean_inc(v_nextMacroScope_824_);
lean_inc(v_env_823_);
lean_dec(v___x_821_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_849_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
uint64_t v_tid_834_; lean_object* v_traces_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_848_; 
v_tid_834_ = lean_ctor_get_uint64(v_traceState_822_, sizeof(void*)*1);
v_traces_835_ = lean_ctor_get(v_traceState_822_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v_traceState_822_);
if (v_isSharedCheck_848_ == 0)
{
v___x_837_ = v_traceState_822_;
v_isShared_838_ = v_isSharedCheck_848_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_traces_835_);
lean_dec(v_traceState_822_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_848_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_839_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_775_, v_traces_835_);
lean_dec_ref(v_traces_835_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_839_);
v___x_841_ = v___x_837_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_839_);
lean_ctor_set_uint64(v_reuseFailAlloc_847_, sizeof(void*)*1, v_tid_834_);
v___x_841_ = v_reuseFailAlloc_847_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_843_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 4, v___x_841_);
v___x_843_ = v___x_832_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_env_823_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_nextMacroScope_824_);
lean_ctor_set(v_reuseFailAlloc_846_, 2, v_ngen_825_);
lean_ctor_set(v_reuseFailAlloc_846_, 3, v_auxDeclNGen_826_);
lean_ctor_set(v_reuseFailAlloc_846_, 4, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_846_, 5, v_cache_827_);
lean_ctor_set(v_reuseFailAlloc_846_, 6, v_messages_828_);
lean_ctor_set(v_reuseFailAlloc_846_, 7, v_infoState_829_);
lean_ctor_set(v_reuseFailAlloc_846_, 8, v_snapshotTasks_830_);
v___x_843_ = v_reuseFailAlloc_846_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_st_ref_put(v___y_781_, v___x_843_);
v___x_845_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_783_);
return v___x_845_;
}
}
}
}
}
else
{
goto v___jp_814_;
}
}
else
{
goto v___jp_814_;
}
}
v___jp_850_:
{
double v___x_852_; double v___x_853_; double v___x_854_; uint8_t v___x_855_; 
v___x_852_ = lean_unbox_float(v_snd_800_);
v___x_853_ = lean_unbox_float(v_fst_799_);
v___x_854_ = lean_float_sub(v___x_852_, v___x_853_);
v___x_855_ = lean_float_decLt(v___y_851_, v___x_854_);
v___y_820_ = v___x_855_;
goto v___jp_819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_866_, lean_object* v_collapsed_867_, lean_object* v_tag_868_, lean_object* v_opts_869_, lean_object* v_clsEnabled_870_, lean_object* v_oldTraces_871_, lean_object* v_msg_872_, lean_object* v_resStartStop_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v_collapsed_boxed_879_; uint8_t v_clsEnabled_boxed_880_; lean_object* v_res_881_; 
v_collapsed_boxed_879_ = lean_unbox(v_collapsed_867_);
v_clsEnabled_boxed_880_ = lean_unbox(v_clsEnabled_870_);
v_res_881_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_866_, v_collapsed_boxed_879_, v_tag_868_, v_opts_869_, v_clsEnabled_boxed_880_, v_oldTraces_871_, v_msg_872_, v_resStartStop_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec_ref(v_opts_869_);
return v_res_881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_head_885_, lean_object* v_x_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_892_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_893_, 0, v_head_885_);
v___x_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_head_896_, lean_object* v_x_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_head_896_, v_x_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec_ref(v_x_897_);
return v_res_903_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object* v_head_907_, lean_object* v_x_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_925_; 
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v_head_907_);
v___x_915_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v___x_914_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_925_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_920_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v_a_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_921_);
v___x_923_ = v___x_918_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object* v_head_926_, lean_object* v_x_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(v_head_926_, v_x_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec_ref(v_x_927_);
return v_res_933_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_934_; double v___x_935_; 
v___x_934_ = lean_unsigned_to_nat(1000000000u);
v___x_935_ = lean_float_of_nat(v___x_934_);
return v___x_935_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_938_ = l_Lean_stringToMessageData(v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* v_tail_947_, lean_object* v_cfg_948_, lean_object* v_trace_949_, lean_object* v_next_950_, lean_object* v_goals_951_, lean_object* v_n_952_, lean_object* v_acc_953_, lean_object* v_r_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(v_tail_947_, v_cfg_948_, v_trace_949_, v_next_950_, v_goals_951_, v_n_952_, v_acc_953_, v_r_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_961_, lean_object* v_trace_962_, lean_object* v_next_963_, lean_object* v_goals_964_, lean_object* v_n_965_, lean_object* v_curr_966_, lean_object* v_acc_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
uint8_t v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; uint8_t v___y_979_; lean_object* v___y_980_; lean_object* v_a_981_; uint8_t v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; uint8_t v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v_a_998_; uint8_t v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; uint8_t v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; uint8_t v___y_1063_; lean_object* v___y_1064_; uint8_t v___y_1065_; lean_object* v_a_1066_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; uint8_t v___y_1081_; uint8_t v___y_1082_; lean_object* v_a_1083_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; uint8_t v___y_1091_; uint8_t v___y_1092_; lean_object* v_a_1093_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; uint8_t v___y_1100_; lean_object* v___y_1101_; uint8_t v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; uint8_t v___y_1112_; uint8_t v___y_1113_; lean_object* v_a_1114_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; uint8_t v___y_1132_; uint8_t v___y_1133_; lean_object* v_a_1134_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; uint8_t v___y_1142_; uint8_t v___y_1143_; lean_object* v_a_1144_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; uint8_t v___y_1152_; uint8_t v___y_1153_; lean_object* v___y_1154_; lean_object* v_zero_1157_; uint8_t v_isZero_1158_; 
v_zero_1157_ = lean_unsigned_to_nat(0u);
v_isZero_1158_ = lean_nat_dec_eq(v_n_965_, v_zero_1157_);
if (v_isZero_1158_ == 1)
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_dec(v_acc_967_);
lean_dec(v_curr_966_);
lean_dec(v_n_965_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
v___x_1159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1160_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1159_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1160_;
}
else
{
lean_object* v_proc_1161_; lean_object* v_suspend_1162_; lean_object* v_discharge_1163_; lean_object* v___f_1164_; lean_object* v___y_1166_; uint8_t v___y_1167_; lean_object* v___y_1168_; uint8_t v___y_1169_; lean_object* v___y_1170_; lean_object* v___f_1206_; lean_object* v___y_1208_; lean_object* v___y_1209_; uint8_t v___y_1210_; lean_object* v___y_1211_; uint8_t v___y_1212_; lean_object* v___y_1213_; lean_object* v_a_1214_; lean_object* v___y_1224_; lean_object* v___y_1225_; uint8_t v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1229_; lean_object* v_a_1230_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; uint8_t v___y_1247_; lean_object* v___y_1248_; uint8_t v___y_1249_; lean_object* v___f_1290_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; uint8_t v___y_1295_; lean_object* v___y_1296_; uint8_t v___y_1297_; lean_object* v_a_1298_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; uint8_t v___y_1315_; uint8_t v___y_1316_; lean_object* v_a_1317_; lean_object* v___f_1326_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; uint8_t v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; uint8_t v___y_1336_; uint8_t v___y_1337_; lean_object* v_a_1338_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; uint8_t v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; uint8_t v___y_1359_; uint8_t v___y_1360_; lean_object* v_a_1361_; lean_object* v___y_1371_; lean_object* v___y_1372_; uint8_t v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; uint8_t v___y_1377_; uint8_t v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; uint8_t v___y_1382_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; uint8_t v___y_1430_; uint8_t v___y_1431_; uint8_t v___y_1432_; lean_object* v_a_1433_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; uint8_t v___y_1453_; uint8_t v___y_1454_; uint8_t v___y_1455_; lean_object* v_a_1456_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; uint8_t v___y_1471_; uint8_t v___y_1472_; uint8_t v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; uint8_t v___y_1477_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; uint8_t v___y_1525_; uint8_t v___y_1526_; uint8_t v___y_1527_; lean_object* v_a_1528_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; uint8_t v___y_1545_; uint8_t v___y_1546_; uint8_t v___y_1547_; lean_object* v_a_1548_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; uint8_t v___y_1567_; lean_object* v___y_1568_; uint8_t v___y_1569_; uint8_t v___y_1570_; lean_object* v_a_1571_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; uint8_t v___y_1587_; lean_object* v___y_1588_; uint8_t v___y_1589_; uint8_t v___y_1590_; lean_object* v_a_1591_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; uint8_t v___y_1608_; uint8_t v___y_1609_; uint8_t v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; uint8_t v___y_1615_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; uint8_t v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; uint8_t v___y_1663_; lean_object* v___y_1664_; uint8_t v___y_1665_; lean_object* v_a_1666_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; uint8_t v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; uint8_t v___y_1686_; lean_object* v___y_1687_; uint8_t v___y_1688_; lean_object* v_a_1689_; lean_object* v___y_1699_; uint8_t v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v___y_1706_; uint8_t v___y_1707_; uint8_t v___y_1708_; lean_object* v_a_1709_; lean_object* v___y_1722_; uint8_t v___y_1723_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; uint8_t v___y_1730_; uint8_t v___y_1731_; lean_object* v_a_1732_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; uint8_t v___y_1747_; uint8_t v___y_1748_; uint8_t v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; uint8_t v___y_1753_; uint8_t v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1799_; lean_object* v_a_1800_; uint8_t v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; uint8_t v___y_1817_; lean_object* v___y_1818_; lean_object* v_a_1819_; uint8_t v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; uint8_t v___y_1835_; lean_object* v_one_1876_; lean_object* v_n_1877_; lean_object* v___y_1879_; lean_object* v___y_1880_; lean_object* v___y_1881_; uint8_t v___y_1882_; uint8_t v___y_1883_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; uint8_t v___y_1932_; uint8_t v___y_1933_; uint8_t v___y_1934_; uint8_t v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; uint8_t v___y_1964_; uint8_t v___y_1965_; lean_object* v___y_1966_; uint8_t v___y_1967_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; uint8_t v___y_2014_; lean_object* v___y_2015_; uint8_t v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; uint8_t v___y_2020_; uint8_t v___y_2021_; uint8_t v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; uint8_t v___y_2049_; uint8_t v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; uint8_t v___y_2098_; uint8_t v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; uint8_t v___y_2104_; uint8_t v___y_2105_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; uint8_t v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; uint8_t v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; uint8_t v___y_2183_; lean_object* v_a_2201_; lean_object* v___y_2295_; lean_object* v___x_2305_; 
v_proc_1161_ = lean_ctor_get(v_cfg_961_, 1);
v_suspend_1162_ = lean_ctor_get(v_cfg_961_, 2);
v_discharge_1163_ = lean_ctor_get(v_cfg_961_, 3);
v___f_1164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1876_ = lean_unsigned_to_nat(1u);
v_n_1877_ = lean_nat_sub(v_n_965_, v_one_1876_);
lean_dec(v_n_965_);
lean_inc_ref(v_proc_1161_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v_curr_966_);
lean_inc(v_goals_964_);
v___x_2305_ = lean_apply_7(v_proc_1161_, v_goals_964_, v_curr_966_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v_a_2201_ = v_a_2306_;
goto v___jp_2200_;
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
lean_object* v___f_2311_; uint8_t v___y_2313_; lean_object* v___y_2314_; uint8_t v___y_2315_; lean_object* v___y_2316_; uint8_t v___y_2353_; uint8_t v___x_2373_; 
lean_inc(v_a_2307_);
v___f_2311_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
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
v___x_2317_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
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
v___x_2323_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2316_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2324_ = lean_io_mono_nanos_now();
v___x_2325_ = lean_io_mono_nanos_now();
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v_a_2307_);
v___x_2327_ = v___x_2320_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2307_);
v___x_2327_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
double v___x_2328_; double v___x_2329_; double v___x_2330_; double v___x_2331_; double v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2328_ = lean_float_of_nat(v___x_2324_);
v___x_2329_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2330_ = lean_float_div(v___x_2328_, v___x_2329_);
v___x_2331_ = lean_float_of_nat(v___x_2325_);
v___x_2332_ = lean_float_div(v___x_2331_, v___x_2329_);
v___x_2333_ = lean_box_float(v___x_2330_);
v___x_2334_ = lean_box_float(v___x_2332_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2327_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
lean_inc_ref(v___y_2314_);
lean_inc(v_trace_962_);
v___x_2337_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_962_, v___y_2315_, v___y_2314_, v___y_2316_, v___y_2313_, v_a_2318_, v___f_2311_, v___x_2336_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_2295_ = v___x_2337_;
goto v___jp_2294_;
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2339_ = lean_io_get_num_heartbeats();
v___x_2340_ = lean_io_get_num_heartbeats();
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v_a_2307_);
v___x_2342_ = v___x_2320_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2307_);
v___x_2342_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
double v___x_2343_; double v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2343_ = lean_float_of_nat(v___x_2339_);
v___x_2344_ = lean_float_of_nat(v___x_2340_);
v___x_2345_ = lean_box_float(v___x_2343_);
v___x_2346_ = lean_box_float(v___x_2344_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2342_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
lean_inc_ref(v___y_2314_);
lean_inc(v_trace_962_);
v___x_2349_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_962_, v___y_2315_, v___y_2314_, v___y_2316_, v___y_2313_, v_a_2318_, v___f_2311_, v___x_2348_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
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
lean_object* v_options_2354_; uint8_t v_hasTrace_2355_; 
v_options_2354_ = lean_ctor_get(v_a_970_, 1);
v_hasTrace_2355_ = lean_ctor_get_uint8(v_options_2354_, sizeof(void*)*1);
if (v_hasTrace_2355_ == 0)
{
lean_object* v___x_2357_; 
lean_dec_ref(v___f_2311_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_curr_966_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
if (v_isShared_2310_ == 0)
{
v___x_2357_ = v___x_2309_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2307_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
else
{
lean_object* v_toCold_2359_; lean_object* v_inheritedTraceOptions_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v_toCold_2359_ = lean_ctor_get(v_a_970_, 0);
v_inheritedTraceOptions_2360_ = lean_ctor_get(v_toCold_2359_, 4);
v___x_2361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_962_);
v___x_2363_ = l_Lean_Name_append(v___x_2362_, v_trace_962_);
v___x_2364_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2360_, v_options_2354_, v___x_2363_);
lean_dec(v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; uint8_t v___x_2366_; 
v___x_2365_ = l_Lean_trace_profiler;
v___x_2366_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2354_, v___x_2365_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2368_; 
lean_dec_ref(v___f_2311_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_curr_966_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
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
v___y_2314_ = v___x_2361_;
v___y_2315_ = v_hasTrace_2355_;
v___y_2316_ = v_options_2354_;
goto v___jp_2312_;
}
}
else
{
lean_del_object(v___x_2309_);
v___y_2313_ = v___x_2364_;
v___y_2314_ = v___x_2361_;
v___y_2315_ = v_hasTrace_2355_;
v___y_2316_ = v_options_2354_;
goto v___jp_2312_;
}
}
}
else
{
lean_object* v___x_2371_; 
lean_dec_ref(v___f_2311_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_curr_966_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
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
v___jp_1165_:
{
lean_object* v___x_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1205_; 
v___x_1171_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1205_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1205_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1177_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1170_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1178_ = lean_io_mono_nanos_now();
v___x_1179_ = lean_io_mono_nanos_now();
if (v_isShared_1175_ == 0)
{
lean_ctor_set_tag(v___x_1174_, 1);
lean_ctor_set(v___x_1174_, 0, v___y_1166_);
v___x_1181_ = v___x_1174_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___y_1166_);
v___x_1181_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
double v___x_1182_; double v___x_1183_; double v___x_1184_; double v___x_1185_; double v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1182_ = lean_float_of_nat(v___x_1178_);
v___x_1183_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1184_ = lean_float_div(v___x_1182_, v___x_1183_);
v___x_1185_ = lean_float_of_nat(v___x_1179_);
v___x_1186_ = lean_float_div(v___x_1185_, v___x_1183_);
v___x_1187_ = lean_box_float(v___x_1184_);
v___x_1188_ = lean_box_float(v___x_1186_);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1181_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
lean_inc_ref(v___y_1168_);
v___x_1191_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1167_, v___y_1168_, v___y_1170_, v___y_1169_, v_a_1172_, v___f_1164_, v___x_1190_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1191_;
}
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1193_ = lean_io_get_num_heartbeats();
v___x_1194_ = lean_io_get_num_heartbeats();
if (v_isShared_1175_ == 0)
{
lean_ctor_set_tag(v___x_1174_, 1);
lean_ctor_set(v___x_1174_, 0, v___y_1166_);
v___x_1196_ = v___x_1174_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___y_1166_);
v___x_1196_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
double v___x_1197_; double v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1197_ = lean_float_of_nat(v___x_1193_);
v___x_1198_ = lean_float_of_nat(v___x_1194_);
v___x_1199_ = lean_box_float(v___x_1197_);
v___x_1200_ = lean_box_float(v___x_1198_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1196_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
lean_inc_ref(v___y_1168_);
v___x_1203_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1167_, v___y_1168_, v___y_1170_, v___y_1169_, v_a_1172_, v___f_1164_, v___x_1202_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1203_;
}
}
}
}
v___jp_1207_:
{
lean_object* v___x_1215_; double v___x_1216_; double v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1215_ = lean_io_get_num_heartbeats();
v___x_1216_ = lean_float_of_nat(v___y_1213_);
v___x_1217_ = lean_float_of_nat(v___x_1215_);
v___x_1218_ = lean_box_float(v___x_1216_);
v___x_1219_ = lean_box_float(v___x_1217_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v_a_1214_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
lean_inc_ref(v___y_1209_);
v___x_1222_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1212_, v___y_1209_, v___y_1211_, v___y_1210_, v___y_1208_, v___f_1206_, v___x_1221_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1222_;
}
v___jp_1223_:
{
lean_object* v___x_1231_; double v___x_1232_; double v___x_1233_; double v___x_1234_; double v___x_1235_; double v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1231_ = lean_io_mono_nanos_now();
v___x_1232_ = lean_float_of_nat(v___y_1228_);
v___x_1233_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1234_ = lean_float_div(v___x_1232_, v___x_1233_);
v___x_1235_ = lean_float_of_nat(v___x_1231_);
v___x_1236_ = lean_float_div(v___x_1235_, v___x_1233_);
v___x_1237_ = lean_box_float(v___x_1234_);
v___x_1238_ = lean_box_float(v___x_1236_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_a_1230_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
lean_inc_ref(v___y_1225_);
v___x_1241_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1229_, v___y_1225_, v___y_1227_, v___y_1226_, v___y_1224_, v___f_1206_, v___x_1240_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1241_;
}
v___jp_1242_:
{
lean_object* v___x_1250_; lean_object* v_a_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1250_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v___x_1250_);
v___x_1252_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1253_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1248_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_io_mono_nanos_now();
lean_inc(v_trace_962_);
v___x_1255_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1244_, v___y_1246_, v___y_1243_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1255_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set_tag(v___x_1258_, 1);
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
v___y_1224_ = v_a_1251_;
v___y_1225_ = v___y_1245_;
v___y_1226_ = v___y_1247_;
v___y_1227_ = v___y_1248_;
v___y_1228_ = v___x_1254_;
v___y_1229_ = v___y_1249_;
v_a_1230_ = v___x_1261_;
goto v___jp_1223_;
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
v_a_1264_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1255_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1255_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set_tag(v___x_1266_, 0);
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
v___y_1224_ = v_a_1251_;
v___y_1225_ = v___y_1245_;
v___y_1226_ = v___y_1247_;
v___y_1227_ = v___y_1248_;
v___y_1228_ = v___x_1254_;
v___y_1229_ = v___y_1249_;
v_a_1230_ = v___x_1269_;
goto v___jp_1223_;
}
}
}
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_962_);
v___x_1273_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1244_, v___y_1246_, v___y_1243_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 1);
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
v___y_1208_ = v_a_1251_;
v___y_1209_ = v___y_1245_;
v___y_1210_ = v___y_1247_;
v___y_1211_ = v___y_1248_;
v___y_1212_ = v___y_1249_;
v___y_1213_ = v___x_1272_;
v_a_1214_ = v___x_1279_;
goto v___jp_1207_;
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1282_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1273_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1273_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set_tag(v___x_1284_, 0);
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
v___y_1208_ = v_a_1251_;
v___y_1209_ = v___y_1245_;
v___y_1210_ = v___y_1247_;
v___y_1211_ = v___y_1248_;
v___y_1212_ = v___y_1249_;
v___y_1213_ = v___x_1272_;
v_a_1214_ = v___x_1287_;
goto v___jp_1207_;
}
}
}
}
}
v___jp_1291_:
{
lean_object* v___x_1299_; double v___x_1300_; double v___x_1301_; double v___x_1302_; double v___x_1303_; double v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1299_ = lean_io_mono_nanos_now();
v___x_1300_ = lean_float_of_nat(v___y_1296_);
v___x_1301_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1302_ = lean_float_div(v___x_1300_, v___x_1301_);
v___x_1303_ = lean_float_of_nat(v___x_1299_);
v___x_1304_ = lean_float_div(v___x_1303_, v___x_1301_);
v___x_1305_ = lean_box_float(v___x_1302_);
v___x_1306_ = lean_box_float(v___x_1304_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1305_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_a_1298_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
lean_inc_ref(v___y_1292_);
v___x_1309_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1295_, v___y_1292_, v___y_1293_, v___y_1297_, v___y_1294_, v___f_1290_, v___x_1308_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1309_;
}
v___jp_1310_:
{
lean_object* v___x_1318_; double v___x_1319_; double v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1318_ = lean_io_get_num_heartbeats();
v___x_1319_ = lean_float_of_nat(v___y_1314_);
v___x_1320_ = lean_float_of_nat(v___x_1318_);
v___x_1321_ = lean_box_float(v___x_1319_);
v___x_1322_ = lean_box_float(v___x_1320_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_a_1317_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
lean_inc_ref(v___y_1311_);
v___x_1325_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1315_, v___y_1311_, v___y_1312_, v___y_1316_, v___y_1313_, v___f_1290_, v___x_1324_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1325_;
}
v___jp_1327_:
{
lean_object* v___x_1339_; double v___x_1340_; double v___x_1341_; double v___x_1342_; double v___x_1343_; double v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1339_ = lean_io_mono_nanos_now();
v___x_1340_ = lean_float_of_nat(v___y_1333_);
v___x_1341_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1342_ = lean_float_div(v___x_1340_, v___x_1341_);
v___x_1343_ = lean_float_of_nat(v___x_1339_);
v___x_1344_ = lean_float_div(v___x_1343_, v___x_1341_);
v___x_1345_ = lean_box_float(v___x_1342_);
v___x_1346_ = lean_box_float(v___x_1344_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v_a_1338_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
lean_inc_ref(v___y_1329_);
lean_inc(v_trace_962_);
v___x_1349_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1337_, v___y_1329_, v___y_1332_, v___y_1331_, v___y_1334_, v___f_1326_, v___x_1348_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1096_ = v___y_1328_;
v___y_1097_ = v___y_1329_;
v___y_1098_ = v___y_1330_;
v___y_1099_ = v___y_1332_;
v___y_1100_ = v___y_1336_;
v___y_1101_ = v___y_1335_;
v___y_1102_ = v___y_1337_;
v___y_1103_ = v___x_1349_;
goto v___jp_1095_;
}
v___jp_1350_:
{
lean_object* v___x_1362_; double v___x_1363_; double v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1362_ = lean_io_get_num_heartbeats();
v___x_1363_ = lean_float_of_nat(v___y_1353_);
v___x_1364_ = lean_float_of_nat(v___x_1362_);
v___x_1365_ = lean_box_float(v___x_1363_);
v___x_1366_ = lean_box_float(v___x_1364_);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v_a_1361_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
lean_inc_ref(v___y_1352_);
lean_inc(v_trace_962_);
v___x_1369_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1360_, v___y_1352_, v___y_1356_, v___y_1355_, v___y_1357_, v___f_1326_, v___x_1368_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1096_ = v___y_1351_;
v___y_1097_ = v___y_1352_;
v___y_1098_ = v___y_1354_;
v___y_1099_ = v___y_1356_;
v___y_1100_ = v___y_1359_;
v___y_1101_ = v___y_1358_;
v___y_1102_ = v___y_1360_;
v___y_1103_ = v___x_1369_;
goto v___jp_1095_;
}
v___jp_1370_:
{
lean_object* v___x_1383_; 
v___x_1383_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
if (v___y_1378_ == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1383_);
v___x_1385_ = lean_io_mono_nanos_now();
lean_inc(v_trace_962_);
v___x_1386_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1375_, v___y_1374_, v___y_1381_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 1);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
v___y_1328_ = v___y_1379_;
v___y_1329_ = v___y_1371_;
v___y_1330_ = v___y_1372_;
v___y_1331_ = v___y_1373_;
v___y_1332_ = v___y_1380_;
v___y_1333_ = v___x_1385_;
v___y_1334_ = v_a_1384_;
v___y_1335_ = v___y_1376_;
v___y_1336_ = v___y_1377_;
v___y_1337_ = v___y_1382_;
v_a_1338_ = v___x_1392_;
goto v___jp_1327_;
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
v_a_1395_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1386_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1386_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
lean_ctor_set_tag(v___x_1397_, 0);
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
v___y_1328_ = v___y_1379_;
v___y_1329_ = v___y_1371_;
v___y_1330_ = v___y_1372_;
v___y_1331_ = v___y_1373_;
v___y_1332_ = v___y_1380_;
v___y_1333_ = v___x_1385_;
v___y_1334_ = v_a_1384_;
v___y_1335_ = v___y_1376_;
v___y_1336_ = v___y_1377_;
v___y_1337_ = v___y_1382_;
v_a_1338_ = v___x_1400_;
goto v___jp_1327_;
}
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v_a_1403_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1403_);
lean_dec_ref(v___x_1383_);
v___x_1404_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_962_);
v___x_1405_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1375_, v___y_1374_, v___y_1381_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set_tag(v___x_1408_, 1);
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1371_;
v___y_1353_ = v___x_1404_;
v___y_1354_ = v___y_1372_;
v___y_1355_ = v___y_1373_;
v___y_1356_ = v___y_1380_;
v___y_1357_ = v_a_1403_;
v___y_1358_ = v___y_1376_;
v___y_1359_ = v___y_1377_;
v___y_1360_ = v___y_1382_;
v_a_1361_ = v___x_1411_;
goto v___jp_1350_;
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_a_1414_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1405_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1405_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 0);
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
v___y_1351_ = v___y_1379_;
v___y_1352_ = v___y_1371_;
v___y_1353_ = v___x_1404_;
v___y_1354_ = v___y_1372_;
v___y_1355_ = v___y_1373_;
v___y_1356_ = v___y_1380_;
v___y_1357_ = v_a_1403_;
v___y_1358_ = v___y_1376_;
v___y_1359_ = v___y_1377_;
v___y_1360_ = v___y_1382_;
v_a_1361_ = v___x_1419_;
goto v___jp_1350_;
}
}
}
}
}
v___jp_1422_:
{
lean_object* v___x_1434_; double v___x_1435_; double v___x_1436_; double v___x_1437_; double v___x_1438_; double v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1434_ = lean_io_mono_nanos_now();
v___x_1435_ = lean_float_of_nat(v___y_1426_);
v___x_1436_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1437_ = lean_float_div(v___x_1435_, v___x_1436_);
v___x_1438_ = lean_float_of_nat(v___x_1434_);
v___x_1439_ = lean_float_div(v___x_1438_, v___x_1436_);
v___x_1440_ = lean_box_float(v___x_1437_);
v___x_1441_ = lean_box_float(v___x_1439_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1440_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v_a_1433_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
lean_inc_ref(v___y_1425_);
lean_inc(v_trace_962_);
v___x_1444_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1432_, v___y_1425_, v___y_1429_, v___y_1430_, v___y_1424_, v___f_1206_, v___x_1443_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1147_ = v___y_1423_;
v___y_1148_ = v___y_1425_;
v___y_1149_ = v___y_1428_;
v___y_1150_ = v___y_1427_;
v___y_1151_ = v___y_1429_;
v___y_1152_ = v___y_1431_;
v___y_1153_ = v___y_1432_;
v___y_1154_ = v___x_1444_;
goto v___jp_1146_;
}
v___jp_1445_:
{
lean_object* v___x_1457_; double v___x_1458_; double v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1457_ = lean_io_get_num_heartbeats();
v___x_1458_ = lean_float_of_nat(v___y_1452_);
v___x_1459_ = lean_float_of_nat(v___x_1457_);
v___x_1460_ = lean_box_float(v___x_1458_);
v___x_1461_ = lean_box_float(v___x_1459_);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_a_1456_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
lean_inc_ref(v___y_1448_);
lean_inc(v_trace_962_);
v___x_1464_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1455_, v___y_1448_, v___y_1451_, v___y_1453_, v___y_1447_, v___f_1206_, v___x_1463_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1147_ = v___y_1446_;
v___y_1148_ = v___y_1448_;
v___y_1149_ = v___y_1450_;
v___y_1150_ = v___y_1449_;
v___y_1151_ = v___y_1451_;
v___y_1152_ = v___y_1454_;
v___y_1153_ = v___y_1455_;
v___y_1154_ = v___x_1464_;
goto v___jp_1146_;
}
v___jp_1465_:
{
lean_object* v___x_1478_; 
v___x_1478_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
if (v___y_1473_ == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1478_);
v___x_1480_ = lean_io_mono_nanos_now();
lean_inc(v_trace_962_);
v___x_1481_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1469_, v___y_1470_, v___y_1468_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set_tag(v___x_1484_, 1);
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
v___y_1423_ = v___y_1474_;
v___y_1424_ = v_a_1479_;
v___y_1425_ = v___y_1466_;
v___y_1426_ = v___x_1480_;
v___y_1427_ = v___y_1475_;
v___y_1428_ = v___y_1467_;
v___y_1429_ = v___y_1476_;
v___y_1430_ = v___y_1471_;
v___y_1431_ = v___y_1472_;
v___y_1432_ = v___y_1477_;
v_a_1433_ = v___x_1487_;
goto v___jp_1422_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
v_a_1490_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1481_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1481_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 0);
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
v___y_1423_ = v___y_1474_;
v___y_1424_ = v_a_1479_;
v___y_1425_ = v___y_1466_;
v___y_1426_ = v___x_1480_;
v___y_1427_ = v___y_1475_;
v___y_1428_ = v___y_1467_;
v___y_1429_ = v___y_1476_;
v___y_1430_ = v___y_1471_;
v___y_1431_ = v___y_1472_;
v___y_1432_ = v___y_1477_;
v_a_1433_ = v___x_1495_;
goto v___jp_1422_;
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_a_1498_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1498_);
lean_dec_ref(v___x_1478_);
v___x_1499_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_962_);
v___x_1500_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1469_, v___y_1470_, v___y_1468_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1500_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1500_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
lean_ctor_set_tag(v___x_1503_, 1);
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
v___y_1446_ = v___y_1474_;
v___y_1447_ = v_a_1498_;
v___y_1448_ = v___y_1466_;
v___y_1449_ = v___y_1475_;
v___y_1450_ = v___y_1467_;
v___y_1451_ = v___y_1476_;
v___y_1452_ = v___x_1499_;
v___y_1453_ = v___y_1471_;
v___y_1454_ = v___y_1472_;
v___y_1455_ = v___y_1477_;
v_a_1456_ = v___x_1506_;
goto v___jp_1445_;
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
v_a_1509_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1500_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1500_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set_tag(v___x_1511_, 0);
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
v___y_1446_ = v___y_1474_;
v___y_1447_ = v_a_1498_;
v___y_1448_ = v___y_1466_;
v___y_1449_ = v___y_1475_;
v___y_1450_ = v___y_1467_;
v___y_1451_ = v___y_1476_;
v___y_1452_ = v___x_1499_;
v___y_1453_ = v___y_1471_;
v___y_1454_ = v___y_1472_;
v___y_1455_ = v___y_1477_;
v_a_1456_ = v___x_1514_;
goto v___jp_1445_;
}
}
}
}
}
v___jp_1517_:
{
lean_object* v___x_1529_; double v___x_1530_; double v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1529_ = lean_io_get_num_heartbeats();
v___x_1530_ = lean_float_of_nat(v___y_1522_);
v___x_1531_ = lean_float_of_nat(v___x_1529_);
v___x_1532_ = lean_box_float(v___x_1530_);
v___x_1533_ = lean_box_float(v___x_1531_);
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1532_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1528_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
lean_inc_ref(v___y_1519_);
lean_inc(v_trace_962_);
v___x_1536_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1527_, v___y_1519_, v___y_1523_, v___y_1525_, v___y_1524_, v___f_1290_, v___x_1535_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1147_ = v___y_1518_;
v___y_1148_ = v___y_1519_;
v___y_1149_ = v___y_1521_;
v___y_1150_ = v___y_1520_;
v___y_1151_ = v___y_1523_;
v___y_1152_ = v___y_1526_;
v___y_1153_ = v___y_1527_;
v___y_1154_ = v___x_1536_;
goto v___jp_1146_;
}
v___jp_1537_:
{
lean_object* v___x_1549_; double v___x_1550_; double v___x_1551_; double v___x_1552_; double v___x_1553_; double v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1549_ = lean_io_mono_nanos_now();
v___x_1550_ = lean_float_of_nat(v___y_1544_);
v___x_1551_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1552_ = lean_float_div(v___x_1550_, v___x_1551_);
v___x_1553_ = lean_float_of_nat(v___x_1549_);
v___x_1554_ = lean_float_div(v___x_1553_, v___x_1551_);
v___x_1555_ = lean_box_float(v___x_1552_);
v___x_1556_ = lean_box_float(v___x_1554_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_a_1548_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
lean_inc_ref(v___y_1539_);
lean_inc(v_trace_962_);
v___x_1559_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1547_, v___y_1539_, v___y_1542_, v___y_1545_, v___y_1543_, v___f_1290_, v___x_1558_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1147_ = v___y_1538_;
v___y_1148_ = v___y_1539_;
v___y_1149_ = v___y_1541_;
v___y_1150_ = v___y_1540_;
v___y_1151_ = v___y_1542_;
v___y_1152_ = v___y_1546_;
v___y_1153_ = v___y_1547_;
v___y_1154_ = v___x_1559_;
goto v___jp_1146_;
}
v___jp_1560_:
{
lean_object* v___x_1572_; double v___x_1573_; double v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1572_ = lean_io_get_num_heartbeats();
v___x_1573_ = lean_float_of_nat(v___y_1561_);
v___x_1574_ = lean_float_of_nat(v___x_1572_);
v___x_1575_ = lean_box_float(v___x_1573_);
v___x_1576_ = lean_box_float(v___x_1574_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v_a_1571_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
lean_inc_ref(v___y_1563_);
lean_inc(v_trace_962_);
v___x_1579_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1570_, v___y_1563_, v___y_1566_, v___y_1569_, v___y_1568_, v___f_1326_, v___x_1578_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1147_ = v___y_1562_;
v___y_1148_ = v___y_1563_;
v___y_1149_ = v___y_1565_;
v___y_1150_ = v___y_1564_;
v___y_1151_ = v___y_1566_;
v___y_1152_ = v___y_1567_;
v___y_1153_ = v___y_1570_;
v___y_1154_ = v___x_1579_;
goto v___jp_1146_;
}
v___jp_1580_:
{
lean_object* v___x_1592_; double v___x_1593_; double v___x_1594_; double v___x_1595_; double v___x_1596_; double v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1592_ = lean_io_mono_nanos_now();
v___x_1593_ = lean_float_of_nat(v___y_1586_);
v___x_1594_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1595_ = lean_float_div(v___x_1593_, v___x_1594_);
v___x_1596_ = lean_float_of_nat(v___x_1592_);
v___x_1597_ = lean_float_div(v___x_1596_, v___x_1594_);
v___x_1598_ = lean_box_float(v___x_1595_);
v___x_1599_ = lean_box_float(v___x_1597_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v_a_1591_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
lean_inc_ref(v___y_1582_);
lean_inc(v_trace_962_);
v___x_1602_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1590_, v___y_1582_, v___y_1585_, v___y_1589_, v___y_1588_, v___f_1326_, v___x_1601_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1147_ = v___y_1581_;
v___y_1148_ = v___y_1582_;
v___y_1149_ = v___y_1584_;
v___y_1150_ = v___y_1583_;
v___y_1151_ = v___y_1585_;
v___y_1152_ = v___y_1587_;
v___y_1153_ = v___y_1590_;
v___y_1154_ = v___x_1602_;
goto v___jp_1146_;
}
v___jp_1603_:
{
lean_object* v___x_1616_; 
v___x_1616_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
if (v___y_1610_ == 0)
{
lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = lean_io_mono_nanos_now();
lean_inc(v_trace_962_);
v___x_1619_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1612_, v___y_1606_, v___y_1607_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 1);
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
v___y_1581_ = v___y_1611_;
v___y_1582_ = v___y_1604_;
v___y_1583_ = v___y_1613_;
v___y_1584_ = v___y_1605_;
v___y_1585_ = v___y_1614_;
v___y_1586_ = v___x_1618_;
v___y_1587_ = v___y_1608_;
v___y_1588_ = v_a_1617_;
v___y_1589_ = v___y_1609_;
v___y_1590_ = v___y_1615_;
v_a_1591_ = v___x_1625_;
goto v___jp_1580_;
}
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_a_1628_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1619_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1619_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set_tag(v___x_1630_, 0);
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
v___y_1581_ = v___y_1611_;
v___y_1582_ = v___y_1604_;
v___y_1583_ = v___y_1613_;
v___y_1584_ = v___y_1605_;
v___y_1585_ = v___y_1614_;
v___y_1586_ = v___x_1618_;
v___y_1587_ = v___y_1608_;
v___y_1588_ = v_a_1617_;
v___y_1589_ = v___y_1609_;
v___y_1590_ = v___y_1615_;
v_a_1591_ = v___x_1633_;
goto v___jp_1580_;
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_a_1636_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1636_);
lean_dec_ref(v___x_1616_);
v___x_1637_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_962_);
v___x_1638_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1612_, v___y_1606_, v___y_1607_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 1);
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
v___y_1561_ = v___x_1637_;
v___y_1562_ = v___y_1611_;
v___y_1563_ = v___y_1604_;
v___y_1564_ = v___y_1613_;
v___y_1565_ = v___y_1605_;
v___y_1566_ = v___y_1614_;
v___y_1567_ = v___y_1608_;
v___y_1568_ = v_a_1636_;
v___y_1569_ = v___y_1609_;
v___y_1570_ = v___y_1615_;
v_a_1571_ = v___x_1644_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
v_a_1647_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1638_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1638_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set_tag(v___x_1649_, 0);
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
v___y_1561_ = v___x_1637_;
v___y_1562_ = v___y_1611_;
v___y_1563_ = v___y_1604_;
v___y_1564_ = v___y_1613_;
v___y_1565_ = v___y_1605_;
v___y_1566_ = v___y_1614_;
v___y_1567_ = v___y_1608_;
v___y_1568_ = v_a_1636_;
v___y_1569_ = v___y_1609_;
v___y_1570_ = v___y_1615_;
v_a_1571_ = v___x_1652_;
goto v___jp_1560_;
}
}
}
}
}
v___jp_1655_:
{
lean_object* v___x_1667_; double v___x_1668_; double v___x_1669_; double v___x_1670_; double v___x_1671_; double v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1667_ = lean_io_mono_nanos_now();
v___x_1668_ = lean_float_of_nat(v___y_1664_);
v___x_1669_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1670_ = lean_float_div(v___x_1668_, v___x_1669_);
v___x_1671_ = lean_float_of_nat(v___x_1667_);
v___x_1672_ = lean_float_div(v___x_1671_, v___x_1669_);
v___x_1673_ = lean_box_float(v___x_1670_);
v___x_1674_ = lean_box_float(v___x_1672_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v_a_1666_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
lean_inc_ref(v___y_1657_);
lean_inc(v_trace_962_);
v___x_1677_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1665_, v___y_1657_, v___y_1659_, v___y_1660_, v___y_1661_, v___f_1290_, v___x_1676_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1096_ = v___y_1656_;
v___y_1097_ = v___y_1657_;
v___y_1098_ = v___y_1658_;
v___y_1099_ = v___y_1659_;
v___y_1100_ = v___y_1663_;
v___y_1101_ = v___y_1662_;
v___y_1102_ = v___y_1665_;
v___y_1103_ = v___x_1677_;
goto v___jp_1095_;
}
v___jp_1678_:
{
lean_object* v___x_1690_; double v___x_1691_; double v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1690_ = lean_io_get_num_heartbeats();
v___x_1691_ = lean_float_of_nat(v___y_1687_);
v___x_1692_ = lean_float_of_nat(v___x_1690_);
v___x_1693_ = lean_box_float(v___x_1691_);
v___x_1694_ = lean_box_float(v___x_1692_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v_a_1689_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
lean_inc_ref(v___y_1680_);
lean_inc(v_trace_962_);
v___x_1697_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1688_, v___y_1680_, v___y_1682_, v___y_1683_, v___y_1684_, v___f_1290_, v___x_1696_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1096_ = v___y_1679_;
v___y_1097_ = v___y_1680_;
v___y_1098_ = v___y_1681_;
v___y_1099_ = v___y_1682_;
v___y_1100_ = v___y_1686_;
v___y_1101_ = v___y_1685_;
v___y_1102_ = v___y_1688_;
v___y_1103_ = v___x_1697_;
goto v___jp_1095_;
}
v___jp_1698_:
{
lean_object* v___x_1710_; double v___x_1711_; double v___x_1712_; double v___x_1713_; double v___x_1714_; double v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1710_ = lean_io_mono_nanos_now();
v___x_1711_ = lean_float_of_nat(v___y_1701_);
v___x_1712_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1713_ = lean_float_div(v___x_1711_, v___x_1712_);
v___x_1714_ = lean_float_of_nat(v___x_1710_);
v___x_1715_ = lean_float_div(v___x_1714_, v___x_1712_);
v___x_1716_ = lean_box_float(v___x_1713_);
v___x_1717_ = lean_box_float(v___x_1715_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1716_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v_a_1709_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
lean_inc_ref(v___y_1703_);
lean_inc(v_trace_962_);
v___x_1720_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1708_, v___y_1703_, v___y_1705_, v___y_1700_, v___y_1699_, v___f_1206_, v___x_1719_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1096_ = v___y_1702_;
v___y_1097_ = v___y_1703_;
v___y_1098_ = v___y_1704_;
v___y_1099_ = v___y_1705_;
v___y_1100_ = v___y_1707_;
v___y_1101_ = v___y_1706_;
v___y_1102_ = v___y_1708_;
v___y_1103_ = v___x_1720_;
goto v___jp_1095_;
}
v___jp_1721_:
{
lean_object* v___x_1733_; double v___x_1734_; double v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1733_ = lean_io_get_num_heartbeats();
v___x_1734_ = lean_float_of_nat(v___y_1728_);
v___x_1735_ = lean_float_of_nat(v___x_1733_);
v___x_1736_ = lean_box_float(v___x_1734_);
v___x_1737_ = lean_box_float(v___x_1735_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v_a_1732_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
lean_inc_ref(v___y_1725_);
lean_inc(v_trace_962_);
v___x_1740_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1731_, v___y_1725_, v___y_1727_, v___y_1723_, v___y_1722_, v___f_1206_, v___x_1739_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1096_ = v___y_1724_;
v___y_1097_ = v___y_1725_;
v___y_1098_ = v___y_1726_;
v___y_1099_ = v___y_1727_;
v___y_1100_ = v___y_1730_;
v___y_1101_ = v___y_1729_;
v___y_1102_ = v___y_1731_;
v___y_1103_ = v___x_1740_;
goto v___jp_1095_;
}
v___jp_1741_:
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
if (v___y_1748_ == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = lean_io_mono_nanos_now();
lean_inc(v_trace_962_);
v___x_1757_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1751_, v___y_1744_, v___y_1745_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 1);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
v___y_1699_ = v_a_1755_;
v___y_1700_ = v___y_1749_;
v___y_1701_ = v___x_1756_;
v___y_1702_ = v___y_1750_;
v___y_1703_ = v___y_1742_;
v___y_1704_ = v___y_1743_;
v___y_1705_ = v___y_1752_;
v___y_1706_ = v___y_1746_;
v___y_1707_ = v___y_1747_;
v___y_1708_ = v___y_1753_;
v_a_1709_ = v___x_1763_;
goto v___jp_1698_;
}
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
v_a_1766_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1757_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1757_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set_tag(v___x_1768_, 0);
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
v___y_1699_ = v_a_1755_;
v___y_1700_ = v___y_1749_;
v___y_1701_ = v___x_1756_;
v___y_1702_ = v___y_1750_;
v___y_1703_ = v___y_1742_;
v___y_1704_ = v___y_1743_;
v___y_1705_ = v___y_1752_;
v___y_1706_ = v___y_1746_;
v___y_1707_ = v___y_1747_;
v___y_1708_ = v___y_1753_;
v_a_1709_ = v___x_1771_;
goto v___jp_1698_;
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_a_1774_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___x_1754_);
v___x_1775_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_962_);
v___x_1776_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1751_, v___y_1744_, v___y_1745_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set_tag(v___x_1779_, 1);
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
v___y_1722_ = v_a_1774_;
v___y_1723_ = v___y_1749_;
v___y_1724_ = v___y_1750_;
v___y_1725_ = v___y_1742_;
v___y_1726_ = v___y_1743_;
v___y_1727_ = v___y_1752_;
v___y_1728_ = v___x_1775_;
v___y_1729_ = v___y_1746_;
v___y_1730_ = v___y_1747_;
v___y_1731_ = v___y_1753_;
v_a_1732_ = v___x_1782_;
goto v___jp_1721_;
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
v_a_1785_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1776_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1776_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
lean_ctor_set_tag(v___x_1787_, 0);
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
v___y_1722_ = v_a_1774_;
v___y_1723_ = v___y_1749_;
v___y_1724_ = v___y_1750_;
v___y_1725_ = v___y_1742_;
v___y_1726_ = v___y_1743_;
v___y_1727_ = v___y_1752_;
v___y_1728_ = v___x_1775_;
v___y_1729_ = v___y_1746_;
v___y_1730_ = v___y_1747_;
v___y_1731_ = v___y_1753_;
v_a_1732_ = v___x_1790_;
goto v___jp_1721_;
}
}
}
}
}
v___jp_1793_:
{
lean_object* v___x_1801_; double v___x_1802_; double v___x_1803_; double v___x_1804_; double v___x_1805_; double v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1801_ = lean_io_mono_nanos_now();
v___x_1802_ = lean_float_of_nat(v___y_1799_);
v___x_1803_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1804_ = lean_float_div(v___x_1802_, v___x_1803_);
v___x_1805_ = lean_float_of_nat(v___x_1801_);
v___x_1806_ = lean_float_div(v___x_1805_, v___x_1803_);
v___x_1807_ = lean_box_float(v___x_1804_);
v___x_1808_ = lean_box_float(v___x_1806_);
v___x_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v_a_1800_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
lean_inc_ref(v___y_1795_);
v___x_1811_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1798_, v___y_1795_, v___y_1797_, v___y_1794_, v___y_1796_, v___f_1326_, v___x_1810_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1811_;
}
v___jp_1812_:
{
lean_object* v___x_1820_; double v___x_1821_; double v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1820_ = lean_io_get_num_heartbeats();
v___x_1821_ = lean_float_of_nat(v___y_1818_);
v___x_1822_ = lean_float_of_nat(v___x_1820_);
v___x_1823_ = lean_box_float(v___x_1821_);
v___x_1824_ = lean_box_float(v___x_1822_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v_a_1819_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
lean_inc_ref(v___y_1814_);
v___x_1827_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1817_, v___y_1814_, v___y_1816_, v___y_1813_, v___y_1815_, v___f_1326_, v___x_1826_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1827_;
}
v___jp_1828_:
{
lean_object* v___x_1836_; lean_object* v_a_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1836_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1839_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1833_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_io_mono_nanos_now();
lean_inc(v_trace_962_);
v___x_1841_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1834_, v___y_1832_, v___y_1831_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set_tag(v___x_1844_, 1);
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
v___y_1794_ = v___y_1829_;
v___y_1795_ = v___y_1830_;
v___y_1796_ = v_a_1837_;
v___y_1797_ = v___y_1833_;
v___y_1798_ = v___y_1835_;
v___y_1799_ = v___x_1840_;
v_a_1800_ = v___x_1847_;
goto v___jp_1793_;
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1841_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1841_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 0);
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
v___y_1794_ = v___y_1829_;
v___y_1795_ = v___y_1830_;
v___y_1796_ = v_a_1837_;
v___y_1797_ = v___y_1833_;
v___y_1798_ = v___y_1835_;
v___y_1799_ = v___x_1840_;
v_a_1800_ = v___x_1855_;
goto v___jp_1793_;
}
}
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_962_);
v___x_1859_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1834_, v___y_1832_, v___y_1831_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 1);
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
v___y_1813_ = v___y_1829_;
v___y_1814_ = v___y_1830_;
v___y_1815_ = v_a_1837_;
v___y_1816_ = v___y_1833_;
v___y_1817_ = v___y_1835_;
v___y_1818_ = v___x_1858_;
v_a_1819_ = v___x_1865_;
goto v___jp_1812_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
v_a_1868_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1859_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1859_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set_tag(v___x_1870_, 0);
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
v___y_1813_ = v___y_1829_;
v___y_1814_ = v___y_1830_;
v___y_1815_ = v_a_1837_;
v___y_1816_ = v___y_1833_;
v___y_1817_ = v___y_1835_;
v___y_1818_ = v___x_1858_;
v_a_1819_ = v___x_1873_;
goto v___jp_1812_;
}
}
}
}
}
v___jp_1878_:
{
lean_object* v___x_1884_; lean_object* v_a_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1884_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1887_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1880_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_io_mono_nanos_now();
lean_inc(v_trace_962_);
v___x_1889_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v_n_1877_, v___y_1881_, v_acc_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set_tag(v___x_1892_, 1);
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
v___y_1292_ = v___y_1879_;
v___y_1293_ = v___y_1880_;
v___y_1294_ = v_a_1885_;
v___y_1295_ = v___y_1882_;
v___y_1296_ = v___x_1888_;
v___y_1297_ = v___y_1883_;
v_a_1298_ = v___x_1895_;
goto v___jp_1291_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_a_1898_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1889_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1889_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set_tag(v___x_1900_, 0);
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
v___y_1292_ = v___y_1879_;
v___y_1293_ = v___y_1880_;
v___y_1294_ = v_a_1885_;
v___y_1295_ = v___y_1882_;
v___y_1296_ = v___x_1888_;
v___y_1297_ = v___y_1883_;
v_a_1298_ = v___x_1903_;
goto v___jp_1291_;
}
}
}
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_962_);
v___x_1907_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v_n_1877_, v___y_1881_, v_acc_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set_tag(v___x_1910_, 1);
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
v___y_1311_ = v___y_1879_;
v___y_1312_ = v___y_1880_;
v___y_1313_ = v_a_1885_;
v___y_1314_ = v___x_1906_;
v___y_1315_ = v___y_1882_;
v___y_1316_ = v___y_1883_;
v_a_1317_ = v___x_1913_;
goto v___jp_1310_;
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
v_a_1916_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1907_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1907_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set_tag(v___x_1918_, 0);
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
v___y_1311_ = v___y_1879_;
v___y_1312_ = v___y_1880_;
v___y_1313_ = v_a_1885_;
v___y_1314_ = v___x_1906_;
v___y_1315_ = v___y_1882_;
v___y_1316_ = v___y_1883_;
v_a_1317_ = v___x_1921_;
goto v___jp_1310_;
}
}
}
}
}
v___jp_1924_:
{
if (v___y_1934_ == 0)
{
lean_object* v___x_1935_; 
lean_dec_ref(v___y_1925_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v___y_1931_);
v___x_1935_ = lean_apply_6(v___y_1928_, v___y_1931_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
if (lean_obj_tag(v_a_1936_) == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1937_ = lean_nat_add(v_n_1877_, v_one_1876_);
lean_dec(v_n_1877_);
v___x_1938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___y_1931_);
lean_ctor_set(v___x_1938_, 1, v_acc_967_);
v___x_1939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_962_);
v___x_1940_ = l_Lean_Name_append(v___x_1939_, v_trace_962_);
v___x_1941_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1926_, v___y_1930_, v___x_1940_);
lean_dec(v___x_1940_);
if (v___x_1941_ == 0)
{
if (v___y_1932_ == 0)
{
v_n_965_ = v___x_1937_;
v_curr_966_ = v___y_1929_;
v_acc_967_ = v___x_1938_;
goto _start;
}
else
{
v___y_1243_ = v___x_1938_;
v___y_1244_ = v___x_1937_;
v___y_1245_ = v___y_1927_;
v___y_1246_ = v___y_1929_;
v___y_1247_ = v___x_1941_;
v___y_1248_ = v___y_1930_;
v___y_1249_ = v___y_1933_;
goto v___jp_1242_;
}
}
else
{
v___y_1243_ = v___x_1938_;
v___y_1244_ = v___x_1937_;
v___y_1245_ = v___y_1927_;
v___y_1246_ = v___y_1929_;
v___y_1247_ = v___x_1941_;
v___y_1248_ = v___y_1930_;
v___y_1249_ = v___y_1933_;
goto v___jp_1242_;
}
}
else
{
lean_object* v_val_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
lean_dec(v___y_1931_);
v_val_1943_ = lean_ctor_get(v_a_1936_, 0);
lean_inc(v_val_1943_);
lean_dec_ref_known(v_a_1936_, 1);
v___x_1944_ = l_List_appendTR___redArg(v_val_1943_, v___y_1929_);
v___x_1945_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_962_);
v___x_1946_ = l_Lean_Name_append(v___x_1945_, v_trace_962_);
v___x_1947_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1926_, v___y_1930_, v___x_1946_);
lean_dec(v___x_1946_);
if (v___x_1947_ == 0)
{
if (v___y_1932_ == 0)
{
v_n_965_ = v_n_1877_;
v_curr_966_ = v___x_1944_;
goto _start;
}
else
{
v___y_1879_ = v___y_1927_;
v___y_1880_ = v___y_1930_;
v___y_1881_ = v___x_1944_;
v___y_1882_ = v___y_1933_;
v___y_1883_ = v___x_1947_;
goto v___jp_1878_;
}
}
else
{
v___y_1879_ = v___y_1927_;
v___y_1880_ = v___y_1930_;
v___y_1881_ = v___x_1944_;
v___y_1882_ = v___y_1933_;
v___y_1883_ = v___x_1947_;
goto v___jp_1878_;
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v___y_1931_);
lean_dec(v___y_1929_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
v_a_1949_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1935_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1935_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_dec(v___y_1931_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
return v___y_1925_;
}
}
v___jp_1957_:
{
lean_object* v___x_1968_; 
v___x_1968_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
if (v___y_1958_ == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1968_);
v___x_1970_ = lean_io_mono_nanos_now();
lean_inc(v_trace_962_);
v___x_1971_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v_n_1877_, v___y_1962_, v_acc_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set_tag(v___x_1974_, 1);
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
v___y_1656_ = v___y_1959_;
v___y_1657_ = v___y_1960_;
v___y_1658_ = v___y_1961_;
v___y_1659_ = v___y_1963_;
v___y_1660_ = v___y_1964_;
v___y_1661_ = v_a_1969_;
v___y_1662_ = v___y_1966_;
v___y_1663_ = v___y_1965_;
v___y_1664_ = v___x_1970_;
v___y_1665_ = v___y_1967_;
v_a_1666_ = v___x_1977_;
goto v___jp_1655_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_a_1980_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1971_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1971_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set_tag(v___x_1982_, 0);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
v___y_1656_ = v___y_1959_;
v___y_1657_ = v___y_1960_;
v___y_1658_ = v___y_1961_;
v___y_1659_ = v___y_1963_;
v___y_1660_ = v___y_1964_;
v___y_1661_ = v_a_1969_;
v___y_1662_ = v___y_1966_;
v___y_1663_ = v___y_1965_;
v___y_1664_ = v___x_1970_;
v___y_1665_ = v___y_1967_;
v_a_1666_ = v___x_1985_;
goto v___jp_1655_;
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v_a_1988_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1988_);
lean_dec_ref(v___x_1968_);
v___x_1989_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_962_);
v___x_1990_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v_n_1877_, v___y_1962_, v_acc_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 1);
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
v___y_1679_ = v___y_1959_;
v___y_1680_ = v___y_1960_;
v___y_1681_ = v___y_1961_;
v___y_1682_ = v___y_1963_;
v___y_1683_ = v___y_1964_;
v___y_1684_ = v_a_1988_;
v___y_1685_ = v___y_1966_;
v___y_1686_ = v___y_1965_;
v___y_1687_ = v___x_1989_;
v___y_1688_ = v___y_1967_;
v_a_1689_ = v___x_1996_;
goto v___jp_1678_;
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
v_a_1999_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1990_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1990_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set_tag(v___x_2001_, 0);
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
v___y_1679_ = v___y_1959_;
v___y_1680_ = v___y_1960_;
v___y_1681_ = v___y_1961_;
v___y_1682_ = v___y_1963_;
v___y_1683_ = v___y_1964_;
v___y_1684_ = v_a_1988_;
v___y_1685_ = v___y_1966_;
v___y_1686_ = v___y_1965_;
v___y_1687_ = v___x_1989_;
v___y_1688_ = v___y_1967_;
v_a_1689_ = v___x_2004_;
goto v___jp_1678_;
}
}
}
}
}
v___jp_2007_:
{
if (v___y_2021_ == 0)
{
lean_object* v___x_2022_; 
lean_dec_ref(v___y_2015_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v___y_2012_);
v___x_2022_ = lean_apply_6(v___y_2018_, v___y_2012_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
if (lean_obj_tag(v_a_2023_) == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2024_ = lean_nat_add(v_n_1877_, v_one_1876_);
lean_dec(v_n_1877_);
v___x_2025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___y_2012_);
lean_ctor_set(v___x_2025_, 1, v_acc_967_);
v___x_2026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_962_);
v___x_2027_ = l_Lean_Name_append(v___x_2026_, v_trace_962_);
v___x_2028_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2008_, v___y_2019_, v___x_2027_);
lean_dec(v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = l_Lean_trace_profiler;
v___x_2030_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2019_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; 
lean_inc(v_trace_962_);
v___x_2031_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___x_2024_, v___y_2011_, v___x_2025_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1096_ = v___y_2017_;
v___y_1097_ = v___y_2009_;
v___y_1098_ = v___y_2010_;
v___y_1099_ = v___y_2019_;
v___y_1100_ = v___y_2014_;
v___y_1101_ = v___y_2013_;
v___y_1102_ = v___y_2020_;
v___y_1103_ = v___x_2031_;
goto v___jp_1095_;
}
else
{
v___y_1742_ = v___y_2009_;
v___y_1743_ = v___y_2010_;
v___y_1744_ = v___y_2011_;
v___y_1745_ = v___x_2025_;
v___y_1746_ = v___y_2013_;
v___y_1747_ = v___y_2014_;
v___y_1748_ = v___y_2016_;
v___y_1749_ = v___x_2028_;
v___y_1750_ = v___y_2017_;
v___y_1751_ = v___x_2024_;
v___y_1752_ = v___y_2019_;
v___y_1753_ = v___y_2020_;
goto v___jp_1741_;
}
}
else
{
v___y_1742_ = v___y_2009_;
v___y_1743_ = v___y_2010_;
v___y_1744_ = v___y_2011_;
v___y_1745_ = v___x_2025_;
v___y_1746_ = v___y_2013_;
v___y_1747_ = v___y_2014_;
v___y_1748_ = v___y_2016_;
v___y_1749_ = v___x_2028_;
v___y_1750_ = v___y_2017_;
v___y_1751_ = v___x_2024_;
v___y_1752_ = v___y_2019_;
v___y_1753_ = v___y_2020_;
goto v___jp_1741_;
}
}
else
{
lean_object* v_val_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
lean_dec(v___y_2012_);
v_val_2032_ = lean_ctor_get(v_a_2023_, 0);
lean_inc(v_val_2032_);
lean_dec_ref_known(v_a_2023_, 1);
v___x_2033_ = l_List_appendTR___redArg(v_val_2032_, v___y_2011_);
v___x_2034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_962_);
v___x_2035_ = l_Lean_Name_append(v___x_2034_, v_trace_962_);
v___x_2036_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2008_, v___y_2019_, v___x_2035_);
lean_dec(v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = l_Lean_trace_profiler;
v___x_2038_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2019_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_inc(v_trace_962_);
v___x_2039_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v_n_1877_, v___x_2033_, v_acc_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1096_ = v___y_2017_;
v___y_1097_ = v___y_2009_;
v___y_1098_ = v___y_2010_;
v___y_1099_ = v___y_2019_;
v___y_1100_ = v___y_2014_;
v___y_1101_ = v___y_2013_;
v___y_1102_ = v___y_2020_;
v___y_1103_ = v___x_2039_;
goto v___jp_1095_;
}
else
{
v___y_1958_ = v___y_2016_;
v___y_1959_ = v___y_2017_;
v___y_1960_ = v___y_2009_;
v___y_1961_ = v___y_2010_;
v___y_1962_ = v___x_2033_;
v___y_1963_ = v___y_2019_;
v___y_1964_ = v___x_2036_;
v___y_1965_ = v___y_2014_;
v___y_1966_ = v___y_2013_;
v___y_1967_ = v___y_2020_;
goto v___jp_1957_;
}
}
else
{
v___y_1958_ = v___y_2016_;
v___y_1959_ = v___y_2017_;
v___y_1960_ = v___y_2009_;
v___y_1961_ = v___y_2010_;
v___y_1962_ = v___x_2033_;
v___y_1963_ = v___y_2019_;
v___y_1964_ = v___x_2036_;
v___y_1965_ = v___y_2014_;
v___y_1966_ = v___y_2013_;
v___y_1967_ = v___y_2020_;
goto v___jp_1957_;
}
}
}
else
{
lean_object* v_a_2040_; 
lean_dec(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec_ref(v_cfg_961_);
v_a_2040_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2022_, 1);
v___y_1086_ = v___y_2017_;
v___y_1087_ = v___y_2009_;
v___y_1088_ = v___y_2010_;
v___y_1089_ = v___y_2019_;
v___y_1090_ = v___y_2013_;
v___y_1091_ = v___y_2014_;
v___y_1092_ = v___y_2020_;
v_a_1093_ = v_a_2040_;
goto v___jp_1085_;
}
}
else
{
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec_ref(v_cfg_961_);
v___y_1086_ = v___y_2017_;
v___y_1087_ = v___y_2009_;
v___y_1088_ = v___y_2010_;
v___y_1089_ = v___y_2019_;
v___y_1090_ = v___y_2013_;
v___y_1091_ = v___y_2014_;
v___y_1092_ = v___y_2020_;
v_a_1093_ = v___y_2015_;
goto v___jp_1085_;
}
}
v___jp_2041_:
{
lean_object* v___x_2052_; 
v___x_2052_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
if (v___y_2042_ == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2052_);
v___x_2054_ = lean_io_mono_nanos_now();
lean_inc(v_trace_962_);
v___x_2055_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v_n_1877_, v___y_2048_, v_acc_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set_tag(v___x_2058_, 1);
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
v___y_1538_ = v___y_2043_;
v___y_1539_ = v___y_2044_;
v___y_1540_ = v___y_2046_;
v___y_1541_ = v___y_2045_;
v___y_1542_ = v___y_2047_;
v___y_1543_ = v_a_2053_;
v___y_1544_ = v___x_2054_;
v___y_1545_ = v___y_2049_;
v___y_1546_ = v___y_2050_;
v___y_1547_ = v___y_2051_;
v_a_1548_ = v___x_2061_;
goto v___jp_1537_;
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
v_a_2064_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2055_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2055_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 0);
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
v___y_1538_ = v___y_2043_;
v___y_1539_ = v___y_2044_;
v___y_1540_ = v___y_2046_;
v___y_1541_ = v___y_2045_;
v___y_1542_ = v___y_2047_;
v___y_1543_ = v_a_2053_;
v___y_1544_ = v___x_2054_;
v___y_1545_ = v___y_2049_;
v___y_1546_ = v___y_2050_;
v___y_1547_ = v___y_2051_;
v_a_1548_ = v___x_2069_;
goto v___jp_1537_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_a_2072_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2052_);
v___x_2073_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_962_);
v___x_2074_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v_n_1877_, v___y_2048_, v_acc_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set_tag(v___x_2077_, 1);
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
v___y_1518_ = v___y_2043_;
v___y_1519_ = v___y_2044_;
v___y_1520_ = v___y_2046_;
v___y_1521_ = v___y_2045_;
v___y_1522_ = v___x_2073_;
v___y_1523_ = v___y_2047_;
v___y_1524_ = v_a_2072_;
v___y_1525_ = v___y_2049_;
v___y_1526_ = v___y_2050_;
v___y_1527_ = v___y_2051_;
v_a_1528_ = v___x_2080_;
goto v___jp_1517_;
}
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
v_a_2083_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2074_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2074_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
lean_ctor_set_tag(v___x_2085_, 0);
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
v___y_1518_ = v___y_2043_;
v___y_1519_ = v___y_2044_;
v___y_1520_ = v___y_2046_;
v___y_1521_ = v___y_2045_;
v___y_1522_ = v___x_2073_;
v___y_1523_ = v___y_2047_;
v___y_1524_ = v_a_2072_;
v___y_1525_ = v___y_2049_;
v___y_1526_ = v___y_2050_;
v___y_1527_ = v___y_2051_;
v_a_1528_ = v___x_2088_;
goto v___jp_1517_;
}
}
}
}
}
v___jp_2091_:
{
if (v___y_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_dec_ref(v___y_2094_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v___y_2097_);
v___x_2106_ = lean_apply_6(v___y_2101_, v___y_2097_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
if (lean_obj_tag(v_a_2107_) == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2108_ = lean_nat_add(v_n_1877_, v_one_1876_);
lean_dec(v_n_1877_);
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___y_2097_);
lean_ctor_set(v___x_2109_, 1, v_acc_967_);
v___x_2110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_962_);
v___x_2111_ = l_Lean_Name_append(v___x_2110_, v_trace_962_);
v___x_2112_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2092_, v___y_2103_, v___x_2111_);
lean_dec(v___x_2111_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2113_ = l_Lean_trace_profiler;
v___x_2114_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2103_, v___x_2113_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; 
lean_inc(v_trace_962_);
v___x_2115_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___x_2108_, v___y_2096_, v___x_2109_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1147_ = v___y_2100_;
v___y_1148_ = v___y_2093_;
v___y_1149_ = v___y_2095_;
v___y_1150_ = v___y_2102_;
v___y_1151_ = v___y_2103_;
v___y_1152_ = v___y_2098_;
v___y_1153_ = v___y_2104_;
v___y_1154_ = v___x_2115_;
goto v___jp_1146_;
}
else
{
v___y_1466_ = v___y_2093_;
v___y_1467_ = v___y_2095_;
v___y_1468_ = v___x_2109_;
v___y_1469_ = v___x_2108_;
v___y_1470_ = v___y_2096_;
v___y_1471_ = v___x_2112_;
v___y_1472_ = v___y_2098_;
v___y_1473_ = v___y_2099_;
v___y_1474_ = v___y_2100_;
v___y_1475_ = v___y_2102_;
v___y_1476_ = v___y_2103_;
v___y_1477_ = v___y_2104_;
goto v___jp_1465_;
}
}
else
{
v___y_1466_ = v___y_2093_;
v___y_1467_ = v___y_2095_;
v___y_1468_ = v___x_2109_;
v___y_1469_ = v___x_2108_;
v___y_1470_ = v___y_2096_;
v___y_1471_ = v___x_2112_;
v___y_1472_ = v___y_2098_;
v___y_1473_ = v___y_2099_;
v___y_1474_ = v___y_2100_;
v___y_1475_ = v___y_2102_;
v___y_1476_ = v___y_2103_;
v___y_1477_ = v___y_2104_;
goto v___jp_1465_;
}
}
else
{
lean_object* v_val_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
lean_dec(v___y_2097_);
v_val_2116_ = lean_ctor_get(v_a_2107_, 0);
lean_inc(v_val_2116_);
lean_dec_ref_known(v_a_2107_, 1);
v___x_2117_ = l_List_appendTR___redArg(v_val_2116_, v___y_2096_);
v___x_2118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_962_);
v___x_2119_ = l_Lean_Name_append(v___x_2118_, v_trace_962_);
v___x_2120_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2092_, v___y_2103_, v___x_2119_);
lean_dec(v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = l_Lean_trace_profiler;
v___x_2122_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2103_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; 
lean_inc(v_trace_962_);
v___x_2123_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v_n_1877_, v___x_2117_, v_acc_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1147_ = v___y_2100_;
v___y_1148_ = v___y_2093_;
v___y_1149_ = v___y_2095_;
v___y_1150_ = v___y_2102_;
v___y_1151_ = v___y_2103_;
v___y_1152_ = v___y_2098_;
v___y_1153_ = v___y_2104_;
v___y_1154_ = v___x_2123_;
goto v___jp_1146_;
}
else
{
v___y_2042_ = v___y_2099_;
v___y_2043_ = v___y_2100_;
v___y_2044_ = v___y_2093_;
v___y_2045_ = v___y_2095_;
v___y_2046_ = v___y_2102_;
v___y_2047_ = v___y_2103_;
v___y_2048_ = v___x_2117_;
v___y_2049_ = v___x_2120_;
v___y_2050_ = v___y_2098_;
v___y_2051_ = v___y_2104_;
goto v___jp_2041_;
}
}
else
{
v___y_2042_ = v___y_2099_;
v___y_2043_ = v___y_2100_;
v___y_2044_ = v___y_2093_;
v___y_2045_ = v___y_2095_;
v___y_2046_ = v___y_2102_;
v___y_2047_ = v___y_2103_;
v___y_2048_ = v___x_2117_;
v___y_2049_ = v___x_2120_;
v___y_2050_ = v___y_2098_;
v___y_2051_ = v___y_2104_;
goto v___jp_2041_;
}
}
}
else
{
lean_object* v_a_2124_; 
lean_dec(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec_ref(v_cfg_961_);
v_a_2124_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2106_, 1);
v___y_1137_ = v___y_2100_;
v___y_1138_ = v___y_2093_;
v___y_1139_ = v___y_2102_;
v___y_1140_ = v___y_2095_;
v___y_1141_ = v___y_2103_;
v___y_1142_ = v___y_2098_;
v___y_1143_ = v___y_2104_;
v_a_1144_ = v_a_2124_;
goto v___jp_1136_;
}
}
else
{
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec_ref(v_cfg_961_);
v___y_1137_ = v___y_2100_;
v___y_1138_ = v___y_2093_;
v___y_1139_ = v___y_2102_;
v___y_1140_ = v___y_2095_;
v___y_1141_ = v___y_2103_;
v___y_1142_ = v___y_2098_;
v___y_1143_ = v___y_2104_;
v_a_1144_ = v___y_2094_;
goto v___jp_1136_;
}
}
v___jp_2125_:
{
lean_object* v___x_2138_; lean_object* v_a_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2138_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___x_2138_);
v___x_2140_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2141_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2135_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec_ref(v___y_2137_);
v___x_2142_ = lean_io_mono_nanos_now();
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v___y_2131_);
v___x_2143_ = lean_apply_6(v___y_2129_, v___y_2131_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; uint8_t v___x_2145_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v___x_2145_ = lean_unbox(v_a_2144_);
lean_dec(v_a_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; 
lean_inc_ref(v_next_963_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v___y_2131_);
v___x_2146_ = lean_apply_7(v_next_963_, v___y_2131_, v___y_2132_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; 
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec_ref(v_cfg_961_);
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
v___y_1127_ = v_a_2139_;
v___y_1128_ = v___y_2127_;
v___y_1129_ = v___x_2142_;
v___y_1130_ = v___y_2128_;
v___y_1131_ = v___y_2135_;
v___y_1132_ = v___y_2133_;
v___y_1133_ = v___y_2136_;
v_a_1134_ = v_a_2147_;
goto v___jp_1126_;
}
else
{
lean_object* v_a_2148_; uint8_t v___x_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2148_);
lean_dec_ref_known(v___x_2146_, 1);
v___x_2149_ = l_Lean_Exception_isInterrupt(v_a_2148_);
if (v___x_2149_ == 0)
{
uint8_t v___x_2150_; 
lean_inc(v_a_2148_);
v___x_2150_ = l_Lean_Exception_isRuntime(v_a_2148_);
v___y_2092_ = v___y_2126_;
v___y_2093_ = v___y_2127_;
v___y_2094_ = v_a_2148_;
v___y_2095_ = v___y_2128_;
v___y_2096_ = v___y_2130_;
v___y_2097_ = v___y_2131_;
v___y_2098_ = v___y_2133_;
v___y_2099_ = v___x_2141_;
v___y_2100_ = v_a_2139_;
v___y_2101_ = v___y_2134_;
v___y_2102_ = v___x_2142_;
v___y_2103_ = v___y_2135_;
v___y_2104_ = v___y_2136_;
v___y_2105_ = v___x_2150_;
goto v___jp_2091_;
}
else
{
v___y_2092_ = v___y_2126_;
v___y_2093_ = v___y_2127_;
v___y_2094_ = v_a_2148_;
v___y_2095_ = v___y_2128_;
v___y_2096_ = v___y_2130_;
v___y_2097_ = v___y_2131_;
v___y_2098_ = v___y_2133_;
v___y_2099_ = v___x_2141_;
v___y_2100_ = v_a_2139_;
v___y_2101_ = v___y_2134_;
v___y_2102_ = v___x_2142_;
v___y_2103_ = v___y_2135_;
v___y_2104_ = v___y_2136_;
v___y_2105_ = v___x_2149_;
goto v___jp_2091_;
}
}
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
lean_dec_ref(v___y_2134_);
lean_dec_ref(v___y_2132_);
v___x_2151_ = lean_nat_add(v_n_1877_, v_one_1876_);
lean_dec(v_n_1877_);
v___x_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___y_2131_);
lean_ctor_set(v___x_2152_, 1, v_acc_967_);
v___x_2153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_962_);
v___x_2154_ = l_Lean_Name_append(v___x_2153_, v_trace_962_);
v___x_2155_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2126_, v___y_2135_, v___x_2154_);
lean_dec(v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = l_Lean_trace_profiler;
v___x_2157_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2135_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; 
lean_inc(v_trace_962_);
v___x_2158_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___x_2151_, v___y_2130_, v___x_2152_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1147_ = v_a_2139_;
v___y_1148_ = v___y_2127_;
v___y_1149_ = v___y_2128_;
v___y_1150_ = v___x_2142_;
v___y_1151_ = v___y_2135_;
v___y_1152_ = v___y_2133_;
v___y_1153_ = v___y_2136_;
v___y_1154_ = v___x_2158_;
goto v___jp_1146_;
}
else
{
v___y_1604_ = v___y_2127_;
v___y_1605_ = v___y_2128_;
v___y_1606_ = v___y_2130_;
v___y_1607_ = v___x_2152_;
v___y_1608_ = v___y_2133_;
v___y_1609_ = v___x_2155_;
v___y_1610_ = v___x_2141_;
v___y_1611_ = v_a_2139_;
v___y_1612_ = v___x_2151_;
v___y_1613_ = v___x_2142_;
v___y_1614_ = v___y_2135_;
v___y_1615_ = v___y_2136_;
goto v___jp_1603_;
}
}
else
{
v___y_1604_ = v___y_2127_;
v___y_1605_ = v___y_2128_;
v___y_1606_ = v___y_2130_;
v___y_1607_ = v___x_2152_;
v___y_1608_ = v___y_2133_;
v___y_1609_ = v___x_2155_;
v___y_1610_ = v___x_2141_;
v___y_1611_ = v_a_2139_;
v___y_1612_ = v___x_2151_;
v___y_1613_ = v___x_2142_;
v___y_1614_ = v___y_2135_;
v___y_1615_ = v___y_2136_;
goto v___jp_1603_;
}
}
}
else
{
lean_object* v_a_2159_; 
lean_dec_ref(v___y_2134_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec_ref(v_cfg_961_);
v_a_2159_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2143_, 1);
v___y_1137_ = v_a_2139_;
v___y_1138_ = v___y_2127_;
v___y_1139_ = v___x_2142_;
v___y_1140_ = v___y_2128_;
v___y_1141_ = v___y_2135_;
v___y_1142_ = v___y_2133_;
v___y_1143_ = v___y_2136_;
v_a_1144_ = v_a_2159_;
goto v___jp_1136_;
}
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v___y_2132_);
v___x_2160_ = lean_io_get_num_heartbeats();
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v___y_2131_);
v___x_2161_ = lean_apply_6(v___y_2129_, v___y_2131_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; uint8_t v___x_2163_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2161_, 1);
v___x_2163_ = lean_unbox(v_a_2162_);
lean_dec(v_a_2162_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; 
lean_inc_ref(v_next_963_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v___y_2131_);
v___x_2164_ = lean_apply_7(v_next_963_, v___y_2131_, v___y_2137_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; 
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec_ref(v_cfg_961_);
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
v___y_1076_ = v_a_2139_;
v___y_1077_ = v___y_2127_;
v___y_1078_ = v___y_2128_;
v___y_1079_ = v___y_2135_;
v___y_1080_ = v___x_2160_;
v___y_1081_ = v___y_2133_;
v___y_1082_ = v___y_2136_;
v_a_1083_ = v_a_2165_;
goto v___jp_1075_;
}
else
{
lean_object* v_a_2166_; uint8_t v___x_2167_; 
v_a_2166_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2167_ = l_Lean_Exception_isInterrupt(v_a_2166_);
if (v___x_2167_ == 0)
{
uint8_t v___x_2168_; 
lean_inc(v_a_2166_);
v___x_2168_ = l_Lean_Exception_isRuntime(v_a_2166_);
v___y_2008_ = v___y_2126_;
v___y_2009_ = v___y_2127_;
v___y_2010_ = v___y_2128_;
v___y_2011_ = v___y_2130_;
v___y_2012_ = v___y_2131_;
v___y_2013_ = v___x_2160_;
v___y_2014_ = v___y_2133_;
v___y_2015_ = v_a_2166_;
v___y_2016_ = v___x_2141_;
v___y_2017_ = v_a_2139_;
v___y_2018_ = v___y_2134_;
v___y_2019_ = v___y_2135_;
v___y_2020_ = v___y_2136_;
v___y_2021_ = v___x_2168_;
goto v___jp_2007_;
}
else
{
v___y_2008_ = v___y_2126_;
v___y_2009_ = v___y_2127_;
v___y_2010_ = v___y_2128_;
v___y_2011_ = v___y_2130_;
v___y_2012_ = v___y_2131_;
v___y_2013_ = v___x_2160_;
v___y_2014_ = v___y_2133_;
v___y_2015_ = v_a_2166_;
v___y_2016_ = v___x_2141_;
v___y_2017_ = v_a_2139_;
v___y_2018_ = v___y_2134_;
v___y_2019_ = v___y_2135_;
v___y_2020_ = v___y_2136_;
v___y_2021_ = v___x_2167_;
goto v___jp_2007_;
}
}
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
lean_dec_ref(v___y_2137_);
lean_dec_ref(v___y_2134_);
v___x_2169_ = lean_nat_add(v_n_1877_, v_one_1876_);
lean_dec(v_n_1877_);
v___x_2170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___y_2131_);
lean_ctor_set(v___x_2170_, 1, v_acc_967_);
v___x_2171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_962_);
v___x_2172_ = l_Lean_Name_append(v___x_2171_, v_trace_962_);
v___x_2173_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2126_, v___y_2135_, v___x_2172_);
lean_dec(v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = l_Lean_trace_profiler;
v___x_2175_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2135_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; 
lean_inc(v_trace_962_);
v___x_2176_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___x_2169_, v___y_2130_, v___x_2170_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
v___y_1096_ = v_a_2139_;
v___y_1097_ = v___y_2127_;
v___y_1098_ = v___y_2128_;
v___y_1099_ = v___y_2135_;
v___y_1100_ = v___y_2133_;
v___y_1101_ = v___x_2160_;
v___y_1102_ = v___y_2136_;
v___y_1103_ = v___x_2176_;
goto v___jp_1095_;
}
else
{
v___y_1371_ = v___y_2127_;
v___y_1372_ = v___y_2128_;
v___y_1373_ = v___x_2173_;
v___y_1374_ = v___y_2130_;
v___y_1375_ = v___x_2169_;
v___y_1376_ = v___x_2160_;
v___y_1377_ = v___y_2133_;
v___y_1378_ = v___x_2141_;
v___y_1379_ = v_a_2139_;
v___y_1380_ = v___y_2135_;
v___y_1381_ = v___x_2170_;
v___y_1382_ = v___y_2136_;
goto v___jp_1370_;
}
}
else
{
v___y_1371_ = v___y_2127_;
v___y_1372_ = v___y_2128_;
v___y_1373_ = v___x_2173_;
v___y_1374_ = v___y_2130_;
v___y_1375_ = v___x_2169_;
v___y_1376_ = v___x_2160_;
v___y_1377_ = v___y_2133_;
v___y_1378_ = v___x_2141_;
v___y_1379_ = v_a_2139_;
v___y_1380_ = v___y_2135_;
v___y_1381_ = v___x_2170_;
v___y_1382_ = v___y_2136_;
goto v___jp_1370_;
}
}
}
else
{
lean_object* v_a_2177_; 
lean_dec_ref(v___y_2137_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec_ref(v_cfg_961_);
v_a_2177_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2161_, 1);
v___y_1086_ = v_a_2139_;
v___y_1087_ = v___y_2127_;
v___y_1088_ = v___y_2128_;
v___y_1089_ = v___y_2135_;
v___y_1090_ = v___x_2160_;
v___y_1091_ = v___y_2133_;
v___y_1092_ = v___y_2136_;
v_a_1093_ = v_a_2177_;
goto v___jp_1085_;
}
}
}
v___jp_2178_:
{
if (v___y_2183_ == 0)
{
lean_object* v___x_2184_; 
lean_dec_ref(v___y_2179_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v___y_2182_);
v___x_2184_ = lean_apply_6(v___y_2180_, v___y_2182_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
if (lean_obj_tag(v_a_2185_) == 0)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_nat_add(v_n_1877_, v_one_1876_);
lean_dec(v_n_1877_);
v___x_2187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___y_2182_);
lean_ctor_set(v___x_2187_, 1, v_acc_967_);
v_n_965_ = v___x_2186_;
v_curr_966_ = v___y_2181_;
v_acc_967_ = v___x_2187_;
goto _start;
}
else
{
lean_object* v_val_2189_; lean_object* v___x_2190_; 
lean_dec(v___y_2182_);
v_val_2189_ = lean_ctor_get(v_a_2185_, 0);
lean_inc(v_val_2189_);
lean_dec_ref_known(v_a_2185_, 1);
v___x_2190_ = l_List_appendTR___redArg(v_val_2189_, v___y_2181_);
v_n_965_ = v_n_1877_;
v_curr_966_ = v___x_2190_;
goto _start;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
v_a_2192_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2184_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2184_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_dec(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
return v___y_2179_;
}
}
v___jp_2200_:
{
if (lean_obj_tag(v_a_2201_) == 0)
{
if (lean_obj_tag(v_curr_966_) == 0)
{
lean_object* v_options_2202_; lean_object* v_toCold_2203_; uint8_t v_hasTrace_2204_; lean_object* v___x_2205_; 
lean_dec(v_n_1877_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec_ref(v_cfg_961_);
v_options_2202_ = lean_ctor_get(v_a_970_, 1);
v_toCold_2203_ = lean_ctor_get(v_a_970_, 0);
v_hasTrace_2204_ = lean_ctor_get_uint8(v_options_2202_, sizeof(void*)*1);
v___x_2205_ = l_List_reverse___redArg(v_acc_967_);
if (v_hasTrace_2204_ == 0)
{
lean_object* v___x_2206_; 
lean_dec(v_trace_962_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
else
{
lean_object* v_inheritedTraceOptions_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; 
v_inheritedTraceOptions_2207_ = lean_ctor_get(v_toCold_2203_, 4);
v___x_2208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_962_);
v___x_2210_ = l_Lean_Name_append(v___x_2209_, v_trace_962_);
v___x_2211_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2207_, v_options_2202_, v___x_2210_);
lean_dec(v___x_2210_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; uint8_t v___x_2213_; 
v___x_2212_ = l_Lean_trace_profiler;
v___x_2213_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2202_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
lean_dec(v_trace_962_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2205_);
return v___x_2214_;
}
else
{
v___y_1166_ = v___x_2205_;
v___y_1167_ = v_hasTrace_2204_;
v___y_1168_ = v___x_2208_;
v___y_1169_ = v___x_2211_;
v___y_1170_ = v_options_2202_;
goto v___jp_1165_;
}
}
else
{
v___y_1166_ = v___x_2205_;
v___y_1167_ = v_hasTrace_2204_;
v___y_1168_ = v___x_2208_;
v___y_1169_ = v___x_2211_;
v___y_1170_ = v_options_2202_;
goto v___jp_1165_;
}
}
}
else
{
lean_object* v_head_2215_; lean_object* v_tail_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2291_; 
v_head_2215_ = lean_ctor_get(v_curr_966_, 0);
v_tail_2216_ = lean_ctor_get(v_curr_966_, 1);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_curr_966_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2218_ = v_curr_966_;
v_isShared_2219_ = v_isSharedCheck_2291_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_tail_2216_);
lean_inc(v_head_2215_);
lean_dec(v_curr_966_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2291_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v_a_2221_; uint8_t v___x_2222_; uint8_t v___x_2223_; 
v___x_2220_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2215_, v_a_969_);
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2220_);
v___x_2222_ = 1;
v___x_2223_ = lean_unbox(v_a_2221_);
lean_dec(v_a_2221_);
if (v___x_2223_ == 0)
{
lean_object* v_options_2224_; uint8_t v_hasTrace_2225_; 
v_options_2224_ = lean_ctor_get(v_a_970_, 1);
v_hasTrace_2225_ = lean_ctor_get_uint8(v_options_2224_, sizeof(void*)*1);
if (v_hasTrace_2225_ == 0)
{
lean_object* v___x_2226_; 
lean_inc_ref(v_suspend_1162_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v_head_2215_);
v___x_2226_ = lean_apply_6(v_suspend_1162_, v_head_2215_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; uint8_t v___x_2228_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2228_ = lean_unbox(v_a_2227_);
lean_dec(v_a_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___f_2229_; lean_object* v___x_2230_; 
lean_del_object(v___x_2218_);
lean_inc(v_acc_967_);
lean_inc(v_n_1877_);
lean_inc(v_goals_964_);
lean_inc_ref_n(v_next_963_, 2);
lean_inc(v_trace_962_);
lean_inc_ref(v_cfg_961_);
lean_inc(v_tail_2216_);
v___f_2229_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2229_, 0, v_tail_2216_);
lean_closure_set(v___f_2229_, 1, v_cfg_961_);
lean_closure_set(v___f_2229_, 2, v_trace_962_);
lean_closure_set(v___f_2229_, 3, v_next_963_);
lean_closure_set(v___f_2229_, 4, v_goals_964_);
lean_closure_set(v___f_2229_, 5, v_n_1877_);
lean_closure_set(v___f_2229_, 6, v_acc_967_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v_head_2215_);
v___x_2230_ = lean_apply_7(v_next_963_, v_head_2215_, v___f_2229_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_dec(v_tail_2216_);
lean_dec(v_head_2215_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
return v___x_2230_;
}
else
{
lean_object* v_a_2231_; uint8_t v___x_2232_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
v___x_2232_ = l_Lean_Exception_isInterrupt(v_a_2231_);
if (v___x_2232_ == 0)
{
uint8_t v___x_2233_; 
v___x_2233_ = l_Lean_Exception_isRuntime(v_a_2231_);
lean_inc_ref(v_discharge_1163_);
v___y_2179_ = v___x_2230_;
v___y_2180_ = v_discharge_1163_;
v___y_2181_ = v_tail_2216_;
v___y_2182_ = v_head_2215_;
v___y_2183_ = v___x_2233_;
goto v___jp_2178_;
}
else
{
lean_dec(v_a_2231_);
lean_inc_ref(v_discharge_1163_);
v___y_2179_ = v___x_2230_;
v___y_2180_ = v_discharge_1163_;
v___y_2181_ = v_tail_2216_;
v___y_2182_ = v_head_2215_;
v___y_2183_ = v___x_2232_;
goto v___jp_2178_;
}
}
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_nat_add(v_n_1877_, v_one_1876_);
lean_dec(v_n_1877_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v_acc_967_);
v___x_2236_ = v___x_2218_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_head_2215_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_acc_967_);
v___x_2236_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
v_n_965_ = v___x_2234_;
v_curr_966_ = v_tail_2216_;
v_acc_967_ = v___x_2236_;
goto _start;
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_del_object(v___x_2218_);
lean_dec(v_tail_2216_);
lean_dec(v_head_2215_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
v_a_2239_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2226_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2226_);
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
lean_object* v_toCold_2247_; lean_object* v_inheritedTraceOptions_2248_; lean_object* v___f_2249_; lean_object* v___f_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v_toCold_2247_ = lean_ctor_get(v_a_970_, 0);
v_inheritedTraceOptions_2248_ = lean_ctor_get(v_toCold_2247_, 4);
lean_inc(v_acc_967_);
lean_inc(v_n_1877_);
lean_inc(v_goals_964_);
lean_inc_ref(v_next_963_);
lean_inc_n(v_trace_962_, 2);
lean_inc_ref(v_cfg_961_);
lean_inc(v_tail_2216_);
v___f_2249_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(v___f_2249_, 0, v_tail_2216_);
lean_closure_set(v___f_2249_, 1, v_cfg_961_);
lean_closure_set(v___f_2249_, 2, v_trace_962_);
lean_closure_set(v___f_2249_, 3, v_next_963_);
lean_closure_set(v___f_2249_, 4, v_goals_964_);
lean_closure_set(v___f_2249_, 5, v_n_1877_);
lean_closure_set(v___f_2249_, 6, v_acc_967_);
lean_inc(v_head_2215_);
v___f_2250_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(v___f_2250_, 0, v_head_2215_);
v___x_2251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
v___x_2253_ = l_Lean_Name_append(v___x_2252_, v_trace_962_);
v___x_2254_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2248_, v_options_2224_, v___x_2253_);
lean_dec(v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2255_ = l_Lean_trace_profiler;
v___x_2256_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2224_, v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; 
lean_dec_ref(v___f_2250_);
lean_inc_ref(v_suspend_1162_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v_head_2215_);
v___x_2257_ = lean_apply_6(v_suspend_1162_, v_head_2215_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; uint8_t v___x_2259_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2257_, 1);
v___x_2259_ = lean_unbox(v_a_2258_);
lean_dec(v_a_2258_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
lean_del_object(v___x_2218_);
lean_inc_ref(v_next_963_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v_head_2215_);
v___x_2260_ = lean_apply_7(v_next_963_, v_head_2215_, v___f_2249_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, lean_box(0));
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_dec(v_tail_2216_);
lean_dec(v_head_2215_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
return v___x_2260_;
}
else
{
lean_object* v_a_2261_; uint8_t v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
v___x_2262_ = l_Lean_Exception_isInterrupt(v_a_2261_);
if (v___x_2262_ == 0)
{
uint8_t v___x_2263_; 
v___x_2263_ = l_Lean_Exception_isRuntime(v_a_2261_);
lean_inc_ref(v_discharge_1163_);
v___y_1925_ = v___x_2260_;
v___y_1926_ = v_inheritedTraceOptions_2248_;
v___y_1927_ = v___x_2251_;
v___y_1928_ = v_discharge_1163_;
v___y_1929_ = v_tail_2216_;
v___y_1930_ = v_options_2224_;
v___y_1931_ = v_head_2215_;
v___y_1932_ = v___x_2256_;
v___y_1933_ = v___x_2222_;
v___y_1934_ = v___x_2263_;
goto v___jp_1924_;
}
else
{
lean_dec(v_a_2261_);
lean_inc_ref(v_discharge_1163_);
v___y_1925_ = v___x_2260_;
v___y_1926_ = v_inheritedTraceOptions_2248_;
v___y_1927_ = v___x_2251_;
v___y_1928_ = v_discharge_1163_;
v___y_1929_ = v_tail_2216_;
v___y_1930_ = v_options_2224_;
v___y_1931_ = v_head_2215_;
v___y_1932_ = v___x_2256_;
v___y_1933_ = v___x_2222_;
v___y_1934_ = v___x_2262_;
goto v___jp_1924_;
}
}
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
lean_dec_ref(v___f_2249_);
v___x_2264_ = lean_nat_add(v_n_1877_, v_one_1876_);
lean_dec(v_n_1877_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v_acc_967_);
v___x_2266_ = v___x_2218_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_head_2215_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_acc_967_);
v___x_2266_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
if (v___x_2254_ == 0)
{
if (v___x_2256_ == 0)
{
v_n_965_ = v___x_2264_;
v_curr_966_ = v_tail_2216_;
v_acc_967_ = v___x_2266_;
goto _start;
}
else
{
v___y_1829_ = v___x_2254_;
v___y_1830_ = v___x_2251_;
v___y_1831_ = v___x_2266_;
v___y_1832_ = v_tail_2216_;
v___y_1833_ = v_options_2224_;
v___y_1834_ = v___x_2264_;
v___y_1835_ = v___x_2222_;
goto v___jp_1828_;
}
}
else
{
v___y_1829_ = v___x_2254_;
v___y_1830_ = v___x_2251_;
v___y_1831_ = v___x_2266_;
v___y_1832_ = v_tail_2216_;
v___y_1833_ = v_options_2224_;
v___y_1834_ = v___x_2264_;
v___y_1835_ = v___x_2222_;
goto v___jp_1828_;
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref(v___f_2249_);
lean_del_object(v___x_2218_);
lean_dec(v_tail_2216_);
lean_dec(v_head_2215_);
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
v_a_2269_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2257_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2257_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_del_object(v___x_2218_);
lean_inc_ref(v_discharge_1163_);
lean_inc_ref(v___f_2249_);
lean_inc_ref(v_suspend_1162_);
v___y_2126_ = v_inheritedTraceOptions_2248_;
v___y_2127_ = v___x_2251_;
v___y_2128_ = v___f_2250_;
v___y_2129_ = v_suspend_1162_;
v___y_2130_ = v_tail_2216_;
v___y_2131_ = v_head_2215_;
v___y_2132_ = v___f_2249_;
v___y_2133_ = v___x_2254_;
v___y_2134_ = v_discharge_1163_;
v___y_2135_ = v_options_2224_;
v___y_2136_ = v___x_2222_;
v___y_2137_ = v___f_2249_;
goto v___jp_2125_;
}
}
else
{
lean_del_object(v___x_2218_);
lean_inc_ref(v_discharge_1163_);
lean_inc_ref(v___f_2249_);
lean_inc_ref(v_suspend_1162_);
v___y_2126_ = v_inheritedTraceOptions_2248_;
v___y_2127_ = v___x_2251_;
v___y_2128_ = v___f_2250_;
v___y_2129_ = v_suspend_1162_;
v___y_2130_ = v_tail_2216_;
v___y_2131_ = v_head_2215_;
v___y_2132_ = v___f_2249_;
v___y_2133_ = v___x_2254_;
v___y_2134_ = v_discharge_1163_;
v___y_2135_ = v_options_2224_;
v___y_2136_ = v___x_2222_;
v___y_2137_ = v___f_2249_;
goto v___jp_2125_;
}
}
}
else
{
lean_object* v_options_2277_; lean_object* v_toCold_2278_; uint8_t v_hasTrace_2279_; lean_object* v___x_2280_; 
lean_del_object(v___x_2218_);
v_options_2277_ = lean_ctor_get(v_a_970_, 1);
v_toCold_2278_ = lean_ctor_get(v_a_970_, 0);
v_hasTrace_2279_ = lean_ctor_get_uint8(v_options_2277_, sizeof(void*)*1);
v___x_2280_ = lean_nat_add(v_n_1877_, v_one_1876_);
lean_dec(v_n_1877_);
if (v_hasTrace_2279_ == 0)
{
lean_dec(v_head_2215_);
v_n_965_ = v___x_2280_;
v_curr_966_ = v_tail_2216_;
goto _start;
}
else
{
lean_object* v_inheritedTraceOptions_2282_; lean_object* v___f_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v_inheritedTraceOptions_2282_ = lean_ctor_get(v_toCold_2278_, 4);
v___f_2283_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2283_, 0, v_head_2215_);
v___x_2284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_962_);
v___x_2286_ = l_Lean_Name_append(v___x_2285_, v_trace_962_);
v___x_2287_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2282_, v_options_2277_, v___x_2286_);
lean_dec(v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2288_ = l_Lean_trace_profiler;
v___x_2289_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2277_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_dec_ref(v___f_2283_);
v_n_965_ = v___x_2280_;
v_curr_966_ = v_tail_2216_;
goto _start;
}
else
{
v___y_1011_ = v___x_2287_;
v___y_1012_ = v___f_2283_;
v___y_1013_ = v_tail_2216_;
v___y_1014_ = v_options_2277_;
v___y_1015_ = v___x_2280_;
v___y_1016_ = v___x_2222_;
v___y_1017_ = v___x_2284_;
goto v___jp_1010_;
}
}
else
{
v___y_1011_ = v___x_2287_;
v___y_1012_ = v___f_2283_;
v___y_1013_ = v_tail_2216_;
v___y_1014_ = v_options_2277_;
v___y_1015_ = v___x_2280_;
v___y_1016_ = v___x_2222_;
v___y_1017_ = v___x_2284_;
goto v___jp_1010_;
}
}
}
}
}
}
else
{
lean_object* v_val_2292_; 
lean_dec(v_curr_966_);
v_val_2292_ = lean_ctor_get(v_a_2201_, 0);
lean_inc(v_val_2292_);
lean_dec_ref_known(v_a_2201_, 1);
v_n_965_ = v_n_1877_;
v_curr_966_ = v_val_2292_;
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
v_a_2201_ = v_a_2296_;
goto v___jp_2200_;
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec(v_n_1877_);
lean_dec(v_acc_967_);
lean_dec(v_curr_966_);
lean_dec(v_goals_964_);
lean_dec_ref(v_next_963_);
lean_dec(v_trace_962_);
lean_dec_ref(v_cfg_961_);
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
v___jp_973_:
{
lean_object* v___x_982_; double v___x_983_; double v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_982_ = lean_io_get_num_heartbeats();
v___x_983_ = lean_float_of_nat(v___y_977_);
v___x_984_ = lean_float_of_nat(v___x_982_);
v___x_985_ = lean_box_float(v___x_983_);
v___x_986_ = lean_box_float(v___x_984_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v_a_981_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
lean_inc_ref(v___y_980_);
v___x_989_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_979_, v___y_980_, v___y_978_, v___y_974_, v___y_976_, v___y_975_, v___x_988_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_989_;
}
v___jp_990_:
{
lean_object* v___x_999_; double v___x_1000_; double v___x_1001_; double v___x_1002_; double v___x_1003_; double v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_999_ = lean_io_mono_nanos_now();
v___x_1000_ = lean_float_of_nat(v___y_996_);
v___x_1001_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1002_ = lean_float_div(v___x_1000_, v___x_1001_);
v___x_1003_ = lean_float_of_nat(v___x_999_);
v___x_1004_ = lean_float_div(v___x_1003_, v___x_1001_);
v___x_1005_ = lean_box_float(v___x_1002_);
v___x_1006_ = lean_box_float(v___x_1004_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v_a_998_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
lean_inc_ref(v___y_997_);
v___x_1009_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_995_, v___y_997_, v___y_994_, v___y_991_, v___y_993_, v___y_992_, v___x_1008_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1009_;
}
v___jp_1010_:
{
lean_object* v___x_1018_; lean_object* v_a_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1018_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_971_);
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1021_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1014_, v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_io_mono_nanos_now();
lean_inc(v_trace_962_);
v___x_1023_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1015_, v___y_1013_, v_acc_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set_tag(v___x_1026_, 1);
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
v___y_991_ = v___y_1011_;
v___y_992_ = v___y_1012_;
v___y_993_ = v_a_1019_;
v___y_994_ = v___y_1014_;
v___y_995_ = v___y_1016_;
v___y_996_ = v___x_1022_;
v___y_997_ = v___y_1017_;
v_a_998_ = v___x_1029_;
goto v___jp_990_;
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_a_1032_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1023_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1023_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 0);
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
v___y_991_ = v___y_1011_;
v___y_992_ = v___y_1012_;
v___y_993_ = v_a_1019_;
v___y_994_ = v___y_1014_;
v___y_995_ = v___y_1016_;
v___y_996_ = v___x_1022_;
v___y_997_ = v___y_1017_;
v_a_998_ = v___x_1037_;
goto v___jp_990_;
}
}
}
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_962_);
v___x_1041_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_961_, v_trace_962_, v_next_963_, v_goals_964_, v___y_1015_, v___y_1013_, v_acc_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set_tag(v___x_1044_, 1);
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
v___y_974_ = v___y_1011_;
v___y_975_ = v___y_1012_;
v___y_976_ = v_a_1019_;
v___y_977_ = v___x_1040_;
v___y_978_ = v___y_1014_;
v___y_979_ = v___y_1016_;
v___y_980_ = v___y_1017_;
v_a_981_ = v___x_1047_;
goto v___jp_973_;
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
v_a_1050_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1041_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1041_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set_tag(v___x_1052_, 0);
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
v___y_974_ = v___y_1011_;
v___y_975_ = v___y_1012_;
v___y_976_ = v_a_1019_;
v___y_977_ = v___x_1040_;
v___y_978_ = v___y_1014_;
v___y_979_ = v___y_1016_;
v___y_980_ = v___y_1017_;
v_a_981_ = v___x_1055_;
goto v___jp_973_;
}
}
}
}
}
v___jp_1058_:
{
lean_object* v___x_1067_; double v___x_1068_; double v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1067_ = lean_io_get_num_heartbeats();
v___x_1068_ = lean_float_of_nat(v___y_1064_);
v___x_1069_ = lean_float_of_nat(v___x_1067_);
v___x_1070_ = lean_box_float(v___x_1068_);
v___x_1071_ = lean_box_float(v___x_1069_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_a_1066_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
lean_inc_ref(v___y_1060_);
v___x_1074_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1065_, v___y_1060_, v___y_1062_, v___y_1063_, v___y_1059_, v___y_1061_, v___x_1073_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1074_;
}
v___jp_1075_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_a_1083_);
v___y_1059_ = v___y_1076_;
v___y_1060_ = v___y_1077_;
v___y_1061_ = v___y_1078_;
v___y_1062_ = v___y_1079_;
v___y_1063_ = v___y_1081_;
v___y_1064_ = v___y_1080_;
v___y_1065_ = v___y_1082_;
v_a_1066_ = v___x_1084_;
goto v___jp_1058_;
}
v___jp_1085_:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_a_1093_);
v___y_1059_ = v___y_1086_;
v___y_1060_ = v___y_1087_;
v___y_1061_ = v___y_1088_;
v___y_1062_ = v___y_1089_;
v___y_1063_ = v___y_1091_;
v___y_1064_ = v___y_1090_;
v___y_1065_ = v___y_1092_;
v_a_1066_ = v___x_1094_;
goto v___jp_1058_;
}
v___jp_1095_:
{
if (lean_obj_tag(v___y_1103_) == 0)
{
lean_object* v_a_1104_; 
v_a_1104_ = lean_ctor_get(v___y_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___y_1103_, 1);
v___y_1076_ = v___y_1096_;
v___y_1077_ = v___y_1097_;
v___y_1078_ = v___y_1098_;
v___y_1079_ = v___y_1099_;
v___y_1080_ = v___y_1101_;
v___y_1081_ = v___y_1100_;
v___y_1082_ = v___y_1102_;
v_a_1083_ = v_a_1104_;
goto v___jp_1075_;
}
else
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v___y_1103_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___y_1103_, 1);
v___y_1086_ = v___y_1096_;
v___y_1087_ = v___y_1097_;
v___y_1088_ = v___y_1098_;
v___y_1089_ = v___y_1099_;
v___y_1090_ = v___y_1101_;
v___y_1091_ = v___y_1100_;
v___y_1092_ = v___y_1102_;
v_a_1093_ = v_a_1105_;
goto v___jp_1085_;
}
}
v___jp_1106_:
{
lean_object* v___x_1115_; double v___x_1116_; double v___x_1117_; double v___x_1118_; double v___x_1119_; double v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1115_ = lean_io_mono_nanos_now();
v___x_1116_ = lean_float_of_nat(v___y_1110_);
v___x_1117_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1118_ = lean_float_div(v___x_1116_, v___x_1117_);
v___x_1119_ = lean_float_of_nat(v___x_1115_);
v___x_1120_ = lean_float_div(v___x_1119_, v___x_1117_);
v___x_1121_ = lean_box_float(v___x_1118_);
v___x_1122_ = lean_box_float(v___x_1120_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1114_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
lean_inc_ref(v___y_1108_);
v___x_1125_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_962_, v___y_1113_, v___y_1108_, v___y_1111_, v___y_1112_, v___y_1107_, v___y_1109_, v___x_1124_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_1125_;
}
v___jp_1126_:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_a_1134_);
v___y_1107_ = v___y_1127_;
v___y_1108_ = v___y_1128_;
v___y_1109_ = v___y_1130_;
v___y_1110_ = v___y_1129_;
v___y_1111_ = v___y_1131_;
v___y_1112_ = v___y_1132_;
v___y_1113_ = v___y_1133_;
v_a_1114_ = v___x_1135_;
goto v___jp_1106_;
}
v___jp_1136_:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v_a_1144_);
v___y_1107_ = v___y_1137_;
v___y_1108_ = v___y_1138_;
v___y_1109_ = v___y_1140_;
v___y_1110_ = v___y_1139_;
v___y_1111_ = v___y_1141_;
v___y_1112_ = v___y_1142_;
v___y_1113_ = v___y_1143_;
v_a_1114_ = v___x_1145_;
goto v___jp_1106_;
}
v___jp_1146_:
{
if (lean_obj_tag(v___y_1154_) == 0)
{
lean_object* v_a_1155_; 
v_a_1155_ = lean_ctor_get(v___y_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___y_1154_, 1);
v___y_1127_ = v___y_1147_;
v___y_1128_ = v___y_1148_;
v___y_1129_ = v___y_1150_;
v___y_1130_ = v___y_1149_;
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
lean_dec_ref_known(v___y_1154_, 1);
v___y_1137_ = v___y_1147_;
v___y_1138_ = v___y_1148_;
v___y_1139_ = v___y_1150_;
v___y_1140_ = v___y_1149_;
v___y_1141_ = v___y_1151_;
v___y_1142_ = v___y_1152_;
v___y_1143_ = v___y_1153_;
v_a_1144_ = v_a_1156_;
goto v___jp_1136_;
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
size_t v_x_77190__boxed_2469_; uint8_t v_res_2470_; lean_object* v_r_2471_; 
v_x_77190__boxed_2469_ = lean_unbox_usize(v_x_2467_);
lean_dec(v_x_2467_);
v_res_2470_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2465_, v_x_2466_, v_x_77190__boxed_2469_, v_x_2468_);
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
uint8_t v___x_45427__boxed_2756_; lean_object* v_res_2757_; 
v___x_45427__boxed_2756_ = lean_unbox(v___x_2751_);
v_res_2757_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_45427__boxed_2756_, v_x_2752_, v_x_2753_, v___y_2754_);
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
uint8_t v___x_45781__boxed_2957_; uint8_t v___x_45782__boxed_2958_; lean_object* v_res_2959_; 
v___x_45781__boxed_2957_ = lean_unbox(v___x_2951_);
v___x_45782__boxed_2958_ = lean_unbox(v___x_2952_);
v_res_2959_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_45781__boxed_2957_, v___x_45782__boxed_2958_, v_x_2953_, v_x_2954_, v___y_2955_);
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
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
lean_inc(v_remaining_2970_);
lean_inc(v_goals_2969_);
v___x_2977_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2969_, v_remaining_2970_, v___x_2976_, v___x_2976_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v_fst_2979_; lean_object* v_snd_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_4181_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v_fst_2979_ = lean_ctor_get(v_a_2978_, 0);
v_snd_2980_ = lean_ctor_get(v_a_2978_, 1);
v_isSharedCheck_4181_ = !lean_is_exclusive(v_a_2978_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_2982_ = v_a_2978_;
v_isShared_2983_ = v_isSharedCheck_4181_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_snd_2980_);
lean_inc(v_fst_2979_);
lean_dec(v_a_2978_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_4181_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
uint8_t v___x_2984_; 
v___x_2984_ = l_List_isEmpty___redArg(v_fst_2979_);
if (v___x_2984_ == 0)
{
lean_object* v_options_2985_; lean_object* v_toCold_2986_; uint8_t v_hasTrace_2987_; lean_object* v___f_2988_; 
lean_dec(v_remaining_2970_);
v_options_2985_ = lean_ctor_get(v_a_2973_, 1);
v_toCold_2986_ = lean_ctor_get(v_a_2973_, 0);
v_hasTrace_2987_ = lean_ctor_get_uint8(v_options_2985_, sizeof(void*)*1);
lean_inc(v_orig_2968_);
lean_inc_ref(v_next_2967_);
lean_inc(v_trace_2966_);
lean_inc_ref(v_cfg_2965_);
v___f_2988_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2988_, 0, v_cfg_2965_);
lean_closure_set(v___f_2988_, 1, v_trace_2966_);
lean_closure_set(v___f_2988_, 2, v_next_2967_);
lean_closure_set(v___f_2988_, 3, v_orig_2968_);
if (v_hasTrace_2987_ == 0)
{
lean_object* v___x_2989_; 
lean_del_object(v___x_2982_);
v___x_2989_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2979_, v___f_2988_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
v___x_2996_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_2995_, v___x_2976_);
v___x_3057_ = lean_box(0);
v___x_3058_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_2984_, v_goals_2969_, v___x_3057_, v_a_2972_);
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
lean_dec(v_snd_2980_);
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
lean_dec_ref(v___y_3008_);
v___x_3011_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3009_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3009_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_dec_ref_known(v___x_3011_, 1);
v_a_2998_ = v_snd_2980_;
goto v___jp_2997_;
}
else
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_dec(v___x_2996_);
lean_dec(v_fst_2994_);
lean_del_object(v___x_2992_);
lean_dec(v_snd_2980_);
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
lean_dec_ref(v___y_3009_);
lean_dec(v_snd_2980_);
v___y_3005_ = v___y_3008_;
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
lean_inc(v_snd_2980_);
v___x_3024_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3021_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_dec(v_a_3023_);
lean_dec(v_snd_2980_);
v___y_3005_ = v___x_3024_;
goto v___jp_3004_;
}
else
{
lean_object* v_a_3025_; uint8_t v___x_3026_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
v___x_3026_ = l_Lean_Exception_isInterrupt(v_a_3025_);
if (v___x_3026_ == 0)
{
uint8_t v___x_3027_; 
v___x_3027_ = l_Lean_Exception_isRuntime(v_a_3025_);
v___y_3008_ = v___x_3024_;
v___y_3009_ = v_a_3023_;
v___y_3010_ = v___x_3027_;
goto v___jp_3007_;
}
else
{
lean_dec(v_a_3025_);
v___y_3008_ = v___x_3024_;
v___y_3009_ = v_a_3023_;
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
lean_dec(v_snd_2980_);
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
lean_dec(v_snd_2980_);
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
v___x_3042_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3037_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
v___y_3038_ = v___x_2984_;
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
v___y_3038_ = v___x_2984_;
goto v___jp_3036_;
}
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v_snd_2980_);
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
lean_object* v_inheritedTraceOptions_3071_; lean_object* v___f_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v_a_3080_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v_a_3094_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v_a_3099_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v_a_3106_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; uint8_t v___y_3124_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3147_; uint8_t v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v_a_3153_; lean_object* v___y_3166_; uint8_t v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v_a_3172_; lean_object* v___y_3175_; uint8_t v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v_a_3181_; lean_object* v___y_3184_; lean_object* v___y_3185_; uint8_t v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v_a_3192_; lean_object* v___y_3196_; lean_object* v___y_3197_; uint8_t v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; uint8_t v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v___y_3218_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; uint8_t v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3239_; uint8_t v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; uint8_t v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; uint8_t v___y_3258_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v_a_3274_; lean_object* v___y_3279_; lean_object* v___y_3280_; uint8_t v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v_a_3285_; lean_object* v___y_3295_; lean_object* v___y_3296_; uint8_t v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v_a_3301_; lean_object* v___y_3304_; lean_object* v___y_3305_; uint8_t v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v_a_3310_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; uint8_t v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v_a_3321_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; uint8_t v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; uint8_t v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; uint8_t v___y_3347_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; uint8_t v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3368_; lean_object* v___y_3369_; uint8_t v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; uint8_t v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; uint8_t v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; uint8_t v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; uint8_t v___y_3400_; uint8_t v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; uint8_t v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v_a_3414_; uint8_t v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; uint8_t v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; uint8_t v___y_3449_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v_a_3461_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v_a_3468_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v_a_3483_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v_a_3488_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v_a_3495_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; uint8_t v___y_3513_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v_a_3542_; uint8_t v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v_a_3558_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; uint8_t v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v_a_3569_; uint8_t v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v_a_3579_; lean_object* v___y_3582_; lean_object* v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3592_; lean_object* v___y_3593_; uint8_t v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3604_; uint8_t v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3616_; uint8_t v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; uint8_t v___y_3626_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; uint8_t v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; uint8_t v___y_3647_; lean_object* v___y_3648_; uint8_t v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; uint8_t v___y_3657_; uint8_t v___y_3662_; lean_object* v___y_3663_; uint8_t v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v_a_3671_; lean_object* v___y_3676_; lean_object* v___y_3677_; uint8_t v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v_a_3682_; uint8_t v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v_a_3701_; uint8_t v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v_a_3710_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; uint8_t v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v_a_3721_; lean_object* v___y_3725_; uint8_t v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3737_; uint8_t v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; uint8_t v___y_3747_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; uint8_t v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3768_; lean_object* v___y_3769_; uint8_t v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3778_; uint8_t v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; uint8_t v___y_3787_; lean_object* v___y_3795_; uint8_t v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v_a_3803_; lean_object* v___y_3808_; uint8_t v___y_3809_; uint8_t v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; uint8_t v___y_3838_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v_a_3850_; 
v_inheritedTraceOptions_3071_ = lean_ctor_get(v_toCold_2986_, 4);
lean_inc(v_snd_2980_);
lean_inc(v_fst_2979_);
v___f_3072_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3072_, 0, v_fst_2979_);
lean_closure_set(v___f_3072_, 1, v_snd_2980_);
v___x_3073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_3074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_2966_);
v___x_3075_ = l_Lean_Name_append(v___x_3074_, v_trace_2966_);
v___x_3076_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3071_, v_options_2985_, v___x_3075_);
lean_dec(v___x_3075_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3899_ = l_Lean_trace_profiler;
v___x_3900_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2985_, v___x_3899_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; 
lean_dec_ref(v___f_3072_);
lean_del_object(v___x_2982_);
v___x_3901_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2979_, v___f_2988_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
lean_object* v___x_3911_; lean_object* v_a_3913_; lean_object* v___y_3920_; lean_object* v___y_3923_; lean_object* v___y_3924_; uint8_t v___y_3925_; lean_object* v___y_3936_; lean_object* v___y_3952_; uint8_t v___y_3953_; lean_object* v_a_3968_; lean_object* v___f_3972_; lean_object* v___x_3973_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v_a_3977_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v_a_3994_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v_a_3999_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v_a_4005_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; uint8_t v___y_4024_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; uint8_t v___y_4042_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v_a_4052_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v_a_4059_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v_a_4071_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v_a_4076_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v_a_4081_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; uint8_t v___y_4095_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; uint8_t v___y_4126_; uint8_t v___y_4127_; lean_object* v___y_4132_; lean_object* v___y_4133_; uint8_t v___y_4134_; lean_object* v_a_4135_; 
v___x_3911_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3907_, v___x_2976_);
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
v___x_4164_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2987_, v___x_2984_, v_goals_2969_, v___x_3973_, v_a_2972_);
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
lean_dec(v_snd_2980_);
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
lean_dec_ref(v___y_3924_);
v___x_3926_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3923_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3923_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_dec_ref_known(v___x_3926_, 1);
v_a_3913_ = v_snd_2980_;
goto v___jp_3912_;
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_del_object(v___x_3904_);
lean_dec(v_snd_2980_);
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
lean_dec_ref(v___y_3923_);
lean_dec(v_snd_2980_);
v___y_3920_ = v___y_3924_;
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
lean_inc(v_snd_2980_);
v___x_3939_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3936_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_dec(v_a_3938_);
lean_dec(v_snd_2980_);
v___y_3920_ = v___x_3939_;
goto v___jp_3919_;
}
else
{
lean_object* v_a_3940_; uint8_t v___x_3941_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
v___x_3941_ = l_Lean_Exception_isInterrupt(v_a_3940_);
if (v___x_3941_ == 0)
{
uint8_t v___x_3942_; 
v___x_3942_ = l_Lean_Exception_isRuntime(v_a_3940_);
v___y_3923_ = v_a_3938_;
v___y_3924_ = v___x_3939_;
v___y_3925_ = v___x_3942_;
goto v___jp_3922_;
}
else
{
lean_dec(v_a_3940_);
v___y_3923_ = v_a_3938_;
v___y_3924_ = v___x_3939_;
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
lean_dec(v_snd_2980_);
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
lean_dec(v_snd_2980_);
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
v___x_3957_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3952_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
v___y_3953_ = v___x_2984_;
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
v___y_3953_ = v___x_2984_;
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
v___x_3989_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2987_, v___x_3073_, v_options_2985_, v___x_3076_, v___y_3976_, v___f_3972_, v___x_3988_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
lean_dec_ref(v___y_4023_);
v___x_4025_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4022_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_4022_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_dec_ref_known(v___x_4025_, 1);
v___y_3997_ = v___y_4020_;
v___y_3998_ = v___y_4021_;
v_a_3999_ = v_snd_2980_;
goto v___jp_3996_;
}
else
{
lean_object* v_a_4026_; 
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2980_);
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4025_, 1);
v___y_4003_ = v___y_4020_;
v___y_4004_ = v___y_4021_;
v_a_4005_ = v_a_4026_;
goto v___jp_4002_;
}
}
else
{
lean_dec_ref(v___y_4022_);
lean_dec(v_snd_2980_);
v___y_4014_ = v___y_4020_;
v___y_4015_ = v___y_4021_;
v___y_4016_ = v___y_4023_;
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
lean_inc(v_snd_2980_);
lean_inc(v_trace_2966_);
v___x_4033_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4028_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_dec(v_a_4032_);
lean_dec(v_snd_2980_);
v___y_4014_ = v___y_4029_;
v___y_4015_ = v___y_4030_;
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
v___y_4020_ = v___y_4029_;
v___y_4021_ = v___y_4030_;
v___y_4022_ = v_a_4032_;
v___y_4023_ = v___x_4033_;
v___y_4024_ = v___x_4036_;
goto v___jp_4019_;
}
else
{
lean_dec(v_a_4034_);
v___y_4020_ = v___y_4029_;
v___y_4021_ = v___y_4030_;
v___y_4022_ = v_a_4032_;
v___y_4023_ = v___x_4033_;
v___y_4024_ = v___x_4035_;
goto v___jp_4019_;
}
}
}
else
{
lean_object* v_a_4037_; 
lean_dec(v___y_4028_);
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_4037_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4031_, 1);
v___y_4003_ = v___y_4029_;
v___y_4004_ = v___y_4030_;
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
lean_dec(v___y_4039_);
lean_dec(v___x_3911_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_4044_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4045_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4044_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_4008_ = v___y_4040_;
v___y_4009_ = v___y_4041_;
v___y_4010_ = v___x_4045_;
goto v___jp_4007_;
}
else
{
lean_object* v___x_4046_; 
lean_inc(v_trace_2966_);
v___x_4046_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4039_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4048_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_a_4047_);
lean_dec_ref_known(v___x_4046_, 1);
v___x_4048_ = l_List_appendTR___redArg(v___x_3911_, v_a_4047_);
v___y_3992_ = v___y_4040_;
v___y_3993_ = v___y_4041_;
v_a_3994_ = v___x_4048_;
goto v___jp_3991_;
}
else
{
lean_dec(v___x_3911_);
v___y_4008_ = v___y_4040_;
v___y_4009_ = v___y_4041_;
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
v___y_4039_ = v___x_4054_;
v___y_4040_ = v___y_4050_;
v___y_4041_ = v___y_4051_;
v___y_4042_ = v___x_2984_;
goto v___jp_4038_;
}
else
{
uint8_t v___x_4055_; 
v___x_4055_ = l_List_isEmpty___redArg(v___x_3911_);
if (v___x_4055_ == 0)
{
v___y_4028_ = v___x_4054_;
v___y_4029_ = v___y_4050_;
v___y_4030_ = v___y_4051_;
goto v___jp_4027_;
}
else
{
v___y_4039_ = v___x_4054_;
v___y_4040_ = v___y_4050_;
v___y_4041_ = v___y_4051_;
v___y_4042_ = v___x_2984_;
goto v___jp_4038_;
}
}
}
v___jp_4056_:
{
lean_object* v___x_4060_; double v___x_4061_; double v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4060_ = lean_io_get_num_heartbeats();
v___x_4061_ = lean_float_of_nat(v___y_4057_);
v___x_4062_ = lean_float_of_nat(v___x_4060_);
v___x_4063_ = lean_box_float(v___x_4061_);
v___x_4064_ = lean_box_float(v___x_4062_);
v___x_4065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4063_);
lean_ctor_set(v___x_4065_, 1, v___x_4064_);
v___x_4066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4066_, 0, v_a_4059_);
lean_ctor_set(v___x_4066_, 1, v___x_4065_);
v___x_4067_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2987_, v___x_3073_, v_options_2985_, v___x_3076_, v___y_4058_, v___f_3972_, v___x_4066_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
return v___x_4067_;
}
v___jp_4068_:
{
lean_object* v___x_4072_; 
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v_a_4071_);
v___y_4057_ = v___y_4069_;
v___y_4058_ = v___y_4070_;
v_a_4059_ = v___x_4072_;
goto v___jp_4056_;
}
v___jp_4073_:
{
lean_object* v___x_4077_; 
v___x_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4077_, 0, v_a_4076_);
v___y_4057_ = v___y_4074_;
v___y_4058_ = v___y_4075_;
v_a_4059_ = v___x_4077_;
goto v___jp_4056_;
}
v___jp_4078_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = l_List_appendTR___redArg(v___x_3911_, v_fst_3906_);
v___x_4083_ = l_List_appendTR___redArg(v___x_4082_, v_a_4081_);
v___y_4074_ = v___y_4079_;
v___y_4075_ = v___y_4080_;
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
v___y_4079_ = v___y_4085_;
v___y_4080_ = v___y_4086_;
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
lean_dec_ref(v___y_4094_);
v___x_4096_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4093_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_4093_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_dec_ref_known(v___x_4096_, 1);
v___y_4079_ = v___y_4091_;
v___y_4080_ = v___y_4092_;
v_a_4081_ = v_snd_2980_;
goto v___jp_4078_;
}
else
{
lean_object* v_a_4097_; 
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2980_);
v_a_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_a_4097_);
lean_dec_ref_known(v___x_4096_, 1);
v___y_4069_ = v___y_4091_;
v___y_4070_ = v___y_4092_;
v_a_4071_ = v_a_4097_;
goto v___jp_4068_;
}
}
else
{
lean_dec_ref(v___y_4093_);
lean_dec(v_snd_2980_);
v___y_4085_ = v___y_4091_;
v___y_4086_ = v___y_4092_;
v___y_4087_ = v___y_4094_;
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
lean_inc(v_snd_2980_);
lean_inc(v_trace_2966_);
v___x_4104_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4100_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_dec(v_a_4103_);
lean_dec(v_snd_2980_);
v___y_4085_ = v___y_4099_;
v___y_4086_ = v___y_4101_;
v___y_4087_ = v___x_4104_;
goto v___jp_4084_;
}
else
{
lean_object* v_a_4105_; uint8_t v___x_4106_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_a_4105_);
v___x_4106_ = l_Lean_Exception_isInterrupt(v_a_4105_);
if (v___x_4106_ == 0)
{
uint8_t v___x_4107_; 
v___x_4107_ = l_Lean_Exception_isRuntime(v_a_4105_);
v___y_4091_ = v___y_4099_;
v___y_4092_ = v___y_4101_;
v___y_4093_ = v_a_4103_;
v___y_4094_ = v___x_4104_;
v___y_4095_ = v___x_4107_;
goto v___jp_4090_;
}
else
{
lean_dec(v_a_4105_);
v___y_4091_ = v___y_4099_;
v___y_4092_ = v___y_4101_;
v___y_4093_ = v_a_4103_;
v___y_4094_ = v___x_4104_;
v___y_4095_ = v___x_4106_;
goto v___jp_4090_;
}
}
}
else
{
lean_object* v_a_4108_; 
lean_dec(v___y_4100_);
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_4108_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4108_);
lean_dec_ref_known(v___x_4102_, 1);
v___y_4069_ = v___y_4099_;
v___y_4070_ = v___y_4101_;
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
v___y_4074_ = v___y_4110_;
v___y_4075_ = v___y_4111_;
v_a_4076_ = v_a_4113_;
goto v___jp_4073_;
}
else
{
lean_object* v_a_4114_; 
v_a_4114_ = lean_ctor_get(v___y_4112_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___y_4112_, 1);
v___y_4069_ = v___y_4110_;
v___y_4070_ = v___y_4111_;
v_a_4071_ = v_a_4114_;
goto v___jp_4068_;
}
}
v___jp_4115_:
{
lean_object* v___x_4119_; 
lean_inc(v_trace_2966_);
v___x_4119_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_4117_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4121_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v___x_4121_ = l_List_appendTR___redArg(v___x_3911_, v_a_4120_);
v___y_4074_ = v___y_4116_;
v___y_4075_ = v___y_4118_;
v_a_4076_ = v___x_4121_;
goto v___jp_4073_;
}
else
{
lean_dec(v___x_3911_);
v___y_4110_ = v___y_4116_;
v___y_4111_ = v___y_4118_;
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
if (v___y_4126_ == 0)
{
v___y_4116_ = v___y_4123_;
v___y_4117_ = v___y_4124_;
v___y_4118_ = v___y_4125_;
goto v___jp_4115_;
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_dec(v___y_4124_);
lean_dec(v___x_3911_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_4129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4130_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4129_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_4110_ = v___y_4123_;
v___y_4111_ = v___y_4125_;
v___y_4112_ = v___x_4130_;
goto v___jp_4109_;
}
}
else
{
v___y_4116_ = v___y_4123_;
v___y_4117_ = v___y_4124_;
v___y_4118_ = v___y_4125_;
goto v___jp_4115_;
}
}
else
{
v___y_4099_ = v___y_4123_;
v___y_4100_ = v___y_4124_;
v___y_4101_ = v___y_4125_;
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
v___y_4124_ = v___x_4137_;
v___y_4125_ = v___y_4133_;
v___y_4126_ = v___y_4134_;
v___y_4127_ = v___x_2984_;
goto v___jp_4122_;
}
else
{
uint8_t v___x_4138_; 
v___x_4138_ = l_List_isEmpty___redArg(v___x_3911_);
if (v___x_4138_ == 0)
{
v___y_4099_ = v___y_4132_;
v___y_4100_ = v___x_4137_;
v___y_4101_ = v___y_4133_;
goto v___jp_4098_;
}
else
{
v___y_4123_ = v___y_4132_;
v___y_4124_ = v___x_4137_;
v___y_4125_ = v___y_4133_;
v___y_4126_ = v___y_4134_;
v___y_4127_ = v___x_2984_;
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
v___x_4143_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2985_, v___x_4142_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4144_ = lean_io_mono_nanos_now();
v___x_4145_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2987_, v___x_2984_, v_goals_2969_, v___x_3973_, v_a_2972_);
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
lean_dec(v_snd_2980_);
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
v___x_4151_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2987_, v___x_2984_, v_goals_2969_, v___x_3973_, v_a_2972_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4153_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4153_ = l_List_reverse___redArg(v_a_4152_);
v___y_4132_ = v___x_4150_;
v___y_4133_ = v_a_4141_;
v___y_4134_ = v___x_4143_;
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
v___y_4132_ = v___x_4150_;
v___y_4133_ = v_a_4141_;
v___y_4134_ = v___x_4143_;
v_a_4135_ = v_a_4154_;
goto v___jp_4131_;
}
else
{
lean_object* v_a_4155_; 
lean_dec(v___x_3911_);
lean_dec(v_fst_3906_);
lean_dec(v_snd_2980_);
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
lean_dec(v_snd_2980_);
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
lean_dec(v_snd_2980_);
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
v___x_3082_ = lean_float_of_nat(v___y_3078_);
v___x_3083_ = lean_float_of_nat(v___x_3081_);
v___x_3084_ = lean_box_float(v___x_3082_);
v___x_3085_ = lean_box_float(v___x_3083_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 1, v___x_3085_);
lean_ctor_set(v___x_2982_, 0, v___x_3084_);
v___x_3087_ = v___x_2982_;
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
v___x_3089_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2987_, v___x_3073_, v_options_2985_, v___x_3076_, v___y_3079_, v___f_3072_, v___x_3088_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
lean_dec_ref(v___y_3120_);
v___x_3125_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3119_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3119_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_dec_ref_known(v___x_3125_, 1);
v___y_3102_ = v___y_3118_;
v___y_3103_ = v___y_3121_;
v___y_3104_ = v___y_3122_;
v___y_3105_ = v___y_3123_;
v_a_3106_ = v_snd_2980_;
goto v___jp_3101_;
}
else
{
lean_object* v_a_3126_; 
lean_dec(v___y_3121_);
lean_dec(v___y_3118_);
lean_dec(v_snd_2980_);
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
lean_dec_ref(v___y_3119_);
lean_dec(v_snd_2980_);
v___y_3110_ = v___y_3118_;
v___y_3111_ = v___y_3121_;
v___y_3112_ = v___y_3122_;
v___y_3113_ = v___y_3123_;
v___y_3114_ = v___y_3120_;
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
lean_inc(v_snd_2980_);
lean_inc(v_trace_2966_);
v___x_3135_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3131_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_dec(v_a_3134_);
lean_dec(v_snd_2980_);
v___y_3110_ = v___y_3128_;
v___y_3111_ = v___y_3129_;
v___y_3112_ = v___y_3130_;
v___y_3113_ = v___y_3132_;
v___y_3114_ = v___x_3135_;
goto v___jp_3109_;
}
else
{
lean_object* v_a_3136_; uint8_t v___x_3137_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
v___x_3137_ = l_Lean_Exception_isInterrupt(v_a_3136_);
if (v___x_3137_ == 0)
{
uint8_t v___x_3138_; 
v___x_3138_ = l_Lean_Exception_isRuntime(v_a_3136_);
v___y_3118_ = v___y_3128_;
v___y_3119_ = v_a_3134_;
v___y_3120_ = v___x_3135_;
v___y_3121_ = v___y_3129_;
v___y_3122_ = v___y_3130_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___x_3138_;
goto v___jp_3117_;
}
else
{
lean_dec(v_a_3136_);
v___y_3118_ = v___y_3128_;
v___y_3119_ = v_a_3134_;
v___y_3120_ = v___x_3135_;
v___y_3121_ = v___y_3129_;
v___y_3122_ = v___y_3130_;
v___y_3123_ = v___y_3132_;
v___y_3124_ = v___x_3137_;
goto v___jp_3117_;
}
}
}
else
{
lean_object* v_a_3139_; 
lean_dec(v___y_3131_);
lean_dec(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3139_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___x_3133_, 1);
v___y_3092_ = v___y_3130_;
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
v___x_3155_ = lean_float_of_nat(v___y_3150_);
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
v___x_3164_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2987_, v___x_3073_, v_options_2985_, v___y_3148_, v___y_3147_, v___y_3149_, v___x_3163_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
v___y_3147_ = v___y_3166_;
v___y_3148_ = v___y_3167_;
v___y_3149_ = v___y_3168_;
v___y_3150_ = v___y_3169_;
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
v___y_3147_ = v___y_3175_;
v___y_3148_ = v___y_3176_;
v___y_3149_ = v___y_3177_;
v___y_3150_ = v___y_3178_;
v___y_3151_ = v___y_3179_;
v___y_3152_ = v___y_3180_;
v_a_3153_ = v___x_3182_;
goto v___jp_3146_;
}
v___jp_3183_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = l_List_appendTR___redArg(v___y_3184_, v___y_3188_);
v___x_3194_ = l_List_appendTR___redArg(v___x_3193_, v_a_3192_);
v___y_3175_ = v___y_3185_;
v___y_3176_ = v___y_3186_;
v___y_3177_ = v___y_3187_;
v___y_3178_ = v___y_3189_;
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
v___y_3186_ = v___y_3198_;
v___y_3187_ = v___y_3200_;
v___y_3188_ = v___y_3199_;
v___y_3189_ = v___y_3201_;
v___y_3190_ = v___y_3202_;
v___y_3191_ = v___y_3203_;
v_a_3192_ = v_a_3205_;
goto v___jp_3183_;
}
else
{
lean_object* v_a_3206_; 
lean_dec(v___y_3199_);
lean_dec(v___y_3196_);
v_a_3206_ = lean_ctor_get(v___y_3204_, 0);
lean_inc(v_a_3206_);
lean_dec_ref_known(v___y_3204_, 1);
v___y_3166_ = v___y_3197_;
v___y_3167_ = v___y_3198_;
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
lean_dec_ref(v___y_3210_);
v___x_3219_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3208_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3208_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_dec_ref_known(v___x_3219_, 1);
v___y_3184_ = v___y_3209_;
v___y_3185_ = v___y_3211_;
v___y_3186_ = v___y_3212_;
v___y_3187_ = v___y_3214_;
v___y_3188_ = v___y_3213_;
v___y_3189_ = v___y_3215_;
v___y_3190_ = v___y_3216_;
v___y_3191_ = v___y_3217_;
v_a_3192_ = v_snd_2980_;
goto v___jp_3183_;
}
else
{
lean_object* v_a_3220_; 
lean_dec(v___y_3213_);
lean_dec(v___y_3209_);
lean_dec(v_snd_2980_);
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v___y_3166_ = v___y_3211_;
v___y_3167_ = v___y_3212_;
v___y_3168_ = v___y_3214_;
v___y_3169_ = v___y_3215_;
v___y_3170_ = v___y_3216_;
v___y_3171_ = v___y_3217_;
v_a_3172_ = v_a_3220_;
goto v___jp_3165_;
}
}
else
{
lean_dec_ref(v___y_3208_);
lean_dec(v_snd_2980_);
v___y_3196_ = v___y_3209_;
v___y_3197_ = v___y_3211_;
v___y_3198_ = v___y_3212_;
v___y_3199_ = v___y_3213_;
v___y_3200_ = v___y_3214_;
v___y_3201_ = v___y_3215_;
v___y_3202_ = v___y_3216_;
v___y_3203_ = v___y_3217_;
v___y_3204_ = v___y_3210_;
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
lean_inc(v_snd_2980_);
lean_inc(v_trace_2966_);
v___x_3233_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3224_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_dec(v_a_3232_);
lean_dec(v_snd_2980_);
v___y_3196_ = v___y_3222_;
v___y_3197_ = v___y_3223_;
v___y_3198_ = v___y_3225_;
v___y_3199_ = v___y_3227_;
v___y_3200_ = v___y_3226_;
v___y_3201_ = v___y_3228_;
v___y_3202_ = v___y_3229_;
v___y_3203_ = v___y_3230_;
v___y_3204_ = v___x_3233_;
goto v___jp_3195_;
}
else
{
lean_object* v_a_3234_; uint8_t v___x_3235_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
lean_inc(v_a_3234_);
v___x_3235_ = l_Lean_Exception_isInterrupt(v_a_3234_);
if (v___x_3235_ == 0)
{
uint8_t v___x_3236_; 
v___x_3236_ = l_Lean_Exception_isRuntime(v_a_3234_);
v___y_3208_ = v_a_3232_;
v___y_3209_ = v___y_3222_;
v___y_3210_ = v___x_3233_;
v___y_3211_ = v___y_3223_;
v___y_3212_ = v___y_3225_;
v___y_3213_ = v___y_3227_;
v___y_3214_ = v___y_3226_;
v___y_3215_ = v___y_3228_;
v___y_3216_ = v___y_3229_;
v___y_3217_ = v___y_3230_;
v___y_3218_ = v___x_3236_;
goto v___jp_3207_;
}
else
{
lean_dec(v_a_3234_);
v___y_3208_ = v_a_3232_;
v___y_3209_ = v___y_3222_;
v___y_3210_ = v___x_3233_;
v___y_3211_ = v___y_3223_;
v___y_3212_ = v___y_3225_;
v___y_3213_ = v___y_3227_;
v___y_3214_ = v___y_3226_;
v___y_3215_ = v___y_3228_;
v___y_3216_ = v___y_3229_;
v___y_3217_ = v___y_3230_;
v___y_3218_ = v___x_3235_;
goto v___jp_3207_;
}
}
}
else
{
lean_object* v_a_3237_; 
lean_dec(v___y_3227_);
lean_dec(v___y_3224_);
lean_dec(v___y_3222_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3237_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3231_, 1);
v___y_3166_ = v___y_3223_;
v___y_3167_ = v___y_3225_;
v___y_3168_ = v___y_3226_;
v___y_3169_ = v___y_3228_;
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
v___y_3175_ = v___y_3239_;
v___y_3176_ = v___y_3240_;
v___y_3177_ = v___y_3241_;
v___y_3178_ = v___y_3242_;
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
v___y_3166_ = v___y_3239_;
v___y_3167_ = v___y_3240_;
v___y_3168_ = v___y_3241_;
v___y_3169_ = v___y_3242_;
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
v___x_3259_ = l_List_isEmpty___redArg(v___y_3254_);
lean_dec(v___y_3254_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec(v___y_3251_);
lean_dec(v___y_3249_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3260_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3261_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3260_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3239_ = v___y_3250_;
v___y_3240_ = v___y_3252_;
v___y_3241_ = v___y_3253_;
v___y_3242_ = v___y_3255_;
v___y_3243_ = v___y_3256_;
v___y_3244_ = v___y_3257_;
v___y_3245_ = v___x_3261_;
goto v___jp_3238_;
}
else
{
lean_object* v___x_3262_; 
lean_inc(v_trace_2966_);
v___x_3262_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3251_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3264_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3264_ = l_List_appendTR___redArg(v___y_3249_, v_a_3263_);
v___y_3175_ = v___y_3250_;
v___y_3176_ = v___y_3252_;
v___y_3177_ = v___y_3253_;
v___y_3178_ = v___y_3255_;
v___y_3179_ = v___y_3256_;
v___y_3180_ = v___y_3257_;
v_a_3181_ = v___x_3264_;
goto v___jp_3174_;
}
else
{
lean_dec(v___y_3249_);
v___y_3239_ = v___y_3250_;
v___y_3240_ = v___y_3252_;
v___y_3241_ = v___y_3253_;
v___y_3242_ = v___y_3255_;
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
v___y_3224_ = v___y_3251_;
v___y_3225_ = v___y_3252_;
v___y_3226_ = v___y_3253_;
v___y_3227_ = v___y_3254_;
v___y_3228_ = v___y_3255_;
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
v___y_3251_ = v___x_3276_;
v___y_3252_ = v___y_3268_;
v___y_3253_ = v___y_3270_;
v___y_3254_ = v___y_3269_;
v___y_3255_ = v___y_3271_;
v___y_3256_ = v___y_3272_;
v___y_3257_ = v___y_3273_;
v___y_3258_ = v___x_2984_;
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
v___y_3224_ = v___x_3276_;
v___y_3225_ = v___y_3268_;
v___y_3226_ = v___y_3270_;
v___y_3227_ = v___y_3269_;
v___y_3228_ = v___y_3271_;
v___y_3229_ = v___y_3272_;
v___y_3230_ = v___y_3273_;
goto v___jp_3221_;
}
else
{
v___y_3249_ = v___y_3266_;
v___y_3250_ = v___y_3267_;
v___y_3251_ = v___x_3276_;
v___y_3252_ = v___y_3268_;
v___y_3253_ = v___y_3270_;
v___y_3254_ = v___y_3269_;
v___y_3255_ = v___y_3271_;
v___y_3256_ = v___y_3272_;
v___y_3257_ = v___y_3273_;
v___y_3258_ = v___x_2984_;
goto v___jp_3248_;
}
}
}
v___jp_3278_:
{
lean_object* v___x_3286_; double v___x_3287_; double v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3286_ = lean_io_get_num_heartbeats();
v___x_3287_ = lean_float_of_nat(v___y_3279_);
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
v___x_3293_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2987_, v___x_3073_, v_options_2985_, v___y_3281_, v___y_3280_, v___y_3282_, v___x_3292_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
v___y_3280_ = v___y_3296_;
v___y_3281_ = v___y_3297_;
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
v___y_3280_ = v___y_3305_;
v___y_3281_ = v___y_3306_;
v___y_3282_ = v___y_3307_;
v___y_3283_ = v___y_3308_;
v___y_3284_ = v___y_3309_;
v_a_3285_ = v___x_3311_;
goto v___jp_3278_;
}
v___jp_3312_:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3322_ = l_List_appendTR___redArg(v___y_3313_, v___y_3318_);
v___x_3323_ = l_List_appendTR___redArg(v___x_3322_, v_a_3321_);
v___y_3304_ = v___y_3314_;
v___y_3305_ = v___y_3315_;
v___y_3306_ = v___y_3316_;
v___y_3307_ = v___y_3317_;
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
v___y_3316_ = v___y_3328_;
v___y_3317_ = v___y_3330_;
v___y_3318_ = v___y_3329_;
v___y_3319_ = v___y_3331_;
v___y_3320_ = v___y_3332_;
v_a_3321_ = v_a_3334_;
goto v___jp_3312_;
}
else
{
lean_object* v_a_3335_; 
lean_dec(v___y_3329_);
lean_dec(v___y_3325_);
v_a_3335_ = lean_ctor_get(v___y_3333_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___y_3333_, 1);
v___y_3295_ = v___y_3326_;
v___y_3296_ = v___y_3327_;
v___y_3297_ = v___y_3328_;
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
lean_dec_ref(v___y_3341_);
v___x_3348_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3340_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3340_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_dec_ref_known(v___x_3348_, 1);
v___y_3313_ = v___y_3337_;
v___y_3314_ = v___y_3338_;
v___y_3315_ = v___y_3339_;
v___y_3316_ = v___y_3342_;
v___y_3317_ = v___y_3344_;
v___y_3318_ = v___y_3343_;
v___y_3319_ = v___y_3345_;
v___y_3320_ = v___y_3346_;
v_a_3321_ = v_snd_2980_;
goto v___jp_3312_;
}
else
{
lean_object* v_a_3349_; 
lean_dec(v___y_3343_);
lean_dec(v___y_3337_);
lean_dec(v_snd_2980_);
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3348_, 1);
v___y_3295_ = v___y_3338_;
v___y_3296_ = v___y_3339_;
v___y_3297_ = v___y_3342_;
v___y_3298_ = v___y_3344_;
v___y_3299_ = v___y_3345_;
v___y_3300_ = v___y_3346_;
v_a_3301_ = v_a_3349_;
goto v___jp_3294_;
}
}
else
{
lean_dec_ref(v___y_3340_);
lean_dec(v_snd_2980_);
v___y_3325_ = v___y_3337_;
v___y_3326_ = v___y_3338_;
v___y_3327_ = v___y_3339_;
v___y_3328_ = v___y_3342_;
v___y_3329_ = v___y_3343_;
v___y_3330_ = v___y_3344_;
v___y_3331_ = v___y_3345_;
v___y_3332_ = v___y_3346_;
v___y_3333_ = v___y_3341_;
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
lean_inc(v_snd_2980_);
lean_inc(v_trace_2966_);
v___x_3362_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3354_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_dec(v_a_3361_);
lean_dec(v_snd_2980_);
v___y_3325_ = v___y_3351_;
v___y_3326_ = v___y_3352_;
v___y_3327_ = v___y_3353_;
v___y_3328_ = v___y_3355_;
v___y_3329_ = v___y_3357_;
v___y_3330_ = v___y_3356_;
v___y_3331_ = v___y_3358_;
v___y_3332_ = v___y_3359_;
v___y_3333_ = v___x_3362_;
goto v___jp_3324_;
}
else
{
lean_object* v_a_3363_; uint8_t v___x_3364_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
v___x_3364_ = l_Lean_Exception_isInterrupt(v_a_3363_);
if (v___x_3364_ == 0)
{
uint8_t v___x_3365_; 
v___x_3365_ = l_Lean_Exception_isRuntime(v_a_3363_);
v___y_3337_ = v___y_3351_;
v___y_3338_ = v___y_3352_;
v___y_3339_ = v___y_3353_;
v___y_3340_ = v_a_3361_;
v___y_3341_ = v___x_3362_;
v___y_3342_ = v___y_3355_;
v___y_3343_ = v___y_3357_;
v___y_3344_ = v___y_3356_;
v___y_3345_ = v___y_3358_;
v___y_3346_ = v___y_3359_;
v___y_3347_ = v___x_3365_;
goto v___jp_3336_;
}
else
{
lean_dec(v_a_3363_);
v___y_3337_ = v___y_3351_;
v___y_3338_ = v___y_3352_;
v___y_3339_ = v___y_3353_;
v___y_3340_ = v_a_3361_;
v___y_3341_ = v___x_3362_;
v___y_3342_ = v___y_3355_;
v___y_3343_ = v___y_3357_;
v___y_3344_ = v___y_3356_;
v___y_3345_ = v___y_3358_;
v___y_3346_ = v___y_3359_;
v___y_3347_ = v___x_3364_;
goto v___jp_3336_;
}
}
}
else
{
lean_object* v_a_3366_; 
lean_dec(v___y_3357_);
lean_dec(v___y_3354_);
lean_dec(v___y_3351_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3366_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3366_);
lean_dec_ref_known(v___x_3360_, 1);
v___y_3295_ = v___y_3352_;
v___y_3296_ = v___y_3353_;
v___y_3297_ = v___y_3355_;
v___y_3298_ = v___y_3356_;
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
v___y_3305_ = v___y_3369_;
v___y_3306_ = v___y_3370_;
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
v___y_3296_ = v___y_3369_;
v___y_3297_ = v___y_3370_;
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
v___x_3386_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3381_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3388_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3388_ = l_List_appendTR___redArg(v___y_3378_, v_a_3387_);
v___y_3304_ = v___y_3379_;
v___y_3305_ = v___y_3380_;
v___y_3306_ = v___y_3382_;
v___y_3307_ = v___y_3383_;
v___y_3308_ = v___y_3384_;
v___y_3309_ = v___y_3385_;
v_a_3310_ = v___x_3388_;
goto v___jp_3303_;
}
else
{
lean_dec(v___y_3378_);
v___y_3368_ = v___y_3379_;
v___y_3369_ = v___y_3380_;
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
v___x_3401_ = l_List_isEmpty___redArg(v___y_3397_);
lean_dec(v___y_3397_);
if (v___x_3401_ == 0)
{
if (v___y_3390_ == 0)
{
v___y_3378_ = v___y_3391_;
v___y_3379_ = v___y_3392_;
v___y_3380_ = v___y_3393_;
v___y_3381_ = v___y_3394_;
v___y_3382_ = v___y_3395_;
v___y_3383_ = v___y_3396_;
v___y_3384_ = v___y_3398_;
v___y_3385_ = v___y_3399_;
goto v___jp_3377_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec(v___y_3394_);
lean_dec(v___y_3391_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3403_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3402_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3368_ = v___y_3392_;
v___y_3369_ = v___y_3393_;
v___y_3370_ = v___y_3395_;
v___y_3371_ = v___y_3396_;
v___y_3372_ = v___y_3398_;
v___y_3373_ = v___y_3399_;
v___y_3374_ = v___x_3403_;
goto v___jp_3367_;
}
}
else
{
v___y_3378_ = v___y_3391_;
v___y_3379_ = v___y_3392_;
v___y_3380_ = v___y_3393_;
v___y_3381_ = v___y_3394_;
v___y_3382_ = v___y_3395_;
v___y_3383_ = v___y_3396_;
v___y_3384_ = v___y_3398_;
v___y_3385_ = v___y_3399_;
goto v___jp_3377_;
}
}
else
{
v___y_3351_ = v___y_3391_;
v___y_3352_ = v___y_3392_;
v___y_3353_ = v___y_3393_;
v___y_3354_ = v___y_3394_;
v___y_3355_ = v___y_3395_;
v___y_3356_ = v___y_3396_;
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
lean_inc(v___y_3406_);
v___x_3416_ = l_List_appendTR___redArg(v_a_3414_, v___y_3406_);
if (v_commitIndependentGoals_3415_ == 0)
{
v___y_3390_ = v___y_3405_;
v___y_3391_ = v___y_3406_;
v___y_3392_ = v___y_3407_;
v___y_3393_ = v___y_3408_;
v___y_3394_ = v___x_3416_;
v___y_3395_ = v___y_3409_;
v___y_3396_ = v___y_3411_;
v___y_3397_ = v___y_3410_;
v___y_3398_ = v___y_3412_;
v___y_3399_ = v___y_3413_;
v___y_3400_ = v___x_2984_;
goto v___jp_3389_;
}
else
{
uint8_t v___x_3417_; 
v___x_3417_ = l_List_isEmpty___redArg(v___y_3406_);
if (v___x_3417_ == 0)
{
v___y_3351_ = v___y_3406_;
v___y_3352_ = v___y_3407_;
v___y_3353_ = v___y_3408_;
v___y_3354_ = v___x_3416_;
v___y_3355_ = v___y_3409_;
v___y_3356_ = v___y_3411_;
v___y_3357_ = v___y_3410_;
v___y_3358_ = v___y_3412_;
v___y_3359_ = v___y_3413_;
goto v___jp_3350_;
}
else
{
v___y_3390_ = v___y_3405_;
v___y_3391_ = v___y_3406_;
v___y_3392_ = v___y_3407_;
v___y_3393_ = v___y_3408_;
v___y_3394_ = v___x_3416_;
v___y_3395_ = v___y_3409_;
v___y_3396_ = v___y_3411_;
v___y_3397_ = v___y_3410_;
v___y_3398_ = v___y_3412_;
v___y_3399_ = v___y_3413_;
v___y_3400_ = v___x_2984_;
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
if (v___y_3419_ == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref_known(v___x_3427_, 1);
v___x_3429_ = lean_io_mono_nanos_now();
v___x_3430_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3419_, v___x_2984_, v_goals_2969_, v___y_3421_, v_a_2972_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3432_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref_known(v___x_3430_, 1);
v___x_3432_ = l_List_reverse___redArg(v_a_3431_);
v___y_3266_ = v___y_3420_;
v___y_3267_ = v_a_3428_;
v___y_3268_ = v___y_3422_;
v___y_3269_ = v___y_3423_;
v___y_3270_ = v___y_3424_;
v___y_3271_ = v___x_3429_;
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
v___y_3266_ = v___y_3420_;
v___y_3267_ = v_a_3428_;
v___y_3268_ = v___y_3422_;
v___y_3269_ = v___y_3423_;
v___y_3270_ = v___y_3424_;
v___y_3271_ = v___x_3429_;
v___y_3272_ = v___y_3425_;
v___y_3273_ = v___y_3426_;
v_a_3274_ = v_a_3433_;
goto v___jp_3265_;
}
else
{
lean_object* v_a_3434_; 
lean_dec(v___y_3423_);
lean_dec(v___y_3420_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3434_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3430_, 1);
v___y_3166_ = v_a_3428_;
v___y_3167_ = v___y_3422_;
v___y_3168_ = v___y_3424_;
v___y_3169_ = v___x_3429_;
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
v___x_3437_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_3419_, v___x_2984_, v_goals_2969_, v___y_3421_, v_a_2972_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3439_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v___x_3439_ = l_List_reverse___redArg(v_a_3438_);
v___y_3405_ = v___y_3419_;
v___y_3406_ = v___y_3420_;
v___y_3407_ = v___x_3436_;
v___y_3408_ = v_a_3435_;
v___y_3409_ = v___y_3422_;
v___y_3410_ = v___y_3423_;
v___y_3411_ = v___y_3424_;
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
v___y_3407_ = v___x_3436_;
v___y_3408_ = v_a_3435_;
v___y_3409_ = v___y_3422_;
v___y_3410_ = v___y_3423_;
v___y_3411_ = v___y_3424_;
v___y_3412_ = v___y_3425_;
v___y_3413_ = v___y_3426_;
v_a_3414_ = v_a_3440_;
goto v___jp_3404_;
}
else
{
lean_object* v_a_3441_; 
lean_dec(v___y_3423_);
lean_dec(v___y_3420_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3441_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v___x_3437_, 1);
v___y_3295_ = v___x_3436_;
v___y_3296_ = v_a_3435_;
v___y_3297_ = v___y_3422_;
v___y_3298_ = v___y_3424_;
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
lean_dec(v___y_3423_);
lean_dec(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec(v_snd_2980_);
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
lean_dec(v_snd_2980_);
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
v___x_3453_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3446_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
v___y_3130_ = v___y_3447_;
v___y_3131_ = v___y_3446_;
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
v___y_3449_ = v___x_2984_;
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
v___y_3130_ = v___y_3459_;
v___y_3131_ = v___x_3463_;
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
v___y_3449_ = v___x_2984_;
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
v___x_3479_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2987_, v___x_3073_, v_options_2985_, v___x_3076_, v___y_3467_, v___f_3072_, v___x_3478_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
v___x_3496_ = l_List_appendTR___redArg(v___y_3493_, v___y_3491_);
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
v___y_3492_ = v___y_3500_;
v___y_3493_ = v___y_3501_;
v___y_3494_ = v___y_3502_;
v_a_3495_ = v_a_3504_;
goto v___jp_3490_;
}
else
{
lean_object* v_a_3505_; 
lean_dec(v___y_3501_);
lean_dec(v___y_3499_);
v_a_3505_ = lean_ctor_get(v___y_3503_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___y_3503_, 1);
v___y_3481_ = v___y_3500_;
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
v___x_3514_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3511_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3511_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_dec_ref_known(v___x_3514_, 1);
v___y_3491_ = v___y_3507_;
v___y_3492_ = v___y_3508_;
v___y_3493_ = v___y_3510_;
v___y_3494_ = v___y_3512_;
v_a_3495_ = v_snd_2980_;
goto v___jp_3490_;
}
else
{
lean_object* v_a_3515_; 
lean_dec(v___y_3510_);
lean_dec(v___y_3507_);
lean_dec(v_snd_2980_);
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___y_3481_ = v___y_3508_;
v___y_3482_ = v___y_3512_;
v_a_3483_ = v_a_3515_;
goto v___jp_3480_;
}
}
else
{
lean_dec_ref(v___y_3511_);
lean_dec(v_snd_2980_);
v___y_3499_ = v___y_3507_;
v___y_3500_ = v___y_3508_;
v___y_3501_ = v___y_3510_;
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
lean_inc(v_snd_2980_);
lean_inc(v_trace_2966_);
v___x_3524_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3518_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_dec(v_a_3523_);
lean_dec(v_snd_2980_);
v___y_3499_ = v___y_3517_;
v___y_3500_ = v___y_3519_;
v___y_3501_ = v___y_3520_;
v___y_3502_ = v___y_3521_;
v___y_3503_ = v___x_3524_;
goto v___jp_3498_;
}
else
{
lean_object* v_a_3525_; uint8_t v___x_3526_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
v___x_3526_ = l_Lean_Exception_isInterrupt(v_a_3525_);
if (v___x_3526_ == 0)
{
uint8_t v___x_3527_; 
v___x_3527_ = l_Lean_Exception_isRuntime(v_a_3525_);
v___y_3507_ = v___y_3517_;
v___y_3508_ = v___y_3519_;
v___y_3509_ = v___x_3524_;
v___y_3510_ = v___y_3520_;
v___y_3511_ = v_a_3523_;
v___y_3512_ = v___y_3521_;
v___y_3513_ = v___x_3527_;
goto v___jp_3506_;
}
else
{
lean_dec(v_a_3525_);
v___y_3507_ = v___y_3517_;
v___y_3508_ = v___y_3519_;
v___y_3509_ = v___x_3524_;
v___y_3510_ = v___y_3520_;
v___y_3511_ = v_a_3523_;
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
lean_dec(v_snd_2980_);
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
v___x_3544_ = lean_float_of_nat(v___y_3540_);
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
v___x_3550_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2987_, v___x_3073_, v_options_2985_, v___y_3538_, v___y_3537_, v___y_3536_, v___x_3549_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3530_ = v___y_3539_;
v___y_3531_ = v___y_3541_;
v___y_3532_ = v___x_3550_;
goto v___jp_3529_;
}
v___jp_3551_:
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3559_, 0, v_a_3558_);
v___y_3536_ = v___y_3554_;
v___y_3537_ = v___y_3553_;
v___y_3538_ = v___y_3552_;
v___y_3539_ = v___y_3556_;
v___y_3540_ = v___y_3555_;
v___y_3541_ = v___y_3557_;
v_a_3542_ = v___x_3559_;
goto v___jp_3535_;
}
v___jp_3560_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = l_List_appendTR___redArg(v___y_3567_, v___y_3561_);
v___x_3571_ = l_List_appendTR___redArg(v___x_3570_, v_a_3569_);
v___y_3552_ = v___y_3564_;
v___y_3553_ = v___y_3563_;
v___y_3554_ = v___y_3562_;
v___y_3555_ = v___y_3566_;
v___y_3556_ = v___y_3565_;
v___y_3557_ = v___y_3568_;
v_a_3558_ = v___x_3571_;
goto v___jp_3551_;
}
v___jp_3572_:
{
lean_object* v___x_3580_; 
v___x_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3580_, 0, v_a_3579_);
v___y_3536_ = v___y_3575_;
v___y_3537_ = v___y_3574_;
v___y_3538_ = v___y_3573_;
v___y_3539_ = v___y_3577_;
v___y_3540_ = v___y_3576_;
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
v___y_3552_ = v___y_3584_;
v___y_3553_ = v___y_3583_;
v___y_3554_ = v___y_3582_;
v___y_3555_ = v___y_3586_;
v___y_3556_ = v___y_3585_;
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
v___y_3573_ = v___y_3584_;
v___y_3574_ = v___y_3583_;
v___y_3575_ = v___y_3582_;
v___y_3576_ = v___y_3586_;
v___y_3577_ = v___y_3585_;
v___y_3578_ = v___y_3587_;
v_a_3579_ = v_a_3590_;
goto v___jp_3572_;
}
}
v___jp_3591_:
{
lean_object* v___x_3600_; 
lean_inc(v_trace_2966_);
v___x_3600_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3598_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3602_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v___x_3602_ = l_List_appendTR___redArg(v___y_3597_, v_a_3601_);
v___y_3552_ = v___y_3594_;
v___y_3553_ = v___y_3593_;
v___y_3554_ = v___y_3592_;
v___y_3555_ = v___y_3596_;
v___y_3556_ = v___y_3595_;
v___y_3557_ = v___y_3599_;
v_a_3558_ = v___x_3602_;
goto v___jp_3551_;
}
else
{
lean_dec(v___y_3597_);
v___y_3582_ = v___y_3592_;
v___y_3583_ = v___y_3593_;
v___y_3584_ = v___y_3594_;
v___y_3585_ = v___y_3595_;
v___y_3586_ = v___y_3596_;
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
v___y_3562_ = v___y_3607_;
v___y_3563_ = v___y_3606_;
v___y_3564_ = v___y_3605_;
v___y_3565_ = v___y_3609_;
v___y_3566_ = v___y_3608_;
v___y_3567_ = v___y_3610_;
v___y_3568_ = v___y_3611_;
v_a_3569_ = v_a_3613_;
goto v___jp_3560_;
}
else
{
lean_object* v_a_3614_; 
lean_dec(v___y_3610_);
lean_dec(v___y_3604_);
v_a_3614_ = lean_ctor_get(v___y_3612_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___y_3612_, 1);
v___y_3573_ = v___y_3605_;
v___y_3574_ = v___y_3606_;
v___y_3575_ = v___y_3607_;
v___y_3576_ = v___y_3608_;
v___y_3577_ = v___y_3609_;
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
lean_dec_ref(v___y_3620_);
v___x_3627_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3624_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3624_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_dec_ref_known(v___x_3627_, 1);
v___y_3561_ = v___y_3616_;
v___y_3562_ = v___y_3619_;
v___y_3563_ = v___y_3618_;
v___y_3564_ = v___y_3617_;
v___y_3565_ = v___y_3622_;
v___y_3566_ = v___y_3621_;
v___y_3567_ = v___y_3623_;
v___y_3568_ = v___y_3625_;
v_a_3569_ = v_snd_2980_;
goto v___jp_3560_;
}
else
{
lean_object* v_a_3628_; 
lean_dec(v___y_3623_);
lean_dec(v___y_3616_);
lean_dec(v_snd_2980_);
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3628_);
lean_dec_ref_known(v___x_3627_, 1);
v___y_3573_ = v___y_3617_;
v___y_3574_ = v___y_3618_;
v___y_3575_ = v___y_3619_;
v___y_3576_ = v___y_3621_;
v___y_3577_ = v___y_3622_;
v___y_3578_ = v___y_3625_;
v_a_3579_ = v_a_3628_;
goto v___jp_3572_;
}
}
else
{
lean_dec_ref(v___y_3624_);
lean_dec(v_snd_2980_);
v___y_3604_ = v___y_3616_;
v___y_3605_ = v___y_3617_;
v___y_3606_ = v___y_3618_;
v___y_3607_ = v___y_3619_;
v___y_3608_ = v___y_3621_;
v___y_3609_ = v___y_3622_;
v___y_3610_ = v___y_3623_;
v___y_3611_ = v___y_3625_;
v___y_3612_ = v___y_3620_;
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
lean_inc(v_snd_2980_);
lean_inc(v_trace_2966_);
v___x_3641_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3637_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_dec(v_a_3640_);
lean_dec(v_snd_2980_);
v___y_3604_ = v___y_3630_;
v___y_3605_ = v___y_3633_;
v___y_3606_ = v___y_3632_;
v___y_3607_ = v___y_3631_;
v___y_3608_ = v___y_3635_;
v___y_3609_ = v___y_3634_;
v___y_3610_ = v___y_3636_;
v___y_3611_ = v___y_3638_;
v___y_3612_ = v___x_3641_;
goto v___jp_3603_;
}
else
{
lean_object* v_a_3642_; uint8_t v___x_3643_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
v___x_3643_ = l_Lean_Exception_isInterrupt(v_a_3642_);
if (v___x_3643_ == 0)
{
uint8_t v___x_3644_; 
v___x_3644_ = l_Lean_Exception_isRuntime(v_a_3642_);
v___y_3616_ = v___y_3630_;
v___y_3617_ = v___y_3633_;
v___y_3618_ = v___y_3632_;
v___y_3619_ = v___y_3631_;
v___y_3620_ = v___x_3641_;
v___y_3621_ = v___y_3635_;
v___y_3622_ = v___y_3634_;
v___y_3623_ = v___y_3636_;
v___y_3624_ = v_a_3640_;
v___y_3625_ = v___y_3638_;
v___y_3626_ = v___x_3644_;
goto v___jp_3615_;
}
else
{
lean_dec(v_a_3642_);
v___y_3616_ = v___y_3630_;
v___y_3617_ = v___y_3633_;
v___y_3618_ = v___y_3632_;
v___y_3619_ = v___y_3631_;
v___y_3620_ = v___x_3641_;
v___y_3621_ = v___y_3635_;
v___y_3622_ = v___y_3634_;
v___y_3623_ = v___y_3636_;
v___y_3624_ = v_a_3640_;
v___y_3625_ = v___y_3638_;
v___y_3626_ = v___x_3643_;
goto v___jp_3615_;
}
}
}
else
{
lean_object* v_a_3645_; 
lean_dec(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec(v___y_3630_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3645_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3639_, 1);
v___y_3573_ = v___y_3633_;
v___y_3574_ = v___y_3632_;
v___y_3575_ = v___y_3631_;
v___y_3576_ = v___y_3635_;
v___y_3577_ = v___y_3634_;
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
v___x_3658_ = l_List_isEmpty___redArg(v___y_3648_);
lean_dec(v___y_3648_);
if (v___x_3658_ == 0)
{
if (v___y_3647_ == 0)
{
v___y_3592_ = v___y_3651_;
v___y_3593_ = v___y_3650_;
v___y_3594_ = v___y_3649_;
v___y_3595_ = v___y_3653_;
v___y_3596_ = v___y_3652_;
v___y_3597_ = v___y_3654_;
v___y_3598_ = v___y_3655_;
v___y_3599_ = v___y_3656_;
goto v___jp_3591_;
}
else
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
lean_dec(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3659_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3660_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3659_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3582_ = v___y_3651_;
v___y_3583_ = v___y_3650_;
v___y_3584_ = v___y_3649_;
v___y_3585_ = v___y_3653_;
v___y_3586_ = v___y_3652_;
v___y_3587_ = v___y_3656_;
v___y_3588_ = v___x_3660_;
goto v___jp_3581_;
}
}
else
{
v___y_3592_ = v___y_3651_;
v___y_3593_ = v___y_3650_;
v___y_3594_ = v___y_3649_;
v___y_3595_ = v___y_3653_;
v___y_3596_ = v___y_3652_;
v___y_3597_ = v___y_3654_;
v___y_3598_ = v___y_3655_;
v___y_3599_ = v___y_3656_;
goto v___jp_3591_;
}
}
else
{
v___y_3630_ = v___y_3648_;
v___y_3631_ = v___y_3651_;
v___y_3632_ = v___y_3650_;
v___y_3633_ = v___y_3649_;
v___y_3634_ = v___y_3653_;
v___y_3635_ = v___y_3652_;
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
lean_inc(v___y_3669_);
v___x_3673_ = l_List_appendTR___redArg(v_a_3671_, v___y_3669_);
if (v_commitIndependentGoals_3672_ == 0)
{
v___y_3647_ = v___y_3662_;
v___y_3648_ = v___y_3663_;
v___y_3649_ = v___y_3664_;
v___y_3650_ = v___y_3665_;
v___y_3651_ = v___y_3666_;
v___y_3652_ = v___y_3667_;
v___y_3653_ = v___y_3668_;
v___y_3654_ = v___y_3669_;
v___y_3655_ = v___x_3673_;
v___y_3656_ = v___y_3670_;
v___y_3657_ = v___x_2984_;
goto v___jp_3646_;
}
else
{
uint8_t v___x_3674_; 
v___x_3674_ = l_List_isEmpty___redArg(v___y_3669_);
if (v___x_3674_ == 0)
{
v___y_3630_ = v___y_3663_;
v___y_3631_ = v___y_3666_;
v___y_3632_ = v___y_3665_;
v___y_3633_ = v___y_3664_;
v___y_3634_ = v___y_3668_;
v___y_3635_ = v___y_3667_;
v___y_3636_ = v___y_3669_;
v___y_3637_ = v___x_3673_;
v___y_3638_ = v___y_3670_;
goto v___jp_3629_;
}
else
{
v___y_3647_ = v___y_3662_;
v___y_3648_ = v___y_3663_;
v___y_3649_ = v___y_3664_;
v___y_3650_ = v___y_3665_;
v___y_3651_ = v___y_3666_;
v___y_3652_ = v___y_3667_;
v___y_3653_ = v___y_3668_;
v___y_3654_ = v___y_3669_;
v___y_3655_ = v___x_3673_;
v___y_3656_ = v___y_3670_;
v___y_3657_ = v___x_2984_;
goto v___jp_3646_;
}
}
}
v___jp_3675_:
{
lean_object* v___x_3683_; double v___x_3684_; double v___x_3685_; double v___x_3686_; double v___x_3687_; double v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3683_ = lean_io_mono_nanos_now();
v___x_3684_ = lean_float_of_nat(v___y_3679_);
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
v___x_3693_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2966_, v_hasTrace_2987_, v___x_3073_, v_options_2985_, v___y_3678_, v___y_3677_, v___y_3676_, v___x_3692_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3530_ = v___y_3680_;
v___y_3531_ = v___y_3681_;
v___y_3532_ = v___x_3693_;
goto v___jp_3529_;
}
v___jp_3694_:
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3702_, 0, v_a_3701_);
v___y_3676_ = v___y_3697_;
v___y_3677_ = v___y_3696_;
v___y_3678_ = v___y_3695_;
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
v___y_3676_ = v___y_3706_;
v___y_3677_ = v___y_3705_;
v___y_3678_ = v___y_3704_;
v___y_3679_ = v___y_3707_;
v___y_3680_ = v___y_3708_;
v___y_3681_ = v___y_3709_;
v_a_3682_ = v___x_3711_;
goto v___jp_3675_;
}
v___jp_3712_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = l_List_appendTR___redArg(v___y_3719_, v___y_3713_);
v___x_3723_ = l_List_appendTR___redArg(v___x_3722_, v_a_3721_);
v___y_3704_ = v___y_3716_;
v___y_3705_ = v___y_3715_;
v___y_3706_ = v___y_3714_;
v___y_3707_ = v___y_3717_;
v___y_3708_ = v___y_3718_;
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
v___y_3714_ = v___y_3728_;
v___y_3715_ = v___y_3727_;
v___y_3716_ = v___y_3726_;
v___y_3717_ = v___y_3729_;
v___y_3718_ = v___y_3730_;
v___y_3719_ = v___y_3731_;
v___y_3720_ = v___y_3732_;
v_a_3721_ = v_a_3734_;
goto v___jp_3712_;
}
else
{
lean_object* v_a_3735_; 
lean_dec(v___y_3731_);
lean_dec(v___y_3725_);
v_a_3735_ = lean_ctor_get(v___y_3733_, 0);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___y_3733_, 1);
v___y_3695_ = v___y_3726_;
v___y_3696_ = v___y_3727_;
v___y_3697_ = v___y_3728_;
v___y_3698_ = v___y_3729_;
v___y_3699_ = v___y_3730_;
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
lean_dec_ref(v___y_3745_);
v___x_3748_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3743_, v_a_2972_, v_a_2974_);
lean_dec_ref(v___y_3743_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_dec_ref_known(v___x_3748_, 1);
v___y_3713_ = v___y_3737_;
v___y_3714_ = v___y_3740_;
v___y_3715_ = v___y_3739_;
v___y_3716_ = v___y_3738_;
v___y_3717_ = v___y_3741_;
v___y_3718_ = v___y_3742_;
v___y_3719_ = v___y_3744_;
v___y_3720_ = v___y_3746_;
v_a_3721_ = v_snd_2980_;
goto v___jp_3712_;
}
else
{
lean_object* v_a_3749_; 
lean_dec(v___y_3744_);
lean_dec(v___y_3737_);
lean_dec(v_snd_2980_);
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3748_, 1);
v___y_3695_ = v___y_3738_;
v___y_3696_ = v___y_3739_;
v___y_3697_ = v___y_3740_;
v___y_3698_ = v___y_3741_;
v___y_3699_ = v___y_3742_;
v___y_3700_ = v___y_3746_;
v_a_3701_ = v_a_3749_;
goto v___jp_3694_;
}
}
else
{
lean_dec_ref(v___y_3743_);
lean_dec(v_snd_2980_);
v___y_3725_ = v___y_3737_;
v___y_3726_ = v___y_3738_;
v___y_3727_ = v___y_3739_;
v___y_3728_ = v___y_3740_;
v___y_3729_ = v___y_3741_;
v___y_3730_ = v___y_3742_;
v___y_3731_ = v___y_3744_;
v___y_3732_ = v___y_3746_;
v___y_3733_ = v___y_3745_;
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
lean_inc(v_snd_2980_);
lean_inc(v_trace_2966_);
v___x_3762_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3759_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_dec(v_a_3761_);
lean_dec(v_snd_2980_);
v___y_3725_ = v___y_3751_;
v___y_3726_ = v___y_3754_;
v___y_3727_ = v___y_3753_;
v___y_3728_ = v___y_3752_;
v___y_3729_ = v___y_3755_;
v___y_3730_ = v___y_3756_;
v___y_3731_ = v___y_3757_;
v___y_3732_ = v___y_3758_;
v___y_3733_ = v___x_3762_;
goto v___jp_3724_;
}
else
{
lean_object* v_a_3763_; uint8_t v___x_3764_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
v___x_3764_ = l_Lean_Exception_isInterrupt(v_a_3763_);
if (v___x_3764_ == 0)
{
uint8_t v___x_3765_; 
v___x_3765_ = l_Lean_Exception_isRuntime(v_a_3763_);
v___y_3737_ = v___y_3751_;
v___y_3738_ = v___y_3754_;
v___y_3739_ = v___y_3753_;
v___y_3740_ = v___y_3752_;
v___y_3741_ = v___y_3755_;
v___y_3742_ = v___y_3756_;
v___y_3743_ = v_a_3761_;
v___y_3744_ = v___y_3757_;
v___y_3745_ = v___x_3762_;
v___y_3746_ = v___y_3758_;
v___y_3747_ = v___x_3765_;
goto v___jp_3736_;
}
else
{
lean_dec(v_a_3763_);
v___y_3737_ = v___y_3751_;
v___y_3738_ = v___y_3754_;
v___y_3739_ = v___y_3753_;
v___y_3740_ = v___y_3752_;
v___y_3741_ = v___y_3755_;
v___y_3742_ = v___y_3756_;
v___y_3743_ = v_a_3761_;
v___y_3744_ = v___y_3757_;
v___y_3745_ = v___x_3762_;
v___y_3746_ = v___y_3758_;
v___y_3747_ = v___x_3764_;
goto v___jp_3736_;
}
}
}
else
{
lean_object* v_a_3766_; 
lean_dec(v___y_3759_);
lean_dec(v___y_3757_);
lean_dec(v___y_3751_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3766_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3766_);
lean_dec_ref_known(v___x_3760_, 1);
v___y_3695_ = v___y_3754_;
v___y_3696_ = v___y_3753_;
v___y_3697_ = v___y_3752_;
v___y_3698_ = v___y_3755_;
v___y_3699_ = v___y_3756_;
v___y_3700_ = v___y_3758_;
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
v___y_3704_ = v___y_3770_;
v___y_3705_ = v___y_3769_;
v___y_3706_ = v___y_3768_;
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
v___y_3695_ = v___y_3770_;
v___y_3696_ = v___y_3769_;
v___y_3697_ = v___y_3768_;
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
v___x_3788_ = l_List_isEmpty___redArg(v___y_3778_);
lean_dec(v___y_3778_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
lean_dec(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v___x_3789_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3790_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3789_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
v___y_3768_ = v___y_3781_;
v___y_3769_ = v___y_3780_;
v___y_3770_ = v___y_3779_;
v___y_3771_ = v___y_3782_;
v___y_3772_ = v___y_3783_;
v___y_3773_ = v___y_3786_;
v___y_3774_ = v___x_3790_;
goto v___jp_3767_;
}
else
{
lean_object* v___x_3791_; 
lean_inc(v_trace_2966_);
v___x_3791_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3785_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3793_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v___x_3793_ = l_List_appendTR___redArg(v___y_3784_, v_a_3792_);
v___y_3704_ = v___y_3779_;
v___y_3705_ = v___y_3780_;
v___y_3706_ = v___y_3781_;
v___y_3707_ = v___y_3782_;
v___y_3708_ = v___y_3783_;
v___y_3709_ = v___y_3786_;
v_a_3710_ = v___x_3793_;
goto v___jp_3703_;
}
else
{
lean_dec(v___y_3784_);
v___y_3768_ = v___y_3781_;
v___y_3769_ = v___y_3780_;
v___y_3770_ = v___y_3779_;
v___y_3771_ = v___y_3782_;
v___y_3772_ = v___y_3783_;
v___y_3773_ = v___y_3786_;
v___y_3774_ = v___x_3791_;
goto v___jp_3767_;
}
}
}
else
{
v___y_3751_ = v___y_3778_;
v___y_3752_ = v___y_3781_;
v___y_3753_ = v___y_3780_;
v___y_3754_ = v___y_3779_;
v___y_3755_ = v___y_3782_;
v___y_3756_ = v___y_3783_;
v___y_3757_ = v___y_3784_;
v___y_3758_ = v___y_3786_;
v___y_3759_ = v___y_3785_;
goto v___jp_3750_;
}
}
v___jp_3794_:
{
uint8_t v_commitIndependentGoals_3804_; lean_object* v___x_3805_; 
v_commitIndependentGoals_3804_ = lean_ctor_get_uint8(v_cfg_2965_, sizeof(void*)*4);
lean_inc(v___y_3801_);
v___x_3805_ = l_List_appendTR___redArg(v_a_3803_, v___y_3801_);
if (v_commitIndependentGoals_3804_ == 0)
{
v___y_3778_ = v___y_3795_;
v___y_3779_ = v___y_3796_;
v___y_3780_ = v___y_3797_;
v___y_3781_ = v___y_3798_;
v___y_3782_ = v___y_3799_;
v___y_3783_ = v___y_3800_;
v___y_3784_ = v___y_3801_;
v___y_3785_ = v___x_3805_;
v___y_3786_ = v___y_3802_;
v___y_3787_ = v___x_2984_;
goto v___jp_3777_;
}
else
{
uint8_t v___x_3806_; 
v___x_3806_ = l_List_isEmpty___redArg(v___y_3801_);
if (v___x_3806_ == 0)
{
v___y_3751_ = v___y_3795_;
v___y_3752_ = v___y_3798_;
v___y_3753_ = v___y_3797_;
v___y_3754_ = v___y_3796_;
v___y_3755_ = v___y_3799_;
v___y_3756_ = v___y_3800_;
v___y_3757_ = v___y_3801_;
v___y_3758_ = v___y_3802_;
v___y_3759_ = v___x_3805_;
goto v___jp_3750_;
}
else
{
v___y_3778_ = v___y_3795_;
v___y_3779_ = v___y_3796_;
v___y_3780_ = v___y_3797_;
v___y_3781_ = v___y_3798_;
v___y_3782_ = v___y_3799_;
v___y_3783_ = v___y_3800_;
v___y_3784_ = v___y_3801_;
v___y_3785_ = v___x_3805_;
v___y_3786_ = v___y_3802_;
v___y_3787_ = v___x_2984_;
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
if (v___y_3809_ == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3816_, 1);
v___x_3818_ = lean_io_mono_nanos_now();
v___x_3819_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2987_, v___x_2984_, v_goals_2969_, v___y_3812_, v_a_2972_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3821_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3819_, 1);
v___x_3821_ = l_List_reverse___redArg(v_a_3820_);
v___y_3795_ = v___y_3808_;
v___y_3796_ = v___y_3810_;
v___y_3797_ = v_a_3817_;
v___y_3798_ = v___y_3811_;
v___y_3799_ = v___x_3818_;
v___y_3800_ = v___y_3813_;
v___y_3801_ = v___y_3814_;
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
v___y_3796_ = v___y_3810_;
v___y_3797_ = v_a_3817_;
v___y_3798_ = v___y_3811_;
v___y_3799_ = v___x_3818_;
v___y_3800_ = v___y_3813_;
v___y_3801_ = v___y_3814_;
v___y_3802_ = v___y_3815_;
v_a_3803_ = v_a_3822_;
goto v___jp_3794_;
}
else
{
lean_object* v_a_3823_; 
lean_dec(v___y_3814_);
lean_dec(v___y_3808_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3823_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3823_);
lean_dec_ref_known(v___x_3819_, 1);
v___y_3695_ = v___y_3810_;
v___y_3696_ = v_a_3817_;
v___y_3697_ = v___y_3811_;
v___y_3698_ = v___x_3818_;
v___y_3699_ = v___y_3813_;
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
v___x_3826_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2987_, v___x_2984_, v_goals_2969_, v___y_3812_, v_a_2972_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3828_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3826_, 1);
v___x_3828_ = l_List_reverse___redArg(v_a_3827_);
v___y_3662_ = v___y_3809_;
v___y_3663_ = v___y_3808_;
v___y_3664_ = v___y_3810_;
v___y_3665_ = v_a_3824_;
v___y_3666_ = v___y_3811_;
v___y_3667_ = v___x_3825_;
v___y_3668_ = v___y_3813_;
v___y_3669_ = v___y_3814_;
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
v___y_3662_ = v___y_3809_;
v___y_3663_ = v___y_3808_;
v___y_3664_ = v___y_3810_;
v___y_3665_ = v_a_3824_;
v___y_3666_ = v___y_3811_;
v___y_3667_ = v___x_3825_;
v___y_3668_ = v___y_3813_;
v___y_3669_ = v___y_3814_;
v___y_3670_ = v___y_3815_;
v_a_3671_ = v_a_3829_;
goto v___jp_3661_;
}
else
{
lean_object* v_a_3830_; 
lean_dec(v___y_3814_);
lean_dec(v___y_3808_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3830_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3830_);
lean_dec_ref_known(v___x_3826_, 1);
v___y_3573_ = v___y_3810_;
v___y_3574_ = v_a_3824_;
v___y_3575_ = v___y_3811_;
v___y_3576_ = v___x_3825_;
v___y_3577_ = v___y_3813_;
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
lean_dec(v___y_3814_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3808_);
lean_dec(v_snd_2980_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3831_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3816_, 1);
v___y_3481_ = v___y_3813_;
v___y_3482_ = v___y_3815_;
v_a_3483_ = v_a_3831_;
goto v___jp_3480_;
}
}
v___jp_3832_:
{
if (v___y_3838_ == 0)
{
uint8_t v___x_3839_; 
v___x_3839_ = l_List_isEmpty___redArg(v___y_3833_);
lean_dec(v___y_3833_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_dec(v___y_3836_);
lean_dec(v___y_3834_);
lean_dec(v_snd_2980_);
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
v___x_3842_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2965_, v_trace_2966_, v_next_2967_, v_orig_2968_, v___y_3834_, v_snd_2980_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3844_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref_known(v___x_3842_, 1);
v___x_3844_ = l_List_appendTR___redArg(v___y_3836_, v_a_3843_);
v___y_3486_ = v___y_3835_;
v___y_3487_ = v___y_3837_;
v_a_3488_ = v___x_3844_;
goto v___jp_3485_;
}
else
{
lean_dec(v___y_3836_);
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
lean_inc(v___y_3848_);
v___x_3852_ = l_List_appendTR___redArg(v_a_3850_, v___y_3848_);
if (v_commitIndependentGoals_3851_ == 0)
{
v___y_3833_ = v___y_3846_;
v___y_3834_ = v___x_3852_;
v___y_3835_ = v___y_3847_;
v___y_3836_ = v___y_3848_;
v___y_3837_ = v___y_3849_;
v___y_3838_ = v___x_2984_;
goto v___jp_3832_;
}
else
{
uint8_t v___x_3853_; 
v___x_3853_ = l_List_isEmpty___redArg(v___y_3848_);
if (v___x_3853_ == 0)
{
v___y_3517_ = v___y_3846_;
v___y_3518_ = v___x_3852_;
v___y_3519_ = v___y_3847_;
v___y_3520_ = v___y_3848_;
v___y_3521_ = v___y_3849_;
goto v___jp_3516_;
}
else
{
v___y_3833_ = v___y_3846_;
v___y_3834_ = v___x_3852_;
v___y_3835_ = v___y_3847_;
v___y_3836_ = v___y_3848_;
v___y_3837_ = v___y_3849_;
v___y_3838_ = v___x_2984_;
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
v___x_3858_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2985_, v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
lean_del_object(v___x_2982_);
v___x_3859_ = lean_io_mono_nanos_now();
v___x_3860_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2979_, v___f_2988_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
v___x_3864_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3863_, v___x_2976_);
lean_inc(v___x_3864_);
v___f_3865_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3865_, 0, v_fst_3862_);
lean_closure_set(v___f_3865_, 1, v___x_3864_);
v___x_3866_ = lean_box(0);
if (v___x_3076_ == 0)
{
lean_object* v___x_3867_; uint8_t v___x_3868_; 
v___x_3867_ = l_Lean_trace_profiler;
v___x_3868_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2985_, v___x_3867_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3869_; 
lean_dec_ref(v___f_3865_);
v___x_3869_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2987_, v___x_2984_, v_goals_2969_, v___x_3866_, v_a_2972_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v___x_3871_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v___x_3871_ = l_List_reverse___redArg(v_a_3870_);
v___y_3846_ = v_fst_3862_;
v___y_3847_ = v___x_3859_;
v___y_3848_ = v___x_3864_;
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
v___y_3846_ = v_fst_3862_;
v___y_3847_ = v___x_3859_;
v___y_3848_ = v___x_3864_;
v___y_3849_ = v_a_3856_;
v_a_3850_ = v_a_3872_;
goto v___jp_3845_;
}
else
{
lean_object* v_a_3873_; 
lean_dec(v___x_3864_);
lean_dec(v_fst_3862_);
lean_dec(v_snd_2980_);
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
v___y_3808_ = v_fst_3862_;
v___y_3809_ = v___x_3858_;
v___y_3810_ = v___x_3076_;
v___y_3811_ = v___f_3865_;
v___y_3812_ = v___x_3866_;
v___y_3813_ = v___x_3859_;
v___y_3814_ = v___x_3864_;
v___y_3815_ = v_a_3856_;
goto v___jp_3807_;
}
}
else
{
v___y_3808_ = v_fst_3862_;
v___y_3809_ = v___x_3858_;
v___y_3810_ = v___x_3076_;
v___y_3811_ = v___f_3865_;
v___y_3812_ = v___x_3866_;
v___y_3813_ = v___x_3859_;
v___y_3814_ = v___x_3864_;
v___y_3815_ = v_a_3856_;
goto v___jp_3807_;
}
}
else
{
lean_object* v_a_3874_; 
lean_dec(v_snd_2980_);
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
v___x_3876_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2979_, v___f_2988_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
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
v___x_3880_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3879_, v___x_2976_);
lean_inc(v___x_3880_);
v___f_3881_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3881_, 0, v_fst_3878_);
lean_closure_set(v___f_3881_, 1, v___x_3880_);
v___x_3882_ = lean_box(0);
if (v___x_3076_ == 0)
{
lean_object* v___x_3883_; uint8_t v___x_3884_; 
v___x_3883_ = l_Lean_trace_profiler;
v___x_3884_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2985_, v___x_3883_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; 
lean_dec_ref(v___f_3881_);
v___x_3885_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3858_, v___x_2984_, v_goals_2969_, v___x_3882_, v_a_2972_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3887_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
v___x_3887_ = l_List_reverse___redArg(v_a_3886_);
v___y_3457_ = v___x_3880_;
v___y_3458_ = v_fst_3878_;
v___y_3459_ = v___x_3875_;
v___y_3460_ = v_a_3856_;
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
v___y_3459_ = v___x_3875_;
v___y_3460_ = v_a_3856_;
v_a_3461_ = v_a_3888_;
goto v___jp_3456_;
}
else
{
lean_object* v_a_3889_; 
lean_dec(v___x_3880_);
lean_dec(v_fst_3878_);
lean_dec(v_snd_2980_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3889_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___x_3885_, 1);
v___y_3092_ = v___x_3875_;
v___y_3093_ = v_a_3856_;
v_a_3094_ = v_a_3889_;
goto v___jp_3091_;
}
}
}
else
{
v___y_3419_ = v___x_3858_;
v___y_3420_ = v___x_3880_;
v___y_3421_ = v___x_3882_;
v___y_3422_ = v___x_3076_;
v___y_3423_ = v_fst_3878_;
v___y_3424_ = v___f_3881_;
v___y_3425_ = v___x_3875_;
v___y_3426_ = v_a_3856_;
goto v___jp_3418_;
}
}
else
{
v___y_3419_ = v___x_3858_;
v___y_3420_ = v___x_3880_;
v___y_3421_ = v___x_3882_;
v___y_3422_ = v___x_3076_;
v___y_3423_ = v_fst_3878_;
v___y_3424_ = v___f_3881_;
v___y_3425_ = v___x_3875_;
v___y_3426_ = v_a_3856_;
goto v___jp_3418_;
}
}
else
{
lean_object* v_a_3890_; 
lean_dec(v_snd_2980_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec_ref(v_cfg_2965_);
v_a_3890_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3876_, 1);
v___y_3092_ = v___x_3875_;
v___y_3093_ = v_a_3856_;
v_a_3094_ = v_a_3890_;
goto v___jp_3091_;
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec_ref(v___f_3072_);
lean_dec_ref(v___f_2988_);
lean_del_object(v___x_2982_);
lean_dec(v_snd_2980_);
lean_dec(v_fst_2979_);
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
lean_del_object(v___x_2982_);
lean_dec(v_snd_2980_);
lean_dec(v_fst_2979_);
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
lean_dec(v_remaining_2970_);
lean_dec(v_goals_2969_);
lean_dec(v_orig_2968_);
lean_dec_ref(v_next_2967_);
lean_dec(v_trace_2966_);
lean_dec_ref(v_cfg_2965_);
v_a_4182_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_2977_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_2977_);
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
uint8_t v___x_48340__boxed_4239_; lean_object* v_res_4240_; 
v___x_48340__boxed_4239_ = lean_unbox(v___x_4231_);
v_res_4240_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_48340__boxed_4239_, v_x_4232_, v_x_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
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
uint8_t v___x_48366__boxed_4260_; uint8_t v___x_48367__boxed_4261_; lean_object* v_res_4262_; 
v___x_48366__boxed_4260_ = lean_unbox(v___x_4251_);
v___x_48367__boxed_4261_ = lean_unbox(v___x_4252_);
v_res_4262_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_48366__boxed_4260_, v___x_48367__boxed_4261_, v_x_4253_, v_x_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
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

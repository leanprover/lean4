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
uint8_t lean_bool_not(uint8_t);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 42, .m_data = "⏭️ deemed acceptable, returning as subgoal"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 35, .m_data = "⏬ discharger generated new subgoals"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "success!"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 45, .m_data = "⏸️ suspending search and returning as subgoal"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "BacktrackConfig.proc failed: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "discarding already assigned goal "};
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
static const lean_closure_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_x_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec_ref(v_x_392_);
return v_res_398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0));
v___x_401_ = l_Lean_stringToMessageData(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object* v_a_402_, lean_object* v_x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1);
v___x_410_ = l_Lean_Exception_toMessageData(v_a_402_);
v___x_411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_409_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object* v_a_413_, lean_object* v_x_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(v_a_413_, v_x_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec_ref(v_x_414_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(lean_object* v_opts_421_, lean_object* v_opt_422_){
_start:
{
lean_object* v_name_423_; lean_object* v_defValue_424_; lean_object* v_map_425_; lean_object* v___x_426_; 
v_name_423_ = lean_ctor_get(v_opt_422_, 0);
v_defValue_424_ = lean_ctor_get(v_opt_422_, 1);
v_map_425_ = lean_ctor_get(v_opts_421_, 0);
v___x_426_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_425_, v_name_423_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_inc(v_defValue_424_);
return v_defValue_424_;
}
else
{
lean_object* v_val_427_; 
v_val_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_val_427_);
lean_dec_ref_known(v___x_426_, 1);
if (lean_obj_tag(v_val_427_) == 3)
{
lean_object* v_v_428_; 
v_v_428_ = lean_ctor_get(v_val_427_, 0);
lean_inc(v_v_428_);
lean_dec_ref_known(v_val_427_, 1);
return v_v_428_;
}
else
{
lean_dec(v_val_427_);
lean_inc(v_defValue_424_);
return v_defValue_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6___boxed(lean_object* v_opts_429_, lean_object* v_opt_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_429_, v_opt_430_);
lean_dec_ref(v_opt_430_);
lean_dec_ref(v_opts_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(lean_object* v_x_432_){
_start:
{
if (lean_obj_tag(v_x_432_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
v_a_434_ = lean_ctor_get(v_x_432_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v_x_432_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v_x_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 1);
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_a_442_ = lean_ctor_get(v_x_432_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v_x_432_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v_x_432_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set_tag(v___x_444_, 0);
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg___boxed(lean_object* v_x_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(size_t v_sz_453_, size_t v_i_454_, lean_object* v_bs_455_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = lean_usize_dec_lt(v_i_454_, v_sz_453_);
if (v___x_456_ == 0)
{
return v_bs_455_;
}
else
{
lean_object* v_v_457_; lean_object* v_msg_458_; lean_object* v___x_459_; lean_object* v_bs_x27_460_; size_t v___x_461_; size_t v___x_462_; lean_object* v___x_463_; 
v_v_457_ = lean_array_uget_borrowed(v_bs_455_, v_i_454_);
v_msg_458_ = lean_ctor_get(v_v_457_, 1);
lean_inc_ref(v_msg_458_);
v___x_459_ = lean_unsigned_to_nat(0u);
v_bs_x27_460_ = lean_array_uset(v_bs_455_, v_i_454_, v___x_459_);
v___x_461_ = ((size_t)1ULL);
v___x_462_ = lean_usize_add(v_i_454_, v___x_461_);
v___x_463_ = lean_array_uset(v_bs_x27_460_, v_i_454_, v_msg_458_);
v_i_454_ = v___x_462_;
v_bs_455_ = v___x_463_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6___boxed(lean_object* v_sz_465_, lean_object* v_i_466_, lean_object* v_bs_467_){
_start:
{
size_t v_sz_boxed_468_; size_t v_i_boxed_469_; lean_object* v_res_470_; 
v_sz_boxed_468_ = lean_unbox_usize(v_sz_465_);
lean_dec(v_sz_465_);
v_i_boxed_469_ = lean_unbox_usize(v_i_466_);
lean_dec(v_i_466_);
v_res_470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_boxed_468_, v_i_boxed_469_, v_bs_467_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object* v_oldTraces_471_, lean_object* v_data_472_, lean_object* v_ref_473_, lean_object* v_msg_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_fileName_480_; lean_object* v_fileMap_481_; lean_object* v_options_482_; lean_object* v_currRecDepth_483_; lean_object* v_maxRecDepth_484_; lean_object* v_ref_485_; lean_object* v_currNamespace_486_; lean_object* v_openDecls_487_; lean_object* v_initHeartbeats_488_; lean_object* v_maxHeartbeats_489_; lean_object* v_quotContext_490_; lean_object* v_currMacroScope_491_; uint8_t v_diag_492_; lean_object* v_cancelTk_x3f_493_; uint8_t v_suppressElabErrors_494_; lean_object* v_inheritedTraceOptions_495_; lean_object* v___x_496_; lean_object* v_traceState_497_; lean_object* v_traces_498_; lean_object* v_ref_499_; lean_object* v___x_500_; lean_object* v___x_501_; size_t v_sz_502_; size_t v___x_503_; lean_object* v___x_504_; lean_object* v_msg_505_; lean_object* v___x_506_; lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_544_; 
v_fileName_480_ = lean_ctor_get(v___y_477_, 0);
v_fileMap_481_ = lean_ctor_get(v___y_477_, 1);
v_options_482_ = lean_ctor_get(v___y_477_, 2);
v_currRecDepth_483_ = lean_ctor_get(v___y_477_, 3);
v_maxRecDepth_484_ = lean_ctor_get(v___y_477_, 4);
v_ref_485_ = lean_ctor_get(v___y_477_, 5);
v_currNamespace_486_ = lean_ctor_get(v___y_477_, 6);
v_openDecls_487_ = lean_ctor_get(v___y_477_, 7);
v_initHeartbeats_488_ = lean_ctor_get(v___y_477_, 8);
v_maxHeartbeats_489_ = lean_ctor_get(v___y_477_, 9);
v_quotContext_490_ = lean_ctor_get(v___y_477_, 10);
v_currMacroScope_491_ = lean_ctor_get(v___y_477_, 11);
v_diag_492_ = lean_ctor_get_uint8(v___y_477_, sizeof(void*)*14);
v_cancelTk_x3f_493_ = lean_ctor_get(v___y_477_, 12);
v_suppressElabErrors_494_ = lean_ctor_get_uint8(v___y_477_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_495_ = lean_ctor_get(v___y_477_, 13);
v___x_496_ = lean_st_ref_get(v___y_478_);
v_traceState_497_ = lean_ctor_get(v___x_496_, 4);
lean_inc_ref(v_traceState_497_);
lean_dec(v___x_496_);
v_traces_498_ = lean_ctor_get(v_traceState_497_, 0);
lean_inc_ref(v_traces_498_);
lean_dec_ref(v_traceState_497_);
v_ref_499_ = l_Lean_replaceRef(v_ref_473_, v_ref_485_);
lean_inc_ref(v_inheritedTraceOptions_495_);
lean_inc(v_cancelTk_x3f_493_);
lean_inc(v_currMacroScope_491_);
lean_inc(v_quotContext_490_);
lean_inc(v_maxHeartbeats_489_);
lean_inc(v_initHeartbeats_488_);
lean_inc(v_openDecls_487_);
lean_inc(v_currNamespace_486_);
lean_inc(v_maxRecDepth_484_);
lean_inc(v_currRecDepth_483_);
lean_inc_ref(v_options_482_);
lean_inc_ref(v_fileMap_481_);
lean_inc_ref(v_fileName_480_);
v___x_500_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_500_, 0, v_fileName_480_);
lean_ctor_set(v___x_500_, 1, v_fileMap_481_);
lean_ctor_set(v___x_500_, 2, v_options_482_);
lean_ctor_set(v___x_500_, 3, v_currRecDepth_483_);
lean_ctor_set(v___x_500_, 4, v_maxRecDepth_484_);
lean_ctor_set(v___x_500_, 5, v_ref_499_);
lean_ctor_set(v___x_500_, 6, v_currNamespace_486_);
lean_ctor_set(v___x_500_, 7, v_openDecls_487_);
lean_ctor_set(v___x_500_, 8, v_initHeartbeats_488_);
lean_ctor_set(v___x_500_, 9, v_maxHeartbeats_489_);
lean_ctor_set(v___x_500_, 10, v_quotContext_490_);
lean_ctor_set(v___x_500_, 11, v_currMacroScope_491_);
lean_ctor_set(v___x_500_, 12, v_cancelTk_x3f_493_);
lean_ctor_set(v___x_500_, 13, v_inheritedTraceOptions_495_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*14, v_diag_492_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*14 + 1, v_suppressElabErrors_494_);
v___x_501_ = l_Lean_PersistentArray_toArray___redArg(v_traces_498_);
lean_dec_ref(v_traces_498_);
v_sz_502_ = lean_array_size(v___x_501_);
v___x_503_ = ((size_t)0ULL);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_502_, v___x_503_, v___x_501_);
v_msg_505_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_505_, 0, v_data_472_);
lean_ctor_set(v_msg_505_, 1, v_msg_474_);
lean_ctor_set(v_msg_505_, 2, v___x_504_);
v___x_506_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_505_, v___y_475_, v___y_476_, v___x_500_, v___y_478_);
lean_dec_ref_known(v___x_500_, 14);
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_544_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_544_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_544_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v_traceState_512_; lean_object* v_env_513_; lean_object* v_nextMacroScope_514_; lean_object* v_ngen_515_; lean_object* v_auxDeclNGen_516_; lean_object* v_cache_517_; lean_object* v_messages_518_; lean_object* v_infoState_519_; lean_object* v_snapshotTasks_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_543_; 
v___x_511_ = lean_st_ref_take(v___y_478_);
v_traceState_512_ = lean_ctor_get(v___x_511_, 4);
v_env_513_ = lean_ctor_get(v___x_511_, 0);
v_nextMacroScope_514_ = lean_ctor_get(v___x_511_, 1);
v_ngen_515_ = lean_ctor_get(v___x_511_, 2);
v_auxDeclNGen_516_ = lean_ctor_get(v___x_511_, 3);
v_cache_517_ = lean_ctor_get(v___x_511_, 5);
v_messages_518_ = lean_ctor_get(v___x_511_, 6);
v_infoState_519_ = lean_ctor_get(v___x_511_, 7);
v_snapshotTasks_520_ = lean_ctor_get(v___x_511_, 8);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_543_ == 0)
{
v___x_522_ = v___x_511_;
v_isShared_523_ = v_isSharedCheck_543_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snapshotTasks_520_);
lean_inc(v_infoState_519_);
lean_inc(v_messages_518_);
lean_inc(v_cache_517_);
lean_inc(v_traceState_512_);
lean_inc(v_auxDeclNGen_516_);
lean_inc(v_ngen_515_);
lean_inc(v_nextMacroScope_514_);
lean_inc(v_env_513_);
lean_dec(v___x_511_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_543_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint64_t v_tid_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_541_; 
v_tid_524_ = lean_ctor_get_uint64(v_traceState_512_, sizeof(void*)*1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_traceState_512_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; 
v_unused_542_ = lean_ctor_get(v_traceState_512_, 0);
lean_dec(v_unused_542_);
v___x_526_ = v_traceState_512_;
v_isShared_527_ = v_isSharedCheck_541_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_traceState_512_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_541_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_ref_473_);
lean_ctor_set(v___x_528_, 1, v_a_507_);
v___x_529_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_471_, v___x_528_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_529_);
v___x_531_ = v___x_526_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_529_);
lean_ctor_set_uint64(v_reuseFailAlloc_540_, sizeof(void*)*1, v_tid_524_);
v___x_531_ = v_reuseFailAlloc_540_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_533_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 4, v___x_531_);
v___x_533_ = v___x_522_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_env_513_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_nextMacroScope_514_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_ngen_515_);
lean_ctor_set(v_reuseFailAlloc_539_, 3, v_auxDeclNGen_516_);
lean_ctor_set(v_reuseFailAlloc_539_, 4, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_539_, 5, v_cache_517_);
lean_ctor_set(v_reuseFailAlloc_539_, 6, v_messages_518_);
lean_ctor_set(v_reuseFailAlloc_539_, 7, v_infoState_519_);
lean_ctor_set(v_reuseFailAlloc_539_, 8, v_snapshotTasks_520_);
v___x_533_ = v_reuseFailAlloc_539_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_534_ = lean_st_ref_set(v___y_478_, v___x_533_);
v___x_535_ = lean_box(0);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_535_);
v___x_537_ = v___x_509_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object* v_oldTraces_545_, lean_object* v_data_546_, lean_object* v_ref_547_, lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_545_, v_data_546_, v_ref_547_, v_msg_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_554_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object* v_e_555_){
_start:
{
if (lean_obj_tag(v_e_555_) == 0)
{
uint8_t v___x_556_; 
v___x_556_ = 2;
return v___x_556_;
}
else
{
lean_object* v_a_557_; 
v_a_557_ = lean_ctor_get(v_e_555_, 0);
if (lean_obj_tag(v_a_557_) == 0)
{
uint8_t v___x_558_; 
v___x_558_ = 1;
return v___x_558_;
}
else
{
uint8_t v___x_559_; 
v___x_559_ = 0;
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object* v_e_560_){
_start:
{
uint8_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_e_560_);
lean_dec_ref(v_e_560_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0(void){
_start:
{
lean_object* v___x_563_; double v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_float_of_nat(v___x_563_);
return v___x_564_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1));
v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
return v___x_567_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3(void){
_start:
{
lean_object* v___x_568_; double v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(1000u);
v___x_569_ = lean_float_of_nat(v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_cls_570_, uint8_t v_collapsed_571_, lean_object* v_tag_572_, lean_object* v_opts_573_, uint8_t v_clsEnabled_574_, lean_object* v_oldTraces_575_, lean_object* v_msg_576_, lean_object* v_resStartStop_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_fst_583_; lean_object* v_snd_584_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v_data_588_; lean_object* v_fst_599_; lean_object* v_snd_600_; lean_object* v___x_601_; uint8_t v___x_602_; lean_object* v___y_604_; lean_object* v_a_605_; uint8_t v___y_620_; double v___y_651_; 
v_fst_583_ = lean_ctor_get(v_resStartStop_577_, 0);
lean_inc(v_fst_583_);
v_snd_584_ = lean_ctor_get(v_resStartStop_577_, 1);
lean_inc(v_snd_584_);
lean_dec_ref(v_resStartStop_577_);
v_fst_599_ = lean_ctor_get(v_snd_584_, 0);
lean_inc(v_fst_599_);
v_snd_600_ = lean_ctor_get(v_snd_584_, 1);
lean_inc(v_snd_600_);
lean_dec(v_snd_584_);
v___x_601_ = l_Lean_trace_profiler;
v___x_602_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_573_, v___x_601_);
if (v___x_602_ == 0)
{
v___y_620_ = v___x_602_;
goto v___jp_619_;
}
else
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = l_Lean_trace_profiler_useHeartbeats;
v___x_657_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_573_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; double v___x_660_; double v___x_661_; double v___x_662_; 
v___x_658_ = l_Lean_trace_profiler_threshold;
v___x_659_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_573_, v___x_658_);
v___x_660_ = lean_float_of_nat(v___x_659_);
v___x_661_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_662_ = lean_float_div(v___x_660_, v___x_661_);
v___y_651_ = v___x_662_;
goto v___jp_650_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; double v___x_665_; 
v___x_663_ = l_Lean_trace_profiler_threshold;
v___x_664_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_573_, v___x_663_);
v___x_665_ = lean_float_of_nat(v___x_664_);
v___y_651_ = v___x_665_;
goto v___jp_650_;
}
}
v___jp_585_:
{
lean_object* v___x_589_; 
lean_inc(v___y_587_);
v___x_589_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_575_, v_data_588_, v___y_587_, v___y_586_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_590_; 
lean_dec_ref_known(v___x_589_, 1);
v___x_590_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_583_);
return v___x_590_;
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec(v_fst_583_);
v_a_591_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_589_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
v___jp_603_:
{
uint8_t v_result_606_; lean_object* v___x_607_; lean_object* v___x_608_; double v___x_609_; lean_object* v_data_610_; 
v_result_606_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_fst_583_);
v___x_607_ = lean_box(v_result_606_);
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
v___x_609_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_572_);
lean_inc_ref(v___x_608_);
lean_inc(v_cls_570_);
v_data_610_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_610_, 0, v_cls_570_);
lean_ctor_set(v_data_610_, 1, v___x_608_);
lean_ctor_set(v_data_610_, 2, v_tag_572_);
lean_ctor_set_float(v_data_610_, sizeof(void*)*3, v___x_609_);
lean_ctor_set_float(v_data_610_, sizeof(void*)*3 + 8, v___x_609_);
lean_ctor_set_uint8(v_data_610_, sizeof(void*)*3 + 16, v_collapsed_571_);
if (v___x_602_ == 0)
{
lean_dec_ref_known(v___x_608_, 1);
lean_dec(v_snd_600_);
lean_dec(v_fst_599_);
lean_dec_ref(v_tag_572_);
lean_dec(v_cls_570_);
v___y_586_ = v_a_605_;
v___y_587_ = v___y_604_;
v_data_588_ = v_data_610_;
goto v___jp_585_;
}
else
{
lean_object* v_data_611_; double v___x_612_; double v___x_613_; 
lean_dec_ref_known(v_data_610_, 3);
v_data_611_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_611_, 0, v_cls_570_);
lean_ctor_set(v_data_611_, 1, v___x_608_);
lean_ctor_set(v_data_611_, 2, v_tag_572_);
v___x_612_ = lean_unbox_float(v_fst_599_);
lean_dec(v_fst_599_);
lean_ctor_set_float(v_data_611_, sizeof(void*)*3, v___x_612_);
v___x_613_ = lean_unbox_float(v_snd_600_);
lean_dec(v_snd_600_);
lean_ctor_set_float(v_data_611_, sizeof(void*)*3 + 8, v___x_613_);
lean_ctor_set_uint8(v_data_611_, sizeof(void*)*3 + 16, v_collapsed_571_);
v___y_586_ = v_a_605_;
v___y_587_ = v___y_604_;
v_data_588_ = v_data_611_;
goto v___jp_585_;
}
}
v___jp_614_:
{
lean_object* v_ref_615_; lean_object* v___x_616_; 
v_ref_615_ = lean_ctor_get(v___y_580_, 5);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
lean_inc(v___y_579_);
lean_inc_ref(v___y_578_);
lean_inc(v_fst_583_);
v___x_616_ = lean_apply_6(v_msg_576_, v_fst_583_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, lean_box(0));
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_616_, 1);
v___y_604_ = v_ref_615_;
v_a_605_ = v_a_617_;
goto v___jp_603_;
}
else
{
lean_object* v___x_618_; 
lean_dec_ref_known(v___x_616_, 1);
v___x_618_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_604_ = v_ref_615_;
v_a_605_ = v___x_618_;
goto v___jp_603_;
}
}
v___jp_619_:
{
if (v_clsEnabled_574_ == 0)
{
if (v___y_620_ == 0)
{
lean_object* v___x_621_; lean_object* v_traceState_622_; lean_object* v_env_623_; lean_object* v_nextMacroScope_624_; lean_object* v_ngen_625_; lean_object* v_auxDeclNGen_626_; lean_object* v_cache_627_; lean_object* v_messages_628_; lean_object* v_infoState_629_; lean_object* v_snapshotTasks_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_649_; 
lean_dec(v_snd_600_);
lean_dec(v_fst_599_);
lean_dec_ref(v_msg_576_);
lean_dec_ref(v_tag_572_);
lean_dec(v_cls_570_);
v___x_621_ = lean_st_ref_take(v___y_581_);
v_traceState_622_ = lean_ctor_get(v___x_621_, 4);
v_env_623_ = lean_ctor_get(v___x_621_, 0);
v_nextMacroScope_624_ = lean_ctor_get(v___x_621_, 1);
v_ngen_625_ = lean_ctor_get(v___x_621_, 2);
v_auxDeclNGen_626_ = lean_ctor_get(v___x_621_, 3);
v_cache_627_ = lean_ctor_get(v___x_621_, 5);
v_messages_628_ = lean_ctor_get(v___x_621_, 6);
v_infoState_629_ = lean_ctor_get(v___x_621_, 7);
v_snapshotTasks_630_ = lean_ctor_get(v___x_621_, 8);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_649_ == 0)
{
v___x_632_ = v___x_621_;
v_isShared_633_ = v_isSharedCheck_649_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_snapshotTasks_630_);
lean_inc(v_infoState_629_);
lean_inc(v_messages_628_);
lean_inc(v_cache_627_);
lean_inc(v_traceState_622_);
lean_inc(v_auxDeclNGen_626_);
lean_inc(v_ngen_625_);
lean_inc(v_nextMacroScope_624_);
lean_inc(v_env_623_);
lean_dec(v___x_621_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_649_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
uint64_t v_tid_634_; lean_object* v_traces_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_648_; 
v_tid_634_ = lean_ctor_get_uint64(v_traceState_622_, sizeof(void*)*1);
v_traces_635_ = lean_ctor_get(v_traceState_622_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v_traceState_622_);
if (v_isSharedCheck_648_ == 0)
{
v___x_637_ = v_traceState_622_;
v_isShared_638_ = v_isSharedCheck_648_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_traces_635_);
lean_dec(v_traceState_622_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_648_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_575_, v_traces_635_);
lean_dec_ref(v_traces_635_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_639_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_639_);
lean_ctor_set_uint64(v_reuseFailAlloc_647_, sizeof(void*)*1, v_tid_634_);
v___x_641_ = v_reuseFailAlloc_647_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_643_; 
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 4, v___x_641_);
v___x_643_ = v___x_632_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_env_623_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_nextMacroScope_624_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_ngen_625_);
lean_ctor_set(v_reuseFailAlloc_646_, 3, v_auxDeclNGen_626_);
lean_ctor_set(v_reuseFailAlloc_646_, 4, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_646_, 5, v_cache_627_);
lean_ctor_set(v_reuseFailAlloc_646_, 6, v_messages_628_);
lean_ctor_set(v_reuseFailAlloc_646_, 7, v_infoState_629_);
lean_ctor_set(v_reuseFailAlloc_646_, 8, v_snapshotTasks_630_);
v___x_643_ = v_reuseFailAlloc_646_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_st_ref_set(v___y_581_, v___x_643_);
v___x_645_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_583_);
return v___x_645_;
}
}
}
}
}
else
{
goto v___jp_614_;
}
}
else
{
goto v___jp_614_;
}
}
v___jp_650_:
{
double v___x_652_; double v___x_653_; double v___x_654_; uint8_t v___x_655_; 
v___x_652_ = lean_unbox_float(v_snd_600_);
v___x_653_ = lean_unbox_float(v_fst_599_);
v___x_654_ = lean_float_sub(v___x_652_, v___x_653_);
v___x_655_ = lean_float_decLt(v___y_651_, v___x_654_);
v___y_620_ = v___x_655_;
goto v___jp_619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_cls_666_, lean_object* v_collapsed_667_, lean_object* v_tag_668_, lean_object* v_opts_669_, lean_object* v_clsEnabled_670_, lean_object* v_oldTraces_671_, lean_object* v_msg_672_, lean_object* v_resStartStop_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
uint8_t v_collapsed_boxed_679_; uint8_t v_clsEnabled_boxed_680_; lean_object* v_res_681_; 
v_collapsed_boxed_679_ = lean_unbox(v_collapsed_667_);
v_clsEnabled_boxed_680_ = lean_unbox(v_clsEnabled_670_);
v_res_681_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_cls_666_, v_collapsed_boxed_679_, v_tag_668_, v_opts_669_, v_clsEnabled_boxed_680_, v_oldTraces_671_, v_msg_672_, v_resStartStop_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec_ref(v_opts_669_);
return v_res_681_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0));
v___x_684_ = l_Lean_stringToMessageData(v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* v_head_685_, lean_object* v_x_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_692_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
v___x_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_693_, 0, v_head_685_);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* v_head_696_, lean_object* v_x_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_head_696_, v_x_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_x_697_);
return v_res_703_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object* v_keys_704_, lean_object* v_i_705_, lean_object* v_k_706_){
_start:
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_array_get_size(v_keys_704_);
v___x_708_ = lean_nat_dec_lt(v_i_705_, v___x_707_);
if (v___x_708_ == 0)
{
lean_dec(v_i_705_);
return v___x_708_;
}
else
{
lean_object* v_k_x27_709_; uint8_t v___x_710_; 
v_k_x27_709_ = lean_array_fget_borrowed(v_keys_704_, v_i_705_);
v___x_710_ = l_Lean_instBEqMVarId_beq(v_k_706_, v_k_x27_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = lean_nat_add(v_i_705_, v___x_711_);
lean_dec(v_i_705_);
v_i_705_ = v___x_712_;
goto _start;
}
else
{
lean_dec(v_i_705_);
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object* v_keys_714_, lean_object* v_i_715_, lean_object* v_k_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_714_, v_i_715_, v_k_716_);
lean_dec(v_k_716_);
lean_dec_ref(v_keys_714_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_719_, size_t v_x_720_, lean_object* v_x_721_){
_start:
{
if (lean_obj_tag(v_x_719_) == 0)
{
lean_object* v_es_722_; lean_object* v___x_723_; size_t v___x_724_; size_t v___x_725_; lean_object* v_j_726_; lean_object* v___x_727_; 
v_es_722_ = lean_ctor_get(v_x_719_, 0);
v___x_723_ = lean_box(2);
v___x_724_ = ((size_t)31ULL);
v___x_725_ = lean_usize_land(v_x_720_, v___x_724_);
v_j_726_ = lean_usize_to_nat(v___x_725_);
v___x_727_ = lean_array_get_borrowed(v___x_723_, v_es_722_, v_j_726_);
lean_dec(v_j_726_);
switch(lean_obj_tag(v___x_727_))
{
case 0:
{
lean_object* v_key_728_; uint8_t v___x_729_; 
v_key_728_ = lean_ctor_get(v___x_727_, 0);
v___x_729_ = l_Lean_instBEqMVarId_beq(v_x_721_, v_key_728_);
return v___x_729_;
}
case 1:
{
lean_object* v_node_730_; size_t v___x_731_; size_t v___x_732_; 
v_node_730_ = lean_ctor_get(v___x_727_, 0);
v___x_731_ = ((size_t)5ULL);
v___x_732_ = lean_usize_shift_right(v_x_720_, v___x_731_);
v_x_719_ = v_node_730_;
v_x_720_ = v___x_732_;
goto _start;
}
default: 
{
uint8_t v___x_734_; 
v___x_734_ = 0;
return v___x_734_;
}
}
}
else
{
lean_object* v_ks_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_ks_735_ = lean_ctor_get(v_x_719_, 0);
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_ks_735_, v___x_736_, v_x_721_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_x_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
size_t v_x_81528__boxed_741_; uint8_t v_res_742_; lean_object* v_r_743_; 
v_x_81528__boxed_741_ = lean_unbox_usize(v_x_739_);
lean_dec(v_x_739_);
v_res_742_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_738_, v_x_81528__boxed_741_, v_x_740_);
lean_dec(v_x_740_);
lean_dec_ref(v_x_738_);
v_r_743_ = lean_box(v_res_742_);
return v_r_743_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
uint64_t v___x_746_; size_t v___x_747_; uint8_t v___x_748_; 
v___x_746_ = l_Lean_instHashableMVarId_hash(v_x_745_);
v___x_747_ = lean_uint64_to_usize(v___x_746_);
v___x_748_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_744_, v___x_747_, v_x_745_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
uint8_t v_res_751_; lean_object* v_r_752_; 
v_res_751_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_749_, v_x_750_);
lean_dec(v_x_750_);
lean_dec_ref(v_x_749_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object* v_mvarId_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; lean_object* v_mctx_757_; lean_object* v_eAssignment_758_; uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_756_ = lean_st_ref_get(v___y_754_);
v_mctx_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc_ref(v_mctx_757_);
lean_dec(v___x_756_);
v_eAssignment_758_ = lean_ctor_get(v_mctx_757_, 8);
lean_inc_ref(v_eAssignment_758_);
lean_dec_ref(v_mctx_757_);
v___x_759_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_eAssignment_758_, v_mvarId_753_);
lean_dec_ref(v_eAssignment_758_);
v___x_760_ = lean_box(v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object* v_mvarId_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec(v_mvarId_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_ref_772_; lean_object* v___x_773_; lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
v_ref_772_ = lean_ctor_get(v___y_769_, 5);
v___x_773_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_782_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
lean_inc(v_ref_772_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v_ref_772_);
lean_ctor_set(v___x_778_, 1, v_a_774_);
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 1);
lean_ctor_set(v___x_776_, 0, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_789_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_e_790_){
_start:
{
if (lean_obj_tag(v_e_790_) == 0)
{
uint8_t v___x_791_; 
v___x_791_ = 2;
return v___x_791_;
}
else
{
uint8_t v___x_792_; 
v___x_792_ = 0;
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_e_793_){
_start:
{
uint8_t v_res_794_; lean_object* v_r_795_; 
v_res_794_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_e_793_);
lean_dec_ref(v_e_793_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_796_, uint8_t v_collapsed_797_, lean_object* v_tag_798_, lean_object* v_opts_799_, uint8_t v_clsEnabled_800_, lean_object* v_oldTraces_801_, lean_object* v_msg_802_, lean_object* v_resStartStop_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_fst_809_; lean_object* v_snd_810_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v_data_814_; lean_object* v_fst_825_; lean_object* v_snd_826_; lean_object* v___x_827_; uint8_t v___x_828_; lean_object* v___y_830_; lean_object* v_a_831_; uint8_t v___y_846_; double v___y_877_; 
v_fst_809_ = lean_ctor_get(v_resStartStop_803_, 0);
lean_inc(v_fst_809_);
v_snd_810_ = lean_ctor_get(v_resStartStop_803_, 1);
lean_inc(v_snd_810_);
lean_dec_ref(v_resStartStop_803_);
v_fst_825_ = lean_ctor_get(v_snd_810_, 0);
lean_inc(v_fst_825_);
v_snd_826_ = lean_ctor_get(v_snd_810_, 1);
lean_inc(v_snd_826_);
lean_dec(v_snd_810_);
v___x_827_ = l_Lean_trace_profiler;
v___x_828_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_799_, v___x_827_);
if (v___x_828_ == 0)
{
v___y_846_ = v___x_828_;
goto v___jp_845_;
}
else
{
lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_882_ = l_Lean_trace_profiler_useHeartbeats;
v___x_883_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_799_, v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; double v___x_886_; double v___x_887_; double v___x_888_; 
v___x_884_ = l_Lean_trace_profiler_threshold;
v___x_885_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_799_, v___x_884_);
v___x_886_ = lean_float_of_nat(v___x_885_);
v___x_887_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_888_ = lean_float_div(v___x_886_, v___x_887_);
v___y_877_ = v___x_888_;
goto v___jp_876_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; double v___x_891_; 
v___x_889_ = l_Lean_trace_profiler_threshold;
v___x_890_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_799_, v___x_889_);
v___x_891_ = lean_float_of_nat(v___x_890_);
v___y_877_ = v___x_891_;
goto v___jp_876_;
}
}
v___jp_811_:
{
lean_object* v___x_815_; 
lean_inc(v___y_813_);
v___x_815_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_801_, v_data_814_, v___y_813_, v___y_812_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v___x_816_; 
lean_dec_ref_known(v___x_815_, 1);
v___x_816_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_809_);
return v___x_816_;
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_fst_809_);
v_a_817_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_815_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_815_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
v___jp_829_:
{
uint8_t v_result_832_; lean_object* v___x_833_; lean_object* v___x_834_; double v___x_835_; lean_object* v_data_836_; 
v_result_832_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_fst_809_);
v___x_833_ = lean_box(v_result_832_);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
v___x_835_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_798_);
lean_inc_ref(v___x_834_);
lean_inc(v_cls_796_);
v_data_836_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_836_, 0, v_cls_796_);
lean_ctor_set(v_data_836_, 1, v___x_834_);
lean_ctor_set(v_data_836_, 2, v_tag_798_);
lean_ctor_set_float(v_data_836_, sizeof(void*)*3, v___x_835_);
lean_ctor_set_float(v_data_836_, sizeof(void*)*3 + 8, v___x_835_);
lean_ctor_set_uint8(v_data_836_, sizeof(void*)*3 + 16, v_collapsed_797_);
if (v___x_828_ == 0)
{
lean_dec_ref_known(v___x_834_, 1);
lean_dec(v_snd_826_);
lean_dec(v_fst_825_);
lean_dec_ref(v_tag_798_);
lean_dec(v_cls_796_);
v___y_812_ = v_a_831_;
v___y_813_ = v___y_830_;
v_data_814_ = v_data_836_;
goto v___jp_811_;
}
else
{
lean_object* v_data_837_; double v___x_838_; double v___x_839_; 
lean_dec_ref_known(v_data_836_, 3);
v_data_837_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_837_, 0, v_cls_796_);
lean_ctor_set(v_data_837_, 1, v___x_834_);
lean_ctor_set(v_data_837_, 2, v_tag_798_);
v___x_838_ = lean_unbox_float(v_fst_825_);
lean_dec(v_fst_825_);
lean_ctor_set_float(v_data_837_, sizeof(void*)*3, v___x_838_);
v___x_839_ = lean_unbox_float(v_snd_826_);
lean_dec(v_snd_826_);
lean_ctor_set_float(v_data_837_, sizeof(void*)*3 + 8, v___x_839_);
lean_ctor_set_uint8(v_data_837_, sizeof(void*)*3 + 16, v_collapsed_797_);
v___y_812_ = v_a_831_;
v___y_813_ = v___y_830_;
v_data_814_ = v_data_837_;
goto v___jp_811_;
}
}
v___jp_840_:
{
lean_object* v_ref_841_; lean_object* v___x_842_; 
v_ref_841_ = lean_ctor_get(v___y_806_, 5);
lean_inc(v___y_807_);
lean_inc_ref(v___y_806_);
lean_inc(v___y_805_);
lean_inc_ref(v___y_804_);
lean_inc(v_fst_809_);
v___x_842_ = lean_apply_6(v_msg_802_, v_fst_809_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, lean_box(0));
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
v___y_830_ = v_ref_841_;
v_a_831_ = v_a_843_;
goto v___jp_829_;
}
else
{
lean_object* v___x_844_; 
lean_dec_ref_known(v___x_842_, 1);
v___x_844_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_830_ = v_ref_841_;
v_a_831_ = v___x_844_;
goto v___jp_829_;
}
}
v___jp_845_:
{
if (v_clsEnabled_800_ == 0)
{
if (v___y_846_ == 0)
{
lean_object* v___x_847_; lean_object* v_traceState_848_; lean_object* v_env_849_; lean_object* v_nextMacroScope_850_; lean_object* v_ngen_851_; lean_object* v_auxDeclNGen_852_; lean_object* v_cache_853_; lean_object* v_messages_854_; lean_object* v_infoState_855_; lean_object* v_snapshotTasks_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_snd_826_);
lean_dec(v_fst_825_);
lean_dec_ref(v_msg_802_);
lean_dec_ref(v_tag_798_);
lean_dec(v_cls_796_);
v___x_847_ = lean_st_ref_take(v___y_807_);
v_traceState_848_ = lean_ctor_get(v___x_847_, 4);
v_env_849_ = lean_ctor_get(v___x_847_, 0);
v_nextMacroScope_850_ = lean_ctor_get(v___x_847_, 1);
v_ngen_851_ = lean_ctor_get(v___x_847_, 2);
v_auxDeclNGen_852_ = lean_ctor_get(v___x_847_, 3);
v_cache_853_ = lean_ctor_get(v___x_847_, 5);
v_messages_854_ = lean_ctor_get(v___x_847_, 6);
v_infoState_855_ = lean_ctor_get(v___x_847_, 7);
v_snapshotTasks_856_ = lean_ctor_get(v___x_847_, 8);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_875_ == 0)
{
v___x_858_ = v___x_847_;
v_isShared_859_ = v_isSharedCheck_875_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_snapshotTasks_856_);
lean_inc(v_infoState_855_);
lean_inc(v_messages_854_);
lean_inc(v_cache_853_);
lean_inc(v_traceState_848_);
lean_inc(v_auxDeclNGen_852_);
lean_inc(v_ngen_851_);
lean_inc(v_nextMacroScope_850_);
lean_inc(v_env_849_);
lean_dec(v___x_847_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_875_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
uint64_t v_tid_860_; lean_object* v_traces_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_874_; 
v_tid_860_ = lean_ctor_get_uint64(v_traceState_848_, sizeof(void*)*1);
v_traces_861_ = lean_ctor_get(v_traceState_848_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v_traceState_848_);
if (v_isSharedCheck_874_ == 0)
{
v___x_863_ = v_traceState_848_;
v_isShared_864_ = v_isSharedCheck_874_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_traces_861_);
lean_dec(v_traceState_848_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_874_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_801_, v_traces_861_);
lean_dec_ref(v_traces_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_865_);
lean_ctor_set_uint64(v_reuseFailAlloc_873_, sizeof(void*)*1, v_tid_860_);
v___x_867_ = v_reuseFailAlloc_873_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_869_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 4, v___x_867_);
v___x_869_ = v___x_858_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_env_849_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_nextMacroScope_850_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_ngen_851_);
lean_ctor_set(v_reuseFailAlloc_872_, 3, v_auxDeclNGen_852_);
lean_ctor_set(v_reuseFailAlloc_872_, 4, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_872_, 5, v_cache_853_);
lean_ctor_set(v_reuseFailAlloc_872_, 6, v_messages_854_);
lean_ctor_set(v_reuseFailAlloc_872_, 7, v_infoState_855_);
lean_ctor_set(v_reuseFailAlloc_872_, 8, v_snapshotTasks_856_);
v___x_869_ = v_reuseFailAlloc_872_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_st_ref_set(v___y_807_, v___x_869_);
v___x_871_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_809_);
return v___x_871_;
}
}
}
}
}
else
{
goto v___jp_840_;
}
}
else
{
goto v___jp_840_;
}
}
v___jp_876_:
{
double v___x_878_; double v___x_879_; double v___x_880_; uint8_t v___x_881_; 
v___x_878_ = lean_unbox_float(v_snd_826_);
v___x_879_ = lean_unbox_float(v_fst_825_);
v___x_880_ = lean_float_sub(v___x_878_, v___x_879_);
v___x_881_ = lean_float_decLt(v___y_877_, v___x_880_);
v___y_846_ = v___x_881_;
goto v___jp_845_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_892_, lean_object* v_collapsed_893_, lean_object* v_tag_894_, lean_object* v_opts_895_, lean_object* v_clsEnabled_896_, lean_object* v_oldTraces_897_, lean_object* v_msg_898_, lean_object* v_resStartStop_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
uint8_t v_collapsed_boxed_905_; uint8_t v_clsEnabled_boxed_906_; lean_object* v_res_907_; 
v_collapsed_boxed_905_ = lean_unbox(v_collapsed_893_);
v_clsEnabled_boxed_906_ = lean_unbox(v_clsEnabled_896_);
v_res_907_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_892_, v_collapsed_boxed_905_, v_tag_894_, v_opts_895_, v_clsEnabled_boxed_906_, v_oldTraces_897_, v_msg_898_, v_resStartStop_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec_ref(v_opts_895_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__11___boxed(lean_object* v_tail_951_, lean_object* v_cfg_952_, lean_object* v_trace_953_, lean_object* v_next_954_, lean_object* v_goals_955_, lean_object* v_n_956_, lean_object* v_acc_957_, lean_object* v_r_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__11(v_tail_951_, v_cfg_952_, v_trace_953_, v_next_954_, v_goals_955_, v_n_956_, v_acc_957_, v_r_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
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
uint8_t v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; uint8_t v___y_983_; lean_object* v___y_984_; lean_object* v_a_985_; uint8_t v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; uint8_t v___y_1000_; lean_object* v___y_1001_; lean_object* v_a_1002_; uint8_t v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; uint8_t v___y_1021_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; uint8_t v___y_1068_; uint8_t v_a_1069_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; uint8_t v___y_1077_; lean_object* v___y_1078_; uint8_t v___y_1079_; lean_object* v___y_1080_; lean_object* v_a_1081_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; uint8_t v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; uint8_t v___y_1097_; lean_object* v_a_1098_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; uint8_t v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; uint8_t v___y_1107_; lean_object* v_a_1108_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; uint8_t v___y_1114_; lean_object* v___y_1115_; uint8_t v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; uint8_t v___y_1126_; uint8_t v___y_1127_; lean_object* v___y_1128_; lean_object* v_a_1129_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; uint8_t v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; uint8_t v___y_1148_; lean_object* v_a_1149_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; uint8_t v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; uint8_t v___y_1158_; lean_object* v_a_1159_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; uint8_t v___y_1166_; uint8_t v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v_zero_1172_; uint8_t v_isZero_1173_; 
v_zero_1172_ = lean_unsigned_to_nat(0u);
v_isZero_1173_ = lean_nat_dec_eq(v_n_969_, v_zero_1172_);
if (v_isZero_1173_ == 1)
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec(v_acc_971_);
lean_dec(v_curr_970_);
lean_dec(v_n_969_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v___x_1174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1175_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1174_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1175_;
}
else
{
lean_object* v_proc_1176_; lean_object* v_suspend_1177_; lean_object* v_discharge_1178_; lean_object* v___f_1179_; uint8_t v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; uint8_t v___y_1186_; lean_object* v_a_1187_; uint8_t v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; uint8_t v___y_1202_; lean_object* v_a_1203_; uint8_t v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; uint8_t v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; uint8_t v___y_1269_; uint8_t v_a_1270_; lean_object* v___f_1274_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; uint8_t v___y_1279_; lean_object* v___y_1280_; uint8_t v___y_1281_; lean_object* v_a_1282_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; uint8_t v___y_1298_; lean_object* v___y_1299_; uint8_t v___y_1300_; lean_object* v_a_1301_; lean_object* v___f_1310_; lean_object* v___y_1312_; uint8_t v___y_1313_; uint8_t v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1353_; uint8_t v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; uint8_t v_a_1357_; lean_object* v___y_1362_; uint8_t v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; uint8_t v___y_1366_; lean_object* v___y_1367_; lean_object* v_a_1368_; lean_object* v___y_1378_; lean_object* v___y_1379_; uint8_t v___y_1380_; lean_object* v___y_1381_; uint8_t v___y_1382_; lean_object* v___y_1383_; lean_object* v_a_1384_; lean_object* v___y_1397_; lean_object* v___y_1398_; uint8_t v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; uint8_t v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1445_; uint8_t v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; uint8_t v___y_1450_; lean_object* v___y_1451_; uint8_t v_a_1452_; lean_object* v___y_1455_; lean_object* v___y_1456_; uint8_t v___y_1457_; lean_object* v___y_1458_; uint8_t v___y_1459_; lean_object* v___y_1460_; lean_object* v_a_1461_; lean_object* v___y_1474_; lean_object* v___y_1475_; uint8_t v___y_1476_; lean_object* v___y_1477_; uint8_t v___y_1478_; lean_object* v___y_1479_; lean_object* v_a_1480_; lean_object* v___f_1489_; lean_object* v___y_1491_; lean_object* v___y_1492_; uint8_t v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; uint8_t v___y_1498_; uint8_t v___y_1499_; lean_object* v___y_1500_; lean_object* v_a_1501_; lean_object* v___y_1511_; uint8_t v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; uint8_t v___y_1517_; lean_object* v___y_1518_; uint8_t v___y_1519_; lean_object* v___y_1520_; lean_object* v_a_1521_; lean_object* v___y_1534_; uint8_t v___y_1535_; uint8_t v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; uint8_t v___y_1539_; lean_object* v___y_1540_; uint8_t v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1586_; lean_object* v___y_1587_; uint8_t v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; uint8_t v___y_1594_; lean_object* v___y_1595_; uint8_t v___y_1596_; uint8_t v_a_1597_; uint8_t v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; uint8_t v___y_1609_; uint8_t v___y_1610_; lean_object* v___y_1611_; lean_object* v_a_1612_; uint8_t v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; uint8_t v___y_1632_; uint8_t v___y_1633_; lean_object* v___y_1634_; lean_object* v_a_1635_; uint8_t v___y_1645_; lean_object* v___y_1646_; uint8_t v___y_1647_; lean_object* v___y_1648_; uint8_t v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; uint8_t v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1697_; lean_object* v___y_1698_; uint8_t v___y_1699_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; uint8_t v___y_1705_; lean_object* v___y_1706_; uint8_t v___y_1707_; uint8_t v_a_1708_; lean_object* v___y_1713_; uint8_t v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; uint8_t v___y_1720_; uint8_t v___y_1721_; lean_object* v___y_1722_; lean_object* v_a_1723_; lean_object* v___y_1733_; uint8_t v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; uint8_t v___y_1740_; uint8_t v___y_1741_; lean_object* v___y_1742_; lean_object* v_a_1743_; lean_object* v___y_1756_; uint8_t v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; uint8_t v___y_1763_; uint8_t v___y_1764_; lean_object* v___y_1765_; lean_object* v_a_1766_; lean_object* v___y_1779_; uint8_t v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; uint8_t v___y_1786_; uint8_t v___y_1787_; lean_object* v___y_1788_; lean_object* v_a_1789_; lean_object* v___y_1799_; uint8_t v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; uint8_t v___y_1803_; uint8_t v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; uint8_t v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; uint8_t v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; uint8_t v___y_1859_; lean_object* v___y_1860_; uint8_t v___y_1861_; uint8_t v_a_1862_; uint8_t v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; uint8_t v___y_1874_; uint8_t v___y_1875_; lean_object* v___y_1876_; lean_object* v_a_1877_; uint8_t v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; uint8_t v___y_1894_; uint8_t v___y_1895_; lean_object* v___y_1896_; lean_object* v_a_1897_; lean_object* v___y_1910_; uint8_t v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; uint8_t v___y_1916_; uint8_t v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v_a_1920_; lean_object* v___y_1933_; lean_object* v___y_1934_; uint8_t v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; uint8_t v___y_1939_; uint8_t v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v_a_1943_; lean_object* v___y_1953_; uint8_t v___y_1954_; uint8_t v___y_1955_; uint8_t v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; uint8_t v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_2005_; lean_object* v___y_2006_; uint8_t v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; uint8_t v___y_2013_; lean_object* v___y_2014_; uint8_t v___y_2015_; uint8_t v_a_2016_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; uint8_t v___y_2025_; lean_object* v___y_2026_; lean_object* v_a_2027_; lean_object* v___y_2037_; lean_object* v___y_2038_; uint8_t v___y_2039_; lean_object* v___y_2040_; uint8_t v___y_2041_; lean_object* v___y_2042_; lean_object* v_a_2043_; lean_object* v___y_2056_; uint8_t v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; uint8_t v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2104_; uint8_t v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; uint8_t v___y_2109_; lean_object* v___y_2110_; uint8_t v_a_2111_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; uint8_t v___y_2118_; uint8_t v___y_2119_; lean_object* v_a_2120_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; uint8_t v___y_2137_; uint8_t v___y_2138_; lean_object* v_a_2139_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; uint8_t v___y_2154_; uint8_t v___y_2155_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2201_; uint8_t v___y_2202_; uint8_t v_a_2203_; lean_object* v_one_2207_; lean_object* v_n_2208_; lean_object* v___y_2210_; lean_object* v___y_2211_; uint8_t v___y_2212_; lean_object* v___y_2213_; uint8_t v___y_2214_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; uint8_t v___y_2259_; uint8_t v_a_2260_; lean_object* v___y_2265_; lean_object* v___y_2266_; uint8_t v___y_2267_; lean_object* v___y_2268_; uint8_t v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; uint8_t v___y_2273_; uint8_t v___y_2274_; lean_object* v___y_2300_; uint8_t v___y_2301_; lean_object* v___y_2302_; uint8_t v___y_2303_; lean_object* v___y_2304_; uint8_t v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; uint8_t v___y_2349_; lean_object* v___y_2350_; uint8_t v_a_2351_; lean_object* v___y_2354_; lean_object* v___y_2355_; uint8_t v___y_2356_; lean_object* v___y_2357_; uint8_t v___y_2358_; uint8_t v___y_2359_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; uint8_t v___y_2363_; lean_object* v___y_2364_; uint8_t v___y_2365_; uint8_t v___y_2389_; lean_object* v___y_2390_; uint8_t v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; uint8_t v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; uint8_t v___y_2398_; lean_object* v___y_2439_; uint8_t v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; uint8_t v___y_2445_; uint8_t v___y_2446_; lean_object* v___y_2447_; uint8_t v_a_2448_; lean_object* v___y_2453_; lean_object* v___y_2454_; uint8_t v___y_2455_; uint8_t v___y_2456_; uint8_t v___y_2457_; lean_object* v___y_2458_; uint8_t v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; uint8_t v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; uint8_t v___y_2468_; lean_object* v___y_2485_; uint8_t v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; uint8_t v___y_2489_; lean_object* v___y_2490_; uint8_t v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; uint8_t v___y_2494_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; uint8_t v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; uint8_t v___y_2541_; uint8_t v___y_2542_; lean_object* v___y_2543_; uint8_t v_a_2544_; lean_object* v___y_2549_; lean_object* v___y_2550_; uint8_t v___y_2551_; uint8_t v___y_2552_; lean_object* v___y_2553_; uint8_t v___y_2554_; lean_object* v___y_2555_; uint8_t v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; uint8_t v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; uint8_t v___y_2564_; lean_object* v___y_2581_; lean_object* v___y_2582_; uint8_t v___y_2583_; uint8_t v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; uint8_t v___y_2587_; uint8_t v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2632_; lean_object* v___y_2633_; uint8_t v___y_2634_; lean_object* v___y_2635_; uint8_t v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2638_; uint8_t v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; uint8_t v_a_2646_; lean_object* v_a_2671_; lean_object* v___y_2742_; lean_object* v___x_2752_; 
v_proc_1176_ = lean_ctor_get(v_cfg_965_, 1);
v_suspend_1177_ = lean_ctor_get(v_cfg_965_, 2);
v_discharge_1178_ = lean_ctor_get(v_cfg_965_, 3);
v___f_1179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_2207_ = lean_unsigned_to_nat(1u);
v_n_2208_ = lean_nat_sub(v_n_969_, v_one_2207_);
lean_dec(v_n_969_);
lean_inc_ref(v_proc_1176_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_curr_970_);
lean_inc(v_goals_968_);
v___x_2752_ = lean_apply_7(v_proc_1176_, v_goals_968_, v_curr_970_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
v_a_2671_ = v_a_2753_;
goto v___jp_2670_;
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2824_; 
v_a_2754_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2756_ = v___x_2752_;
v_isShared_2757_ = v_isSharedCheck_2824_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2752_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2824_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___f_2758_; uint8_t v___y_2760_; lean_object* v___y_2761_; uint8_t v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2800_; uint8_t v___y_2801_; lean_object* v___y_2802_; uint8_t v_a_2803_; uint8_t v___y_2810_; uint8_t v___x_2822_; 
lean_inc(v_a_2754_);
v___f_2758_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed), 7, 1);
lean_closure_set(v___f_2758_, 0, v_a_2754_);
v___x_2822_ = l_Lean_Exception_isInterrupt(v_a_2754_);
if (v___x_2822_ == 0)
{
uint8_t v___x_2823_; 
lean_inc(v_a_2754_);
v___x_2823_ = l_Lean_Exception_isRuntime(v_a_2754_);
v___y_2810_ = v___x_2823_;
goto v___jp_2809_;
}
else
{
v___y_2810_ = v___x_2822_;
goto v___jp_2809_;
}
v___jp_2759_:
{
lean_object* v___x_2764_; lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2798_; 
v___x_2764_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2798_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2798_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2769_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2770_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2763_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2771_ = lean_io_mono_nanos_now();
v___x_2772_ = lean_io_mono_nanos_now();
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v_a_2754_);
v___x_2774_ = v___x_2767_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2754_);
v___x_2774_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
double v___x_2775_; double v___x_2776_; double v___x_2777_; double v___x_2778_; double v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2775_ = lean_float_of_nat(v___x_2771_);
v___x_2776_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2777_ = lean_float_div(v___x_2775_, v___x_2776_);
v___x_2778_ = lean_float_of_nat(v___x_2772_);
v___x_2779_ = lean_float_div(v___x_2778_, v___x_2776_);
v___x_2780_ = lean_box_float(v___x_2777_);
v___x_2781_ = lean_box_float(v___x_2779_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2774_);
lean_ctor_set(v___x_2783_, 1, v___x_2782_);
lean_inc_ref(v___y_2761_);
lean_inc(v_trace_966_);
v___x_2784_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_966_, v___y_2762_, v___y_2761_, v___y_2763_, v___y_2760_, v_a_2765_, v___f_2758_, v___x_2783_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_2742_ = v___x_2784_;
goto v___jp_2741_;
}
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v___x_2786_ = lean_io_get_num_heartbeats();
v___x_2787_ = lean_io_get_num_heartbeats();
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v_a_2754_);
v___x_2789_ = v___x_2767_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2754_);
v___x_2789_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
double v___x_2790_; double v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2790_ = lean_float_of_nat(v___x_2786_);
v___x_2791_ = lean_float_of_nat(v___x_2787_);
v___x_2792_ = lean_box_float(v___x_2790_);
v___x_2793_ = lean_box_float(v___x_2791_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2789_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
lean_inc_ref(v___y_2761_);
lean_inc(v_trace_966_);
v___x_2796_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_966_, v___y_2762_, v___y_2761_, v___y_2763_, v___y_2760_, v_a_2765_, v___f_2758_, v___x_2795_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_2742_ = v___x_2796_;
goto v___jp_2741_;
}
}
}
}
v___jp_2799_:
{
lean_object* v___x_2804_; uint8_t v___x_2805_; 
v___x_2804_ = l_Lean_trace_profiler;
v___x_2805_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2802_, v___x_2804_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2807_; 
lean_dec_ref(v___f_2758_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_curr_970_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
if (v_isShared_2757_ == 0)
{
v___x_2807_ = v___x_2756_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2754_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
else
{
lean_del_object(v___x_2756_);
v___y_2760_ = v_a_2803_;
v___y_2761_ = v___y_2800_;
v___y_2762_ = v___y_2801_;
v___y_2763_ = v___y_2802_;
goto v___jp_2759_;
}
}
v___jp_2809_:
{
if (v___y_2810_ == 0)
{
lean_object* v_options_2811_; lean_object* v_inheritedTraceOptions_2812_; uint8_t v_hasTrace_2813_; uint8_t v___x_2814_; 
v_options_2811_ = lean_ctor_get(v_a_974_, 2);
v_inheritedTraceOptions_2812_ = lean_ctor_get(v_a_974_, 13);
v_hasTrace_2813_ = lean_ctor_get_uint8(v_options_2811_, sizeof(void*)*1);
v___x_2814_ = lean_bool_not(v_hasTrace_2813_);
if (v___x_2814_ == 0)
{
uint8_t v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = 1;
v___x_2816_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
if (v_hasTrace_2813_ == 0)
{
v___y_2800_ = v___x_2816_;
v___y_2801_ = v___x_2815_;
v___y_2802_ = v_options_2811_;
v_a_2803_ = v_hasTrace_2813_;
goto v___jp_2799_;
}
else
{
lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2818_ = l_Lean_Name_append(v___x_2817_, v_trace_966_);
v___x_2819_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2812_, v_options_2811_, v___x_2818_);
lean_dec(v___x_2818_);
if (v___x_2819_ == 0)
{
v___y_2800_ = v___x_2816_;
v___y_2801_ = v___x_2815_;
v___y_2802_ = v_options_2811_;
v_a_2803_ = v___x_2819_;
goto v___jp_2799_;
}
else
{
lean_del_object(v___x_2756_);
v___y_2760_ = v___x_2819_;
v___y_2761_ = v___x_2816_;
v___y_2762_ = v___x_2815_;
v___y_2763_ = v_options_2811_;
goto v___jp_2759_;
}
}
}
else
{
lean_object* v___x_2820_; 
lean_dec_ref(v___f_2758_);
lean_del_object(v___x_2756_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_curr_970_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v___x_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2820_, 0, v_a_2754_);
return v___x_2820_;
}
}
else
{
lean_object* v___x_2821_; 
lean_dec_ref(v___f_2758_);
lean_del_object(v___x_2756_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_curr_970_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v___x_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_a_2754_);
return v___x_2821_;
}
}
}
}
v___jp_1180_:
{
lean_object* v___x_1188_; double v___x_1189_; double v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1188_ = lean_io_get_num_heartbeats();
v___x_1189_ = lean_float_of_nat(v___y_1184_);
v___x_1190_ = lean_float_of_nat(v___x_1188_);
v___x_1191_ = lean_box_float(v___x_1189_);
v___x_1192_ = lean_box_float(v___x_1190_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_a_1187_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
lean_inc_ref(v___y_1185_);
v___x_1195_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1186_, v___y_1185_, v___y_1183_, v___y_1181_, v___y_1182_, v___f_1179_, v___x_1194_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1195_;
}
v___jp_1196_:
{
lean_object* v___x_1204_; double v___x_1205_; double v___x_1206_; double v___x_1207_; double v___x_1208_; double v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1204_ = lean_io_mono_nanos_now();
v___x_1205_ = lean_float_of_nat(v___y_1198_);
v___x_1206_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1207_ = lean_float_div(v___x_1205_, v___x_1206_);
v___x_1208_ = lean_float_of_nat(v___x_1204_);
v___x_1209_ = lean_float_div(v___x_1208_, v___x_1206_);
v___x_1210_ = lean_box_float(v___x_1207_);
v___x_1211_ = lean_box_float(v___x_1209_);
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_a_1203_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
lean_inc_ref(v___y_1201_);
v___x_1214_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1202_, v___y_1201_, v___y_1200_, v___y_1197_, v___y_1199_, v___f_1179_, v___x_1213_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1214_;
}
v___jp_1215_:
{
lean_object* v___x_1223_; lean_object* v_a_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1223_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref(v___x_1223_);
v___x_1225_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1226_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1220_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1228_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1218_, v___y_1219_, v___y_1217_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set_tag(v___x_1231_, 1);
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
v___y_1197_ = v___y_1216_;
v___y_1198_ = v___x_1227_;
v___y_1199_ = v_a_1224_;
v___y_1200_ = v___y_1220_;
v___y_1201_ = v___y_1222_;
v___y_1202_ = v___y_1221_;
v_a_1203_ = v___x_1234_;
goto v___jp_1196_;
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
v_a_1237_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1228_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1228_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set_tag(v___x_1239_, 0);
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
v___y_1197_ = v___y_1216_;
v___y_1198_ = v___x_1227_;
v___y_1199_ = v_a_1224_;
v___y_1200_ = v___y_1220_;
v___y_1201_ = v___y_1222_;
v___y_1202_ = v___y_1221_;
v_a_1203_ = v___x_1242_;
goto v___jp_1196_;
}
}
}
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1246_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1218_, v___y_1219_, v___y_1217_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set_tag(v___x_1249_, 1);
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
v___y_1181_ = v___y_1216_;
v___y_1182_ = v_a_1224_;
v___y_1183_ = v___y_1220_;
v___y_1184_ = v___x_1245_;
v___y_1185_ = v___y_1222_;
v___y_1186_ = v___y_1221_;
v_a_1187_ = v___x_1252_;
goto v___jp_1180_;
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_a_1255_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1246_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1246_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 0);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
v___y_1181_ = v___y_1216_;
v___y_1182_ = v_a_1224_;
v___y_1183_ = v___y_1220_;
v___y_1184_ = v___x_1245_;
v___y_1185_ = v___y_1222_;
v___y_1186_ = v___y_1221_;
v_a_1187_ = v___x_1260_;
goto v___jp_1180_;
}
}
}
}
}
v___jp_1263_:
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = l_Lean_trace_profiler;
v___x_1272_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1266_, v___x_1271_);
if (v___x_1272_ == 0)
{
v_n_969_ = v___y_1265_;
v_curr_970_ = v___y_1267_;
v_acc_971_ = v___y_1264_;
goto _start;
}
else
{
v___y_1216_ = v_a_1270_;
v___y_1217_ = v___y_1264_;
v___y_1218_ = v___y_1265_;
v___y_1219_ = v___y_1267_;
v___y_1220_ = v___y_1266_;
v___y_1221_ = v___y_1269_;
v___y_1222_ = v___y_1268_;
goto v___jp_1215_;
}
}
v___jp_1275_:
{
lean_object* v___x_1283_; double v___x_1284_; double v___x_1285_; double v___x_1286_; double v___x_1287_; double v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1283_ = lean_io_mono_nanos_now();
v___x_1284_ = lean_float_of_nat(v___y_1276_);
v___x_1285_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1286_ = lean_float_div(v___x_1284_, v___x_1285_);
v___x_1287_ = lean_float_of_nat(v___x_1283_);
v___x_1288_ = lean_float_div(v___x_1287_, v___x_1285_);
v___x_1289_ = lean_box_float(v___x_1286_);
v___x_1290_ = lean_box_float(v___x_1288_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1289_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_a_1282_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
lean_inc_ref(v___y_1278_);
v___x_1293_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1281_, v___y_1278_, v___y_1280_, v___y_1279_, v___y_1277_, v___f_1274_, v___x_1292_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1293_;
}
v___jp_1294_:
{
lean_object* v___x_1302_; double v___x_1303_; double v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1302_ = lean_io_get_num_heartbeats();
v___x_1303_ = lean_float_of_nat(v___y_1296_);
v___x_1304_ = lean_float_of_nat(v___x_1302_);
v___x_1305_ = lean_box_float(v___x_1303_);
v___x_1306_ = lean_box_float(v___x_1304_);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1305_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_a_1301_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
lean_inc_ref(v___y_1297_);
v___x_1309_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1300_, v___y_1297_, v___y_1299_, v___y_1298_, v___y_1295_, v___f_1274_, v___x_1308_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1309_;
}
v___jp_1311_:
{
lean_object* v___x_1317_; lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1351_; 
v___x_1317_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1351_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1351_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1323_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1316_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1324_ = lean_io_mono_nanos_now();
v___x_1325_ = lean_io_mono_nanos_now();
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 1);
lean_ctor_set(v___x_1320_, 0, v___y_1312_);
v___x_1327_ = v___x_1320_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___y_1312_);
v___x_1327_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
double v___x_1328_; double v___x_1329_; double v___x_1330_; double v___x_1331_; double v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1328_ = lean_float_of_nat(v___x_1324_);
v___x_1329_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1330_ = lean_float_div(v___x_1328_, v___x_1329_);
v___x_1331_ = lean_float_of_nat(v___x_1325_);
v___x_1332_ = lean_float_div(v___x_1331_, v___x_1329_);
v___x_1333_ = lean_box_float(v___x_1330_);
v___x_1334_ = lean_box_float(v___x_1332_);
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1327_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
lean_inc_ref(v___y_1315_);
v___x_1337_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1313_, v_a_1318_, v___f_1310_, v___x_1336_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1337_;
}
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1339_ = lean_io_get_num_heartbeats();
v___x_1340_ = lean_io_get_num_heartbeats();
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 1);
lean_ctor_set(v___x_1320_, 0, v___y_1312_);
v___x_1342_ = v___x_1320_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___y_1312_);
v___x_1342_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
double v___x_1343_; double v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1343_ = lean_float_of_nat(v___x_1339_);
v___x_1344_ = lean_float_of_nat(v___x_1340_);
v___x_1345_ = lean_box_float(v___x_1343_);
v___x_1346_ = lean_box_float(v___x_1344_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1342_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
lean_inc_ref(v___y_1315_);
v___x_1349_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1313_, v_a_1318_, v___f_1310_, v___x_1348_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1349_;
}
}
}
}
v___jp_1352_:
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = l_Lean_trace_profiler;
v___x_1359_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1356_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
lean_dec(v_trace_966_);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___y_1353_);
return v___x_1360_;
}
else
{
v___y_1312_ = v___y_1353_;
v___y_1313_ = v_a_1357_;
v___y_1314_ = v___y_1354_;
v___y_1315_ = v___y_1355_;
v___y_1316_ = v___y_1356_;
goto v___jp_1311_;
}
}
v___jp_1361_:
{
lean_object* v___x_1369_; double v___x_1370_; double v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1369_ = lean_io_get_num_heartbeats();
v___x_1370_ = lean_float_of_nat(v___y_1364_);
v___x_1371_ = lean_float_of_nat(v___x_1369_);
v___x_1372_ = lean_box_float(v___x_1370_);
v___x_1373_ = lean_box_float(v___x_1371_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_a_1368_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
lean_inc_ref(v___y_1367_);
v___x_1376_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1366_, v___y_1367_, v___y_1365_, v___y_1363_, v___y_1362_, v___f_1179_, v___x_1375_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1376_;
}
v___jp_1377_:
{
lean_object* v___x_1385_; double v___x_1386_; double v___x_1387_; double v___x_1388_; double v___x_1389_; double v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1385_ = lean_io_mono_nanos_now();
v___x_1386_ = lean_float_of_nat(v___y_1378_);
v___x_1387_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1388_ = lean_float_div(v___x_1386_, v___x_1387_);
v___x_1389_ = lean_float_of_nat(v___x_1385_);
v___x_1390_ = lean_float_div(v___x_1389_, v___x_1387_);
v___x_1391_ = lean_box_float(v___x_1388_);
v___x_1392_ = lean_box_float(v___x_1390_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v_a_1384_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
lean_inc_ref(v___y_1383_);
v___x_1395_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1382_, v___y_1383_, v___y_1381_, v___y_1380_, v___y_1379_, v___f_1179_, v___x_1394_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1395_;
}
v___jp_1396_:
{
lean_object* v___x_1404_; lean_object* v_a_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1404_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1407_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1401_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1409_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1398_, v___y_1400_, v___y_1397_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
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
v___y_1378_ = v___x_1408_;
v___y_1379_ = v_a_1405_;
v___y_1380_ = v___y_1399_;
v___y_1381_ = v___y_1401_;
v___y_1382_ = v___y_1402_;
v___y_1383_ = v___y_1403_;
v_a_1384_ = v___x_1415_;
goto v___jp_1377_;
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
v___y_1378_ = v___x_1408_;
v___y_1379_ = v_a_1405_;
v___y_1380_ = v___y_1399_;
v___y_1381_ = v___y_1401_;
v___y_1382_ = v___y_1402_;
v___y_1383_ = v___y_1403_;
v_a_1384_ = v___x_1423_;
goto v___jp_1377_;
}
}
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1427_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1398_, v___y_1400_, v___y_1397_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
lean_ctor_set_tag(v___x_1430_, 1);
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
v___y_1362_ = v_a_1405_;
v___y_1363_ = v___y_1399_;
v___y_1364_ = v___x_1426_;
v___y_1365_ = v___y_1401_;
v___y_1366_ = v___y_1402_;
v___y_1367_ = v___y_1403_;
v_a_1368_ = v___x_1433_;
goto v___jp_1361_;
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1427_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1427_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set_tag(v___x_1438_, 0);
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
v___y_1362_ = v_a_1405_;
v___y_1363_ = v___y_1399_;
v___y_1364_ = v___x_1426_;
v___y_1365_ = v___y_1401_;
v___y_1366_ = v___y_1402_;
v___y_1367_ = v___y_1403_;
v_a_1368_ = v___x_1441_;
goto v___jp_1361_;
}
}
}
}
}
v___jp_1444_:
{
if (v___y_1446_ == 0)
{
v_n_969_ = v___y_1447_;
v_curr_970_ = v___y_1449_;
v_acc_971_ = v___y_1445_;
goto _start;
}
else
{
v___y_1397_ = v___y_1445_;
v___y_1398_ = v___y_1447_;
v___y_1399_ = v_a_1452_;
v___y_1400_ = v___y_1449_;
v___y_1401_ = v___y_1448_;
v___y_1402_ = v___y_1450_;
v___y_1403_ = v___y_1451_;
goto v___jp_1396_;
}
}
v___jp_1454_:
{
lean_object* v___x_1462_; double v___x_1463_; double v___x_1464_; double v___x_1465_; double v___x_1466_; double v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1462_ = lean_io_mono_nanos_now();
v___x_1463_ = lean_float_of_nat(v___y_1455_);
v___x_1464_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1465_ = lean_float_div(v___x_1463_, v___x_1464_);
v___x_1466_ = lean_float_of_nat(v___x_1462_);
v___x_1467_ = lean_float_div(v___x_1466_, v___x_1464_);
v___x_1468_ = lean_box_float(v___x_1465_);
v___x_1469_ = lean_box_float(v___x_1467_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1468_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v_a_1461_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
lean_inc_ref(v___y_1460_);
v___x_1472_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1459_, v___y_1460_, v___y_1458_, v___y_1457_, v___y_1456_, v___f_1274_, v___x_1471_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1472_;
}
v___jp_1473_:
{
lean_object* v___x_1481_; double v___x_1482_; double v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1481_ = lean_io_get_num_heartbeats();
v___x_1482_ = lean_float_of_nat(v___y_1474_);
v___x_1483_ = lean_float_of_nat(v___x_1481_);
v___x_1484_ = lean_box_float(v___x_1482_);
v___x_1485_ = lean_box_float(v___x_1483_);
v___x_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_a_1480_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
lean_inc_ref(v___y_1479_);
v___x_1488_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1478_, v___y_1479_, v___y_1477_, v___y_1476_, v___y_1475_, v___f_1274_, v___x_1487_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1488_;
}
v___jp_1490_:
{
lean_object* v___x_1502_; double v___x_1503_; double v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1502_ = lean_io_get_num_heartbeats();
v___x_1503_ = lean_float_of_nat(v___y_1492_);
v___x_1504_ = lean_float_of_nat(v___x_1502_);
v___x_1505_ = lean_box_float(v___x_1503_);
v___x_1506_ = lean_box_float(v___x_1504_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v_a_1501_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
lean_inc_ref(v___y_1500_);
lean_inc(v_trace_966_);
v___x_1509_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1498_, v___y_1500_, v___y_1495_, v___y_1493_, v___y_1491_, v___f_1489_, v___x_1508_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v___y_1494_;
v___y_1112_ = v___y_1495_;
v___y_1113_ = v___y_1497_;
v___y_1114_ = v___y_1498_;
v___y_1115_ = v___y_1496_;
v___y_1116_ = v___y_1499_;
v___y_1117_ = v___y_1500_;
v___y_1118_ = v___x_1509_;
goto v___jp_1110_;
}
v___jp_1510_:
{
lean_object* v___x_1522_; double v___x_1523_; double v___x_1524_; double v___x_1525_; double v___x_1526_; double v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1522_ = lean_io_mono_nanos_now();
v___x_1523_ = lean_float_of_nat(v___y_1518_);
v___x_1524_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1525_ = lean_float_div(v___x_1523_, v___x_1524_);
v___x_1526_ = lean_float_of_nat(v___x_1522_);
v___x_1527_ = lean_float_div(v___x_1526_, v___x_1524_);
v___x_1528_ = lean_box_float(v___x_1525_);
v___x_1529_ = lean_box_float(v___x_1527_);
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_a_1521_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
lean_inc_ref(v___y_1520_);
lean_inc(v_trace_966_);
v___x_1532_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1517_, v___y_1520_, v___y_1514_, v___y_1512_, v___y_1511_, v___f_1489_, v___x_1531_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v___y_1513_;
v___y_1112_ = v___y_1514_;
v___y_1113_ = v___y_1516_;
v___y_1114_ = v___y_1517_;
v___y_1115_ = v___y_1515_;
v___y_1116_ = v___y_1519_;
v___y_1117_ = v___y_1520_;
v___y_1118_ = v___x_1532_;
goto v___jp_1110_;
}
v___jp_1533_:
{
lean_object* v___x_1546_; 
v___x_1546_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_1541_ == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1549_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1534_, v___y_1543_, v___y_1538_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
lean_ctor_set_tag(v___x_1552_, 1);
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
v___y_1511_ = v_a_1547_;
v___y_1512_ = v___y_1539_;
v___y_1513_ = v___y_1540_;
v___y_1514_ = v___y_1542_;
v___y_1515_ = v___y_1544_;
v___y_1516_ = v___y_1545_;
v___y_1517_ = v___y_1535_;
v___y_1518_ = v___x_1548_;
v___y_1519_ = v___y_1536_;
v___y_1520_ = v___y_1537_;
v_a_1521_ = v___x_1555_;
goto v___jp_1510_;
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
v_a_1558_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1549_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1549_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set_tag(v___x_1560_, 0);
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
v___y_1511_ = v_a_1547_;
v___y_1512_ = v___y_1539_;
v___y_1513_ = v___y_1540_;
v___y_1514_ = v___y_1542_;
v___y_1515_ = v___y_1544_;
v___y_1516_ = v___y_1545_;
v___y_1517_ = v___y_1535_;
v___y_1518_ = v___x_1548_;
v___y_1519_ = v___y_1536_;
v___y_1520_ = v___y_1537_;
v_a_1521_ = v___x_1563_;
goto v___jp_1510_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_a_1566_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1546_);
v___x_1567_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1568_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1534_, v___y_1543_, v___y_1538_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 1);
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
v___y_1491_ = v_a_1566_;
v___y_1492_ = v___x_1567_;
v___y_1493_ = v___y_1539_;
v___y_1494_ = v___y_1540_;
v___y_1495_ = v___y_1542_;
v___y_1496_ = v___y_1544_;
v___y_1497_ = v___y_1545_;
v___y_1498_ = v___y_1535_;
v___y_1499_ = v___y_1536_;
v___y_1500_ = v___y_1537_;
v_a_1501_ = v___x_1574_;
goto v___jp_1490_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
v_a_1577_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1568_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1568_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 0);
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
v___y_1491_ = v_a_1566_;
v___y_1492_ = v___x_1567_;
v___y_1493_ = v___y_1539_;
v___y_1494_ = v___y_1540_;
v___y_1495_ = v___y_1542_;
v___y_1496_ = v___y_1544_;
v___y_1497_ = v___y_1545_;
v___y_1498_ = v___y_1535_;
v___y_1499_ = v___y_1536_;
v___y_1500_ = v___y_1537_;
v_a_1501_ = v___x_1582_;
goto v___jp_1490_;
}
}
}
}
}
v___jp_1585_:
{
lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = l_Lean_trace_profiler;
v___x_1599_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1591_, v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; 
lean_inc(v_trace_966_);
v___x_1600_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1589_, v___y_1590_, v___y_1586_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v___y_1587_;
v___y_1112_ = v___y_1591_;
v___y_1113_ = v___y_1592_;
v___y_1114_ = v___y_1594_;
v___y_1115_ = v___y_1593_;
v___y_1116_ = v___y_1596_;
v___y_1117_ = v___y_1595_;
v___y_1118_ = v___x_1600_;
goto v___jp_1110_;
}
else
{
v___y_1534_ = v___y_1589_;
v___y_1535_ = v___y_1594_;
v___y_1536_ = v___y_1596_;
v___y_1537_ = v___y_1595_;
v___y_1538_ = v___y_1586_;
v___y_1539_ = v_a_1597_;
v___y_1540_ = v___y_1587_;
v___y_1541_ = v___y_1588_;
v___y_1542_ = v___y_1591_;
v___y_1543_ = v___y_1590_;
v___y_1544_ = v___y_1593_;
v___y_1545_ = v___y_1592_;
goto v___jp_1533_;
}
}
v___jp_1601_:
{
lean_object* v___x_1613_; double v___x_1614_; double v___x_1615_; double v___x_1616_; double v___x_1617_; double v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1613_ = lean_io_mono_nanos_now();
v___x_1614_ = lean_float_of_nat(v___y_1603_);
v___x_1615_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1616_ = lean_float_div(v___x_1614_, v___x_1615_);
v___x_1617_ = lean_float_of_nat(v___x_1613_);
v___x_1618_ = lean_float_div(v___x_1617_, v___x_1615_);
v___x_1619_ = lean_box_float(v___x_1616_);
v___x_1620_ = lean_box_float(v___x_1618_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v_a_1612_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
lean_inc_ref(v___y_1611_);
lean_inc(v_trace_966_);
v___x_1623_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1609_, v___y_1611_, v___y_1607_, v___y_1602_, v___y_1606_, v___f_1179_, v___x_1622_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___y_1604_;
v___y_1163_ = v___y_1605_;
v___y_1164_ = v___y_1607_;
v___y_1165_ = v___y_1608_;
v___y_1166_ = v___y_1609_;
v___y_1167_ = v___y_1610_;
v___y_1168_ = v___y_1611_;
v___y_1169_ = v___x_1623_;
goto v___jp_1161_;
}
v___jp_1624_:
{
lean_object* v___x_1636_; double v___x_1637_; double v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1636_ = lean_io_get_num_heartbeats();
v___x_1637_ = lean_float_of_nat(v___y_1628_);
v___x_1638_ = lean_float_of_nat(v___x_1636_);
v___x_1639_ = lean_box_float(v___x_1637_);
v___x_1640_ = lean_box_float(v___x_1638_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_a_1635_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
lean_inc_ref(v___y_1634_);
lean_inc(v_trace_966_);
v___x_1643_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1632_, v___y_1634_, v___y_1630_, v___y_1625_, v___y_1629_, v___f_1179_, v___x_1642_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___y_1626_;
v___y_1163_ = v___y_1627_;
v___y_1164_ = v___y_1630_;
v___y_1165_ = v___y_1631_;
v___y_1166_ = v___y_1632_;
v___y_1167_ = v___y_1633_;
v___y_1168_ = v___y_1634_;
v___y_1169_ = v___x_1643_;
goto v___jp_1161_;
}
v___jp_1644_:
{
lean_object* v___x_1657_; 
v___x_1657_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_1652_ == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref(v___x_1657_);
v___x_1659_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1660_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1656_, v___y_1654_, v___y_1648_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 1);
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
v___y_1602_ = v___y_1645_;
v___y_1603_ = v___x_1659_;
v___y_1604_ = v___y_1646_;
v___y_1605_ = v___y_1651_;
v___y_1606_ = v_a_1658_;
v___y_1607_ = v___y_1653_;
v___y_1608_ = v___y_1655_;
v___y_1609_ = v___y_1647_;
v___y_1610_ = v___y_1649_;
v___y_1611_ = v___y_1650_;
v_a_1612_ = v___x_1666_;
goto v___jp_1601_;
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1660_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1660_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set_tag(v___x_1671_, 0);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
v___y_1602_ = v___y_1645_;
v___y_1603_ = v___x_1659_;
v___y_1604_ = v___y_1646_;
v___y_1605_ = v___y_1651_;
v___y_1606_ = v_a_1658_;
v___y_1607_ = v___y_1653_;
v___y_1608_ = v___y_1655_;
v___y_1609_ = v___y_1647_;
v___y_1610_ = v___y_1649_;
v___y_1611_ = v___y_1650_;
v_a_1612_ = v___x_1674_;
goto v___jp_1601_;
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_a_1677_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1677_);
lean_dec_ref(v___x_1657_);
v___x_1678_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1679_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1656_, v___y_1654_, v___y_1648_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 1);
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
v___y_1625_ = v___y_1645_;
v___y_1626_ = v___y_1646_;
v___y_1627_ = v___y_1651_;
v___y_1628_ = v___x_1678_;
v___y_1629_ = v_a_1677_;
v___y_1630_ = v___y_1653_;
v___y_1631_ = v___y_1655_;
v___y_1632_ = v___y_1647_;
v___y_1633_ = v___y_1649_;
v___y_1634_ = v___y_1650_;
v_a_1635_ = v___x_1685_;
goto v___jp_1624_;
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
v_a_1688_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1679_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1679_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set_tag(v___x_1690_, 0);
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
v___y_1625_ = v___y_1645_;
v___y_1626_ = v___y_1646_;
v___y_1627_ = v___y_1651_;
v___y_1628_ = v___x_1678_;
v___y_1629_ = v_a_1677_;
v___y_1630_ = v___y_1653_;
v___y_1631_ = v___y_1655_;
v___y_1632_ = v___y_1647_;
v___y_1633_ = v___y_1649_;
v___y_1634_ = v___y_1650_;
v_a_1635_ = v___x_1693_;
goto v___jp_1624_;
}
}
}
}
}
v___jp_1696_:
{
lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1709_ = l_Lean_trace_profiler;
v___x_1710_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1701_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_inc(v_trace_966_);
v___x_1711_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1702_, v___y_1700_, v___y_1704_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___y_1697_;
v___y_1163_ = v___y_1698_;
v___y_1164_ = v___y_1701_;
v___y_1165_ = v___y_1703_;
v___y_1166_ = v___y_1705_;
v___y_1167_ = v___y_1707_;
v___y_1168_ = v___y_1706_;
v___y_1169_ = v___x_1711_;
goto v___jp_1161_;
}
else
{
v___y_1645_ = v_a_1708_;
v___y_1646_ = v___y_1697_;
v___y_1647_ = v___y_1705_;
v___y_1648_ = v___y_1704_;
v___y_1649_ = v___y_1707_;
v___y_1650_ = v___y_1706_;
v___y_1651_ = v___y_1698_;
v___y_1652_ = v___y_1699_;
v___y_1653_ = v___y_1701_;
v___y_1654_ = v___y_1700_;
v___y_1655_ = v___y_1703_;
v___y_1656_ = v___y_1702_;
goto v___jp_1644_;
}
}
v___jp_1712_:
{
lean_object* v___x_1724_; double v___x_1725_; double v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1724_ = lean_io_get_num_heartbeats();
v___x_1725_ = lean_float_of_nat(v___y_1718_);
v___x_1726_ = lean_float_of_nat(v___x_1724_);
v___x_1727_ = lean_box_float(v___x_1725_);
v___x_1728_ = lean_box_float(v___x_1726_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1727_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_a_1723_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
lean_inc_ref(v___y_1722_);
lean_inc(v_trace_966_);
v___x_1731_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1720_, v___y_1722_, v___y_1717_, v___y_1714_, v___y_1713_, v___f_1274_, v___x_1730_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___y_1715_;
v___y_1163_ = v___y_1716_;
v___y_1164_ = v___y_1717_;
v___y_1165_ = v___y_1719_;
v___y_1166_ = v___y_1720_;
v___y_1167_ = v___y_1721_;
v___y_1168_ = v___y_1722_;
v___y_1169_ = v___x_1731_;
goto v___jp_1161_;
}
v___jp_1732_:
{
lean_object* v___x_1744_; double v___x_1745_; double v___x_1746_; double v___x_1747_; double v___x_1748_; double v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1744_ = lean_io_mono_nanos_now();
v___x_1745_ = lean_float_of_nat(v___y_1738_);
v___x_1746_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1747_ = lean_float_div(v___x_1745_, v___x_1746_);
v___x_1748_ = lean_float_of_nat(v___x_1744_);
v___x_1749_ = lean_float_div(v___x_1748_, v___x_1746_);
v___x_1750_ = lean_box_float(v___x_1747_);
v___x_1751_ = lean_box_float(v___x_1749_);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1750_);
lean_ctor_set(v___x_1752_, 1, v___x_1751_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v_a_1743_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
lean_inc_ref(v___y_1742_);
lean_inc(v_trace_966_);
v___x_1754_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1740_, v___y_1742_, v___y_1737_, v___y_1734_, v___y_1733_, v___f_1274_, v___x_1753_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___y_1735_;
v___y_1163_ = v___y_1736_;
v___y_1164_ = v___y_1737_;
v___y_1165_ = v___y_1739_;
v___y_1166_ = v___y_1740_;
v___y_1167_ = v___y_1741_;
v___y_1168_ = v___y_1742_;
v___y_1169_ = v___x_1754_;
goto v___jp_1161_;
}
v___jp_1755_:
{
lean_object* v___x_1767_; double v___x_1768_; double v___x_1769_; double v___x_1770_; double v___x_1771_; double v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1767_ = lean_io_mono_nanos_now();
v___x_1768_ = lean_float_of_nat(v___y_1759_);
v___x_1769_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1770_ = lean_float_div(v___x_1768_, v___x_1769_);
v___x_1771_ = lean_float_of_nat(v___x_1767_);
v___x_1772_ = lean_float_div(v___x_1771_, v___x_1769_);
v___x_1773_ = lean_box_float(v___x_1770_);
v___x_1774_ = lean_box_float(v___x_1772_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_a_1766_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
lean_inc_ref(v___y_1765_);
lean_inc(v_trace_966_);
v___x_1777_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1763_, v___y_1765_, v___y_1761_, v___y_1757_, v___y_1756_, v___f_1489_, v___x_1776_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___y_1758_;
v___y_1163_ = v___y_1760_;
v___y_1164_ = v___y_1761_;
v___y_1165_ = v___y_1762_;
v___y_1166_ = v___y_1763_;
v___y_1167_ = v___y_1764_;
v___y_1168_ = v___y_1765_;
v___y_1169_ = v___x_1777_;
goto v___jp_1161_;
}
v___jp_1778_:
{
lean_object* v___x_1790_; double v___x_1791_; double v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1790_ = lean_io_get_num_heartbeats();
v___x_1791_ = lean_float_of_nat(v___y_1784_);
v___x_1792_ = lean_float_of_nat(v___x_1790_);
v___x_1793_ = lean_box_float(v___x_1791_);
v___x_1794_ = lean_box_float(v___x_1792_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1793_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1796_, 0, v_a_1789_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
lean_inc_ref(v___y_1788_);
lean_inc(v_trace_966_);
v___x_1797_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1786_, v___y_1788_, v___y_1783_, v___y_1780_, v___y_1779_, v___f_1489_, v___x_1796_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___y_1781_;
v___y_1163_ = v___y_1782_;
v___y_1164_ = v___y_1783_;
v___y_1165_ = v___y_1785_;
v___y_1166_ = v___y_1786_;
v___y_1167_ = v___y_1787_;
v___y_1168_ = v___y_1788_;
v___y_1169_ = v___x_1797_;
goto v___jp_1161_;
}
v___jp_1798_:
{
lean_object* v___x_1811_; 
v___x_1811_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_1807_ == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref(v___x_1811_);
v___x_1813_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1814_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1799_, v___y_1809_, v___y_1801_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1822_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1822_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1820_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 1);
v___x_1820_ = v___x_1817_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
v___y_1756_ = v_a_1812_;
v___y_1757_ = v___y_1800_;
v___y_1758_ = v___y_1802_;
v___y_1759_ = v___x_1813_;
v___y_1760_ = v___y_1806_;
v___y_1761_ = v___y_1808_;
v___y_1762_ = v___y_1810_;
v___y_1763_ = v___y_1803_;
v___y_1764_ = v___y_1804_;
v___y_1765_ = v___y_1805_;
v_a_1766_ = v___x_1820_;
goto v___jp_1755_;
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
v_a_1823_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1814_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1814_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set_tag(v___x_1825_, 0);
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
v___y_1756_ = v_a_1812_;
v___y_1757_ = v___y_1800_;
v___y_1758_ = v___y_1802_;
v___y_1759_ = v___x_1813_;
v___y_1760_ = v___y_1806_;
v___y_1761_ = v___y_1808_;
v___y_1762_ = v___y_1810_;
v___y_1763_ = v___y_1803_;
v___y_1764_ = v___y_1804_;
v___y_1765_ = v___y_1805_;
v_a_1766_ = v___x_1828_;
goto v___jp_1755_;
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_a_1831_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1811_);
v___x_1832_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1833_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1799_, v___y_1809_, v___y_1801_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set_tag(v___x_1836_, 1);
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
v___y_1779_ = v_a_1831_;
v___y_1780_ = v___y_1800_;
v___y_1781_ = v___y_1802_;
v___y_1782_ = v___y_1806_;
v___y_1783_ = v___y_1808_;
v___y_1784_ = v___x_1832_;
v___y_1785_ = v___y_1810_;
v___y_1786_ = v___y_1803_;
v___y_1787_ = v___y_1804_;
v___y_1788_ = v___y_1805_;
v_a_1789_ = v___x_1839_;
goto v___jp_1778_;
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_a_1842_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1833_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1833_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set_tag(v___x_1844_, 0);
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
v___y_1779_ = v_a_1831_;
v___y_1780_ = v___y_1800_;
v___y_1781_ = v___y_1802_;
v___y_1782_ = v___y_1806_;
v___y_1783_ = v___y_1808_;
v___y_1784_ = v___x_1832_;
v___y_1785_ = v___y_1810_;
v___y_1786_ = v___y_1803_;
v___y_1787_ = v___y_1804_;
v___y_1788_ = v___y_1805_;
v_a_1789_ = v___x_1847_;
goto v___jp_1778_;
}
}
}
}
}
v___jp_1850_:
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = l_Lean_trace_profiler;
v___x_1864_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1857_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
lean_inc(v_trace_966_);
v___x_1865_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1851_, v___y_1856_, v___y_1852_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___y_1853_;
v___y_1163_ = v___y_1854_;
v___y_1164_ = v___y_1857_;
v___y_1165_ = v___y_1858_;
v___y_1166_ = v___y_1859_;
v___y_1167_ = v___y_1861_;
v___y_1168_ = v___y_1860_;
v___y_1169_ = v___x_1865_;
goto v___jp_1161_;
}
else
{
v___y_1799_ = v___y_1851_;
v___y_1800_ = v_a_1862_;
v___y_1801_ = v___y_1852_;
v___y_1802_ = v___y_1853_;
v___y_1803_ = v___y_1859_;
v___y_1804_ = v___y_1861_;
v___y_1805_ = v___y_1860_;
v___y_1806_ = v___y_1854_;
v___y_1807_ = v___y_1855_;
v___y_1808_ = v___y_1857_;
v___y_1809_ = v___y_1856_;
v___y_1810_ = v___y_1858_;
goto v___jp_1798_;
}
}
v___jp_1866_:
{
lean_object* v___x_1878_; double v___x_1879_; double v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1878_ = lean_io_get_num_heartbeats();
v___x_1879_ = lean_float_of_nat(v___y_1869_);
v___x_1880_ = lean_float_of_nat(v___x_1878_);
v___x_1881_ = lean_box_float(v___x_1879_);
v___x_1882_ = lean_box_float(v___x_1880_);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_a_1877_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
lean_inc_ref(v___y_1876_);
lean_inc(v_trace_966_);
v___x_1885_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1874_, v___y_1876_, v___y_1871_, v___y_1867_, v___y_1868_, v___f_1274_, v___x_1884_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v___y_1870_;
v___y_1112_ = v___y_1871_;
v___y_1113_ = v___y_1873_;
v___y_1114_ = v___y_1874_;
v___y_1115_ = v___y_1872_;
v___y_1116_ = v___y_1875_;
v___y_1117_ = v___y_1876_;
v___y_1118_ = v___x_1885_;
goto v___jp_1110_;
}
v___jp_1886_:
{
lean_object* v___x_1898_; double v___x_1899_; double v___x_1900_; double v___x_1901_; double v___x_1902_; double v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1898_ = lean_io_mono_nanos_now();
v___x_1899_ = lean_float_of_nat(v___y_1888_);
v___x_1900_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1901_ = lean_float_div(v___x_1899_, v___x_1900_);
v___x_1902_ = lean_float_of_nat(v___x_1898_);
v___x_1903_ = lean_float_div(v___x_1902_, v___x_1900_);
v___x_1904_ = lean_box_float(v___x_1901_);
v___x_1905_ = lean_box_float(v___x_1903_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v_a_1897_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
lean_inc_ref(v___y_1896_);
lean_inc(v_trace_966_);
v___x_1908_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1894_, v___y_1896_, v___y_1891_, v___y_1887_, v___y_1889_, v___f_1274_, v___x_1907_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v___y_1890_;
v___y_1112_ = v___y_1891_;
v___y_1113_ = v___y_1893_;
v___y_1114_ = v___y_1894_;
v___y_1115_ = v___y_1892_;
v___y_1116_ = v___y_1895_;
v___y_1117_ = v___y_1896_;
v___y_1118_ = v___x_1908_;
goto v___jp_1110_;
}
v___jp_1909_:
{
lean_object* v___x_1921_; double v___x_1922_; double v___x_1923_; double v___x_1924_; double v___x_1925_; double v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1921_ = lean_io_mono_nanos_now();
v___x_1922_ = lean_float_of_nat(v___y_1913_);
v___x_1923_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1924_ = lean_float_div(v___x_1922_, v___x_1923_);
v___x_1925_ = lean_float_of_nat(v___x_1921_);
v___x_1926_ = lean_float_div(v___x_1925_, v___x_1923_);
v___x_1927_ = lean_box_float(v___x_1924_);
v___x_1928_ = lean_box_float(v___x_1926_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1920_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
lean_inc_ref(v___y_1919_);
lean_inc(v_trace_966_);
v___x_1931_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1916_, v___y_1919_, v___y_1912_, v___y_1911_, v___y_1918_, v___f_1179_, v___x_1930_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v___y_1910_;
v___y_1112_ = v___y_1912_;
v___y_1113_ = v___y_1915_;
v___y_1114_ = v___y_1916_;
v___y_1115_ = v___y_1914_;
v___y_1116_ = v___y_1917_;
v___y_1117_ = v___y_1919_;
v___y_1118_ = v___x_1931_;
goto v___jp_1110_;
}
v___jp_1932_:
{
lean_object* v___x_1944_; double v___x_1945_; double v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1944_ = lean_io_get_num_heartbeats();
v___x_1945_ = lean_float_of_nat(v___y_1933_);
v___x_1946_ = lean_float_of_nat(v___x_1944_);
v___x_1947_ = lean_box_float(v___x_1945_);
v___x_1948_ = lean_box_float(v___x_1946_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v_a_1943_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
lean_inc_ref(v___y_1942_);
lean_inc(v_trace_966_);
v___x_1951_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1939_, v___y_1942_, v___y_1936_, v___y_1935_, v___y_1941_, v___f_1179_, v___x_1950_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v___y_1934_;
v___y_1112_ = v___y_1936_;
v___y_1113_ = v___y_1938_;
v___y_1114_ = v___y_1939_;
v___y_1115_ = v___y_1937_;
v___y_1116_ = v___y_1940_;
v___y_1117_ = v___y_1942_;
v___y_1118_ = v___x_1951_;
goto v___jp_1110_;
}
v___jp_1952_:
{
lean_object* v___x_1965_; 
v___x_1965_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_1959_ == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1968_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1953_, v___y_1961_, v___y_1962_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
lean_ctor_set_tag(v___x_1971_, 1);
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
v___y_1910_ = v___y_1958_;
v___y_1911_ = v___y_1954_;
v___y_1912_ = v___y_1960_;
v___y_1913_ = v___x_1967_;
v___y_1914_ = v___y_1963_;
v___y_1915_ = v___y_1964_;
v___y_1916_ = v___y_1955_;
v___y_1917_ = v___y_1956_;
v___y_1918_ = v_a_1966_;
v___y_1919_ = v___y_1957_;
v_a_1920_ = v___x_1974_;
goto v___jp_1909_;
}
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
v_a_1977_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1968_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1968_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set_tag(v___x_1979_, 0);
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
v___y_1910_ = v___y_1958_;
v___y_1911_ = v___y_1954_;
v___y_1912_ = v___y_1960_;
v___y_1913_ = v___x_1967_;
v___y_1914_ = v___y_1963_;
v___y_1915_ = v___y_1964_;
v___y_1916_ = v___y_1955_;
v___y_1917_ = v___y_1956_;
v___y_1918_ = v_a_1966_;
v___y_1919_ = v___y_1957_;
v_a_1920_ = v___x_1982_;
goto v___jp_1909_;
}
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_a_1985_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1985_);
lean_dec_ref(v___x_1965_);
v___x_1986_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_1987_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1953_, v___y_1961_, v___y_1962_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 1);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
v___y_1933_ = v___x_1986_;
v___y_1934_ = v___y_1958_;
v___y_1935_ = v___y_1954_;
v___y_1936_ = v___y_1960_;
v___y_1937_ = v___y_1963_;
v___y_1938_ = v___y_1964_;
v___y_1939_ = v___y_1955_;
v___y_1940_ = v___y_1956_;
v___y_1941_ = v_a_1985_;
v___y_1942_ = v___y_1957_;
v_a_1943_ = v___x_1993_;
goto v___jp_1932_;
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
v_a_1996_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1987_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1987_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 0);
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
v___y_1933_ = v___x_1986_;
v___y_1934_ = v___y_1958_;
v___y_1935_ = v___y_1954_;
v___y_1936_ = v___y_1960_;
v___y_1937_ = v___y_1963_;
v___y_1938_ = v___y_1964_;
v___y_1939_ = v___y_1955_;
v___y_1940_ = v___y_1956_;
v___y_1941_ = v_a_1985_;
v___y_1942_ = v___y_1957_;
v_a_1943_ = v___x_2001_;
goto v___jp_1932_;
}
}
}
}
}
v___jp_2004_:
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = l_Lean_trace_profiler;
v___x_2018_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2010_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
lean_inc(v_trace_966_);
v___x_2019_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_2005_, v___y_2009_, v___y_2008_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v___y_2006_;
v___y_1112_ = v___y_2010_;
v___y_1113_ = v___y_2011_;
v___y_1114_ = v___y_2013_;
v___y_1115_ = v___y_2012_;
v___y_1116_ = v___y_2015_;
v___y_1117_ = v___y_2014_;
v___y_1118_ = v___x_2019_;
goto v___jp_1110_;
}
else
{
v___y_1953_ = v___y_2005_;
v___y_1954_ = v_a_2016_;
v___y_1955_ = v___y_2013_;
v___y_1956_ = v___y_2015_;
v___y_1957_ = v___y_2014_;
v___y_1958_ = v___y_2006_;
v___y_1959_ = v___y_2007_;
v___y_1960_ = v___y_2010_;
v___y_1961_ = v___y_2009_;
v___y_1962_ = v___y_2008_;
v___y_1963_ = v___y_2012_;
v___y_1964_ = v___y_2011_;
goto v___jp_1952_;
}
}
v___jp_2020_:
{
lean_object* v___x_2028_; double v___x_2029_; double v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2028_ = lean_io_get_num_heartbeats();
v___x_2029_ = lean_float_of_nat(v___y_2023_);
v___x_2030_ = lean_float_of_nat(v___x_2028_);
v___x_2031_ = lean_box_float(v___x_2029_);
v___x_2032_ = lean_box_float(v___x_2030_);
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v_a_2027_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
lean_inc_ref(v___y_2026_);
v___x_2035_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_2025_, v___y_2026_, v___y_2024_, v___y_2022_, v___y_2021_, v___f_1489_, v___x_2034_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_2035_;
}
v___jp_2036_:
{
lean_object* v___x_2044_; double v___x_2045_; double v___x_2046_; double v___x_2047_; double v___x_2048_; double v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2044_ = lean_io_mono_nanos_now();
v___x_2045_ = lean_float_of_nat(v___y_2037_);
v___x_2046_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2047_ = lean_float_div(v___x_2045_, v___x_2046_);
v___x_2048_ = lean_float_of_nat(v___x_2044_);
v___x_2049_ = lean_float_div(v___x_2048_, v___x_2046_);
v___x_2050_ = lean_box_float(v___x_2047_);
v___x_2051_ = lean_box_float(v___x_2049_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v_a_2043_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
lean_inc_ref(v___y_2042_);
v___x_2054_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_2041_, v___y_2042_, v___y_2040_, v___y_2039_, v___y_2038_, v___f_1489_, v___x_2053_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_2054_;
}
v___jp_2055_:
{
lean_object* v___x_2063_; lean_object* v_a_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2063_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2063_);
v___x_2065_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2066_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2060_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_2068_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_2058_, v___y_2059_, v___y_2056_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
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
v___y_2037_ = v___x_2067_;
v___y_2038_ = v_a_2064_;
v___y_2039_ = v___y_2057_;
v___y_2040_ = v___y_2060_;
v___y_2041_ = v___y_2061_;
v___y_2042_ = v___y_2062_;
v_a_2043_ = v___x_2074_;
goto v___jp_2036_;
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
v___y_2037_ = v___x_2067_;
v___y_2038_ = v_a_2064_;
v___y_2039_ = v___y_2057_;
v___y_2040_ = v___y_2060_;
v___y_2041_ = v___y_2061_;
v___y_2042_ = v___y_2062_;
v_a_2043_ = v___x_2082_;
goto v___jp_2036_;
}
}
}
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_2086_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_2058_, v___y_2059_, v___y_2056_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2086_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2086_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set_tag(v___x_2089_, 1);
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
v___y_2021_ = v_a_2064_;
v___y_2022_ = v___y_2057_;
v___y_2023_ = v___x_2085_;
v___y_2024_ = v___y_2060_;
v___y_2025_ = v___y_2061_;
v___y_2026_ = v___y_2062_;
v_a_2027_ = v___x_2092_;
goto v___jp_2020_;
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
v_a_2095_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2086_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2086_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 0);
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
v___y_2021_ = v_a_2064_;
v___y_2022_ = v___y_2057_;
v___y_2023_ = v___x_2085_;
v___y_2024_ = v___y_2060_;
v___y_2025_ = v___y_2061_;
v___y_2026_ = v___y_2062_;
v_a_2027_ = v___x_2100_;
goto v___jp_2020_;
}
}
}
}
}
v___jp_2103_:
{
if (v___y_2105_ == 0)
{
v_n_969_ = v___y_2106_;
v_curr_970_ = v___y_2108_;
v_acc_971_ = v___y_2104_;
goto _start;
}
else
{
v___y_2056_ = v___y_2104_;
v___y_2057_ = v_a_2111_;
v___y_2058_ = v___y_2106_;
v___y_2059_ = v___y_2108_;
v___y_2060_ = v___y_2107_;
v___y_2061_ = v___y_2109_;
v___y_2062_ = v___y_2110_;
goto v___jp_2055_;
}
}
v___jp_2113_:
{
lean_object* v___x_2121_; double v___x_2122_; double v___x_2123_; double v___x_2124_; double v___x_2125_; double v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2121_ = lean_io_mono_nanos_now();
v___x_2122_ = lean_float_of_nat(v___y_2115_);
v___x_2123_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2124_ = lean_float_div(v___x_2122_, v___x_2123_);
v___x_2125_ = lean_float_of_nat(v___x_2121_);
v___x_2126_ = lean_float_div(v___x_2125_, v___x_2123_);
v___x_2127_ = lean_box_float(v___x_2124_);
v___x_2128_ = lean_box_float(v___x_2126_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_a_2120_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
lean_inc_ref(v___y_2114_);
v___x_2131_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_2118_, v___y_2114_, v___y_2116_, v___y_2119_, v___y_2117_, v___f_1489_, v___x_2130_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_2131_;
}
v___jp_2132_:
{
lean_object* v___x_2140_; double v___x_2141_; double v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2140_ = lean_io_get_num_heartbeats();
v___x_2141_ = lean_float_of_nat(v___y_2133_);
v___x_2142_ = lean_float_of_nat(v___x_2140_);
v___x_2143_ = lean_box_float(v___x_2141_);
v___x_2144_ = lean_box_float(v___x_2142_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2146_, 0, v_a_2139_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
lean_inc_ref(v___y_2134_);
v___x_2147_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_2137_, v___y_2134_, v___y_2135_, v___y_2138_, v___y_2136_, v___f_1489_, v___x_2146_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_2147_;
}
v___jp_2148_:
{
lean_object* v___x_2156_; lean_object* v_a_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2156_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2156_);
v___x_2158_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2159_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2153_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_2161_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_2149_, v___y_2152_, v___y_2150_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
lean_ctor_set_tag(v___x_2164_, 1);
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
v___y_2114_ = v___y_2151_;
v___y_2115_ = v___x_2160_;
v___y_2116_ = v___y_2153_;
v___y_2117_ = v_a_2157_;
v___y_2118_ = v___y_2154_;
v___y_2119_ = v___y_2155_;
v_a_2120_ = v___x_2167_;
goto v___jp_2113_;
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
v_a_2170_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2161_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2161_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 0);
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
v___y_2114_ = v___y_2151_;
v___y_2115_ = v___x_2160_;
v___y_2116_ = v___y_2153_;
v___y_2117_ = v_a_2157_;
v___y_2118_ = v___y_2154_;
v___y_2119_ = v___y_2155_;
v_a_2120_ = v___x_2175_;
goto v___jp_2113_;
}
}
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_2179_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_2149_, v___y_2152_, v___y_2150_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set_tag(v___x_2182_, 1);
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
v___y_2133_ = v___x_2178_;
v___y_2134_ = v___y_2151_;
v___y_2135_ = v___y_2153_;
v___y_2136_ = v_a_2157_;
v___y_2137_ = v___y_2154_;
v___y_2138_ = v___y_2155_;
v_a_2139_ = v___x_2185_;
goto v___jp_2132_;
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
v_a_2188_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2179_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2179_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
lean_ctor_set_tag(v___x_2190_, 0);
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
v___y_2133_ = v___x_2178_;
v___y_2134_ = v___y_2151_;
v___y_2135_ = v___y_2153_;
v___y_2136_ = v_a_2157_;
v___y_2137_ = v___y_2154_;
v___y_2138_ = v___y_2155_;
v_a_2139_ = v___x_2193_;
goto v___jp_2132_;
}
}
}
}
}
v___jp_2196_:
{
lean_object* v___x_2204_; uint8_t v___x_2205_; 
v___x_2204_ = l_Lean_trace_profiler;
v___x_2205_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2200_, v___x_2204_);
if (v___x_2205_ == 0)
{
v_n_969_ = v___y_2197_;
v_curr_970_ = v___y_2201_;
v_acc_971_ = v___y_2198_;
goto _start;
}
else
{
v___y_2149_ = v___y_2197_;
v___y_2150_ = v___y_2198_;
v___y_2151_ = v___y_2199_;
v___y_2152_ = v___y_2201_;
v___y_2153_ = v___y_2200_;
v___y_2154_ = v___y_2202_;
v___y_2155_ = v_a_2203_;
goto v___jp_2148_;
}
}
v___jp_2209_:
{
lean_object* v___x_2215_; lean_object* v_a_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; 
v___x_2215_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref(v___x_2215_);
v___x_2217_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2218_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2213_, v___x_2217_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_2220_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___y_2210_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 1);
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
v___y_1276_ = v___x_2219_;
v___y_1277_ = v_a_2216_;
v___y_1278_ = v___y_2211_;
v___y_1279_ = v___y_2212_;
v___y_1280_ = v___y_2213_;
v___y_1281_ = v___y_2214_;
v_a_1282_ = v___x_2226_;
goto v___jp_1275_;
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
v_a_2229_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2220_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2220_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
lean_ctor_set_tag(v___x_2231_, 0);
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
v___y_1276_ = v___x_2219_;
v___y_1277_ = v_a_2216_;
v___y_1278_ = v___y_2211_;
v___y_1279_ = v___y_2212_;
v___y_1280_ = v___y_2213_;
v___y_1281_ = v___y_2214_;
v_a_1282_ = v___x_2234_;
goto v___jp_1275_;
}
}
}
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_2238_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___y_2210_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set_tag(v___x_2241_, 1);
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
v___y_1295_ = v_a_2216_;
v___y_1296_ = v___x_2237_;
v___y_1297_ = v___y_2211_;
v___y_1298_ = v___y_2212_;
v___y_1299_ = v___y_2213_;
v___y_1300_ = v___y_2214_;
v_a_1301_ = v___x_2244_;
goto v___jp_1294_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_a_2247_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2238_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2238_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
lean_ctor_set_tag(v___x_2249_, 0);
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
v___y_1295_ = v_a_2216_;
v___y_1296_ = v___x_2237_;
v___y_1297_ = v___y_2211_;
v___y_1298_ = v___y_2212_;
v___y_1299_ = v___y_2213_;
v___y_1300_ = v___y_2214_;
v_a_1301_ = v___x_2252_;
goto v___jp_1294_;
}
}
}
}
}
v___jp_2255_:
{
lean_object* v___x_2261_; uint8_t v___x_2262_; 
v___x_2261_ = l_Lean_trace_profiler;
v___x_2262_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2258_, v___x_2261_);
if (v___x_2262_ == 0)
{
v_n_969_ = v_n_2208_;
v_curr_970_ = v___y_2256_;
goto _start;
}
else
{
v___y_2210_ = v___y_2256_;
v___y_2211_ = v___y_2257_;
v___y_2212_ = v_a_2260_;
v___y_2213_ = v___y_2258_;
v___y_2214_ = v___y_2259_;
goto v___jp_2209_;
}
}
v___jp_2264_:
{
if (v___y_2274_ == 0)
{
lean_object* v___x_2275_; 
lean_dec_ref(v___y_2270_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2265_);
v___x_2275_ = lean_apply_6(v___y_2268_, v___y_2265_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2275_, 1);
if (lean_obj_tag(v_a_2276_) == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_nat_add(v_n_2208_, v_one_2207_);
lean_dec(v_n_2208_);
v___x_2278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___y_2265_);
lean_ctor_set(v___x_2278_, 1, v_acc_971_);
if (v___y_2267_ == 0)
{
lean_object* v___x_2279_; 
v___x_2279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
if (v___y_2269_ == 0)
{
v___y_1264_ = v___x_2278_;
v___y_1265_ = v___x_2277_;
v___y_1266_ = v___y_2272_;
v___y_1267_ = v___y_2271_;
v___y_1268_ = v___x_2279_;
v___y_1269_ = v___y_2273_;
v_a_1270_ = v___y_2269_;
goto v___jp_1263_;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v___x_2280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2281_ = l_Lean_Name_append(v___x_2280_, v_trace_966_);
v___x_2282_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2266_, v___y_2272_, v___x_2281_);
lean_dec(v___x_2281_);
if (v___x_2282_ == 0)
{
v___y_1264_ = v___x_2278_;
v___y_1265_ = v___x_2277_;
v___y_1266_ = v___y_2272_;
v___y_1267_ = v___y_2271_;
v___y_1268_ = v___x_2279_;
v___y_1269_ = v___y_2273_;
v_a_1270_ = v___x_2282_;
goto v___jp_1263_;
}
else
{
v___y_1216_ = v___x_2282_;
v___y_1217_ = v___x_2278_;
v___y_1218_ = v___x_2277_;
v___y_1219_ = v___y_2271_;
v___y_1220_ = v___y_2272_;
v___y_1221_ = v___y_2273_;
v___y_1222_ = v___x_2279_;
goto v___jp_1215_;
}
}
}
else
{
v_n_969_ = v___x_2277_;
v_curr_970_ = v___y_2271_;
v_acc_971_ = v___x_2278_;
goto _start;
}
}
else
{
lean_object* v_val_2284_; lean_object* v___x_2285_; 
lean_dec(v___y_2265_);
v_val_2284_ = lean_ctor_get(v_a_2276_, 0);
lean_inc(v_val_2284_);
lean_dec_ref_known(v_a_2276_, 1);
v___x_2285_ = l_List_appendTR___redArg(v_val_2284_, v___y_2271_);
if (v___y_2267_ == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
if (v___y_2269_ == 0)
{
v___y_2256_ = v___x_2285_;
v___y_2257_ = v___x_2286_;
v___y_2258_ = v___y_2272_;
v___y_2259_ = v___y_2273_;
v_a_2260_ = v___y_2269_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2288_ = l_Lean_Name_append(v___x_2287_, v_trace_966_);
v___x_2289_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2266_, v___y_2272_, v___x_2288_);
lean_dec(v___x_2288_);
if (v___x_2289_ == 0)
{
v___y_2256_ = v___x_2285_;
v___y_2257_ = v___x_2286_;
v___y_2258_ = v___y_2272_;
v___y_2259_ = v___y_2273_;
v_a_2260_ = v___x_2289_;
goto v___jp_2255_;
}
else
{
v___y_2210_ = v___x_2285_;
v___y_2211_ = v___x_2286_;
v___y_2212_ = v___x_2289_;
v___y_2213_ = v___y_2272_;
v___y_2214_ = v___y_2273_;
goto v___jp_2209_;
}
}
}
else
{
v_n_969_ = v_n_2208_;
v_curr_970_ = v___x_2285_;
goto _start;
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v___y_2271_);
lean_dec(v___y_2265_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v_a_2291_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2275_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2275_);
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
else
{
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2265_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
return v___y_2270_;
}
}
v___jp_2299_:
{
lean_object* v___x_2305_; lean_object* v_a_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2305_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref(v___x_2305_);
v___x_2307_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2308_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2302_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_2310_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___y_2300_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2310_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2310_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set_tag(v___x_2313_, 1);
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
v___y_1455_ = v___x_2309_;
v___y_1456_ = v_a_2306_;
v___y_1457_ = v___y_2301_;
v___y_1458_ = v___y_2302_;
v___y_1459_ = v___y_2303_;
v___y_1460_ = v___y_2304_;
v_a_1461_ = v___x_2316_;
goto v___jp_1454_;
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
v_a_2319_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2310_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2310_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set_tag(v___x_2321_, 0);
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
v___y_1455_ = v___x_2309_;
v___y_1456_ = v_a_2306_;
v___y_1457_ = v___y_2301_;
v___y_1458_ = v___y_2302_;
v___y_1459_ = v___y_2303_;
v___y_1460_ = v___y_2304_;
v_a_1461_ = v___x_2324_;
goto v___jp_1454_;
}
}
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_2328_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___y_2300_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set_tag(v___x_2331_, 1);
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
v___y_1474_ = v___x_2327_;
v___y_1475_ = v_a_2306_;
v___y_1476_ = v___y_2301_;
v___y_1477_ = v___y_2302_;
v___y_1478_ = v___y_2303_;
v___y_1479_ = v___y_2304_;
v_a_1480_ = v___x_2334_;
goto v___jp_1473_;
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
v_a_2337_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2328_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2328_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
lean_ctor_set_tag(v___x_2339_, 0);
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
v___y_1474_ = v___x_2327_;
v___y_1475_ = v_a_2306_;
v___y_1476_ = v___y_2301_;
v___y_1477_ = v___y_2302_;
v___y_1478_ = v___y_2303_;
v___y_1479_ = v___y_2304_;
v_a_1480_ = v___x_2342_;
goto v___jp_1473_;
}
}
}
}
}
v___jp_2345_:
{
if (v___y_2346_ == 0)
{
v_n_969_ = v_n_2208_;
v_curr_970_ = v___y_2347_;
goto _start;
}
else
{
v___y_2300_ = v___y_2347_;
v___y_2301_ = v_a_2351_;
v___y_2302_ = v___y_2348_;
v___y_2303_ = v___y_2349_;
v___y_2304_ = v___y_2350_;
goto v___jp_2299_;
}
}
v___jp_2353_:
{
if (v___y_2365_ == 0)
{
lean_object* v___x_2366_; 
lean_dec_ref(v___y_2360_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2354_);
v___x_2366_ = lean_apply_6(v___y_2357_, v___y_2354_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
if (lean_obj_tag(v_a_2367_) == 0)
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_nat_add(v_n_2208_, v_one_2207_);
lean_dec(v_n_2208_);
v___x_2369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___y_2354_);
lean_ctor_set(v___x_2369_, 1, v_acc_971_);
if (v___y_2356_ == 0)
{
if (v___y_2359_ == 0)
{
v___y_1445_ = v___x_2369_;
v___y_1446_ = v___y_2358_;
v___y_1447_ = v___x_2368_;
v___y_1448_ = v___y_2362_;
v___y_1449_ = v___y_2361_;
v___y_1450_ = v___y_2363_;
v___y_1451_ = v___y_2364_;
v_a_1452_ = v___y_2359_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2371_ = l_Lean_Name_append(v___x_2370_, v_trace_966_);
v___x_2372_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2355_, v___y_2362_, v___x_2371_);
lean_dec(v___x_2371_);
if (v___x_2372_ == 0)
{
v___y_1445_ = v___x_2369_;
v___y_1446_ = v___y_2358_;
v___y_1447_ = v___x_2368_;
v___y_1448_ = v___y_2362_;
v___y_1449_ = v___y_2361_;
v___y_1450_ = v___y_2363_;
v___y_1451_ = v___y_2364_;
v_a_1452_ = v___x_2372_;
goto v___jp_1444_;
}
else
{
v___y_1397_ = v___x_2369_;
v___y_1398_ = v___x_2368_;
v___y_1399_ = v___x_2372_;
v___y_1400_ = v___y_2361_;
v___y_1401_ = v___y_2362_;
v___y_1402_ = v___y_2363_;
v___y_1403_ = v___y_2364_;
goto v___jp_1396_;
}
}
}
else
{
v_n_969_ = v___x_2368_;
v_curr_970_ = v___y_2361_;
v_acc_971_ = v___x_2369_;
goto _start;
}
}
else
{
lean_object* v_val_2374_; lean_object* v___x_2375_; 
lean_dec(v___y_2354_);
v_val_2374_ = lean_ctor_get(v_a_2367_, 0);
lean_inc(v_val_2374_);
lean_dec_ref_known(v_a_2367_, 1);
v___x_2375_ = l_List_appendTR___redArg(v_val_2374_, v___y_2361_);
if (v___y_2356_ == 0)
{
if (v___y_2359_ == 0)
{
v___y_2346_ = v___y_2358_;
v___y_2347_ = v___x_2375_;
v___y_2348_ = v___y_2362_;
v___y_2349_ = v___y_2363_;
v___y_2350_ = v___y_2364_;
v_a_2351_ = v___y_2359_;
goto v___jp_2345_;
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2377_ = l_Lean_Name_append(v___x_2376_, v_trace_966_);
v___x_2378_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2355_, v___y_2362_, v___x_2377_);
lean_dec(v___x_2377_);
if (v___x_2378_ == 0)
{
v___y_2346_ = v___y_2358_;
v___y_2347_ = v___x_2375_;
v___y_2348_ = v___y_2362_;
v___y_2349_ = v___y_2363_;
v___y_2350_ = v___y_2364_;
v_a_2351_ = v___x_2378_;
goto v___jp_2345_;
}
else
{
v___y_2300_ = v___x_2375_;
v___y_2301_ = v___x_2378_;
v___y_2302_ = v___y_2362_;
v___y_2303_ = v___y_2363_;
v___y_2304_ = v___y_2364_;
goto v___jp_2299_;
}
}
}
else
{
v_n_969_ = v_n_2208_;
v_curr_970_ = v___x_2375_;
goto _start;
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec(v___y_2361_);
lean_dec(v___y_2354_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v_a_2380_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2366_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2366_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2354_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
return v___y_2360_;
}
}
v___jp_2388_:
{
lean_object* v___x_2399_; 
v___x_2399_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_2391_ == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref(v___x_2399_);
v___x_2401_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_2402_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___y_2392_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set_tag(v___x_2405_, 1);
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
v___y_1887_ = v___y_2389_;
v___y_1888_ = v___x_2401_;
v___y_1889_ = v_a_2400_;
v___y_1890_ = v___y_2390_;
v___y_1891_ = v___y_2393_;
v___y_1892_ = v___y_2396_;
v___y_1893_ = v___y_2395_;
v___y_1894_ = v___y_2394_;
v___y_1895_ = v___y_2398_;
v___y_1896_ = v___y_2397_;
v_a_1897_ = v___x_2408_;
goto v___jp_1886_;
}
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
v_a_2411_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2402_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2402_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set_tag(v___x_2413_, 0);
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
v___y_1887_ = v___y_2389_;
v___y_1888_ = v___x_2401_;
v___y_1889_ = v_a_2400_;
v___y_1890_ = v___y_2390_;
v___y_1891_ = v___y_2393_;
v___y_1892_ = v___y_2396_;
v___y_1893_ = v___y_2395_;
v___y_1894_ = v___y_2394_;
v___y_1895_ = v___y_2398_;
v___y_1896_ = v___y_2397_;
v_a_1897_ = v___x_2416_;
goto v___jp_1886_;
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_a_2419_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2419_);
lean_dec_ref(v___x_2399_);
v___x_2420_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_2421_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___y_2392_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set_tag(v___x_2424_, 1);
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
v___y_1867_ = v___y_2389_;
v___y_1868_ = v_a_2419_;
v___y_1869_ = v___x_2420_;
v___y_1870_ = v___y_2390_;
v___y_1871_ = v___y_2393_;
v___y_1872_ = v___y_2396_;
v___y_1873_ = v___y_2395_;
v___y_1874_ = v___y_2394_;
v___y_1875_ = v___y_2398_;
v___y_1876_ = v___y_2397_;
v_a_1877_ = v___x_2427_;
goto v___jp_1866_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
v_a_2430_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2421_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2421_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set_tag(v___x_2432_, 0);
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
v___y_1867_ = v___y_2389_;
v___y_1868_ = v_a_2419_;
v___y_1869_ = v___x_2420_;
v___y_1870_ = v___y_2390_;
v___y_1871_ = v___y_2393_;
v___y_1872_ = v___y_2396_;
v___y_1873_ = v___y_2395_;
v___y_1874_ = v___y_2394_;
v___y_1875_ = v___y_2398_;
v___y_1876_ = v___y_2397_;
v_a_1877_ = v___x_2435_;
goto v___jp_1866_;
}
}
}
}
}
v___jp_2438_:
{
lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = l_Lean_trace_profiler;
v___x_2450_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2441_, v___x_2449_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; 
lean_inc(v_trace_966_);
v___x_2451_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___y_2442_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v___y_2439_;
v___y_1112_ = v___y_2441_;
v___y_1113_ = v___y_2444_;
v___y_1114_ = v___y_2445_;
v___y_1115_ = v___y_2443_;
v___y_1116_ = v___y_2446_;
v___y_1117_ = v___y_2447_;
v___y_1118_ = v___x_2451_;
goto v___jp_1110_;
}
else
{
v___y_2389_ = v_a_2448_;
v___y_2390_ = v___y_2439_;
v___y_2391_ = v___y_2440_;
v___y_2392_ = v___y_2442_;
v___y_2393_ = v___y_2441_;
v___y_2394_ = v___y_2445_;
v___y_2395_ = v___y_2444_;
v___y_2396_ = v___y_2443_;
v___y_2397_ = v___y_2447_;
v___y_2398_ = v___y_2446_;
goto v___jp_2388_;
}
}
v___jp_2452_:
{
if (v___y_2468_ == 0)
{
lean_object* v___x_2469_; 
lean_dec_ref(v___y_2461_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2453_);
v___x_2469_ = lean_apply_6(v___y_2460_, v___y_2453_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
if (lean_obj_tag(v_a_2470_) == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_nat_add(v_n_2208_, v_one_2207_);
lean_dec(v_n_2208_);
v___x_2472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___y_2453_);
lean_ctor_set(v___x_2472_, 1, v_acc_971_);
if (v___y_2455_ == 0)
{
if (v___y_2456_ == 0)
{
v___y_2005_ = v___x_2471_;
v___y_2006_ = v___y_2462_;
v___y_2007_ = v___y_2463_;
v___y_2008_ = v___x_2472_;
v___y_2009_ = v___y_2464_;
v___y_2010_ = v___y_2465_;
v___y_2011_ = v___y_2466_;
v___y_2012_ = v___y_2467_;
v___y_2013_ = v___y_2457_;
v___y_2014_ = v___y_2458_;
v___y_2015_ = v___y_2459_;
v_a_2016_ = v___y_2456_;
goto v___jp_2004_;
}
else
{
lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2474_ = l_Lean_Name_append(v___x_2473_, v_trace_966_);
v___x_2475_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2454_, v___y_2465_, v___x_2474_);
lean_dec(v___x_2474_);
if (v___x_2475_ == 0)
{
v___y_2005_ = v___x_2471_;
v___y_2006_ = v___y_2462_;
v___y_2007_ = v___y_2463_;
v___y_2008_ = v___x_2472_;
v___y_2009_ = v___y_2464_;
v___y_2010_ = v___y_2465_;
v___y_2011_ = v___y_2466_;
v___y_2012_ = v___y_2467_;
v___y_2013_ = v___y_2457_;
v___y_2014_ = v___y_2458_;
v___y_2015_ = v___y_2459_;
v_a_2016_ = v___x_2475_;
goto v___jp_2004_;
}
else
{
v___y_1953_ = v___x_2471_;
v___y_1954_ = v___x_2475_;
v___y_1955_ = v___y_2457_;
v___y_1956_ = v___y_2459_;
v___y_1957_ = v___y_2458_;
v___y_1958_ = v___y_2462_;
v___y_1959_ = v___y_2463_;
v___y_1960_ = v___y_2465_;
v___y_1961_ = v___y_2464_;
v___y_1962_ = v___x_2472_;
v___y_1963_ = v___y_2467_;
v___y_1964_ = v___y_2466_;
goto v___jp_1952_;
}
}
}
else
{
lean_object* v___x_2476_; 
lean_inc(v_trace_966_);
v___x_2476_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___x_2471_, v___y_2464_, v___x_2472_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v___y_2462_;
v___y_1112_ = v___y_2465_;
v___y_1113_ = v___y_2466_;
v___y_1114_ = v___y_2457_;
v___y_1115_ = v___y_2467_;
v___y_1116_ = v___y_2459_;
v___y_1117_ = v___y_2458_;
v___y_1118_ = v___x_2476_;
goto v___jp_1110_;
}
}
else
{
lean_object* v_val_2477_; lean_object* v___x_2478_; 
lean_dec(v___y_2453_);
v_val_2477_ = lean_ctor_get(v_a_2470_, 0);
lean_inc(v_val_2477_);
lean_dec_ref_known(v_a_2470_, 1);
v___x_2478_ = l_List_appendTR___redArg(v_val_2477_, v___y_2464_);
if (v___y_2455_ == 0)
{
if (v___y_2456_ == 0)
{
v___y_2439_ = v___y_2462_;
v___y_2440_ = v___y_2463_;
v___y_2441_ = v___y_2465_;
v___y_2442_ = v___x_2478_;
v___y_2443_ = v___y_2467_;
v___y_2444_ = v___y_2466_;
v___y_2445_ = v___y_2457_;
v___y_2446_ = v___y_2459_;
v___y_2447_ = v___y_2458_;
v_a_2448_ = v___y_2456_;
goto v___jp_2438_;
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2480_ = l_Lean_Name_append(v___x_2479_, v_trace_966_);
v___x_2481_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2454_, v___y_2465_, v___x_2480_);
lean_dec(v___x_2480_);
if (v___x_2481_ == 0)
{
v___y_2439_ = v___y_2462_;
v___y_2440_ = v___y_2463_;
v___y_2441_ = v___y_2465_;
v___y_2442_ = v___x_2478_;
v___y_2443_ = v___y_2467_;
v___y_2444_ = v___y_2466_;
v___y_2445_ = v___y_2457_;
v___y_2446_ = v___y_2459_;
v___y_2447_ = v___y_2458_;
v_a_2448_ = v___x_2481_;
goto v___jp_2438_;
}
else
{
v___y_2389_ = v___x_2481_;
v___y_2390_ = v___y_2462_;
v___y_2391_ = v___y_2463_;
v___y_2392_ = v___x_2478_;
v___y_2393_ = v___y_2465_;
v___y_2394_ = v___y_2457_;
v___y_2395_ = v___y_2466_;
v___y_2396_ = v___y_2467_;
v___y_2397_ = v___y_2458_;
v___y_2398_ = v___y_2459_;
goto v___jp_2388_;
}
}
}
else
{
lean_object* v___x_2482_; 
lean_inc(v_trace_966_);
v___x_2482_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___x_2478_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v___y_2462_;
v___y_1112_ = v___y_2465_;
v___y_1113_ = v___y_2466_;
v___y_1114_ = v___y_2457_;
v___y_1115_ = v___y_2467_;
v___y_1116_ = v___y_2459_;
v___y_1117_ = v___y_2458_;
v___y_1118_ = v___x_2482_;
goto v___jp_1110_;
}
}
}
else
{
lean_object* v_a_2483_; 
lean_dec(v___y_2464_);
lean_dec(v___y_2453_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2483_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2469_, 1);
v___y_1101_ = v___y_2462_;
v___y_1102_ = v___y_2465_;
v___y_1103_ = v___y_2467_;
v___y_1104_ = v___y_2457_;
v___y_1105_ = v___y_2466_;
v___y_1106_ = v___y_2458_;
v___y_1107_ = v___y_2459_;
v_a_1108_ = v_a_2483_;
goto v___jp_1100_;
}
}
else
{
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2453_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v___y_1101_ = v___y_2462_;
v___y_1102_ = v___y_2465_;
v___y_1103_ = v___y_2467_;
v___y_1104_ = v___y_2457_;
v___y_1105_ = v___y_2466_;
v___y_1106_ = v___y_2458_;
v___y_1107_ = v___y_2459_;
v_a_1108_ = v___y_2461_;
goto v___jp_1100_;
}
}
v___jp_2484_:
{
lean_object* v___x_2495_; 
v___x_2495_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
if (v___y_2489_ == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref(v___x_2495_);
v___x_2497_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_2498_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___y_2485_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set_tag(v___x_2501_, 1);
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
v___y_1733_ = v_a_2496_;
v___y_1734_ = v___y_2486_;
v___y_1735_ = v___y_2487_;
v___y_1736_ = v___y_2488_;
v___y_1737_ = v___y_2490_;
v___y_1738_ = v___x_2497_;
v___y_1739_ = v___y_2492_;
v___y_1740_ = v___y_2491_;
v___y_1741_ = v___y_2494_;
v___y_1742_ = v___y_2493_;
v_a_1743_ = v___x_2504_;
goto v___jp_1732_;
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
v_a_2507_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2498_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2498_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
lean_ctor_set_tag(v___x_2509_, 0);
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
v___y_1733_ = v_a_2496_;
v___y_1734_ = v___y_2486_;
v___y_1735_ = v___y_2487_;
v___y_1736_ = v___y_2488_;
v___y_1737_ = v___y_2490_;
v___y_1738_ = v___x_2497_;
v___y_1739_ = v___y_2492_;
v___y_1740_ = v___y_2491_;
v___y_1741_ = v___y_2494_;
v___y_1742_ = v___y_2493_;
v_a_1743_ = v___x_2512_;
goto v___jp_1732_;
}
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_a_2515_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2515_);
lean_dec_ref(v___x_2495_);
v___x_2516_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_966_);
v___x_2517_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___y_2485_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set_tag(v___x_2520_, 1);
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
v___y_1713_ = v_a_2515_;
v___y_1714_ = v___y_2486_;
v___y_1715_ = v___y_2487_;
v___y_1716_ = v___y_2488_;
v___y_1717_ = v___y_2490_;
v___y_1718_ = v___x_2516_;
v___y_1719_ = v___y_2492_;
v___y_1720_ = v___y_2491_;
v___y_1721_ = v___y_2494_;
v___y_1722_ = v___y_2493_;
v_a_1723_ = v___x_2523_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2517_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2517_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 0);
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
v___y_1713_ = v_a_2515_;
v___y_1714_ = v___y_2486_;
v___y_1715_ = v___y_2487_;
v___y_1716_ = v___y_2488_;
v___y_1717_ = v___y_2490_;
v___y_1718_ = v___x_2516_;
v___y_1719_ = v___y_2492_;
v___y_1720_ = v___y_2491_;
v___y_1721_ = v___y_2494_;
v___y_1722_ = v___y_2493_;
v_a_1723_ = v___x_2531_;
goto v___jp_1712_;
}
}
}
}
}
v___jp_2534_:
{
lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2545_ = l_Lean_trace_profiler;
v___x_2546_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2539_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
lean_inc(v_trace_966_);
v___x_2547_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___y_2535_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___y_2536_;
v___y_1163_ = v___y_2537_;
v___y_1164_ = v___y_2539_;
v___y_1165_ = v___y_2540_;
v___y_1166_ = v___y_2541_;
v___y_1167_ = v___y_2542_;
v___y_1168_ = v___y_2543_;
v___y_1169_ = v___x_2547_;
goto v___jp_1161_;
}
else
{
v___y_2485_ = v___y_2535_;
v___y_2486_ = v_a_2544_;
v___y_2487_ = v___y_2536_;
v___y_2488_ = v___y_2537_;
v___y_2489_ = v___y_2538_;
v___y_2490_ = v___y_2539_;
v___y_2491_ = v___y_2541_;
v___y_2492_ = v___y_2540_;
v___y_2493_ = v___y_2543_;
v___y_2494_ = v___y_2542_;
goto v___jp_2484_;
}
}
v___jp_2548_:
{
if (v___y_2564_ == 0)
{
lean_object* v___x_2565_; 
lean_dec_ref(v___y_2558_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2549_);
v___x_2565_ = lean_apply_6(v___y_2557_, v___y_2549_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
if (lean_obj_tag(v_a_2566_) == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_nat_add(v_n_2208_, v_one_2207_);
lean_dec(v_n_2208_);
v___x_2568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___y_2549_);
lean_ctor_set(v___x_2568_, 1, v_acc_971_);
if (v___y_2551_ == 0)
{
if (v___y_2552_ == 0)
{
v___y_1697_ = v___y_2553_;
v___y_1698_ = v___y_2559_;
v___y_1699_ = v___y_2560_;
v___y_1700_ = v___y_2561_;
v___y_1701_ = v___y_2562_;
v___y_1702_ = v___x_2567_;
v___y_1703_ = v___y_2563_;
v___y_1704_ = v___x_2568_;
v___y_1705_ = v___y_2554_;
v___y_1706_ = v___y_2555_;
v___y_1707_ = v___y_2556_;
v_a_1708_ = v___y_2552_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2570_ = l_Lean_Name_append(v___x_2569_, v_trace_966_);
v___x_2571_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2550_, v___y_2562_, v___x_2570_);
lean_dec(v___x_2570_);
if (v___x_2571_ == 0)
{
v___y_1697_ = v___y_2553_;
v___y_1698_ = v___y_2559_;
v___y_1699_ = v___y_2560_;
v___y_1700_ = v___y_2561_;
v___y_1701_ = v___y_2562_;
v___y_1702_ = v___x_2567_;
v___y_1703_ = v___y_2563_;
v___y_1704_ = v___x_2568_;
v___y_1705_ = v___y_2554_;
v___y_1706_ = v___y_2555_;
v___y_1707_ = v___y_2556_;
v_a_1708_ = v___x_2571_;
goto v___jp_1696_;
}
else
{
v___y_1645_ = v___x_2571_;
v___y_1646_ = v___y_2553_;
v___y_1647_ = v___y_2554_;
v___y_1648_ = v___x_2568_;
v___y_1649_ = v___y_2556_;
v___y_1650_ = v___y_2555_;
v___y_1651_ = v___y_2559_;
v___y_1652_ = v___y_2560_;
v___y_1653_ = v___y_2562_;
v___y_1654_ = v___y_2561_;
v___y_1655_ = v___y_2563_;
v___y_1656_ = v___x_2567_;
goto v___jp_1644_;
}
}
}
else
{
lean_object* v___x_2572_; 
lean_inc(v_trace_966_);
v___x_2572_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___x_2567_, v___y_2561_, v___x_2568_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___y_2553_;
v___y_1163_ = v___y_2559_;
v___y_1164_ = v___y_2562_;
v___y_1165_ = v___y_2563_;
v___y_1166_ = v___y_2554_;
v___y_1167_ = v___y_2556_;
v___y_1168_ = v___y_2555_;
v___y_1169_ = v___x_2572_;
goto v___jp_1161_;
}
}
else
{
lean_object* v_val_2573_; lean_object* v___x_2574_; 
lean_dec(v___y_2549_);
v_val_2573_ = lean_ctor_get(v_a_2566_, 0);
lean_inc(v_val_2573_);
lean_dec_ref_known(v_a_2566_, 1);
v___x_2574_ = l_List_appendTR___redArg(v_val_2573_, v___y_2561_);
if (v___y_2551_ == 0)
{
if (v___y_2552_ == 0)
{
v___y_2535_ = v___x_2574_;
v___y_2536_ = v___y_2553_;
v___y_2537_ = v___y_2559_;
v___y_2538_ = v___y_2560_;
v___y_2539_ = v___y_2562_;
v___y_2540_ = v___y_2563_;
v___y_2541_ = v___y_2554_;
v___y_2542_ = v___y_2556_;
v___y_2543_ = v___y_2555_;
v_a_2544_ = v___y_2552_;
goto v___jp_2534_;
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2575_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2576_ = l_Lean_Name_append(v___x_2575_, v_trace_966_);
v___x_2577_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2550_, v___y_2562_, v___x_2576_);
lean_dec(v___x_2576_);
if (v___x_2577_ == 0)
{
v___y_2535_ = v___x_2574_;
v___y_2536_ = v___y_2553_;
v___y_2537_ = v___y_2559_;
v___y_2538_ = v___y_2560_;
v___y_2539_ = v___y_2562_;
v___y_2540_ = v___y_2563_;
v___y_2541_ = v___y_2554_;
v___y_2542_ = v___y_2556_;
v___y_2543_ = v___y_2555_;
v_a_2544_ = v___x_2577_;
goto v___jp_2534_;
}
else
{
v___y_2485_ = v___x_2574_;
v___y_2486_ = v___x_2577_;
v___y_2487_ = v___y_2553_;
v___y_2488_ = v___y_2559_;
v___y_2489_ = v___y_2560_;
v___y_2490_ = v___y_2562_;
v___y_2491_ = v___y_2554_;
v___y_2492_ = v___y_2563_;
v___y_2493_ = v___y_2555_;
v___y_2494_ = v___y_2556_;
goto v___jp_2484_;
}
}
}
else
{
lean_object* v___x_2578_; 
lean_inc(v_trace_966_);
v___x_2578_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v_n_2208_, v___x_2574_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___y_2553_;
v___y_1163_ = v___y_2559_;
v___y_1164_ = v___y_2562_;
v___y_1165_ = v___y_2563_;
v___y_1166_ = v___y_2554_;
v___y_1167_ = v___y_2556_;
v___y_1168_ = v___y_2555_;
v___y_1169_ = v___x_2578_;
goto v___jp_1161_;
}
}
}
else
{
lean_object* v_a_2579_; 
lean_dec(v___y_2561_);
lean_dec(v___y_2549_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2579_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2565_, 1);
v___y_1152_ = v___y_2553_;
v___y_1153_ = v___y_2559_;
v___y_1154_ = v___y_2562_;
v___y_1155_ = v___y_2554_;
v___y_1156_ = v___y_2563_;
v___y_1157_ = v___y_2555_;
v___y_1158_ = v___y_2556_;
v_a_1159_ = v_a_2579_;
goto v___jp_1151_;
}
}
else
{
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2549_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v___y_1152_ = v___y_2553_;
v___y_1153_ = v___y_2559_;
v___y_1154_ = v___y_2562_;
v___y_1155_ = v___y_2554_;
v___y_1156_ = v___y_2563_;
v___y_1157_ = v___y_2555_;
v___y_1158_ = v___y_2556_;
v_a_1159_ = v___y_2558_;
goto v___jp_1151_;
}
}
v___jp_2580_:
{
lean_object* v___x_2595_; lean_object* v_a_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2595_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_975_);
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref(v___x_2595_);
v___x_2597_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2598_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2593_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
lean_dec_ref(v___y_2585_);
v___x_2599_ = lean_io_mono_nanos_now();
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2581_);
v___x_2600_ = lean_apply_6(v___y_2590_, v___y_2581_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; uint8_t v___x_2602_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v___x_2602_ = lean_unbox(v_a_2601_);
lean_dec(v_a_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; 
lean_inc_ref(v_next_967_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2581_);
v___x_2603_ = lean_apply_7(v_next_967_, v___y_2581_, v___y_2586_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; 
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2581_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v___y_1142_ = v___x_2599_;
v___y_1143_ = v_a_2596_;
v___y_1144_ = v___y_2593_;
v___y_1145_ = v___y_2587_;
v___y_1146_ = v___y_2594_;
v___y_1147_ = v___y_2589_;
v___y_1148_ = v___y_2588_;
v_a_1149_ = v_a_2604_;
goto v___jp_1141_;
}
else
{
lean_object* v_a_2605_; uint8_t v___x_2606_; 
v_a_2605_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2603_, 1);
v___x_2606_ = l_Lean_Exception_isInterrupt(v_a_2605_);
if (v___x_2606_ == 0)
{
uint8_t v___x_2607_; 
lean_inc(v_a_2605_);
v___x_2607_ = l_Lean_Exception_isRuntime(v_a_2605_);
v___y_2549_ = v___y_2581_;
v___y_2550_ = v___y_2582_;
v___y_2551_ = v___y_2583_;
v___y_2552_ = v___y_2584_;
v___y_2553_ = v___x_2599_;
v___y_2554_ = v___y_2587_;
v___y_2555_ = v___y_2589_;
v___y_2556_ = v___y_2588_;
v___y_2557_ = v___y_2591_;
v___y_2558_ = v_a_2605_;
v___y_2559_ = v_a_2596_;
v___y_2560_ = v___x_2598_;
v___y_2561_ = v___y_2592_;
v___y_2562_ = v___y_2593_;
v___y_2563_ = v___y_2594_;
v___y_2564_ = v___x_2607_;
goto v___jp_2548_;
}
else
{
v___y_2549_ = v___y_2581_;
v___y_2550_ = v___y_2582_;
v___y_2551_ = v___y_2583_;
v___y_2552_ = v___y_2584_;
v___y_2553_ = v___x_2599_;
v___y_2554_ = v___y_2587_;
v___y_2555_ = v___y_2589_;
v___y_2556_ = v___y_2588_;
v___y_2557_ = v___y_2591_;
v___y_2558_ = v_a_2605_;
v___y_2559_ = v_a_2596_;
v___y_2560_ = v___x_2598_;
v___y_2561_ = v___y_2592_;
v___y_2562_ = v___y_2593_;
v___y_2563_ = v___y_2594_;
v___y_2564_ = v___x_2606_;
goto v___jp_2548_;
}
}
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2586_);
v___x_2608_ = lean_nat_add(v_n_2208_, v_one_2207_);
lean_dec(v_n_2208_);
v___x_2609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___y_2581_);
lean_ctor_set(v___x_2609_, 1, v_acc_971_);
if (v___y_2583_ == 0)
{
if (v___y_2584_ == 0)
{
v___y_1851_ = v___x_2608_;
v___y_1852_ = v___x_2609_;
v___y_1853_ = v___x_2599_;
v___y_1854_ = v_a_2596_;
v___y_1855_ = v___x_2598_;
v___y_1856_ = v___y_2592_;
v___y_1857_ = v___y_2593_;
v___y_1858_ = v___y_2594_;
v___y_1859_ = v___y_2587_;
v___y_1860_ = v___y_2589_;
v___y_1861_ = v___y_2588_;
v_a_1862_ = v___y_2584_;
goto v___jp_1850_;
}
else
{
lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2611_ = l_Lean_Name_append(v___x_2610_, v_trace_966_);
v___x_2612_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2582_, v___y_2593_, v___x_2611_);
lean_dec(v___x_2611_);
if (v___x_2612_ == 0)
{
v___y_1851_ = v___x_2608_;
v___y_1852_ = v___x_2609_;
v___y_1853_ = v___x_2599_;
v___y_1854_ = v_a_2596_;
v___y_1855_ = v___x_2598_;
v___y_1856_ = v___y_2592_;
v___y_1857_ = v___y_2593_;
v___y_1858_ = v___y_2594_;
v___y_1859_ = v___y_2587_;
v___y_1860_ = v___y_2589_;
v___y_1861_ = v___y_2588_;
v_a_1862_ = v___x_2612_;
goto v___jp_1850_;
}
else
{
v___y_1799_ = v___x_2608_;
v___y_1800_ = v___x_2612_;
v___y_1801_ = v___x_2609_;
v___y_1802_ = v___x_2599_;
v___y_1803_ = v___y_2587_;
v___y_1804_ = v___y_2588_;
v___y_1805_ = v___y_2589_;
v___y_1806_ = v_a_2596_;
v___y_1807_ = v___x_2598_;
v___y_1808_ = v___y_2593_;
v___y_1809_ = v___y_2592_;
v___y_1810_ = v___y_2594_;
goto v___jp_1798_;
}
}
}
else
{
lean_object* v___x_2613_; 
lean_inc(v_trace_966_);
v___x_2613_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___x_2608_, v___y_2592_, v___x_2609_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1162_ = v___x_2599_;
v___y_1163_ = v_a_2596_;
v___y_1164_ = v___y_2593_;
v___y_1165_ = v___y_2594_;
v___y_1166_ = v___y_2587_;
v___y_1167_ = v___y_2588_;
v___y_1168_ = v___y_2589_;
v___y_1169_ = v___x_2613_;
goto v___jp_1161_;
}
}
}
else
{
lean_object* v_a_2614_; 
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2581_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2614_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2600_, 1);
v___y_1152_ = v___x_2599_;
v___y_1153_ = v_a_2596_;
v___y_1154_ = v___y_2593_;
v___y_1155_ = v___y_2587_;
v___y_1156_ = v___y_2594_;
v___y_1157_ = v___y_2589_;
v___y_1158_ = v___y_2588_;
v_a_1159_ = v_a_2614_;
goto v___jp_1151_;
}
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_dec_ref(v___y_2586_);
v___x_2615_ = lean_io_get_num_heartbeats();
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2581_);
v___x_2616_ = lean_apply_6(v___y_2590_, v___y_2581_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; uint8_t v___x_2618_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = lean_unbox(v_a_2617_);
lean_dec(v_a_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; 
lean_inc_ref(v_next_967_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2581_);
v___x_2619_ = lean_apply_7(v_next_967_, v___y_2581_, v___y_2585_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; 
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2581_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2619_, 1);
v___y_1091_ = v_a_2596_;
v___y_1092_ = v___y_2593_;
v___y_1093_ = v___x_2615_;
v___y_1094_ = v___y_2587_;
v___y_1095_ = v___y_2594_;
v___y_1096_ = v___y_2589_;
v___y_1097_ = v___y_2588_;
v_a_1098_ = v_a_2620_;
goto v___jp_1090_;
}
else
{
lean_object* v_a_2621_; uint8_t v___x_2622_; 
v_a_2621_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2619_, 1);
v___x_2622_ = l_Lean_Exception_isInterrupt(v_a_2621_);
if (v___x_2622_ == 0)
{
uint8_t v___x_2623_; 
lean_inc(v_a_2621_);
v___x_2623_ = l_Lean_Exception_isRuntime(v_a_2621_);
v___y_2453_ = v___y_2581_;
v___y_2454_ = v___y_2582_;
v___y_2455_ = v___y_2583_;
v___y_2456_ = v___y_2584_;
v___y_2457_ = v___y_2587_;
v___y_2458_ = v___y_2589_;
v___y_2459_ = v___y_2588_;
v___y_2460_ = v___y_2591_;
v___y_2461_ = v_a_2621_;
v___y_2462_ = v_a_2596_;
v___y_2463_ = v___x_2598_;
v___y_2464_ = v___y_2592_;
v___y_2465_ = v___y_2593_;
v___y_2466_ = v___y_2594_;
v___y_2467_ = v___x_2615_;
v___y_2468_ = v___x_2623_;
goto v___jp_2452_;
}
else
{
v___y_2453_ = v___y_2581_;
v___y_2454_ = v___y_2582_;
v___y_2455_ = v___y_2583_;
v___y_2456_ = v___y_2584_;
v___y_2457_ = v___y_2587_;
v___y_2458_ = v___y_2589_;
v___y_2459_ = v___y_2588_;
v___y_2460_ = v___y_2591_;
v___y_2461_ = v_a_2621_;
v___y_2462_ = v_a_2596_;
v___y_2463_ = v___x_2598_;
v___y_2464_ = v___y_2592_;
v___y_2465_ = v___y_2593_;
v___y_2466_ = v___y_2594_;
v___y_2467_ = v___x_2615_;
v___y_2468_ = v___x_2622_;
goto v___jp_2452_;
}
}
}
else
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2585_);
v___x_2624_ = lean_nat_add(v_n_2208_, v_one_2207_);
lean_dec(v_n_2208_);
v___x_2625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___y_2581_);
lean_ctor_set(v___x_2625_, 1, v_acc_971_);
if (v___y_2583_ == 0)
{
if (v___y_2584_ == 0)
{
v___y_1586_ = v___x_2625_;
v___y_1587_ = v_a_2596_;
v___y_1588_ = v___x_2598_;
v___y_1589_ = v___x_2624_;
v___y_1590_ = v___y_2592_;
v___y_1591_ = v___y_2593_;
v___y_1592_ = v___y_2594_;
v___y_1593_ = v___x_2615_;
v___y_1594_ = v___y_2587_;
v___y_1595_ = v___y_2589_;
v___y_1596_ = v___y_2588_;
v_a_1597_ = v___y_2584_;
goto v___jp_1585_;
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2627_ = l_Lean_Name_append(v___x_2626_, v_trace_966_);
v___x_2628_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2582_, v___y_2593_, v___x_2627_);
lean_dec(v___x_2627_);
if (v___x_2628_ == 0)
{
v___y_1586_ = v___x_2625_;
v___y_1587_ = v_a_2596_;
v___y_1588_ = v___x_2598_;
v___y_1589_ = v___x_2624_;
v___y_1590_ = v___y_2592_;
v___y_1591_ = v___y_2593_;
v___y_1592_ = v___y_2594_;
v___y_1593_ = v___x_2615_;
v___y_1594_ = v___y_2587_;
v___y_1595_ = v___y_2589_;
v___y_1596_ = v___y_2588_;
v_a_1597_ = v___x_2628_;
goto v___jp_1585_;
}
else
{
v___y_1534_ = v___x_2624_;
v___y_1535_ = v___y_2587_;
v___y_1536_ = v___y_2588_;
v___y_1537_ = v___y_2589_;
v___y_1538_ = v___x_2625_;
v___y_1539_ = v___x_2628_;
v___y_1540_ = v_a_2596_;
v___y_1541_ = v___x_2598_;
v___y_1542_ = v___y_2593_;
v___y_1543_ = v___y_2592_;
v___y_1544_ = v___x_2615_;
v___y_1545_ = v___y_2594_;
goto v___jp_1533_;
}
}
}
else
{
lean_object* v___x_2629_; 
lean_inc(v_trace_966_);
v___x_2629_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___x_2624_, v___y_2592_, v___x_2625_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
v___y_1111_ = v_a_2596_;
v___y_1112_ = v___y_2593_;
v___y_1113_ = v___y_2594_;
v___y_1114_ = v___y_2587_;
v___y_1115_ = v___x_2615_;
v___y_1116_ = v___y_2588_;
v___y_1117_ = v___y_2589_;
v___y_1118_ = v___x_2629_;
goto v___jp_1110_;
}
}
}
else
{
lean_object* v_a_2630_; 
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2581_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_a_2630_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2616_, 1);
v___y_1101_ = v_a_2596_;
v___y_1102_ = v___y_2593_;
v___y_1103_ = v___x_2615_;
v___y_1104_ = v___y_2587_;
v___y_1105_ = v___y_2594_;
v___y_1106_ = v___y_2589_;
v___y_1107_ = v___y_2588_;
v_a_1108_ = v_a_2630_;
goto v___jp_1100_;
}
}
}
v___jp_2631_:
{
lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2647_ = l_Lean_trace_profiler;
v___x_2648_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_2644_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; 
lean_dec_ref(v___y_2645_);
lean_dec_ref(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2632_);
v___x_2649_ = lean_apply_6(v___y_2641_, v___y_2632_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; uint8_t v___x_2651_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
v___x_2651_ = lean_unbox(v_a_2650_);
lean_dec(v_a_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; 
lean_inc_ref(v_next_967_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v___y_2632_);
v___x_2652_ = lean_apply_7(v_next_967_, v___y_2632_, v___y_2635_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2632_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
return v___x_2652_;
}
else
{
lean_object* v_a_2653_; uint8_t v___x_2654_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
v___x_2654_ = l_Lean_Exception_isInterrupt(v_a_2653_);
if (v___x_2654_ == 0)
{
uint8_t v___x_2655_; 
v___x_2655_ = l_Lean_Exception_isRuntime(v_a_2653_);
v___y_2354_ = v___y_2632_;
v___y_2355_ = v___y_2633_;
v___y_2356_ = v___y_2634_;
v___y_2357_ = v___y_2642_;
v___y_2358_ = v___x_2648_;
v___y_2359_ = v___y_2636_;
v___y_2360_ = v___x_2652_;
v___y_2361_ = v___y_2643_;
v___y_2362_ = v___y_2644_;
v___y_2363_ = v___y_2639_;
v___y_2364_ = v___y_2640_;
v___y_2365_ = v___x_2655_;
goto v___jp_2353_;
}
else
{
lean_dec(v_a_2653_);
v___y_2354_ = v___y_2632_;
v___y_2355_ = v___y_2633_;
v___y_2356_ = v___y_2634_;
v___y_2357_ = v___y_2642_;
v___y_2358_ = v___x_2648_;
v___y_2359_ = v___y_2636_;
v___y_2360_ = v___x_2652_;
v___y_2361_ = v___y_2643_;
v___y_2362_ = v___y_2644_;
v___y_2363_ = v___y_2639_;
v___y_2364_ = v___y_2640_;
v___y_2365_ = v___x_2654_;
goto v___jp_2353_;
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_dec_ref(v___y_2642_);
lean_dec_ref(v___y_2635_);
v___x_2656_ = lean_nat_add(v_n_2208_, v_one_2207_);
lean_dec(v_n_2208_);
v___x_2657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___y_2632_);
lean_ctor_set(v___x_2657_, 1, v_acc_971_);
if (v___y_2634_ == 0)
{
if (v___y_2636_ == 0)
{
v___y_2104_ = v___x_2657_;
v___y_2105_ = v___x_2648_;
v___y_2106_ = v___x_2656_;
v___y_2107_ = v___y_2644_;
v___y_2108_ = v___y_2643_;
v___y_2109_ = v___y_2639_;
v___y_2110_ = v___y_2640_;
v_a_2111_ = v___y_2636_;
goto v___jp_2103_;
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2659_ = l_Lean_Name_append(v___x_2658_, v_trace_966_);
v___x_2660_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2633_, v___y_2644_, v___x_2659_);
lean_dec(v___x_2659_);
if (v___x_2660_ == 0)
{
v___y_2104_ = v___x_2657_;
v___y_2105_ = v___x_2648_;
v___y_2106_ = v___x_2656_;
v___y_2107_ = v___y_2644_;
v___y_2108_ = v___y_2643_;
v___y_2109_ = v___y_2639_;
v___y_2110_ = v___y_2640_;
v_a_2111_ = v___x_2660_;
goto v___jp_2103_;
}
else
{
v___y_2056_ = v___x_2657_;
v___y_2057_ = v___x_2660_;
v___y_2058_ = v___x_2656_;
v___y_2059_ = v___y_2643_;
v___y_2060_ = v___y_2644_;
v___y_2061_ = v___y_2639_;
v___y_2062_ = v___y_2640_;
goto v___jp_2055_;
}
}
}
else
{
v_n_969_ = v___x_2656_;
v_curr_970_ = v___y_2643_;
v_acc_971_ = v___x_2657_;
goto _start;
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2632_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v_a_2662_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2649_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2649_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
else
{
lean_dec_ref(v___y_2635_);
v___y_2581_ = v___y_2632_;
v___y_2582_ = v___y_2633_;
v___y_2583_ = v___y_2634_;
v___y_2584_ = v___y_2636_;
v___y_2585_ = v___y_2637_;
v___y_2586_ = v___y_2638_;
v___y_2587_ = v___y_2639_;
v___y_2588_ = v_a_2646_;
v___y_2589_ = v___y_2640_;
v___y_2590_ = v___y_2641_;
v___y_2591_ = v___y_2642_;
v___y_2592_ = v___y_2643_;
v___y_2593_ = v___y_2644_;
v___y_2594_ = v___y_2645_;
goto v___jp_2580_;
}
}
v___jp_2670_:
{
if (lean_obj_tag(v_a_2671_) == 0)
{
if (lean_obj_tag(v_curr_970_) == 0)
{
lean_object* v_options_2672_; lean_object* v_inheritedTraceOptions_2673_; uint8_t v_hasTrace_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
lean_dec(v_n_2208_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec_ref(v_cfg_965_);
v_options_2672_ = lean_ctor_get(v_a_974_, 2);
v_inheritedTraceOptions_2673_ = lean_ctor_get(v_a_974_, 13);
v_hasTrace_2674_ = lean_ctor_get_uint8(v_options_2672_, sizeof(void*)*1);
v___x_2675_ = l_List_reverse___redArg(v_acc_971_);
v___x_2676_ = lean_bool_not(v_hasTrace_2674_);
if (v___x_2676_ == 0)
{
uint8_t v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = 1;
v___x_2678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
if (v_hasTrace_2674_ == 0)
{
v___y_1353_ = v___x_2675_;
v___y_1354_ = v___x_2677_;
v___y_1355_ = v___x_2678_;
v___y_1356_ = v_options_2672_;
v_a_1357_ = v_hasTrace_2674_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v___x_2679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2680_ = l_Lean_Name_append(v___x_2679_, v_trace_966_);
v___x_2681_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2673_, v_options_2672_, v___x_2680_);
lean_dec(v___x_2680_);
if (v___x_2681_ == 0)
{
v___y_1353_ = v___x_2675_;
v___y_1354_ = v___x_2677_;
v___y_1355_ = v___x_2678_;
v___y_1356_ = v_options_2672_;
v_a_1357_ = v___x_2681_;
goto v___jp_1352_;
}
else
{
v___y_1312_ = v___x_2675_;
v___y_1313_ = v___x_2681_;
v___y_1314_ = v___x_2677_;
v___y_1315_ = v___x_2678_;
v___y_1316_ = v_options_2672_;
goto v___jp_1311_;
}
}
}
else
{
lean_object* v___x_2682_; 
lean_dec(v_trace_966_);
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2675_);
return v___x_2682_;
}
}
else
{
lean_object* v_head_2683_; lean_object* v_tail_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2738_; 
v_head_2683_ = lean_ctor_get(v_curr_970_, 0);
v_tail_2684_ = lean_ctor_get(v_curr_970_, 1);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_curr_970_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2686_ = v_curr_970_;
v_isShared_2687_ = v_isSharedCheck_2738_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_tail_2684_);
lean_inc(v_head_2683_);
lean_dec(v_curr_970_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2738_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; lean_object* v_a_2689_; uint8_t v___x_2690_; uint8_t v___x_2691_; 
v___x_2688_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2683_, v_a_973_);
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref(v___x_2688_);
v___x_2690_ = 1;
v___x_2691_ = lean_unbox(v_a_2689_);
lean_dec(v_a_2689_);
if (v___x_2691_ == 0)
{
lean_object* v_options_2692_; lean_object* v_inheritedTraceOptions_2693_; uint8_t v_hasTrace_2694_; uint8_t v___x_2695_; 
v_options_2692_ = lean_ctor_get(v_a_974_, 2);
v_inheritedTraceOptions_2693_ = lean_ctor_get(v_a_974_, 13);
v_hasTrace_2694_ = lean_ctor_get_uint8(v_options_2692_, sizeof(void*)*1);
v___x_2695_ = lean_bool_not(v_hasTrace_2694_);
if (v___x_2695_ == 0)
{
lean_object* v___f_2696_; lean_object* v___f_2697_; lean_object* v___x_2698_; 
lean_del_object(v___x_2686_);
lean_inc(v_acc_971_);
lean_inc(v_n_2208_);
lean_inc(v_goals_968_);
lean_inc_ref(v_next_967_);
lean_inc(v_trace_966_);
lean_inc_ref(v_cfg_965_);
lean_inc(v_tail_2684_);
v___f_2696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__11___boxed), 13, 7);
lean_closure_set(v___f_2696_, 0, v_tail_2684_);
lean_closure_set(v___f_2696_, 1, v_cfg_965_);
lean_closure_set(v___f_2696_, 2, v_trace_966_);
lean_closure_set(v___f_2696_, 3, v_next_967_);
lean_closure_set(v___f_2696_, 4, v_goals_968_);
lean_closure_set(v___f_2696_, 5, v_n_2208_);
lean_closure_set(v___f_2696_, 6, v_acc_971_);
lean_inc(v_head_2683_);
v___f_2697_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(v___f_2697_, 0, v_head_2683_);
v___x_2698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
if (v_hasTrace_2694_ == 0)
{
lean_inc_ref(v_discharge_1178_);
lean_inc_ref(v_suspend_1177_);
lean_inc_ref_n(v___f_2696_, 2);
v___y_2632_ = v_head_2683_;
v___y_2633_ = v_inheritedTraceOptions_2693_;
v___y_2634_ = v___x_2695_;
v___y_2635_ = v___f_2696_;
v___y_2636_ = v_hasTrace_2694_;
v___y_2637_ = v___f_2696_;
v___y_2638_ = v___f_2696_;
v___y_2639_ = v___x_2690_;
v___y_2640_ = v___x_2698_;
v___y_2641_ = v_suspend_1177_;
v___y_2642_ = v_discharge_1178_;
v___y_2643_ = v_tail_2684_;
v___y_2644_ = v_options_2692_;
v___y_2645_ = v___f_2697_;
v_a_2646_ = v_hasTrace_2694_;
goto v___jp_2631_;
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2700_ = l_Lean_Name_append(v___x_2699_, v_trace_966_);
v___x_2701_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2693_, v_options_2692_, v___x_2700_);
lean_dec(v___x_2700_);
if (v___x_2701_ == 0)
{
lean_inc_ref(v_discharge_1178_);
lean_inc_ref(v_suspend_1177_);
lean_inc_ref_n(v___f_2696_, 2);
v___y_2632_ = v_head_2683_;
v___y_2633_ = v_inheritedTraceOptions_2693_;
v___y_2634_ = v___x_2695_;
v___y_2635_ = v___f_2696_;
v___y_2636_ = v_hasTrace_2694_;
v___y_2637_ = v___f_2696_;
v___y_2638_ = v___f_2696_;
v___y_2639_ = v___x_2690_;
v___y_2640_ = v___x_2698_;
v___y_2641_ = v_suspend_1177_;
v___y_2642_ = v_discharge_1178_;
v___y_2643_ = v_tail_2684_;
v___y_2644_ = v_options_2692_;
v___y_2645_ = v___f_2697_;
v_a_2646_ = v___x_2701_;
goto v___jp_2631_;
}
else
{
lean_inc_ref(v_discharge_1178_);
lean_inc_ref(v_suspend_1177_);
lean_inc_ref(v___f_2696_);
v___y_2581_ = v_head_2683_;
v___y_2582_ = v_inheritedTraceOptions_2693_;
v___y_2583_ = v___x_2695_;
v___y_2584_ = v_hasTrace_2694_;
v___y_2585_ = v___f_2696_;
v___y_2586_ = v___f_2696_;
v___y_2587_ = v___x_2690_;
v___y_2588_ = v___x_2701_;
v___y_2589_ = v___x_2698_;
v___y_2590_ = v_suspend_1177_;
v___y_2591_ = v_discharge_1178_;
v___y_2592_ = v_tail_2684_;
v___y_2593_ = v_options_2692_;
v___y_2594_ = v___f_2697_;
goto v___jp_2580_;
}
}
}
else
{
lean_object* v___x_2702_; 
lean_inc_ref(v_suspend_1177_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_head_2683_);
v___x_2702_ = lean_apply_6(v_suspend_1177_, v_head_2683_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; uint8_t v___x_2704_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v___x_2704_ = lean_unbox(v_a_2703_);
lean_dec(v_a_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___f_2705_; lean_object* v___x_2706_; 
lean_del_object(v___x_2686_);
lean_inc(v_acc_971_);
lean_inc(v_n_2208_);
lean_inc(v_goals_968_);
lean_inc_ref_n(v_next_967_, 2);
lean_inc(v_trace_966_);
lean_inc_ref(v_cfg_965_);
lean_inc(v_tail_2684_);
v___f_2705_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__11___boxed), 13, 7);
lean_closure_set(v___f_2705_, 0, v_tail_2684_);
lean_closure_set(v___f_2705_, 1, v_cfg_965_);
lean_closure_set(v___f_2705_, 2, v_trace_966_);
lean_closure_set(v___f_2705_, 3, v_next_967_);
lean_closure_set(v___f_2705_, 4, v_goals_968_);
lean_closure_set(v___f_2705_, 5, v_n_2208_);
lean_closure_set(v___f_2705_, 6, v_acc_971_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_head_2683_);
v___x_2706_ = lean_apply_7(v_next_967_, v_head_2683_, v___f_2705_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, lean_box(0));
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_dec(v_tail_2684_);
lean_dec(v_head_2683_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
return v___x_2706_;
}
else
{
lean_object* v_a_2707_; uint8_t v___x_2708_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2707_);
v___x_2708_ = l_Lean_Exception_isInterrupt(v_a_2707_);
if (v___x_2708_ == 0)
{
uint8_t v___x_2709_; 
v___x_2709_ = l_Lean_Exception_isRuntime(v_a_2707_);
lean_inc_ref(v_discharge_1178_);
v___y_2265_ = v_head_2683_;
v___y_2266_ = v_inheritedTraceOptions_2693_;
v___y_2267_ = v___x_2695_;
v___y_2268_ = v_discharge_1178_;
v___y_2269_ = v_hasTrace_2694_;
v___y_2270_ = v___x_2706_;
v___y_2271_ = v_tail_2684_;
v___y_2272_ = v_options_2692_;
v___y_2273_ = v___x_2690_;
v___y_2274_ = v___x_2709_;
goto v___jp_2264_;
}
else
{
lean_dec(v_a_2707_);
lean_inc_ref(v_discharge_1178_);
v___y_2265_ = v_head_2683_;
v___y_2266_ = v_inheritedTraceOptions_2693_;
v___y_2267_ = v___x_2695_;
v___y_2268_ = v_discharge_1178_;
v___y_2269_ = v_hasTrace_2694_;
v___y_2270_ = v___x_2706_;
v___y_2271_ = v_tail_2684_;
v___y_2272_ = v_options_2692_;
v___y_2273_ = v___x_2690_;
v___y_2274_ = v___x_2708_;
goto v___jp_2264_;
}
}
}
else
{
lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2710_ = lean_nat_add(v_n_2208_, v_one_2207_);
lean_dec(v_n_2208_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 1, v_acc_971_);
v___x_2712_ = v___x_2686_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_head_2683_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_acc_971_);
v___x_2712_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
if (v___x_2695_ == 0)
{
lean_object* v___x_2713_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
if (v_hasTrace_2694_ == 0)
{
v___y_2197_ = v___x_2710_;
v___y_2198_ = v___x_2712_;
v___y_2199_ = v___x_2713_;
v___y_2200_ = v_options_2692_;
v___y_2201_ = v_tail_2684_;
v___y_2202_ = v___x_2690_;
v_a_2203_ = v_hasTrace_2694_;
goto v___jp_2196_;
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2715_ = l_Lean_Name_append(v___x_2714_, v_trace_966_);
v___x_2716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2693_, v_options_2692_, v___x_2715_);
lean_dec(v___x_2715_);
if (v___x_2716_ == 0)
{
v___y_2197_ = v___x_2710_;
v___y_2198_ = v___x_2712_;
v___y_2199_ = v___x_2713_;
v___y_2200_ = v_options_2692_;
v___y_2201_ = v_tail_2684_;
v___y_2202_ = v___x_2690_;
v_a_2203_ = v___x_2716_;
goto v___jp_2196_;
}
else
{
v___y_2149_ = v___x_2710_;
v___y_2150_ = v___x_2712_;
v___y_2151_ = v___x_2713_;
v___y_2152_ = v_tail_2684_;
v___y_2153_ = v_options_2692_;
v___y_2154_ = v___x_2690_;
v___y_2155_ = v___x_2716_;
goto v___jp_2148_;
}
}
}
else
{
v_n_969_ = v___x_2710_;
v_curr_970_ = v_tail_2684_;
v_acc_971_ = v___x_2712_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_del_object(v___x_2686_);
lean_dec(v_tail_2684_);
lean_dec(v_head_2683_);
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v_a_2719_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2702_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2702_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
else
{
lean_object* v_options_2727_; lean_object* v_inheritedTraceOptions_2728_; uint8_t v_hasTrace_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
lean_del_object(v___x_2686_);
v_options_2727_ = lean_ctor_get(v_a_974_, 2);
v_inheritedTraceOptions_2728_ = lean_ctor_get(v_a_974_, 13);
v_hasTrace_2729_ = lean_ctor_get_uint8(v_options_2727_, sizeof(void*)*1);
v___x_2730_ = lean_nat_add(v_n_2208_, v_one_2207_);
lean_dec(v_n_2208_);
v___x_2731_ = lean_bool_not(v_hasTrace_2729_);
if (v___x_2731_ == 0)
{
lean_object* v___f_2732_; lean_object* v___x_2733_; 
v___f_2732_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(v___f_2732_, 0, v_head_2683_);
v___x_2733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
if (v_hasTrace_2729_ == 0)
{
v___y_1063_ = v_options_2727_;
v___y_1064_ = v___f_2732_;
v___y_1065_ = v___x_2730_;
v___y_1066_ = v___x_2733_;
v___y_1067_ = v_tail_2684_;
v___y_1068_ = v___x_2690_;
v_a_1069_ = v_hasTrace_2729_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_966_);
v___x_2735_ = l_Lean_Name_append(v___x_2734_, v_trace_966_);
v___x_2736_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2728_, v_options_2727_, v___x_2735_);
lean_dec(v___x_2735_);
if (v___x_2736_ == 0)
{
v___y_1063_ = v_options_2727_;
v___y_1064_ = v___f_2732_;
v___y_1065_ = v___x_2730_;
v___y_1066_ = v___x_2733_;
v___y_1067_ = v_tail_2684_;
v___y_1068_ = v___x_2690_;
v_a_1069_ = v___x_2736_;
goto v___jp_1062_;
}
else
{
v___y_1015_ = v___x_2736_;
v___y_1016_ = v___f_2732_;
v___y_1017_ = v_options_2727_;
v___y_1018_ = v___x_2730_;
v___y_1019_ = v_tail_2684_;
v___y_1020_ = v___x_2733_;
v___y_1021_ = v___x_2690_;
goto v___jp_1014_;
}
}
}
else
{
lean_dec(v_head_2683_);
v_n_969_ = v___x_2730_;
v_curr_970_ = v_tail_2684_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_val_2739_; 
lean_dec(v_curr_970_);
v_val_2739_ = lean_ctor_get(v_a_2671_, 0);
lean_inc(v_val_2739_);
lean_dec_ref_known(v_a_2671_, 1);
v_n_969_ = v_n_2208_;
v_curr_970_ = v_val_2739_;
goto _start;
}
}
v___jp_2741_:
{
if (lean_obj_tag(v___y_2742_) == 0)
{
lean_object* v_a_2743_; 
v_a_2743_ = lean_ctor_get(v___y_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___y_2742_, 1);
v_a_2671_ = v_a_2743_;
goto v___jp_2670_;
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec(v_n_2208_);
lean_dec(v_acc_971_);
lean_dec(v_curr_970_);
lean_dec(v_goals_968_);
lean_dec_ref(v_next_967_);
lean_dec(v_trace_966_);
lean_dec_ref(v_cfg_965_);
v_a_2744_ = lean_ctor_get(v___y_2742_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___y_2742_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___y_2742_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___y_2742_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
v___jp_977_:
{
lean_object* v___x_986_; double v___x_987_; double v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_986_ = lean_io_get_num_heartbeats();
v___x_987_ = lean_float_of_nat(v___y_982_);
v___x_988_ = lean_float_of_nat(v___x_986_);
v___x_989_ = lean_box_float(v___x_987_);
v___x_990_ = lean_box_float(v___x_988_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v_a_985_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
lean_inc_ref(v___y_981_);
v___x_993_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_983_, v___y_981_, v___y_980_, v___y_978_, v___y_984_, v___y_979_, v___x_992_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_993_;
}
v___jp_994_:
{
lean_object* v___x_1003_; double v___x_1004_; double v___x_1005_; double v___x_1006_; double v___x_1007_; double v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1003_ = lean_io_mono_nanos_now();
v___x_1004_ = lean_float_of_nat(v___y_998_);
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
lean_inc_ref(v___y_999_);
v___x_1013_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1000_, v___y_999_, v___y_997_, v___y_995_, v___y_1001_, v___y_996_, v___x_1012_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
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
v___x_1025_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1017_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_io_mono_nanos_now();
lean_inc(v_trace_966_);
v___x_1027_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1018_, v___y_1019_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
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
v___y_996_ = v___y_1016_;
v___y_997_ = v___y_1017_;
v___y_998_ = v___x_1026_;
v___y_999_ = v___y_1020_;
v___y_1000_ = v___y_1021_;
v___y_1001_ = v_a_1023_;
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
v___y_996_ = v___y_1016_;
v___y_997_ = v___y_1017_;
v___y_998_ = v___x_1026_;
v___y_999_ = v___y_1020_;
v___y_1000_ = v___y_1021_;
v___y_1001_ = v_a_1023_;
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
v___x_1045_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_965_, v_trace_966_, v_next_967_, v_goals_968_, v___y_1018_, v___y_1019_, v_acc_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
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
v___y_978_ = v___y_1015_;
v___y_979_ = v___y_1016_;
v___y_980_ = v___y_1017_;
v___y_981_ = v___y_1020_;
v___y_982_ = v___x_1044_;
v___y_983_ = v___y_1021_;
v___y_984_ = v_a_1023_;
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
v___y_978_ = v___y_1015_;
v___y_979_ = v___y_1016_;
v___y_980_ = v___y_1017_;
v___y_981_ = v___y_1020_;
v___y_982_ = v___x_1044_;
v___y_983_ = v___y_1021_;
v___y_984_ = v_a_1023_;
v_a_985_ = v___x_1059_;
goto v___jp_977_;
}
}
}
}
}
v___jp_1062_:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = l_Lean_trace_profiler;
v___x_1071_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1063_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v___y_1064_);
v_n_969_ = v___y_1065_;
v_curr_970_ = v___y_1067_;
goto _start;
}
else
{
v___y_1015_ = v_a_1069_;
v___y_1016_ = v___y_1064_;
v___y_1017_ = v___y_1063_;
v___y_1018_ = v___y_1065_;
v___y_1019_ = v___y_1067_;
v___y_1020_ = v___y_1066_;
v___y_1021_ = v___y_1068_;
goto v___jp_1014_;
}
}
v___jp_1073_:
{
lean_object* v___x_1082_; double v___x_1083_; double v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1082_ = lean_io_get_num_heartbeats();
v___x_1083_ = lean_float_of_nat(v___y_1078_);
v___x_1084_ = lean_float_of_nat(v___x_1082_);
v___x_1085_ = lean_box_float(v___x_1083_);
v___x_1086_ = lean_box_float(v___x_1084_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v_a_1081_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
lean_inc_ref(v___y_1080_);
v___x_1089_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1077_, v___y_1080_, v___y_1075_, v___y_1079_, v___y_1074_, v___y_1076_, v___x_1088_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1089_;
}
v___jp_1090_:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_a_1098_);
v___y_1074_ = v___y_1091_;
v___y_1075_ = v___y_1092_;
v___y_1076_ = v___y_1095_;
v___y_1077_ = v___y_1094_;
v___y_1078_ = v___y_1093_;
v___y_1079_ = v___y_1097_;
v___y_1080_ = v___y_1096_;
v_a_1081_ = v___x_1099_;
goto v___jp_1073_;
}
v___jp_1100_:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_a_1108_);
v___y_1074_ = v___y_1101_;
v___y_1075_ = v___y_1102_;
v___y_1076_ = v___y_1105_;
v___y_1077_ = v___y_1104_;
v___y_1078_ = v___y_1103_;
v___y_1079_ = v___y_1107_;
v___y_1080_ = v___y_1106_;
v_a_1081_ = v___x_1109_;
goto v___jp_1073_;
}
v___jp_1110_:
{
if (lean_obj_tag(v___y_1118_) == 0)
{
lean_object* v_a_1119_; 
v_a_1119_ = lean_ctor_get(v___y_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___y_1118_, 1);
v___y_1091_ = v___y_1111_;
v___y_1092_ = v___y_1112_;
v___y_1093_ = v___y_1115_;
v___y_1094_ = v___y_1114_;
v___y_1095_ = v___y_1113_;
v___y_1096_ = v___y_1117_;
v___y_1097_ = v___y_1116_;
v_a_1098_ = v_a_1119_;
goto v___jp_1090_;
}
else
{
lean_object* v_a_1120_; 
v_a_1120_ = lean_ctor_get(v___y_1118_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___y_1118_, 1);
v___y_1101_ = v___y_1111_;
v___y_1102_ = v___y_1112_;
v___y_1103_ = v___y_1115_;
v___y_1104_ = v___y_1114_;
v___y_1105_ = v___y_1113_;
v___y_1106_ = v___y_1117_;
v___y_1107_ = v___y_1116_;
v_a_1108_ = v_a_1120_;
goto v___jp_1100_;
}
}
v___jp_1121_:
{
lean_object* v___x_1130_; double v___x_1131_; double v___x_1132_; double v___x_1133_; double v___x_1134_; double v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1130_ = lean_io_mono_nanos_now();
v___x_1131_ = lean_float_of_nat(v___y_1122_);
v___x_1132_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1133_ = lean_float_div(v___x_1131_, v___x_1132_);
v___x_1134_ = lean_float_of_nat(v___x_1130_);
v___x_1135_ = lean_float_div(v___x_1134_, v___x_1132_);
v___x_1136_ = lean_box_float(v___x_1133_);
v___x_1137_ = lean_box_float(v___x_1135_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_a_1129_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
lean_inc_ref(v___y_1128_);
v___x_1140_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_966_, v___y_1126_, v___y_1128_, v___y_1124_, v___y_1127_, v___y_1123_, v___y_1125_, v___x_1139_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
return v___x_1140_;
}
v___jp_1141_:
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v_a_1149_);
v___y_1122_ = v___y_1142_;
v___y_1123_ = v___y_1143_;
v___y_1124_ = v___y_1144_;
v___y_1125_ = v___y_1146_;
v___y_1126_ = v___y_1145_;
v___y_1127_ = v___y_1148_;
v___y_1128_ = v___y_1147_;
v_a_1129_ = v___x_1150_;
goto v___jp_1121_;
}
v___jp_1151_:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_a_1159_);
v___y_1122_ = v___y_1152_;
v___y_1123_ = v___y_1153_;
v___y_1124_ = v___y_1154_;
v___y_1125_ = v___y_1156_;
v___y_1126_ = v___y_1155_;
v___y_1127_ = v___y_1158_;
v___y_1128_ = v___y_1157_;
v_a_1129_ = v___x_1160_;
goto v___jp_1121_;
}
v___jp_1161_:
{
if (lean_obj_tag(v___y_1169_) == 0)
{
lean_object* v_a_1170_; 
v_a_1170_ = lean_ctor_get(v___y_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___y_1169_, 1);
v___y_1142_ = v___y_1162_;
v___y_1143_ = v___y_1163_;
v___y_1144_ = v___y_1164_;
v___y_1145_ = v___y_1166_;
v___y_1146_ = v___y_1165_;
v___y_1147_ = v___y_1168_;
v___y_1148_ = v___y_1167_;
v_a_1149_ = v_a_1170_;
goto v___jp_1141_;
}
else
{
lean_object* v_a_1171_; 
v_a_1171_ = lean_ctor_get(v___y_1169_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___y_1169_, 1);
v___y_1152_ = v___y_1162_;
v___y_1153_ = v___y_1163_;
v___y_1154_ = v___y_1164_;
v___y_1155_ = v___y_1166_;
v___y_1156_ = v___y_1165_;
v___y_1157_ = v___y_1168_;
v___y_1158_ = v___y_1167_;
v_a_1159_ = v_a_1171_;
goto v___jp_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2825_, lean_object* v_trace_2826_, lean_object* v_next_2827_, lean_object* v_goals_2828_, lean_object* v_n_2829_, lean_object* v_curr_2830_, lean_object* v_acc_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2825_, v_trace_2826_, v_next_2827_, v_goals_2828_, v_n_2829_, v_curr_2830_, v_acc_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__11(lean_object* v_tail_2838_, lean_object* v_cfg_2839_, lean_object* v_trace_2840_, lean_object* v_next_2841_, lean_object* v_goals_2842_, lean_object* v_n_2843_, lean_object* v_acc_2844_, lean_object* v_r_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = l_List_appendTR___redArg(v_r_2845_, v_tail_2838_);
v___x_2852_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2852_, 0, v_cfg_2839_);
lean_closure_set(v___x_2852_, 1, v_trace_2840_);
lean_closure_set(v___x_2852_, 2, v_next_2841_);
lean_closure_set(v___x_2852_, 3, v_goals_2842_);
lean_closure_set(v___x_2852_, 4, v_n_2843_);
lean_closure_set(v___x_2852_, 5, v___x_2851_);
lean_closure_set(v___x_2852_, 6, v_acc_2844_);
v___x_2853_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v___x_2852_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2854_, lean_object* v_msg_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2862_, lean_object* v_msg_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2862_, v_msg_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object* v_00_u03b1_2870_, lean_object* v_x_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_2871_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2878_, lean_object* v_x_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_00_u03b1_2878_, v_x_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* v_mvarId_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_2886_, v___y_2888_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* v_mvarId_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_mvarId_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v_mvarId_2893_);
return v_res_2899_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_object* v_00_u03b2_2900_, lean_object* v_x_2901_, lean_object* v_x_2902_){
_start:
{
uint8_t v___x_2903_; 
v___x_2903_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_2901_, v_x_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2904_, lean_object* v_x_2905_, lean_object* v_x_2906_){
_start:
{
uint8_t v_res_2907_; lean_object* v_r_2908_; 
v_res_2907_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(v_00_u03b2_2904_, v_x_2905_, v_x_2906_);
lean_dec(v_x_2906_);
lean_dec_ref(v_x_2905_);
v_r_2908_ = lean_box(v_res_2907_);
return v_r_2908_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_2909_, lean_object* v_x_2910_, size_t v_x_2911_, lean_object* v_x_2912_){
_start:
{
uint8_t v___x_2913_; 
v___x_2913_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_2910_, v_x_2911_, v_x_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___boxed(lean_object* v_00_u03b2_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_, lean_object* v_x_2917_){
_start:
{
size_t v_x_85744__boxed_2918_; uint8_t v_res_2919_; lean_object* v_r_2920_; 
v_x_85744__boxed_2918_ = lean_unbox_usize(v_x_2916_);
lean_dec(v_x_2916_);
v_res_2919_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2914_, v_x_2915_, v_x_85744__boxed_2918_, v_x_2917_);
lean_dec(v_x_2917_);
lean_dec_ref(v_x_2915_);
v_r_2920_ = lean_box(v_res_2919_);
return v_r_2920_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_object* v_00_u03b2_2921_, lean_object* v_keys_2922_, lean_object* v_vals_2923_, lean_object* v_heq_2924_, lean_object* v_i_2925_, lean_object* v_k_2926_){
_start:
{
uint8_t v___x_2927_; 
v___x_2927_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_2922_, v_i_2925_, v_k_2926_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2928_, lean_object* v_keys_2929_, lean_object* v_vals_2930_, lean_object* v_heq_2931_, lean_object* v_i_2932_, lean_object* v_k_2933_){
_start:
{
uint8_t v_res_2934_; lean_object* v_r_2935_; 
v_res_2934_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(v_00_u03b2_2928_, v_keys_2929_, v_vals_2930_, v_heq_2931_, v_i_2932_, v_k_2933_);
lean_dec(v_k_2933_);
lean_dec_ref(v_vals_2930_);
lean_dec_ref(v_keys_2929_);
v_r_2935_ = lean_box(v_res_2934_);
return v_r_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2936_, lean_object* v_h__1_2937_, lean_object* v_h__2_2938_){
_start:
{
lean_object* v_zero_2939_; uint8_t v_isZero_2940_; 
v_zero_2939_ = lean_unsigned_to_nat(0u);
v_isZero_2940_ = lean_nat_dec_eq(v_n_2936_, v_zero_2939_);
if (v_isZero_2940_ == 1)
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec(v_h__2_2938_);
v___x_2941_ = lean_box(0);
v___x_2942_ = lean_apply_1(v_h__1_2937_, v___x_2941_);
return v___x_2942_;
}
else
{
lean_object* v_one_2943_; lean_object* v_n_2944_; lean_object* v___x_2945_; 
lean_dec(v_h__1_2937_);
v_one_2943_ = lean_unsigned_to_nat(1u);
v_n_2944_ = lean_nat_sub(v_n_2936_, v_one_2943_);
v___x_2945_ = lean_apply_1(v_h__2_2938_, v_n_2944_);
return v___x_2945_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2946_, lean_object* v_h__1_2947_, lean_object* v_h__2_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2946_, v_h__1_2947_, v_h__2_2948_);
lean_dec(v_n_2946_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2950_, lean_object* v_n_2951_, lean_object* v_h__1_2952_, lean_object* v_h__2_2953_){
_start:
{
lean_object* v_zero_2954_; uint8_t v_isZero_2955_; 
v_zero_2954_ = lean_unsigned_to_nat(0u);
v_isZero_2955_ = lean_nat_dec_eq(v_n_2951_, v_zero_2954_);
if (v_isZero_2955_ == 1)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
lean_dec(v_h__2_2953_);
v___x_2956_ = lean_box(0);
v___x_2957_ = lean_apply_1(v_h__1_2952_, v___x_2956_);
return v___x_2957_;
}
else
{
lean_object* v_one_2958_; lean_object* v_n_2959_; lean_object* v___x_2960_; 
lean_dec(v_h__1_2952_);
v_one_2958_ = lean_unsigned_to_nat(1u);
v_n_2959_ = lean_nat_sub(v_n_2951_, v_one_2958_);
v___x_2960_ = lean_apply_1(v_h__2_2953_, v_n_2959_);
return v___x_2960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* v_motive_2961_, lean_object* v_n_2962_, lean_object* v_h__1_2963_, lean_object* v_h__2_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(v_motive_2961_, v_n_2962_, v_h__1_2963_, v_h__2_2964_);
lean_dec(v_n_2962_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* v_procResult_x3f_2966_, lean_object* v_h__1_2967_, lean_object* v_h__2_2968_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2966_) == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_dec(v_h__1_2967_);
v___x_2969_ = lean_box(0);
v___x_2970_ = lean_apply_1(v_h__2_2968_, v___x_2969_);
return v___x_2970_;
}
else
{
lean_object* v_val_2971_; lean_object* v___x_2972_; 
lean_dec(v_h__2_2968_);
v_val_2971_ = lean_ctor_get(v_procResult_x3f_2966_, 0);
lean_inc(v_val_2971_);
lean_dec_ref_known(v_procResult_x3f_2966_, 1);
v___x_2972_ = lean_apply_1(v_h__1_2967_, v_val_2971_);
return v___x_2972_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* v_motive_2973_, lean_object* v_procResult_x3f_2974_, lean_object* v_h__1_2975_, lean_object* v_h__2_2976_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2974_) == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec(v_h__1_2975_);
v___x_2977_ = lean_box(0);
v___x_2978_ = lean_apply_1(v_h__2_2976_, v___x_2977_);
return v___x_2978_;
}
else
{
lean_object* v_val_2979_; lean_object* v___x_2980_; 
lean_dec(v_h__2_2976_);
v_val_2979_ = lean_ctor_get(v_procResult_x3f_2974_, 0);
lean_inc(v_val_2979_);
lean_dec_ref_known(v_procResult_x3f_2974_, 1);
v___x_2980_ = lean_apply_1(v_h__1_2975_, v_val_2979_);
return v___x_2980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2981_, lean_object* v_h__1_2982_, lean_object* v_h__2_2983_){
_start:
{
if (lean_obj_tag(v_curr_2981_) == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
lean_dec(v_h__2_2983_);
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_apply_1(v_h__1_2982_, v___x_2984_);
return v___x_2985_;
}
else
{
lean_object* v_head_2986_; lean_object* v_tail_2987_; lean_object* v___x_2988_; 
lean_dec(v_h__1_2982_);
v_head_2986_ = lean_ctor_get(v_curr_2981_, 0);
lean_inc(v_head_2986_);
v_tail_2987_ = lean_ctor_get(v_curr_2981_, 1);
lean_inc(v_tail_2987_);
lean_dec_ref_known(v_curr_2981_, 2);
v___x_2988_ = lean_apply_2(v_h__2_2983_, v_head_2986_, v_tail_2987_);
return v___x_2988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2989_, lean_object* v_curr_2990_, lean_object* v_h__1_2991_, lean_object* v_h__2_2992_){
_start:
{
if (lean_obj_tag(v_curr_2990_) == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
lean_dec(v_h__2_2992_);
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_apply_1(v_h__1_2991_, v___x_2993_);
return v___x_2994_;
}
else
{
lean_object* v_head_2995_; lean_object* v_tail_2996_; lean_object* v___x_2997_; 
lean_dec(v_h__1_2991_);
v_head_2995_ = lean_ctor_get(v_curr_2990_, 0);
lean_inc(v_head_2995_);
v_tail_2996_ = lean_ctor_get(v_curr_2990_, 1);
lean_inc(v_tail_2996_);
lean_dec_ref_known(v_curr_2990_, 2);
v___x_2997_ = lean_apply_2(v_h__2_2992_, v_head_2995_, v_tail_2996_);
return v___x_2997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2998_, lean_object* v_h__1_2999_, lean_object* v_h__2_3000_){
_start:
{
if (lean_obj_tag(v_____do__lift_2998_) == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
lean_dec(v_h__2_3000_);
v___x_3001_ = lean_box(0);
v___x_3002_ = lean_apply_1(v_h__1_2999_, v___x_3001_);
return v___x_3002_;
}
else
{
lean_object* v_val_3003_; lean_object* v___x_3004_; 
lean_dec(v_h__1_2999_);
v_val_3003_ = lean_ctor_get(v_____do__lift_2998_, 0);
lean_inc(v_val_3003_);
lean_dec_ref_known(v_____do__lift_2998_, 1);
v___x_3004_ = lean_apply_1(v_h__2_3000_, v_val_3003_);
return v___x_3004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_3005_, lean_object* v_____do__lift_3006_, lean_object* v_h__1_3007_, lean_object* v_h__2_3008_){
_start:
{
if (lean_obj_tag(v_____do__lift_3006_) == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec(v_h__2_3008_);
v___x_3009_ = lean_box(0);
v___x_3010_ = lean_apply_1(v_h__1_3007_, v___x_3009_);
return v___x_3010_;
}
else
{
lean_object* v_val_3011_; lean_object* v___x_3012_; 
lean_dec(v_h__1_3007_);
v_val_3011_ = lean_ctor_get(v_____do__lift_3006_, 0);
lean_inc(v_val_3011_);
lean_dec_ref_known(v_____do__lift_3006_, 1);
v___x_3012_ = lean_apply_1(v_h__2_3008_, v_val_3011_);
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_3013_, lean_object* v_trace_3014_, lean_object* v_next_3015_, lean_object* v_orig_3016_, lean_object* v_g_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_maxDepth_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v_maxDepth_3023_ = lean_ctor_get(v_cfg_3013_, 0);
lean_inc(v_maxDepth_3023_);
v___x_3024_ = lean_box(0);
v___x_3025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3025_, 0, v_g_3017_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_3013_, v_trace_3014_, v_next_3015_, v_orig_3016_, v_maxDepth_3023_, v___x_3025_, v___x_3024_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_3027_, lean_object* v_trace_3028_, lean_object* v_next_3029_, lean_object* v_orig_3030_, lean_object* v_g_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_3027_, v_trace_3028_, v_next_3029_, v_orig_3030_, v_g_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
if (lean_obj_tag(v_a_3038_) == 0)
{
lean_object* v___x_3040_; 
v___x_3040_ = l_List_reverse___redArg(v_a_3039_);
return v___x_3040_;
}
else
{
lean_object* v_head_3041_; lean_object* v_tail_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3051_; 
v_head_3041_ = lean_ctor_get(v_a_3038_, 0);
v_tail_3042_ = lean_ctor_get(v_a_3038_, 1);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_a_3038_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3044_ = v_a_3038_;
v_isShared_3045_ = v_isSharedCheck_3051_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_tail_3042_);
lean_inc(v_head_3041_);
lean_dec(v_a_3038_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3051_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3046_ = l_Lean_MessageData_ofFormat(v_head_3041_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 1, v_a_3039_);
lean_ctor_set(v___x_3044_, 0, v___x_3046_);
v___x_3048_ = v___x_3044_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_a_3039_);
v___x_3048_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
v_a_3038_ = v_tail_3042_;
v_a_3039_ = v___x_3048_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_3054_ = l_Lean_stringToMessageData(v___x_3053_);
return v___x_3054_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_3057_ = l_Lean_stringToMessageData(v___x_3056_);
return v___x_3057_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_3060_ = l_Lean_stringToMessageData(v___x_3059_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_3061_, lean_object* v_snd_3062_, lean_object* v_x_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_3061_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3071_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_a_3070_);
lean_dec_ref_known(v___x_3069_, 1);
v___x_3071_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_3062_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3091_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3074_ = v___x_3071_;
v_isShared_3075_ = v_isSharedCheck_3091_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3071_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3091_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3076_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_3077_ = lean_box(0);
v___x_3078_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_3070_, v___x_3077_);
v___x_3079_ = l_Lean_MessageData_ofList(v___x_3078_);
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3076_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_3084_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_3072_, v___x_3077_);
v___x_3085_ = l_Lean_MessageData_ofList(v___x_3084_);
v___x_3086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3083_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3082_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 0, v___x_3087_);
v___x_3089_ = v___x_3074_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_a_3070_);
v_a_3092_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3071_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3071_);
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
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec(v_snd_3062_);
v_a_3100_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3069_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3069_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_3108_, lean_object* v_snd_3109_, lean_object* v_x_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_3108_, v_snd_3109_, v_x_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec_ref(v_x_3110_);
return v_res_3116_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_3119_ = l_Lean_stringToMessageData(v___x_3118_);
return v___x_3119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_3122_ = l_Lean_stringToMessageData(v___x_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_3123_, lean_object* v___x_3124_, lean_object* v_x_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_3123_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3133_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3131_, 1);
v___x_3133_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_3124_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3151_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3136_ = v___x_3133_;
v_isShared_3137_ = v_isSharedCheck_3151_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3151_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3138_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_3139_ = lean_box(0);
v___x_3140_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_3132_, v___x_3139_);
v___x_3141_ = l_Lean_MessageData_ofList(v___x_3140_);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3138_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3142_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_3134_, v___x_3139_);
v___x_3146_ = l_Lean_MessageData_ofList(v___x_3145_);
v___x_3147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3144_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v___x_3147_);
v___x_3149_ = v___x_3136_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_a_3132_);
v_a_3152_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3133_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3133_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v___x_3124_);
v_a_3160_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3131_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3131_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_3168_, lean_object* v___x_3169_, lean_object* v_x_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_3168_, v___x_3169_, v_x_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v_x_3170_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(lean_object* v_x_3177_, lean_object* v_x_3178_, lean_object* v___y_3179_){
_start:
{
if (lean_obj_tag(v_x_3177_) == 0)
{
lean_object* v___x_3181_; 
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_x_3178_);
return v___x_3181_;
}
else
{
lean_object* v_head_3182_; lean_object* v_tail_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3198_; 
v_head_3182_ = lean_ctor_get(v_x_3177_, 0);
v_tail_3183_ = lean_ctor_get(v_x_3177_, 1);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_x_3177_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3185_ = v_x_3177_;
v_isShared_3186_ = v_isSharedCheck_3198_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_tail_3183_);
lean_inc(v_head_3182_);
lean_dec(v_x_3177_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3198_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
uint8_t v_a_3188_; lean_object* v___x_3194_; lean_object* v_a_3195_; uint8_t v___x_3196_; uint8_t v___x_3197_; 
v___x_3194_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_3182_, v___y_3179_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref(v___x_3194_);
v___x_3196_ = lean_unbox(v_a_3195_);
lean_dec(v_a_3195_);
v___x_3197_ = lean_bool_not(v___x_3196_);
v_a_3188_ = v___x_3197_;
goto v___jp_3187_;
v___jp_3187_:
{
if (v_a_3188_ == 0)
{
lean_del_object(v___x_3185_);
lean_dec(v_head_3182_);
v_x_3177_ = v_tail_3183_;
goto _start;
}
else
{
lean_object* v___x_3191_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 1, v_x_3178_);
v___x_3191_ = v___x_3185_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_head_3182_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_x_3178_);
v___x_3191_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
v_x_3177_ = v_tail_3183_;
v_x_3178_ = v___x_3191_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v_x_3199_, lean_object* v_x_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_x_3199_, v_x_3200_, v___y_3201_);
lean_dec(v___y_3201_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
if (lean_obj_tag(v_a_3204_) == 0)
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_array_to_list(v_a_3205_);
return v___x_3206_;
}
else
{
lean_object* v_head_3207_; lean_object* v_tail_3208_; lean_object* v___x_3209_; 
v_head_3207_ = lean_ctor_get(v_a_3204_, 0);
lean_inc(v_head_3207_);
v_tail_3208_ = lean_ctor_get(v_a_3204_, 1);
lean_inc(v_tail_3208_);
lean_dec_ref_known(v_a_3204_, 2);
v___x_3209_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_3205_, v_head_3207_);
v_a_3204_ = v_tail_3208_;
v_a_3205_ = v___x_3209_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
if (lean_obj_tag(v_a_3212_) == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec(v_goals_3211_);
v___x_3220_ = lean_array_to_list(v_a_3213_);
v___x_3221_ = lean_array_to_list(v_a_3214_);
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3220_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
else
{
lean_object* v_head_3224_; lean_object* v_tail_3225_; lean_object* v___x_3226_; 
v_head_3224_ = lean_ctor_get(v_a_3212_, 0);
lean_inc_n(v_head_3224_, 2);
v_tail_3225_ = lean_ctor_get(v_a_3212_, 1);
lean_inc(v_tail_3225_);
lean_dec_ref_known(v_a_3212_, 2);
lean_inc(v_goals_3211_);
v___x_3226_ = l_Lean_MVarId_isIndependentOf(v_goals_3211_, v_head_3224_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; uint8_t v___x_3228_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___x_3228_ = lean_unbox(v_a_3227_);
lean_dec(v_a_3227_);
if (v___x_3228_ == 0)
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_array_push(v_a_3214_, v_head_3224_);
v_a_3212_ = v_tail_3225_;
v_a_3214_ = v___x_3229_;
goto _start;
}
else
{
lean_object* v___x_3231_; 
v___x_3231_ = lean_array_push(v_a_3213_, v_head_3224_);
v_a_3212_ = v_tail_3225_;
v_a_3213_ = v___x_3231_;
goto _start;
}
}
else
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
lean_dec(v_tail_3225_);
lean_dec(v_head_3224_);
lean_dec_ref(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_goals_3211_);
v_a_3233_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3226_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3226_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
if (lean_obj_tag(v_a_3251_) == 0)
{
lean_object* v___x_3253_; 
v___x_3253_ = lean_array_to_list(v_a_3252_);
return v___x_3253_;
}
else
{
lean_object* v_head_3254_; 
v_head_3254_ = lean_ctor_get(v_a_3251_, 0);
if (lean_obj_tag(v_head_3254_) == 0)
{
lean_object* v_tail_3255_; lean_object* v_val_3256_; lean_object* v___x_3257_; 
lean_inc_ref(v_head_3254_);
v_tail_3255_ = lean_ctor_get(v_a_3251_, 1);
lean_inc(v_tail_3255_);
lean_dec_ref_known(v_a_3251_, 2);
v_val_3256_ = lean_ctor_get(v_head_3254_, 0);
lean_inc(v_val_3256_);
lean_dec_ref_known(v_head_3254_, 1);
v___x_3257_ = lean_array_push(v_a_3252_, v_val_3256_);
v_a_3251_ = v_tail_3255_;
v_a_3252_ = v___x_3257_;
goto _start;
}
else
{
lean_object* v_tail_3259_; 
v_tail_3259_ = lean_ctor_get(v_a_3251_, 1);
lean_inc(v_tail_3259_);
lean_dec_ref_known(v_a_3251_, 2);
v_a_3251_ = v_tail_3259_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_3261_, lean_object* v_x_3262_, lean_object* v_x_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
if (lean_obj_tag(v_x_3262_) == 0)
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_dec_ref(v_f_3261_);
v___x_3269_ = l_List_reverse___redArg(v_x_3263_);
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
return v___x_3270_;
}
else
{
lean_object* v_head_3271_; lean_object* v_tail_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3317_; 
v_head_3271_ = lean_ctor_get(v_x_3262_, 0);
v_tail_3272_ = lean_ctor_get(v_x_3262_, 1);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_x_3262_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3274_ = v_x_3262_;
v_isShared_3275_ = v_isSharedCheck_3317_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_tail_3272_);
lean_inc(v_head_3271_);
lean_dec(v_x_3262_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3317_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v_a_3277_; lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_Meta_saveState___redArg(v___y_3265_, v___y_3267_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v___x_3284_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___x_3282_, 1);
lean_inc_ref(v_f_3261_);
lean_inc(v___y_3267_);
lean_inc_ref(v___y_3266_);
lean_inc(v___y_3265_);
lean_inc_ref(v___y_3264_);
lean_inc(v_head_3271_);
v___x_3284_ = lean_apply_6(v_f_3261_, v_head_3271_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, lean_box(0));
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3286_; 
lean_dec(v_a_3283_);
lean_dec(v_head_3271_);
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_a_3285_);
v_a_3277_ = v___x_3286_;
goto v___jp_3276_;
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3308_; 
v_a_3287_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3289_ = v___x_3284_;
v_isShared_3290_ = v_isSharedCheck_3308_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3284_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3308_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
uint8_t v___y_3292_; uint8_t v___x_3306_; 
v___x_3306_ = l_Lean_Exception_isInterrupt(v_a_3287_);
if (v___x_3306_ == 0)
{
uint8_t v___x_3307_; 
lean_inc(v_a_3287_);
v___x_3307_ = l_Lean_Exception_isRuntime(v_a_3287_);
v___y_3292_ = v___x_3307_;
goto v___jp_3291_;
}
else
{
v___y_3292_ = v___x_3306_;
goto v___jp_3291_;
}
v___jp_3291_:
{
if (v___y_3292_ == 0)
{
lean_object* v___x_3293_; 
lean_del_object(v___x_3289_);
lean_dec(v_a_3287_);
v___x_3293_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3283_, v___y_3265_, v___y_3267_);
lean_dec(v_a_3283_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v___x_3294_; 
lean_dec_ref_known(v___x_3293_, 1);
v___x_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3294_, 0, v_head_3271_);
v_a_3277_ = v___x_3294_;
goto v___jp_3276_;
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_del_object(v___x_3274_);
lean_dec(v_tail_3272_);
lean_dec(v_head_3271_);
lean_dec(v_x_3263_);
lean_dec_ref(v_f_3261_);
v_a_3295_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3293_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3293_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v___x_3304_; 
lean_dec(v_a_3283_);
lean_del_object(v___x_3274_);
lean_dec(v_tail_3272_);
lean_dec(v_head_3271_);
lean_dec(v_x_3263_);
lean_dec_ref(v_f_3261_);
if (v_isShared_3290_ == 0)
{
v___x_3304_ = v___x_3289_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3287_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_del_object(v___x_3274_);
lean_dec(v_tail_3272_);
lean_dec(v_head_3271_);
lean_dec(v_x_3263_);
lean_dec_ref(v_f_3261_);
v_a_3309_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3282_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3282_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
v___jp_3276_:
{
lean_object* v___x_3279_; 
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 1, v_x_3263_);
lean_ctor_set(v___x_3274_, 0, v_a_3277_);
v___x_3279_ = v___x_3274_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3277_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_x_3263_);
v___x_3279_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
v_x_3262_ = v_tail_3272_;
v_x_3263_ = v___x_3279_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_3318_, v_x_3319_, v_x_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
if (lean_obj_tag(v_a_3327_) == 0)
{
lean_object* v___x_3329_; 
v___x_3329_ = lean_array_to_list(v_a_3328_);
return v___x_3329_;
}
else
{
lean_object* v_head_3330_; 
v_head_3330_ = lean_ctor_get(v_a_3327_, 0);
if (lean_obj_tag(v_head_3330_) == 1)
{
lean_object* v_tail_3331_; lean_object* v_val_3332_; lean_object* v___x_3333_; 
lean_inc_ref(v_head_3330_);
v_tail_3331_ = lean_ctor_get(v_a_3327_, 1);
lean_inc(v_tail_3331_);
lean_dec_ref_known(v_a_3327_, 2);
v_val_3332_ = lean_ctor_get(v_head_3330_, 0);
lean_inc(v_val_3332_);
lean_dec_ref_known(v_head_3330_, 1);
v___x_3333_ = lean_array_push(v_a_3328_, v_val_3332_);
v_a_3327_ = v_tail_3331_;
v_a_3328_ = v___x_3333_;
goto _start;
}
else
{
lean_object* v_tail_3335_; 
v_tail_3335_ = lean_ctor_get(v_a_3327_, 1);
lean_inc(v_tail_3335_);
lean_dec_ref_known(v_a_3327_, 2);
v_a_3327_ = v_tail_3335_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_3337_, lean_object* v_f_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = lean_box(0);
v___x_3345_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_3338_, v_L_3337_, v___x_3344_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3357_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3348_ = v___x_3345_;
v_isShared_3349_ = v_isSharedCheck_3357_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3345_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3357_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3350_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_3346_);
v___x_3351_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_3346_, v___x_3350_);
v___x_3352_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_3346_, v___x_3350_);
v___x_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3351_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 0, v___x_3353_);
v___x_3355_ = v___x_3348_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
v_a_3358_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3345_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3345_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* v_L_3366_, lean_object* v_f_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_3366_, v_f_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
return v_res_3373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2(void){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1));
v___x_3378_ = l_Lean_stringToMessageData(v___x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_3379_, lean_object* v_trace_3380_, lean_object* v_next_3381_, lean_object* v_orig_3382_, lean_object* v_goals_3383_, lean_object* v_remaining_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v_a_3393_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v_a_3405_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
lean_inc(v_remaining_3384_);
lean_inc(v_goals_3383_);
v___x_3415_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_3383_, v_remaining_3384_, v___x_3414_, v___x_3414_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_5150_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_5150_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_5150_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_5150_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_5150_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v_fst_3420_; lean_object* v_snd_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_5149_; 
v_fst_3420_ = lean_ctor_get(v_a_3416_, 0);
v_snd_3421_ = lean_ctor_get(v_a_3416_, 1);
v_isSharedCheck_5149_ = !lean_is_exclusive(v_a_3416_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_3423_ = v_a_3416_;
v_isShared_3424_ = v_isSharedCheck_5149_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_snd_3421_);
lean_inc(v_fst_3420_);
lean_dec(v_a_3416_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_5149_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; uint8_t v___y_3430_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v_a_3461_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; uint8_t v___y_3485_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v_a_3516_; uint8_t v___x_3535_; 
v___x_3535_ = l_List_isEmpty___redArg(v_fst_3420_);
if (v___x_3535_ == 0)
{
lean_object* v_options_3536_; lean_object* v_inheritedTraceOptions_3537_; uint8_t v_hasTrace_3538_; lean_object* v___f_3539_; uint8_t v___x_3540_; uint8_t v___x_3541_; 
lean_dec(v_remaining_3384_);
v_options_3536_ = lean_ctor_get(v_a_3387_, 2);
v_inheritedTraceOptions_3537_ = lean_ctor_get(v_a_3387_, 13);
v_hasTrace_3538_ = lean_ctor_get_uint8(v_options_3536_, sizeof(void*)*1);
lean_inc(v_orig_3382_);
lean_inc_ref(v_next_3381_);
lean_inc(v_trace_3380_);
lean_inc_ref(v_cfg_3379_);
v___f_3539_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3539_, 0, v_cfg_3379_);
lean_closure_set(v___f_3539_, 1, v_trace_3380_);
lean_closure_set(v___f_3539_, 2, v_next_3381_);
lean_closure_set(v___f_3539_, 3, v_orig_3382_);
v___x_3540_ = 1;
v___x_3541_ = lean_bool_not(v_hasTrace_3538_);
if (v___x_3541_ == 0)
{
lean_object* v___f_3542_; lean_object* v___x_3543_; lean_object* v___y_3545_; uint8_t v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v_a_3549_; uint8_t v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v_a_3565_; uint8_t v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v_a_3572_; lean_object* v___y_3575_; lean_object* v___y_3576_; uint8_t v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v_a_3581_; lean_object* v___y_3585_; uint8_t v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3595_; lean_object* v___y_3596_; uint8_t v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; uint8_t v___y_3603_; lean_object* v___y_3607_; uint8_t v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3615_; lean_object* v___y_3616_; uint8_t v___y_3617_; lean_object* v___y_3618_; lean_object* v___y_3619_; lean_object* v___y_3620_; lean_object* v___y_3621_; lean_object* v___y_3630_; uint8_t v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v_a_3636_; lean_object* v___y_3649_; lean_object* v___y_3650_; uint8_t v___y_3651_; lean_object* v___y_3652_; lean_object* v_a_3653_; lean_object* v___y_3666_; uint8_t v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v_a_3670_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; uint8_t v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v_a_3679_; lean_object* v___y_3683_; uint8_t v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v_a_3687_; lean_object* v___y_3690_; lean_object* v___y_3691_; uint8_t v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; uint8_t v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3713_; lean_object* v___y_3714_; uint8_t v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3723_; lean_object* v___y_3724_; uint8_t v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; uint8_t v___y_3731_; lean_object* v___y_3735_; lean_object* v___y_3736_; uint8_t v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v_a_3741_; lean_object* v___y_3754_; uint8_t v___y_3755_; lean_object* v___y_3756_; lean_object* v___y_3757_; lean_object* v___y_3758_; uint8_t v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; uint8_t v_a_3789_; uint8_t v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v_a_3798_; uint8_t v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v_a_3814_; lean_object* v___y_3817_; uint8_t v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v_a_3822_; lean_object* v___y_3826_; uint8_t v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v_a_3831_; uint8_t v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v_a_3838_; lean_object* v___y_3841_; uint8_t v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; uint8_t v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; uint8_t v___y_3857_; lean_object* v___y_3861_; uint8_t v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; uint8_t v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; uint8_t v___y_3877_; uint8_t v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3888_; lean_object* v___y_3889_; uint8_t v___y_3890_; uint8_t v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v_a_3895_; lean_object* v___y_3905_; lean_object* v___y_3906_; uint8_t v___y_3907_; uint8_t v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v_a_3912_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; uint8_t v___y_3918_; uint8_t v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v_a_3924_; lean_object* v___y_3928_; lean_object* v___y_3929_; uint8_t v___y_3930_; uint8_t v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v_a_3935_; lean_object* v___y_3938_; lean_object* v___y_3939_; uint8_t v___y_3940_; uint8_t v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; uint8_t v___y_3952_; uint8_t v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; uint8_t v___y_3970_; uint8_t v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; uint8_t v___y_3985_; uint8_t v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; uint8_t v___y_3991_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; uint8_t v___y_3998_; uint8_t v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v_a_4004_; lean_object* v___y_4017_; lean_object* v___y_4018_; uint8_t v___y_4019_; uint8_t v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v_a_4024_; lean_object* v___y_4037_; lean_object* v___y_4038_; uint8_t v___y_4039_; uint8_t v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v_a_4044_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; uint8_t v___y_4050_; uint8_t v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v_a_4056_; lean_object* v___y_4060_; lean_object* v___y_4061_; uint8_t v___y_4062_; uint8_t v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v_a_4067_; lean_object* v___y_4070_; lean_object* v___y_4071_; uint8_t v___y_4072_; uint8_t v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; uint8_t v___y_4085_; uint8_t v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; uint8_t v___y_4102_; uint8_t v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; uint8_t v___y_4116_; uint8_t v___y_4117_; lean_object* v___y_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; uint8_t v___y_4123_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; uint8_t v___y_4130_; uint8_t v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v_a_4136_; lean_object* v___y_4149_; lean_object* v___y_4150_; uint8_t v___y_4151_; uint8_t v___y_4152_; uint8_t v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4175_; uint8_t v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v___y_4189_; uint8_t v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v_a_4194_; lean_object* v___y_4207_; uint8_t v___y_4208_; lean_object* v___y_4209_; uint8_t v___y_4210_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; uint8_t v_a_4215_; lean_object* v___y_4224_; lean_object* v___y_4225_; uint8_t v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4238_; uint8_t v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v_a_4243_; lean_object* v___y_4256_; uint8_t v___y_4257_; lean_object* v___y_4258_; lean_object* v_a_4259_; lean_object* v___y_4269_; uint8_t v___y_4270_; lean_object* v___y_4271_; lean_object* v_a_4272_; lean_object* v___y_4275_; uint8_t v___y_4276_; lean_object* v___y_4277_; lean_object* v_a_4278_; lean_object* v___y_4281_; uint8_t v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4288_; lean_object* v___y_4289_; uint8_t v___y_4290_; lean_object* v___y_4291_; uint8_t v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v_a_4295_; lean_object* v___y_4308_; lean_object* v___y_4309_; uint8_t v___y_4310_; lean_object* v___y_4311_; uint8_t v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v_a_4315_; lean_object* v___y_4318_; lean_object* v___y_4319_; uint8_t v___y_4320_; lean_object* v___y_4321_; uint8_t v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v_a_4325_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; uint8_t v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; uint8_t v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v_a_4337_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; uint8_t v___y_4345_; lean_object* v___y_4346_; uint8_t v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; uint8_t v___y_4359_; lean_object* v___y_4360_; uint8_t v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; uint8_t v___y_4365_; lean_object* v___y_4369_; lean_object* v___y_4370_; uint8_t v___y_4371_; lean_object* v___y_4372_; uint8_t v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; uint8_t v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; uint8_t v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; uint8_t v___y_4401_; lean_object* v___y_4402_; lean_object* v___y_4403_; uint8_t v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; lean_object* v_a_4407_; lean_object* v___y_4420_; lean_object* v___y_4421_; uint8_t v___y_4422_; lean_object* v___y_4423_; uint8_t v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v_a_4427_; lean_object* v___y_4437_; lean_object* v___y_4438_; uint8_t v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; uint8_t v___y_4442_; lean_object* v___y_4443_; lean_object* v_a_4444_; lean_object* v___y_4447_; lean_object* v___y_4448_; uint8_t v___y_4449_; lean_object* v___y_4450_; lean_object* v___y_4451_; uint8_t v___y_4452_; lean_object* v___y_4453_; lean_object* v_a_4454_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; uint8_t v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; uint8_t v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v_a_4466_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; uint8_t v___y_4474_; lean_object* v___y_4475_; lean_object* v___y_4476_; uint8_t v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; uint8_t v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; uint8_t v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; uint8_t v___y_4494_; lean_object* v___y_4498_; lean_object* v___y_4499_; uint8_t v___y_4500_; lean_object* v___y_4501_; uint8_t v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; uint8_t v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; uint8_t v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; uint8_t v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; uint8_t v___y_4534_; lean_object* v___y_4535_; lean_object* v_a_4536_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; uint8_t v___y_4553_; lean_object* v___y_4554_; uint8_t v___y_4555_; uint8_t v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4577_; uint8_t v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___y_4589_; lean_object* v___y_4590_; uint8_t v___y_4591_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v___y_4603_; lean_object* v___y_4604_; uint8_t v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v_a_4608_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; uint8_t v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; uint8_t v___y_4625_; lean_object* v___y_4626_; lean_object* v___y_4627_; uint8_t v___y_4628_; lean_object* v___y_4632_; lean_object* v___y_4633_; uint8_t v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v_a_4637_; lean_object* v___y_4650_; lean_object* v___y_4651_; uint8_t v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v_a_4655_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; uint8_t v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; uint8_t v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; uint8_t v___y_4675_; lean_object* v___y_4679_; lean_object* v___y_4680_; uint8_t v___y_4681_; lean_object* v___y_4682_; lean_object* v___y_4683_; lean_object* v_a_4684_; lean_object* v___y_4697_; lean_object* v___y_4698_; lean_object* v___y_4699_; lean_object* v___y_4700_; uint8_t v___y_4701_; uint8_t v___y_4702_; lean_object* v___y_4703_; lean_object* v___y_4704_; uint8_t v_a_4705_; uint8_t v___y_4714_; uint8_t v_a_4762_; 
lean_del_object(v___x_3418_);
lean_inc(v_snd_3421_);
lean_inc(v_fst_3420_);
v___f_3542_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3542_, 0, v_fst_3420_);
lean_closure_set(v___f_3542_, 1, v_snd_3421_);
v___x_3543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
if (v_hasTrace_3538_ == 0)
{
v_a_4762_ = v_hasTrace_3538_;
goto v___jp_4761_;
}
else
{
lean_object* v___x_4787_; lean_object* v___x_4788_; uint8_t v___x_4789_; 
v___x_4787_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_3380_);
v___x_4788_ = l_Lean_Name_append(v___x_4787_, v_trace_3380_);
v___x_4789_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3537_, v_options_3536_, v___x_4788_);
lean_dec(v___x_4788_);
if (v___x_4789_ == 0)
{
v_a_4762_ = v___x_4789_;
goto v___jp_4761_;
}
else
{
lean_del_object(v___x_3423_);
v___y_4714_ = v___x_4789_;
goto v___jp_4713_;
}
}
v___jp_3544_:
{
lean_object* v___x_3550_; double v___x_3551_; double v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3550_ = lean_io_get_num_heartbeats();
v___x_3551_ = lean_float_of_nat(v___y_3548_);
v___x_3552_ = lean_float_of_nat(v___x_3550_);
v___x_3553_ = lean_box_float(v___x_3551_);
v___x_3554_ = lean_box_float(v___x_3552_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 1, v___x_3554_);
lean_ctor_set(v___x_3423_, 0, v___x_3553_);
v___x_3556_ = v___x_3423_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3557_, 0, v_a_3549_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3380_, v___x_3540_, v___x_3543_, v_options_3536_, v___y_3546_, v___y_3547_, v___y_3545_, v___x_3557_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_3558_;
}
}
v___jp_3560_:
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v_a_3565_);
v___y_3545_ = v___y_3562_;
v___y_3546_ = v___y_3561_;
v___y_3547_ = v___y_3564_;
v___y_3548_ = v___y_3563_;
v_a_3549_ = v___x_3566_;
goto v___jp_3544_;
}
v___jp_3567_:
{
lean_object* v___x_3573_; 
v___x_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3573_, 0, v_a_3572_);
v___y_3545_ = v___y_3569_;
v___y_3546_ = v___y_3568_;
v___y_3547_ = v___y_3571_;
v___y_3548_ = v___y_3570_;
v_a_3549_ = v___x_3573_;
goto v___jp_3544_;
}
v___jp_3574_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3582_ = l_List_appendTR___redArg(v___y_3575_, v___y_3578_);
v___x_3583_ = l_List_appendTR___redArg(v___x_3582_, v_a_3581_);
v___y_3568_ = v___y_3577_;
v___y_3569_ = v___y_3576_;
v___y_3570_ = v___y_3580_;
v___y_3571_ = v___y_3579_;
v_a_3572_ = v___x_3583_;
goto v___jp_3567_;
}
v___jp_3584_:
{
if (lean_obj_tag(v___y_3591_) == 0)
{
lean_object* v_a_3592_; 
v_a_3592_ = lean_ctor_get(v___y_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref_known(v___y_3591_, 1);
v___y_3575_ = v___y_3585_;
v___y_3576_ = v___y_3587_;
v___y_3577_ = v___y_3586_;
v___y_3578_ = v___y_3588_;
v___y_3579_ = v___y_3590_;
v___y_3580_ = v___y_3589_;
v_a_3581_ = v_a_3592_;
goto v___jp_3574_;
}
else
{
lean_object* v_a_3593_; 
lean_dec(v___y_3588_);
lean_dec(v___y_3585_);
v_a_3593_ = lean_ctor_get(v___y_3591_, 0);
lean_inc(v_a_3593_);
lean_dec_ref_known(v___y_3591_, 1);
v___y_3561_ = v___y_3586_;
v___y_3562_ = v___y_3587_;
v___y_3563_ = v___y_3589_;
v___y_3564_ = v___y_3590_;
v_a_3565_ = v_a_3593_;
goto v___jp_3560_;
}
}
v___jp_3594_:
{
if (v___y_3603_ == 0)
{
lean_object* v___x_3604_; 
lean_dec_ref(v___y_3595_);
v___x_3604_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3602_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_3602_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_dec_ref_known(v___x_3604_, 1);
v___y_3575_ = v___y_3596_;
v___y_3576_ = v___y_3598_;
v___y_3577_ = v___y_3597_;
v___y_3578_ = v___y_3599_;
v___y_3579_ = v___y_3601_;
v___y_3580_ = v___y_3600_;
v_a_3581_ = v_snd_3421_;
goto v___jp_3574_;
}
else
{
lean_object* v_a_3605_; 
lean_dec(v___y_3599_);
lean_dec(v___y_3596_);
lean_dec(v_snd_3421_);
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref_known(v___x_3604_, 1);
v___y_3561_ = v___y_3597_;
v___y_3562_ = v___y_3598_;
v___y_3563_ = v___y_3600_;
v___y_3564_ = v___y_3601_;
v_a_3565_ = v_a_3605_;
goto v___jp_3560_;
}
}
else
{
lean_dec_ref(v___y_3602_);
lean_dec(v_snd_3421_);
v___y_3585_ = v___y_3596_;
v___y_3586_ = v___y_3597_;
v___y_3587_ = v___y_3598_;
v___y_3588_ = v___y_3599_;
v___y_3589_ = v___y_3600_;
v___y_3590_ = v___y_3601_;
v___y_3591_ = v___y_3595_;
goto v___jp_3584_;
}
}
v___jp_3606_:
{
if (lean_obj_tag(v___y_3611_) == 0)
{
lean_object* v_a_3612_; 
v_a_3612_ = lean_ctor_get(v___y_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___y_3611_, 1);
v___y_3568_ = v___y_3608_;
v___y_3569_ = v___y_3607_;
v___y_3570_ = v___y_3610_;
v___y_3571_ = v___y_3609_;
v_a_3572_ = v_a_3612_;
goto v___jp_3567_;
}
else
{
lean_object* v_a_3613_; 
v_a_3613_ = lean_ctor_get(v___y_3611_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___y_3611_, 1);
v___y_3561_ = v___y_3608_;
v___y_3562_ = v___y_3607_;
v___y_3563_ = v___y_3610_;
v___y_3564_ = v___y_3609_;
v_a_3565_ = v_a_3613_;
goto v___jp_3560_;
}
}
v___jp_3614_:
{
uint8_t v___x_3622_; uint8_t v___x_3623_; 
v___x_3622_ = l_List_isEmpty___redArg(v___y_3619_);
lean_dec(v___y_3619_);
v___x_3623_ = lean_bool_not(v___x_3622_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; 
lean_inc(v_trace_3380_);
v___x_3624_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_3618_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3626_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
v___x_3626_ = l_List_appendTR___redArg(v___y_3615_, v_a_3625_);
v___y_3568_ = v___y_3617_;
v___y_3569_ = v___y_3616_;
v___y_3570_ = v___y_3621_;
v___y_3571_ = v___y_3620_;
v_a_3572_ = v___x_3626_;
goto v___jp_3567_;
}
else
{
lean_dec(v___y_3615_);
v___y_3607_ = v___y_3616_;
v___y_3608_ = v___y_3617_;
v___y_3609_ = v___y_3620_;
v___y_3610_ = v___y_3621_;
v___y_3611_ = v___x_3624_;
goto v___jp_3606_;
}
}
else
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
lean_dec(v___y_3618_);
lean_dec(v___y_3615_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_3627_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3628_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3627_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_3607_ = v___y_3616_;
v___y_3608_ = v___y_3617_;
v___y_3609_ = v___y_3620_;
v___y_3610_ = v___y_3621_;
v___y_3611_ = v___x_3628_;
goto v___jp_3606_;
}
}
v___jp_3629_:
{
uint8_t v_commitIndependentGoals_3637_; lean_object* v___x_3638_; 
v_commitIndependentGoals_3637_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_3630_);
v___x_3638_ = l_List_appendTR___redArg(v_a_3636_, v___y_3630_);
if (v_commitIndependentGoals_3637_ == 0)
{
v___y_3615_ = v___y_3630_;
v___y_3616_ = v___y_3632_;
v___y_3617_ = v___y_3631_;
v___y_3618_ = v___x_3638_;
v___y_3619_ = v___y_3633_;
v___y_3620_ = v___y_3635_;
v___y_3621_ = v___y_3634_;
goto v___jp_3614_;
}
else
{
uint8_t v___x_3639_; uint8_t v___x_3640_; 
v___x_3639_ = l_List_isEmpty___redArg(v___y_3630_);
v___x_3640_ = lean_bool_not(v___x_3639_);
if (v___x_3640_ == 0)
{
v___y_3615_ = v___y_3630_;
v___y_3616_ = v___y_3632_;
v___y_3617_ = v___y_3631_;
v___y_3618_ = v___x_3638_;
v___y_3619_ = v___y_3633_;
v___y_3620_ = v___y_3635_;
v___y_3621_ = v___y_3634_;
goto v___jp_3614_;
}
else
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3643_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___x_3641_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_3643_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_3638_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_dec(v_a_3642_);
lean_dec(v_snd_3421_);
v___y_3585_ = v___y_3630_;
v___y_3586_ = v___y_3631_;
v___y_3587_ = v___y_3632_;
v___y_3588_ = v___y_3633_;
v___y_3589_ = v___y_3634_;
v___y_3590_ = v___y_3635_;
v___y_3591_ = v___x_3643_;
goto v___jp_3584_;
}
else
{
lean_object* v_a_3644_; uint8_t v___x_3645_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
v___x_3645_ = l_Lean_Exception_isInterrupt(v_a_3644_);
if (v___x_3645_ == 0)
{
uint8_t v___x_3646_; 
v___x_3646_ = l_Lean_Exception_isRuntime(v_a_3644_);
v___y_3595_ = v___x_3643_;
v___y_3596_ = v___y_3630_;
v___y_3597_ = v___y_3631_;
v___y_3598_ = v___y_3632_;
v___y_3599_ = v___y_3633_;
v___y_3600_ = v___y_3634_;
v___y_3601_ = v___y_3635_;
v___y_3602_ = v_a_3642_;
v___y_3603_ = v___x_3646_;
goto v___jp_3594_;
}
else
{
lean_dec(v_a_3644_);
v___y_3595_ = v___x_3643_;
v___y_3596_ = v___y_3630_;
v___y_3597_ = v___y_3631_;
v___y_3598_ = v___y_3632_;
v___y_3599_ = v___y_3633_;
v___y_3600_ = v___y_3634_;
v___y_3601_ = v___y_3635_;
v___y_3602_ = v_a_3642_;
v___y_3603_ = v___x_3645_;
goto v___jp_3594_;
}
}
}
else
{
lean_object* v_a_3647_; 
lean_dec(v___x_3638_);
lean_dec(v___y_3633_);
lean_dec(v___y_3630_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_3647_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3647_);
lean_dec_ref_known(v___x_3641_, 1);
v___y_3561_ = v___y_3631_;
v___y_3562_ = v___y_3632_;
v___y_3563_ = v___y_3634_;
v___y_3564_ = v___y_3635_;
v_a_3565_ = v_a_3647_;
goto v___jp_3560_;
}
}
}
}
v___jp_3648_:
{
lean_object* v___x_3654_; double v___x_3655_; double v___x_3656_; double v___x_3657_; double v___x_3658_; double v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3654_ = lean_io_mono_nanos_now();
v___x_3655_ = lean_float_of_nat(v___y_3649_);
v___x_3656_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3657_ = lean_float_div(v___x_3655_, v___x_3656_);
v___x_3658_ = lean_float_of_nat(v___x_3654_);
v___x_3659_ = lean_float_div(v___x_3658_, v___x_3656_);
v___x_3660_ = lean_box_float(v___x_3657_);
v___x_3661_ = lean_box_float(v___x_3659_);
v___x_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3663_, 0, v_a_3653_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3380_, v___x_3540_, v___x_3543_, v_options_3536_, v___y_3651_, v___y_3652_, v___y_3650_, v___x_3663_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_3664_;
}
v___jp_3665_:
{
lean_object* v___x_3671_; 
v___x_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3671_, 0, v_a_3670_);
v___y_3649_ = v___y_3666_;
v___y_3650_ = v___y_3668_;
v___y_3651_ = v___y_3667_;
v___y_3652_ = v___y_3669_;
v_a_3653_ = v___x_3671_;
goto v___jp_3648_;
}
v___jp_3672_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = l_List_appendTR___redArg(v___y_3674_, v___y_3677_);
v___x_3681_ = l_List_appendTR___redArg(v___x_3680_, v_a_3679_);
v___y_3666_ = v___y_3673_;
v___y_3667_ = v___y_3676_;
v___y_3668_ = v___y_3675_;
v___y_3669_ = v___y_3678_;
v_a_3670_ = v___x_3681_;
goto v___jp_3665_;
}
v___jp_3682_:
{
lean_object* v___x_3688_; 
v___x_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3688_, 0, v_a_3687_);
v___y_3649_ = v___y_3683_;
v___y_3650_ = v___y_3685_;
v___y_3651_ = v___y_3684_;
v___y_3652_ = v___y_3686_;
v_a_3653_ = v___x_3688_;
goto v___jp_3648_;
}
v___jp_3689_:
{
if (lean_obj_tag(v___y_3694_) == 0)
{
lean_object* v_a_3695_; 
v_a_3695_ = lean_ctor_get(v___y_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___y_3694_, 1);
v___y_3666_ = v___y_3690_;
v___y_3667_ = v___y_3692_;
v___y_3668_ = v___y_3691_;
v___y_3669_ = v___y_3693_;
v_a_3670_ = v_a_3695_;
goto v___jp_3665_;
}
else
{
lean_object* v_a_3696_; 
v_a_3696_ = lean_ctor_get(v___y_3694_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___y_3694_, 1);
v___y_3683_ = v___y_3690_;
v___y_3684_ = v___y_3692_;
v___y_3685_ = v___y_3691_;
v___y_3686_ = v___y_3693_;
v_a_3687_ = v_a_3696_;
goto v___jp_3682_;
}
}
v___jp_3697_:
{
uint8_t v___x_3705_; uint8_t v___x_3706_; 
v___x_3705_ = l_List_isEmpty___redArg(v___y_3703_);
lean_dec(v___y_3703_);
v___x_3706_ = lean_bool_not(v___x_3705_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; 
lean_inc(v_trace_3380_);
v___x_3707_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_3699_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; lean_object* v___x_3709_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3707_, 1);
v___x_3709_ = l_List_appendTR___redArg(v___y_3700_, v_a_3708_);
v___y_3666_ = v___y_3698_;
v___y_3667_ = v___y_3702_;
v___y_3668_ = v___y_3701_;
v___y_3669_ = v___y_3704_;
v_a_3670_ = v___x_3709_;
goto v___jp_3665_;
}
else
{
lean_dec(v___y_3700_);
v___y_3690_ = v___y_3698_;
v___y_3691_ = v___y_3701_;
v___y_3692_ = v___y_3702_;
v___y_3693_ = v___y_3704_;
v___y_3694_ = v___x_3707_;
goto v___jp_3689_;
}
}
else
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
lean_dec(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_3710_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3711_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3710_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_3690_ = v___y_3698_;
v___y_3691_ = v___y_3701_;
v___y_3692_ = v___y_3702_;
v___y_3693_ = v___y_3704_;
v___y_3694_ = v___x_3711_;
goto v___jp_3689_;
}
}
v___jp_3712_:
{
if (lean_obj_tag(v___y_3719_) == 0)
{
lean_object* v_a_3720_; 
v_a_3720_ = lean_ctor_get(v___y_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref_known(v___y_3719_, 1);
v___y_3673_ = v___y_3713_;
v___y_3674_ = v___y_3714_;
v___y_3675_ = v___y_3716_;
v___y_3676_ = v___y_3715_;
v___y_3677_ = v___y_3717_;
v___y_3678_ = v___y_3718_;
v_a_3679_ = v_a_3720_;
goto v___jp_3672_;
}
else
{
lean_object* v_a_3721_; 
lean_dec(v___y_3717_);
lean_dec(v___y_3714_);
v_a_3721_ = lean_ctor_get(v___y_3719_, 0);
lean_inc(v_a_3721_);
lean_dec_ref_known(v___y_3719_, 1);
v___y_3683_ = v___y_3713_;
v___y_3684_ = v___y_3715_;
v___y_3685_ = v___y_3716_;
v___y_3686_ = v___y_3718_;
v_a_3687_ = v_a_3721_;
goto v___jp_3682_;
}
}
v___jp_3722_:
{
if (v___y_3731_ == 0)
{
lean_object* v___x_3732_; 
lean_dec_ref(v___y_3727_);
v___x_3732_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3730_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_3730_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_dec_ref_known(v___x_3732_, 1);
v___y_3673_ = v___y_3723_;
v___y_3674_ = v___y_3724_;
v___y_3675_ = v___y_3726_;
v___y_3676_ = v___y_3725_;
v___y_3677_ = v___y_3728_;
v___y_3678_ = v___y_3729_;
v_a_3679_ = v_snd_3421_;
goto v___jp_3672_;
}
else
{
lean_object* v_a_3733_; 
lean_dec(v___y_3728_);
lean_dec(v___y_3724_);
lean_dec(v_snd_3421_);
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v___x_3732_, 1);
v___y_3683_ = v___y_3723_;
v___y_3684_ = v___y_3725_;
v___y_3685_ = v___y_3726_;
v___y_3686_ = v___y_3729_;
v_a_3687_ = v_a_3733_;
goto v___jp_3682_;
}
}
else
{
lean_dec_ref(v___y_3730_);
lean_dec(v_snd_3421_);
v___y_3713_ = v___y_3723_;
v___y_3714_ = v___y_3724_;
v___y_3715_ = v___y_3725_;
v___y_3716_ = v___y_3726_;
v___y_3717_ = v___y_3728_;
v___y_3718_ = v___y_3729_;
v___y_3719_ = v___y_3727_;
goto v___jp_3712_;
}
}
v___jp_3734_:
{
uint8_t v_commitIndependentGoals_3742_; lean_object* v___x_3743_; 
v_commitIndependentGoals_3742_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_3736_);
v___x_3743_ = l_List_appendTR___redArg(v_a_3741_, v___y_3736_);
if (v_commitIndependentGoals_3742_ == 0)
{
v___y_3698_ = v___y_3735_;
v___y_3699_ = v___x_3743_;
v___y_3700_ = v___y_3736_;
v___y_3701_ = v___y_3738_;
v___y_3702_ = v___y_3737_;
v___y_3703_ = v___y_3739_;
v___y_3704_ = v___y_3740_;
goto v___jp_3697_;
}
else
{
uint8_t v___x_3744_; uint8_t v___x_3745_; 
v___x_3744_ = l_List_isEmpty___redArg(v___y_3736_);
v___x_3745_ = lean_bool_not(v___x_3744_);
if (v___x_3745_ == 0)
{
v___y_3698_ = v___y_3735_;
v___y_3699_ = v___x_3743_;
v___y_3700_ = v___y_3736_;
v___y_3701_ = v___y_3738_;
v___y_3702_ = v___y_3737_;
v___y_3703_ = v___y_3739_;
v___y_3704_ = v___y_3740_;
goto v___jp_3697_;
}
else
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3748_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3746_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_3748_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_3743_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_dec(v_a_3747_);
lean_dec(v_snd_3421_);
v___y_3713_ = v___y_3735_;
v___y_3714_ = v___y_3736_;
v___y_3715_ = v___y_3737_;
v___y_3716_ = v___y_3738_;
v___y_3717_ = v___y_3739_;
v___y_3718_ = v___y_3740_;
v___y_3719_ = v___x_3748_;
goto v___jp_3712_;
}
else
{
lean_object* v_a_3749_; uint8_t v___x_3750_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
v___x_3750_ = l_Lean_Exception_isInterrupt(v_a_3749_);
if (v___x_3750_ == 0)
{
uint8_t v___x_3751_; 
v___x_3751_ = l_Lean_Exception_isRuntime(v_a_3749_);
v___y_3723_ = v___y_3735_;
v___y_3724_ = v___y_3736_;
v___y_3725_ = v___y_3737_;
v___y_3726_ = v___y_3738_;
v___y_3727_ = v___x_3748_;
v___y_3728_ = v___y_3739_;
v___y_3729_ = v___y_3740_;
v___y_3730_ = v_a_3747_;
v___y_3731_ = v___x_3751_;
goto v___jp_3722_;
}
else
{
lean_dec(v_a_3749_);
v___y_3723_ = v___y_3735_;
v___y_3724_ = v___y_3736_;
v___y_3725_ = v___y_3737_;
v___y_3726_ = v___y_3738_;
v___y_3727_ = v___x_3748_;
v___y_3728_ = v___y_3739_;
v___y_3729_ = v___y_3740_;
v___y_3730_ = v_a_3747_;
v___y_3731_ = v___x_3750_;
goto v___jp_3722_;
}
}
}
else
{
lean_object* v_a_3752_; 
lean_dec(v___x_3743_);
lean_dec(v___y_3739_);
lean_dec(v___y_3736_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_3752_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3752_);
lean_dec_ref_known(v___x_3746_, 1);
v___y_3683_ = v___y_3735_;
v___y_3684_ = v___y_3737_;
v___y_3685_ = v___y_3738_;
v___y_3686_ = v___y_3740_;
v_a_3687_ = v_a_3752_;
goto v___jp_3682_;
}
}
}
}
v___jp_3753_:
{
lean_object* v___x_3759_; 
v___x_3759_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3388_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v___x_3761_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3762_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3536_, v___x_3761_);
if (v___x_3762_ == 0)
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
lean_del_object(v___x_3423_);
v___x_3763_ = lean_io_mono_nanos_now();
v___x_3764_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___y_3758_, v_a_3386_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3766_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
v___x_3766_ = l_List_reverse___redArg(v_a_3765_);
v___y_3735_ = v___x_3763_;
v___y_3736_ = v___y_3754_;
v___y_3737_ = v___y_3755_;
v___y_3738_ = v___y_3756_;
v___y_3739_ = v___y_3757_;
v___y_3740_ = v_a_3760_;
v_a_3741_ = v___x_3766_;
goto v___jp_3734_;
}
else
{
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3767_; 
v_a_3767_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3764_, 1);
v___y_3735_ = v___x_3763_;
v___y_3736_ = v___y_3754_;
v___y_3737_ = v___y_3755_;
v___y_3738_ = v___y_3756_;
v___y_3739_ = v___y_3757_;
v___y_3740_ = v_a_3760_;
v_a_3741_ = v_a_3767_;
goto v___jp_3734_;
}
else
{
lean_object* v_a_3768_; 
lean_dec(v___y_3757_);
lean_dec(v___y_3754_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_3768_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___x_3764_, 1);
v___y_3683_ = v___x_3763_;
v___y_3684_ = v___y_3755_;
v___y_3685_ = v___y_3756_;
v___y_3686_ = v_a_3760_;
v_a_3687_ = v_a_3768_;
goto v___jp_3682_;
}
}
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = lean_io_get_num_heartbeats();
v___x_3770_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___y_3758_, v_a_3386_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3772_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref_known(v___x_3770_, 1);
v___x_3772_ = l_List_reverse___redArg(v_a_3771_);
v___y_3630_ = v___y_3754_;
v___y_3631_ = v___y_3755_;
v___y_3632_ = v___y_3756_;
v___y_3633_ = v___y_3757_;
v___y_3634_ = v___x_3769_;
v___y_3635_ = v_a_3760_;
v_a_3636_ = v___x_3772_;
goto v___jp_3629_;
}
else
{
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3773_; 
v_a_3773_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3773_);
lean_dec_ref_known(v___x_3770_, 1);
v___y_3630_ = v___y_3754_;
v___y_3631_ = v___y_3755_;
v___y_3632_ = v___y_3756_;
v___y_3633_ = v___y_3757_;
v___y_3634_ = v___x_3769_;
v___y_3635_ = v_a_3760_;
v_a_3636_ = v_a_3773_;
goto v___jp_3629_;
}
else
{
lean_object* v_a_3774_; 
lean_dec(v___y_3757_);
lean_dec(v___y_3754_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_3774_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___x_3770_, 1);
v___y_3561_ = v___y_3755_;
v___y_3562_ = v___y_3756_;
v___y_3563_ = v___x_3769_;
v___y_3564_ = v_a_3760_;
v_a_3565_ = v_a_3774_;
goto v___jp_3560_;
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3754_);
lean_del_object(v___x_3423_);
lean_dec(v_snd_3421_);
lean_dec(v_goals_3383_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v_a_3775_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3759_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3759_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
v___jp_3783_:
{
if (v___y_3784_ == 0)
{
lean_object* v___x_3790_; 
lean_dec_ref(v___y_3786_);
lean_del_object(v___x_3423_);
v___x_3790_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___y_3788_, v_a_3386_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; lean_object* v___x_3792_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___x_3790_, 1);
v___x_3792_ = l_List_reverse___redArg(v_a_3791_);
v___y_3459_ = v___y_3785_;
v___y_3460_ = v___y_3787_;
v_a_3461_ = v___x_3792_;
goto v___jp_3458_;
}
else
{
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3793_; 
v_a_3793_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3790_, 1);
v___y_3459_ = v___y_3785_;
v___y_3460_ = v___y_3787_;
v_a_3461_ = v_a_3793_;
goto v___jp_3458_;
}
else
{
lean_dec(v___y_3787_);
lean_dec(v___y_3785_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
return v___x_3790_;
}
}
}
else
{
v___y_3754_ = v___y_3785_;
v___y_3755_ = v_a_3789_;
v___y_3756_ = v___y_3786_;
v___y_3757_ = v___y_3787_;
v___y_3758_ = v___y_3788_;
goto v___jp_3753_;
}
}
v___jp_3794_:
{
lean_object* v___x_3799_; double v___x_3800_; double v___x_3801_; double v___x_3802_; double v___x_3803_; double v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3799_ = lean_io_mono_nanos_now();
v___x_3800_ = lean_float_of_nat(v___y_3796_);
v___x_3801_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3802_ = lean_float_div(v___x_3800_, v___x_3801_);
v___x_3803_ = lean_float_of_nat(v___x_3799_);
v___x_3804_ = lean_float_div(v___x_3803_, v___x_3801_);
v___x_3805_ = lean_box_float(v___x_3802_);
v___x_3806_ = lean_box_float(v___x_3804_);
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3805_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3808_, 0, v_a_3798_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3380_, v___x_3540_, v___x_3543_, v_options_3536_, v___y_3795_, v___y_3797_, v___f_3542_, v___x_3808_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_3809_;
}
v___jp_3810_:
{
lean_object* v___x_3815_; 
v___x_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3815_, 0, v_a_3814_);
v___y_3795_ = v___y_3811_;
v___y_3796_ = v___y_3812_;
v___y_3797_ = v___y_3813_;
v_a_3798_ = v___x_3815_;
goto v___jp_3794_;
}
v___jp_3816_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = l_List_appendTR___redArg(v___y_3820_, v___y_3817_);
v___x_3824_ = l_List_appendTR___redArg(v___x_3823_, v_a_3822_);
v___y_3811_ = v___y_3818_;
v___y_3812_ = v___y_3819_;
v___y_3813_ = v___y_3821_;
v_a_3814_ = v___x_3824_;
goto v___jp_3810_;
}
v___jp_3825_:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3832_ = l_List_appendTR___redArg(v___y_3829_, v___y_3826_);
v___x_3833_ = l_List_appendTR___redArg(v___x_3832_, v_a_3831_);
v___y_3811_ = v___y_3827_;
v___y_3812_ = v___y_3828_;
v___y_3813_ = v___y_3830_;
v_a_3814_ = v___x_3833_;
goto v___jp_3810_;
}
v___jp_3834_:
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3839_, 0, v_a_3838_);
v___y_3795_ = v___y_3835_;
v___y_3796_ = v___y_3836_;
v___y_3797_ = v___y_3837_;
v_a_3798_ = v___x_3839_;
goto v___jp_3794_;
}
v___jp_3840_:
{
if (lean_obj_tag(v___y_3846_) == 0)
{
lean_object* v_a_3847_; 
v_a_3847_ = lean_ctor_get(v___y_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v___y_3846_, 1);
v___y_3817_ = v___y_3841_;
v___y_3818_ = v___y_3842_;
v___y_3819_ = v___y_3843_;
v___y_3820_ = v___y_3844_;
v___y_3821_ = v___y_3845_;
v_a_3822_ = v_a_3847_;
goto v___jp_3816_;
}
else
{
lean_object* v_a_3848_; 
lean_dec(v___y_3844_);
lean_dec(v___y_3841_);
v_a_3848_ = lean_ctor_get(v___y_3846_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___y_3846_, 1);
v___y_3835_ = v___y_3842_;
v___y_3836_ = v___y_3843_;
v___y_3837_ = v___y_3845_;
v_a_3838_ = v_a_3848_;
goto v___jp_3834_;
}
}
v___jp_3849_:
{
if (v___y_3857_ == 0)
{
lean_object* v___x_3858_; 
lean_dec_ref(v___y_3852_);
v___x_3858_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3851_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_3851_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_dec_ref_known(v___x_3858_, 1);
v___y_3817_ = v___y_3850_;
v___y_3818_ = v___y_3853_;
v___y_3819_ = v___y_3854_;
v___y_3820_ = v___y_3855_;
v___y_3821_ = v___y_3856_;
v_a_3822_ = v_snd_3421_;
goto v___jp_3816_;
}
else
{
lean_object* v_a_3859_; 
lean_dec(v___y_3855_);
lean_dec(v___y_3850_);
lean_dec(v_snd_3421_);
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref_known(v___x_3858_, 1);
v___y_3835_ = v___y_3853_;
v___y_3836_ = v___y_3854_;
v___y_3837_ = v___y_3856_;
v_a_3838_ = v_a_3859_;
goto v___jp_3834_;
}
}
else
{
lean_dec_ref(v___y_3851_);
lean_dec(v_snd_3421_);
v___y_3841_ = v___y_3850_;
v___y_3842_ = v___y_3853_;
v___y_3843_ = v___y_3854_;
v___y_3844_ = v___y_3855_;
v___y_3845_ = v___y_3856_;
v___y_3846_ = v___y_3852_;
goto v___jp_3840_;
}
}
v___jp_3860_:
{
if (lean_obj_tag(v___y_3866_) == 0)
{
lean_object* v_a_3867_; 
v_a_3867_ = lean_ctor_get(v___y_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___y_3866_, 1);
v___y_3826_ = v___y_3861_;
v___y_3827_ = v___y_3862_;
v___y_3828_ = v___y_3863_;
v___y_3829_ = v___y_3864_;
v___y_3830_ = v___y_3865_;
v_a_3831_ = v_a_3867_;
goto v___jp_3825_;
}
else
{
lean_object* v_a_3868_; 
lean_dec(v___y_3864_);
lean_dec(v___y_3861_);
v_a_3868_ = lean_ctor_get(v___y_3866_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___y_3866_, 1);
v___y_3835_ = v___y_3862_;
v___y_3836_ = v___y_3863_;
v___y_3837_ = v___y_3865_;
v_a_3838_ = v_a_3868_;
goto v___jp_3834_;
}
}
v___jp_3869_:
{
if (v___y_3877_ == 0)
{
lean_object* v___x_3878_; 
lean_dec_ref(v___y_3872_);
v___x_3878_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3871_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_3871_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_dec_ref_known(v___x_3878_, 1);
v___y_3826_ = v___y_3870_;
v___y_3827_ = v___y_3873_;
v___y_3828_ = v___y_3874_;
v___y_3829_ = v___y_3875_;
v___y_3830_ = v___y_3876_;
v_a_3831_ = v_snd_3421_;
goto v___jp_3825_;
}
else
{
lean_object* v_a_3879_; 
lean_dec(v___y_3875_);
lean_dec(v___y_3870_);
lean_dec(v_snd_3421_);
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
v___y_3835_ = v___y_3873_;
v___y_3836_ = v___y_3874_;
v___y_3837_ = v___y_3876_;
v_a_3838_ = v_a_3879_;
goto v___jp_3834_;
}
}
else
{
lean_dec_ref(v___y_3871_);
lean_dec(v_snd_3421_);
v___y_3861_ = v___y_3870_;
v___y_3862_ = v___y_3873_;
v___y_3863_ = v___y_3874_;
v___y_3864_ = v___y_3875_;
v___y_3865_ = v___y_3876_;
v___y_3866_ = v___y_3872_;
goto v___jp_3860_;
}
}
v___jp_3880_:
{
if (lean_obj_tag(v___y_3884_) == 0)
{
lean_object* v_a_3885_; 
v_a_3885_ = lean_ctor_get(v___y_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___y_3884_, 1);
v___y_3811_ = v___y_3881_;
v___y_3812_ = v___y_3882_;
v___y_3813_ = v___y_3883_;
v_a_3814_ = v_a_3885_;
goto v___jp_3810_;
}
else
{
lean_object* v_a_3886_; 
v_a_3886_ = lean_ctor_get(v___y_3884_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___y_3884_, 1);
v___y_3835_ = v___y_3881_;
v___y_3836_ = v___y_3882_;
v___y_3837_ = v___y_3883_;
v_a_3838_ = v_a_3886_;
goto v___jp_3834_;
}
}
v___jp_3887_:
{
lean_object* v___x_3896_; double v___x_3897_; double v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3896_ = lean_io_get_num_heartbeats();
v___x_3897_ = lean_float_of_nat(v___y_3888_);
v___x_3898_ = lean_float_of_nat(v___x_3896_);
v___x_3899_ = lean_box_float(v___x_3897_);
v___x_3900_ = lean_box_float(v___x_3898_);
v___x_3901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3899_);
lean_ctor_set(v___x_3901_, 1, v___x_3900_);
v___x_3902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3902_, 0, v_a_3895_);
lean_ctor_set(v___x_3902_, 1, v___x_3901_);
lean_inc(v_trace_3380_);
v___x_3903_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3380_, v___x_3540_, v___x_3543_, v_options_3536_, v___y_3891_, v___y_3889_, v___y_3894_, v___x_3902_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_3881_ = v___y_3890_;
v___y_3882_ = v___y_3892_;
v___y_3883_ = v___y_3893_;
v___y_3884_ = v___x_3903_;
goto v___jp_3880_;
}
v___jp_3904_:
{
lean_object* v___x_3913_; 
v___x_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3913_, 0, v_a_3912_);
v___y_3888_ = v___y_3905_;
v___y_3889_ = v___y_3906_;
v___y_3890_ = v___y_3908_;
v___y_3891_ = v___y_3907_;
v___y_3892_ = v___y_3909_;
v___y_3893_ = v___y_3910_;
v___y_3894_ = v___y_3911_;
v_a_3895_ = v___x_3913_;
goto v___jp_3887_;
}
v___jp_3914_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = l_List_appendTR___redArg(v___y_3921_, v___y_3915_);
v___x_3926_ = l_List_appendTR___redArg(v___x_3925_, v_a_3924_);
v___y_3905_ = v___y_3916_;
v___y_3906_ = v___y_3917_;
v___y_3907_ = v___y_3919_;
v___y_3908_ = v___y_3918_;
v___y_3909_ = v___y_3920_;
v___y_3910_ = v___y_3922_;
v___y_3911_ = v___y_3923_;
v_a_3912_ = v___x_3926_;
goto v___jp_3904_;
}
v___jp_3927_:
{
lean_object* v___x_3936_; 
v___x_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3936_, 0, v_a_3935_);
v___y_3888_ = v___y_3928_;
v___y_3889_ = v___y_3929_;
v___y_3890_ = v___y_3931_;
v___y_3891_ = v___y_3930_;
v___y_3892_ = v___y_3932_;
v___y_3893_ = v___y_3933_;
v___y_3894_ = v___y_3934_;
v_a_3895_ = v___x_3936_;
goto v___jp_3887_;
}
v___jp_3937_:
{
if (lean_obj_tag(v___y_3945_) == 0)
{
lean_object* v_a_3946_; 
v_a_3946_ = lean_ctor_get(v___y_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___y_3945_, 1);
v___y_3905_ = v___y_3938_;
v___y_3906_ = v___y_3939_;
v___y_3907_ = v___y_3941_;
v___y_3908_ = v___y_3940_;
v___y_3909_ = v___y_3942_;
v___y_3910_ = v___y_3943_;
v___y_3911_ = v___y_3944_;
v_a_3912_ = v_a_3946_;
goto v___jp_3904_;
}
else
{
lean_object* v_a_3947_; 
v_a_3947_ = lean_ctor_get(v___y_3945_, 0);
lean_inc(v_a_3947_);
lean_dec_ref_known(v___y_3945_, 1);
v___y_3928_ = v___y_3938_;
v___y_3929_ = v___y_3939_;
v___y_3930_ = v___y_3941_;
v___y_3931_ = v___y_3940_;
v___y_3932_ = v___y_3942_;
v___y_3933_ = v___y_3943_;
v___y_3934_ = v___y_3944_;
v_a_3935_ = v_a_3947_;
goto v___jp_3927_;
}
}
v___jp_3948_:
{
uint8_t v___x_3959_; uint8_t v___x_3960_; 
v___x_3959_ = l_List_isEmpty___redArg(v___y_3949_);
lean_dec(v___y_3949_);
v___x_3960_ = lean_bool_not(v___x_3959_);
if (v___x_3960_ == 0)
{
lean_object* v___x_3961_; 
lean_inc(v_trace_3380_);
v___x_3961_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_3955_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v___x_3963_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3961_, 1);
v___x_3963_ = l_List_appendTR___redArg(v___y_3956_, v_a_3962_);
v___y_3905_ = v___y_3950_;
v___y_3906_ = v___y_3951_;
v___y_3907_ = v___y_3953_;
v___y_3908_ = v___y_3952_;
v___y_3909_ = v___y_3954_;
v___y_3910_ = v___y_3957_;
v___y_3911_ = v___y_3958_;
v_a_3912_ = v___x_3963_;
goto v___jp_3904_;
}
else
{
lean_dec(v___y_3956_);
v___y_3938_ = v___y_3950_;
v___y_3939_ = v___y_3951_;
v___y_3940_ = v___y_3952_;
v___y_3941_ = v___y_3953_;
v___y_3942_ = v___y_3954_;
v___y_3943_ = v___y_3957_;
v___y_3944_ = v___y_3958_;
v___y_3945_ = v___x_3961_;
goto v___jp_3937_;
}
}
else
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
lean_dec(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_3964_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3965_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3964_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_3938_ = v___y_3950_;
v___y_3939_ = v___y_3951_;
v___y_3940_ = v___y_3952_;
v___y_3941_ = v___y_3953_;
v___y_3942_ = v___y_3954_;
v___y_3943_ = v___y_3957_;
v___y_3944_ = v___y_3958_;
v___y_3945_ = v___x_3965_;
goto v___jp_3937_;
}
}
v___jp_3966_:
{
if (lean_obj_tag(v___y_3976_) == 0)
{
lean_object* v_a_3977_; 
v_a_3977_ = lean_ctor_get(v___y_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___y_3976_, 1);
v___y_3915_ = v___y_3967_;
v___y_3916_ = v___y_3968_;
v___y_3917_ = v___y_3969_;
v___y_3918_ = v___y_3971_;
v___y_3919_ = v___y_3970_;
v___y_3920_ = v___y_3972_;
v___y_3921_ = v___y_3973_;
v___y_3922_ = v___y_3974_;
v___y_3923_ = v___y_3975_;
v_a_3924_ = v_a_3977_;
goto v___jp_3914_;
}
else
{
lean_object* v_a_3978_; 
lean_dec(v___y_3973_);
lean_dec(v___y_3967_);
v_a_3978_ = lean_ctor_get(v___y_3976_, 0);
lean_inc(v_a_3978_);
lean_dec_ref_known(v___y_3976_, 1);
v___y_3928_ = v___y_3968_;
v___y_3929_ = v___y_3969_;
v___y_3930_ = v___y_3970_;
v___y_3931_ = v___y_3971_;
v___y_3932_ = v___y_3972_;
v___y_3933_ = v___y_3974_;
v___y_3934_ = v___y_3975_;
v_a_3935_ = v_a_3978_;
goto v___jp_3927_;
}
}
v___jp_3979_:
{
if (v___y_3991_ == 0)
{
lean_object* v___x_3992_; 
lean_dec_ref(v___y_3980_);
v___x_3992_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3983_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_3983_);
if (lean_obj_tag(v___x_3992_) == 0)
{
lean_dec_ref_known(v___x_3992_, 1);
v___y_3915_ = v___y_3981_;
v___y_3916_ = v___y_3982_;
v___y_3917_ = v___y_3984_;
v___y_3918_ = v___y_3986_;
v___y_3919_ = v___y_3985_;
v___y_3920_ = v___y_3987_;
v___y_3921_ = v___y_3988_;
v___y_3922_ = v___y_3989_;
v___y_3923_ = v___y_3990_;
v_a_3924_ = v_snd_3421_;
goto v___jp_3914_;
}
else
{
lean_object* v_a_3993_; 
lean_dec(v___y_3988_);
lean_dec(v___y_3981_);
lean_dec(v_snd_3421_);
v_a_3993_ = lean_ctor_get(v___x_3992_, 0);
lean_inc(v_a_3993_);
lean_dec_ref_known(v___x_3992_, 1);
v___y_3928_ = v___y_3982_;
v___y_3929_ = v___y_3984_;
v___y_3930_ = v___y_3985_;
v___y_3931_ = v___y_3986_;
v___y_3932_ = v___y_3987_;
v___y_3933_ = v___y_3989_;
v___y_3934_ = v___y_3990_;
v_a_3935_ = v_a_3993_;
goto v___jp_3927_;
}
}
else
{
lean_dec_ref(v___y_3983_);
lean_dec(v_snd_3421_);
v___y_3967_ = v___y_3981_;
v___y_3968_ = v___y_3982_;
v___y_3969_ = v___y_3984_;
v___y_3970_ = v___y_3985_;
v___y_3971_ = v___y_3986_;
v___y_3972_ = v___y_3987_;
v___y_3973_ = v___y_3988_;
v___y_3974_ = v___y_3989_;
v___y_3975_ = v___y_3990_;
v___y_3976_ = v___y_3980_;
goto v___jp_3966_;
}
}
v___jp_3994_:
{
uint8_t v_commitIndependentGoals_4005_; lean_object* v___x_4006_; 
v_commitIndependentGoals_4005_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_4001_);
v___x_4006_ = l_List_appendTR___redArg(v_a_4004_, v___y_4001_);
if (v_commitIndependentGoals_4005_ == 0)
{
v___y_3949_ = v___y_3995_;
v___y_3950_ = v___y_3996_;
v___y_3951_ = v___y_3997_;
v___y_3952_ = v___y_3999_;
v___y_3953_ = v___y_3998_;
v___y_3954_ = v___y_4000_;
v___y_3955_ = v___x_4006_;
v___y_3956_ = v___y_4001_;
v___y_3957_ = v___y_4002_;
v___y_3958_ = v___y_4003_;
goto v___jp_3948_;
}
else
{
uint8_t v___x_4007_; uint8_t v___x_4008_; 
v___x_4007_ = l_List_isEmpty___redArg(v___y_4001_);
v___x_4008_ = lean_bool_not(v___x_4007_);
if (v___x_4008_ == 0)
{
v___y_3949_ = v___y_3995_;
v___y_3950_ = v___y_3996_;
v___y_3951_ = v___y_3997_;
v___y_3952_ = v___y_3999_;
v___y_3953_ = v___y_3998_;
v___y_3954_ = v___y_4000_;
v___y_3955_ = v___x_4006_;
v___y_3956_ = v___y_4001_;
v___y_3957_ = v___y_4002_;
v___y_3958_ = v___y_4003_;
goto v___jp_3948_;
}
else
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v___x_4011_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4009_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_4011_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_4006_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_dec(v_a_4010_);
lean_dec(v_snd_3421_);
v___y_3967_ = v___y_3995_;
v___y_3968_ = v___y_3996_;
v___y_3969_ = v___y_3997_;
v___y_3970_ = v___y_3998_;
v___y_3971_ = v___y_3999_;
v___y_3972_ = v___y_4000_;
v___y_3973_ = v___y_4001_;
v___y_3974_ = v___y_4002_;
v___y_3975_ = v___y_4003_;
v___y_3976_ = v___x_4011_;
goto v___jp_3966_;
}
else
{
lean_object* v_a_4012_; uint8_t v___x_4013_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
v___x_4013_ = l_Lean_Exception_isInterrupt(v_a_4012_);
if (v___x_4013_ == 0)
{
uint8_t v___x_4014_; 
v___x_4014_ = l_Lean_Exception_isRuntime(v_a_4012_);
v___y_3980_ = v___x_4011_;
v___y_3981_ = v___y_3995_;
v___y_3982_ = v___y_3996_;
v___y_3983_ = v_a_4010_;
v___y_3984_ = v___y_3997_;
v___y_3985_ = v___y_3998_;
v___y_3986_ = v___y_3999_;
v___y_3987_ = v___y_4000_;
v___y_3988_ = v___y_4001_;
v___y_3989_ = v___y_4002_;
v___y_3990_ = v___y_4003_;
v___y_3991_ = v___x_4014_;
goto v___jp_3979_;
}
else
{
lean_dec(v_a_4012_);
v___y_3980_ = v___x_4011_;
v___y_3981_ = v___y_3995_;
v___y_3982_ = v___y_3996_;
v___y_3983_ = v_a_4010_;
v___y_3984_ = v___y_3997_;
v___y_3985_ = v___y_3998_;
v___y_3986_ = v___y_3999_;
v___y_3987_ = v___y_4000_;
v___y_3988_ = v___y_4001_;
v___y_3989_ = v___y_4002_;
v___y_3990_ = v___y_4003_;
v___y_3991_ = v___x_4013_;
goto v___jp_3979_;
}
}
}
else
{
lean_object* v_a_4015_; 
lean_dec(v___x_4006_);
lean_dec(v___y_4001_);
lean_dec(v___y_3995_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4015_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4015_);
lean_dec_ref_known(v___x_4009_, 1);
v___y_3928_ = v___y_3996_;
v___y_3929_ = v___y_3997_;
v___y_3930_ = v___y_3998_;
v___y_3931_ = v___y_3999_;
v___y_3932_ = v___y_4000_;
v___y_3933_ = v___y_4002_;
v___y_3934_ = v___y_4003_;
v_a_3935_ = v_a_4015_;
goto v___jp_3927_;
}
}
}
}
v___jp_4016_:
{
lean_object* v___x_4025_; double v___x_4026_; double v___x_4027_; double v___x_4028_; double v___x_4029_; double v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4025_ = lean_io_mono_nanos_now();
v___x_4026_ = lean_float_of_nat(v___y_4017_);
v___x_4027_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_4028_ = lean_float_div(v___x_4026_, v___x_4027_);
v___x_4029_ = lean_float_of_nat(v___x_4025_);
v___x_4030_ = lean_float_div(v___x_4029_, v___x_4027_);
v___x_4031_ = lean_box_float(v___x_4028_);
v___x_4032_ = lean_box_float(v___x_4030_);
v___x_4033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4031_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
v___x_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4034_, 0, v_a_4024_);
lean_ctor_set(v___x_4034_, 1, v___x_4033_);
lean_inc(v_trace_3380_);
v___x_4035_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3380_, v___x_3540_, v___x_3543_, v_options_3536_, v___y_4020_, v___y_4018_, v___y_4023_, v___x_4034_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_3881_ = v___y_4019_;
v___y_3882_ = v___y_4021_;
v___y_3883_ = v___y_4022_;
v___y_3884_ = v___x_4035_;
goto v___jp_3880_;
}
v___jp_4036_:
{
lean_object* v___x_4045_; 
v___x_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4045_, 0, v_a_4044_);
v___y_4017_ = v___y_4037_;
v___y_4018_ = v___y_4038_;
v___y_4019_ = v___y_4040_;
v___y_4020_ = v___y_4039_;
v___y_4021_ = v___y_4041_;
v___y_4022_ = v___y_4042_;
v___y_4023_ = v___y_4043_;
v_a_4024_ = v___x_4045_;
goto v___jp_4016_;
}
v___jp_4046_:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = l_List_appendTR___redArg(v___y_4053_, v___y_4048_);
v___x_4058_ = l_List_appendTR___redArg(v___x_4057_, v_a_4056_);
v___y_4037_ = v___y_4047_;
v___y_4038_ = v___y_4049_;
v___y_4039_ = v___y_4051_;
v___y_4040_ = v___y_4050_;
v___y_4041_ = v___y_4052_;
v___y_4042_ = v___y_4054_;
v___y_4043_ = v___y_4055_;
v_a_4044_ = v___x_4058_;
goto v___jp_4036_;
}
v___jp_4059_:
{
lean_object* v___x_4068_; 
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v_a_4067_);
v___y_4017_ = v___y_4060_;
v___y_4018_ = v___y_4061_;
v___y_4019_ = v___y_4063_;
v___y_4020_ = v___y_4062_;
v___y_4021_ = v___y_4064_;
v___y_4022_ = v___y_4065_;
v___y_4023_ = v___y_4066_;
v_a_4024_ = v___x_4068_;
goto v___jp_4016_;
}
v___jp_4069_:
{
if (lean_obj_tag(v___y_4077_) == 0)
{
lean_object* v_a_4078_; 
v_a_4078_ = lean_ctor_get(v___y_4077_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___y_4077_, 1);
v___y_4037_ = v___y_4070_;
v___y_4038_ = v___y_4071_;
v___y_4039_ = v___y_4073_;
v___y_4040_ = v___y_4072_;
v___y_4041_ = v___y_4074_;
v___y_4042_ = v___y_4075_;
v___y_4043_ = v___y_4076_;
v_a_4044_ = v_a_4078_;
goto v___jp_4036_;
}
else
{
lean_object* v_a_4079_; 
v_a_4079_ = lean_ctor_get(v___y_4077_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v___y_4077_, 1);
v___y_4060_ = v___y_4070_;
v___y_4061_ = v___y_4071_;
v___y_4062_ = v___y_4073_;
v___y_4063_ = v___y_4072_;
v___y_4064_ = v___y_4074_;
v___y_4065_ = v___y_4075_;
v___y_4066_ = v___y_4076_;
v_a_4067_ = v_a_4079_;
goto v___jp_4059_;
}
}
v___jp_4080_:
{
uint8_t v___x_4091_; uint8_t v___x_4092_; 
v___x_4091_ = l_List_isEmpty___redArg(v___y_4083_);
lean_dec(v___y_4083_);
v___x_4092_ = lean_bool_not(v___x_4091_);
if (v___x_4092_ == 0)
{
lean_object* v___x_4093_; 
lean_inc(v_trace_3380_);
v___x_4093_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_4081_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4095_; 
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_a_4094_);
lean_dec_ref_known(v___x_4093_, 1);
v___x_4095_ = l_List_appendTR___redArg(v___y_4088_, v_a_4094_);
v___y_4037_ = v___y_4082_;
v___y_4038_ = v___y_4084_;
v___y_4039_ = v___y_4086_;
v___y_4040_ = v___y_4085_;
v___y_4041_ = v___y_4087_;
v___y_4042_ = v___y_4089_;
v___y_4043_ = v___y_4090_;
v_a_4044_ = v___x_4095_;
goto v___jp_4036_;
}
else
{
lean_dec(v___y_4088_);
v___y_4070_ = v___y_4082_;
v___y_4071_ = v___y_4084_;
v___y_4072_ = v___y_4085_;
v___y_4073_ = v___y_4086_;
v___y_4074_ = v___y_4087_;
v___y_4075_ = v___y_4089_;
v___y_4076_ = v___y_4090_;
v___y_4077_ = v___x_4093_;
goto v___jp_4069_;
}
}
else
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
lean_dec(v___y_4088_);
lean_dec(v___y_4081_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_4096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4097_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4096_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_4070_ = v___y_4082_;
v___y_4071_ = v___y_4084_;
v___y_4072_ = v___y_4085_;
v___y_4073_ = v___y_4086_;
v___y_4074_ = v___y_4087_;
v___y_4075_ = v___y_4089_;
v___y_4076_ = v___y_4090_;
v___y_4077_ = v___x_4097_;
goto v___jp_4069_;
}
}
v___jp_4098_:
{
if (lean_obj_tag(v___y_4108_) == 0)
{
lean_object* v_a_4109_; 
v_a_4109_ = lean_ctor_get(v___y_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref_known(v___y_4108_, 1);
v___y_4047_ = v___y_4099_;
v___y_4048_ = v___y_4100_;
v___y_4049_ = v___y_4101_;
v___y_4050_ = v___y_4103_;
v___y_4051_ = v___y_4102_;
v___y_4052_ = v___y_4104_;
v___y_4053_ = v___y_4105_;
v___y_4054_ = v___y_4106_;
v___y_4055_ = v___y_4107_;
v_a_4056_ = v_a_4109_;
goto v___jp_4046_;
}
else
{
lean_object* v_a_4110_; 
lean_dec(v___y_4105_);
lean_dec(v___y_4100_);
v_a_4110_ = lean_ctor_get(v___y_4108_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___y_4108_, 1);
v___y_4060_ = v___y_4099_;
v___y_4061_ = v___y_4101_;
v___y_4062_ = v___y_4102_;
v___y_4063_ = v___y_4103_;
v___y_4064_ = v___y_4104_;
v___y_4065_ = v___y_4106_;
v___y_4066_ = v___y_4107_;
v_a_4067_ = v_a_4110_;
goto v___jp_4059_;
}
}
v___jp_4111_:
{
if (v___y_4123_ == 0)
{
lean_object* v___x_4124_; 
lean_dec_ref(v___y_4114_);
v___x_4124_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4119_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_4119_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_dec_ref_known(v___x_4124_, 1);
v___y_4047_ = v___y_4112_;
v___y_4048_ = v___y_4113_;
v___y_4049_ = v___y_4115_;
v___y_4050_ = v___y_4117_;
v___y_4051_ = v___y_4116_;
v___y_4052_ = v___y_4118_;
v___y_4053_ = v___y_4120_;
v___y_4054_ = v___y_4121_;
v___y_4055_ = v___y_4122_;
v_a_4056_ = v_snd_3421_;
goto v___jp_4046_;
}
else
{
lean_object* v_a_4125_; 
lean_dec(v___y_4120_);
lean_dec(v___y_4113_);
lean_dec(v_snd_3421_);
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
lean_dec_ref_known(v___x_4124_, 1);
v___y_4060_ = v___y_4112_;
v___y_4061_ = v___y_4115_;
v___y_4062_ = v___y_4116_;
v___y_4063_ = v___y_4117_;
v___y_4064_ = v___y_4118_;
v___y_4065_ = v___y_4121_;
v___y_4066_ = v___y_4122_;
v_a_4067_ = v_a_4125_;
goto v___jp_4059_;
}
}
else
{
lean_dec_ref(v___y_4119_);
lean_dec(v_snd_3421_);
v___y_4099_ = v___y_4112_;
v___y_4100_ = v___y_4113_;
v___y_4101_ = v___y_4115_;
v___y_4102_ = v___y_4116_;
v___y_4103_ = v___y_4117_;
v___y_4104_ = v___y_4118_;
v___y_4105_ = v___y_4120_;
v___y_4106_ = v___y_4121_;
v___y_4107_ = v___y_4122_;
v___y_4108_ = v___y_4114_;
goto v___jp_4098_;
}
}
v___jp_4126_:
{
uint8_t v_commitIndependentGoals_4137_; lean_object* v___x_4138_; 
v_commitIndependentGoals_4137_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_4133_);
v___x_4138_ = l_List_appendTR___redArg(v_a_4136_, v___y_4133_);
if (v_commitIndependentGoals_4137_ == 0)
{
v___y_4081_ = v___x_4138_;
v___y_4082_ = v___y_4127_;
v___y_4083_ = v___y_4128_;
v___y_4084_ = v___y_4129_;
v___y_4085_ = v___y_4131_;
v___y_4086_ = v___y_4130_;
v___y_4087_ = v___y_4132_;
v___y_4088_ = v___y_4133_;
v___y_4089_ = v___y_4134_;
v___y_4090_ = v___y_4135_;
goto v___jp_4080_;
}
else
{
uint8_t v___x_4139_; uint8_t v___x_4140_; 
v___x_4139_ = l_List_isEmpty___redArg(v___y_4133_);
v___x_4140_ = lean_bool_not(v___x_4139_);
if (v___x_4140_ == 0)
{
v___y_4081_ = v___x_4138_;
v___y_4082_ = v___y_4127_;
v___y_4083_ = v___y_4128_;
v___y_4084_ = v___y_4129_;
v___y_4085_ = v___y_4131_;
v___y_4086_ = v___y_4130_;
v___y_4087_ = v___y_4132_;
v___y_4088_ = v___y_4133_;
v___y_4089_ = v___y_4134_;
v___y_4090_ = v___y_4135_;
goto v___jp_4080_;
}
else
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4143_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_4143_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_4138_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_dec(v_a_4142_);
lean_dec(v_snd_3421_);
v___y_4099_ = v___y_4127_;
v___y_4100_ = v___y_4128_;
v___y_4101_ = v___y_4129_;
v___y_4102_ = v___y_4130_;
v___y_4103_ = v___y_4131_;
v___y_4104_ = v___y_4132_;
v___y_4105_ = v___y_4133_;
v___y_4106_ = v___y_4134_;
v___y_4107_ = v___y_4135_;
v___y_4108_ = v___x_4143_;
goto v___jp_4098_;
}
else
{
lean_object* v_a_4144_; uint8_t v___x_4145_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
v___x_4145_ = l_Lean_Exception_isInterrupt(v_a_4144_);
if (v___x_4145_ == 0)
{
uint8_t v___x_4146_; 
v___x_4146_ = l_Lean_Exception_isRuntime(v_a_4144_);
v___y_4112_ = v___y_4127_;
v___y_4113_ = v___y_4128_;
v___y_4114_ = v___x_4143_;
v___y_4115_ = v___y_4129_;
v___y_4116_ = v___y_4130_;
v___y_4117_ = v___y_4131_;
v___y_4118_ = v___y_4132_;
v___y_4119_ = v_a_4142_;
v___y_4120_ = v___y_4133_;
v___y_4121_ = v___y_4134_;
v___y_4122_ = v___y_4135_;
v___y_4123_ = v___x_4146_;
goto v___jp_4111_;
}
else
{
lean_dec(v_a_4144_);
v___y_4112_ = v___y_4127_;
v___y_4113_ = v___y_4128_;
v___y_4114_ = v___x_4143_;
v___y_4115_ = v___y_4129_;
v___y_4116_ = v___y_4130_;
v___y_4117_ = v___y_4131_;
v___y_4118_ = v___y_4132_;
v___y_4119_ = v_a_4142_;
v___y_4120_ = v___y_4133_;
v___y_4121_ = v___y_4134_;
v___y_4122_ = v___y_4135_;
v___y_4123_ = v___x_4145_;
goto v___jp_4111_;
}
}
}
else
{
lean_object* v_a_4147_; 
lean_dec(v___x_4138_);
lean_dec(v___y_4133_);
lean_dec(v___y_4128_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4147_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4141_, 1);
v___y_4060_ = v___y_4127_;
v___y_4061_ = v___y_4129_;
v___y_4062_ = v___y_4130_;
v___y_4063_ = v___y_4131_;
v___y_4064_ = v___y_4132_;
v___y_4065_ = v___y_4134_;
v___y_4066_ = v___y_4135_;
v_a_4067_ = v_a_4147_;
goto v___jp_4059_;
}
}
}
}
v___jp_4148_:
{
lean_object* v___x_4158_; 
v___x_4158_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3388_);
if (lean_obj_tag(v___x_4158_) == 0)
{
if (v___y_4151_ == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref_known(v___x_4158_, 1);
v___x_4160_ = lean_io_mono_nanos_now();
v___x_4161_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___y_4150_, v_a_3386_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4163_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v___x_4161_, 1);
v___x_4163_ = l_List_reverse___redArg(v_a_4162_);
v___y_4127_ = v___x_4160_;
v___y_4128_ = v___y_4149_;
v___y_4129_ = v_a_4159_;
v___y_4130_ = v___y_4152_;
v___y_4131_ = v___y_4153_;
v___y_4132_ = v___y_4154_;
v___y_4133_ = v___y_4155_;
v___y_4134_ = v___y_4156_;
v___y_4135_ = v___y_4157_;
v_a_4136_ = v___x_4163_;
goto v___jp_4126_;
}
else
{
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4164_; 
v_a_4164_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4161_, 1);
v___y_4127_ = v___x_4160_;
v___y_4128_ = v___y_4149_;
v___y_4129_ = v_a_4159_;
v___y_4130_ = v___y_4152_;
v___y_4131_ = v___y_4153_;
v___y_4132_ = v___y_4154_;
v___y_4133_ = v___y_4155_;
v___y_4134_ = v___y_4156_;
v___y_4135_ = v___y_4157_;
v_a_4136_ = v_a_4164_;
goto v___jp_4126_;
}
else
{
lean_object* v_a_4165_; 
lean_dec(v___y_4155_);
lean_dec(v___y_4149_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4165_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4161_, 1);
v___y_4060_ = v___x_4160_;
v___y_4061_ = v_a_4159_;
v___y_4062_ = v___y_4152_;
v___y_4063_ = v___y_4153_;
v___y_4064_ = v___y_4154_;
v___y_4065_ = v___y_4156_;
v___y_4066_ = v___y_4157_;
v_a_4067_ = v_a_4165_;
goto v___jp_4059_;
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v_a_4166_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4158_, 1);
v___x_4167_ = lean_io_get_num_heartbeats();
v___x_4168_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___y_4150_, v_a_3386_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4170_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v___x_4168_, 1);
v___x_4170_ = l_List_reverse___redArg(v_a_4169_);
v___y_3995_ = v___y_4149_;
v___y_3996_ = v___x_4167_;
v___y_3997_ = v_a_4166_;
v___y_3998_ = v___y_4152_;
v___y_3999_ = v___y_4153_;
v___y_4000_ = v___y_4154_;
v___y_4001_ = v___y_4155_;
v___y_4002_ = v___y_4156_;
v___y_4003_ = v___y_4157_;
v_a_4004_ = v___x_4170_;
goto v___jp_3994_;
}
else
{
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4171_; 
v_a_4171_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v___x_4168_, 1);
v___y_3995_ = v___y_4149_;
v___y_3996_ = v___x_4167_;
v___y_3997_ = v_a_4166_;
v___y_3998_ = v___y_4152_;
v___y_3999_ = v___y_4153_;
v___y_4000_ = v___y_4154_;
v___y_4001_ = v___y_4155_;
v___y_4002_ = v___y_4156_;
v___y_4003_ = v___y_4157_;
v_a_4004_ = v_a_4171_;
goto v___jp_3994_;
}
else
{
lean_object* v_a_4172_; 
lean_dec(v___y_4155_);
lean_dec(v___y_4149_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4172_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___x_4168_, 1);
v___y_3928_ = v___x_4167_;
v___y_3929_ = v_a_4166_;
v___y_3930_ = v___y_4152_;
v___y_3931_ = v___y_4153_;
v___y_3932_ = v___y_4154_;
v___y_3933_ = v___y_4156_;
v___y_3934_ = v___y_4157_;
v_a_3935_ = v_a_4172_;
goto v___jp_3927_;
}
}
}
}
else
{
lean_object* v_a_4173_; 
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4155_);
lean_dec(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec(v_snd_3421_);
lean_dec(v_goals_3383_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4173_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4158_, 1);
v___y_3835_ = v___y_4153_;
v___y_3836_ = v___y_4154_;
v___y_3837_ = v___y_4156_;
v_a_3838_ = v_a_4173_;
goto v___jp_3834_;
}
}
v___jp_4174_:
{
uint8_t v___x_4181_; uint8_t v___x_4182_; 
v___x_4181_ = l_List_isEmpty___redArg(v___y_4175_);
lean_dec(v___y_4175_);
v___x_4182_ = lean_bool_not(v___x_4181_);
if (v___x_4182_ == 0)
{
lean_object* v___x_4183_; 
lean_inc(v_trace_3380_);
v___x_4183_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_4179_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4185_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v___x_4185_ = l_List_appendTR___redArg(v___y_4178_, v_a_4184_);
v___y_3811_ = v___y_4176_;
v___y_3812_ = v___y_4177_;
v___y_3813_ = v___y_4180_;
v_a_3814_ = v___x_4185_;
goto v___jp_3810_;
}
else
{
lean_dec(v___y_4178_);
v___y_3881_ = v___y_4176_;
v___y_3882_ = v___y_4177_;
v___y_3883_ = v___y_4180_;
v___y_3884_ = v___x_4183_;
goto v___jp_3880_;
}
}
else
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
lean_dec(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_4186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4187_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4186_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_3881_ = v___y_4176_;
v___y_3882_ = v___y_4177_;
v___y_3883_ = v___y_4180_;
v___y_3884_ = v___x_4187_;
goto v___jp_3880_;
}
}
v___jp_4188_:
{
uint8_t v_commitIndependentGoals_4195_; lean_object* v___x_4196_; 
v_commitIndependentGoals_4195_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_4192_);
v___x_4196_ = l_List_appendTR___redArg(v_a_4194_, v___y_4192_);
if (v_commitIndependentGoals_4195_ == 0)
{
v___y_4175_ = v___y_4189_;
v___y_4176_ = v___y_4190_;
v___y_4177_ = v___y_4191_;
v___y_4178_ = v___y_4192_;
v___y_4179_ = v___x_4196_;
v___y_4180_ = v___y_4193_;
goto v___jp_4174_;
}
else
{
uint8_t v___x_4197_; uint8_t v___x_4198_; 
v___x_4197_ = l_List_isEmpty___redArg(v___y_4192_);
v___x_4198_ = lean_bool_not(v___x_4197_);
if (v___x_4198_ == 0)
{
v___y_4175_ = v___y_4189_;
v___y_4176_ = v___y_4190_;
v___y_4177_ = v___y_4191_;
v___y_4178_ = v___y_4192_;
v___y_4179_ = v___x_4196_;
v___y_4180_ = v___y_4193_;
goto v___jp_4174_;
}
else
{
lean_object* v___x_4199_; 
v___x_4199_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4201_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4199_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_4201_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_4196_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_dec(v_a_4200_);
lean_dec(v_snd_3421_);
v___y_3841_ = v___y_4189_;
v___y_3842_ = v___y_4190_;
v___y_3843_ = v___y_4191_;
v___y_3844_ = v___y_4192_;
v___y_3845_ = v___y_4193_;
v___y_3846_ = v___x_4201_;
goto v___jp_3840_;
}
else
{
lean_object* v_a_4202_; uint8_t v___x_4203_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
v___x_4203_ = l_Lean_Exception_isInterrupt(v_a_4202_);
if (v___x_4203_ == 0)
{
uint8_t v___x_4204_; 
v___x_4204_ = l_Lean_Exception_isRuntime(v_a_4202_);
v___y_3850_ = v___y_4189_;
v___y_3851_ = v_a_4200_;
v___y_3852_ = v___x_4201_;
v___y_3853_ = v___y_4190_;
v___y_3854_ = v___y_4191_;
v___y_3855_ = v___y_4192_;
v___y_3856_ = v___y_4193_;
v___y_3857_ = v___x_4204_;
goto v___jp_3849_;
}
else
{
lean_dec(v_a_4202_);
v___y_3850_ = v___y_4189_;
v___y_3851_ = v_a_4200_;
v___y_3852_ = v___x_4201_;
v___y_3853_ = v___y_4190_;
v___y_3854_ = v___y_4191_;
v___y_3855_ = v___y_4192_;
v___y_3856_ = v___y_4193_;
v___y_3857_ = v___x_4203_;
goto v___jp_3849_;
}
}
}
else
{
lean_object* v_a_4205_; 
lean_dec(v___x_4196_);
lean_dec(v___y_4192_);
lean_dec(v___y_4189_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4205_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4205_);
lean_dec_ref_known(v___x_4199_, 1);
v___y_3835_ = v___y_4190_;
v___y_3836_ = v___y_4191_;
v___y_3837_ = v___y_4193_;
v_a_3838_ = v_a_4205_;
goto v___jp_3834_;
}
}
}
}
v___jp_4206_:
{
lean_object* v___x_4216_; uint8_t v___x_4217_; 
v___x_4216_ = l_Lean_trace_profiler;
v___x_4217_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3536_, v___x_4216_);
if (v___x_4217_ == 0)
{
lean_object* v___x_4218_; 
lean_dec_ref(v___y_4214_);
v___x_4218_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___y_4209_, v_a_3386_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4220_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
lean_inc(v_a_4219_);
lean_dec_ref_known(v___x_4218_, 1);
v___x_4220_ = l_List_reverse___redArg(v_a_4219_);
v___y_4189_ = v___y_4207_;
v___y_4190_ = v___y_4210_;
v___y_4191_ = v___y_4211_;
v___y_4192_ = v___y_4212_;
v___y_4193_ = v___y_4213_;
v_a_4194_ = v___x_4220_;
goto v___jp_4188_;
}
else
{
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4221_; 
v_a_4221_ = lean_ctor_get(v___x_4218_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v___x_4218_, 1);
v___y_4189_ = v___y_4207_;
v___y_4190_ = v___y_4210_;
v___y_4191_ = v___y_4211_;
v___y_4192_ = v___y_4212_;
v___y_4193_ = v___y_4213_;
v_a_4194_ = v_a_4221_;
goto v___jp_4188_;
}
else
{
lean_object* v_a_4222_; 
lean_dec(v___y_4212_);
lean_dec(v___y_4207_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4222_ = lean_ctor_get(v___x_4218_, 0);
lean_inc(v_a_4222_);
lean_dec_ref_known(v___x_4218_, 1);
v___y_3835_ = v___y_4210_;
v___y_3836_ = v___y_4211_;
v___y_3837_ = v___y_4213_;
v_a_3838_ = v_a_4222_;
goto v___jp_3834_;
}
}
}
else
{
v___y_4149_ = v___y_4207_;
v___y_4150_ = v___y_4209_;
v___y_4151_ = v___y_4208_;
v___y_4152_ = v_a_4215_;
v___y_4153_ = v___y_4210_;
v___y_4154_ = v___y_4211_;
v___y_4155_ = v___y_4212_;
v___y_4156_ = v___y_4213_;
v___y_4157_ = v___y_4214_;
goto v___jp_4148_;
}
}
v___jp_4223_:
{
uint8_t v___x_4230_; uint8_t v___x_4231_; 
v___x_4230_ = l_List_isEmpty___redArg(v___y_4224_);
lean_dec(v___y_4224_);
v___x_4231_ = lean_bool_not(v___x_4230_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; 
lean_inc(v_trace_3380_);
v___x_4232_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_4225_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4234_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_a_4233_);
lean_dec_ref_known(v___x_4232_, 1);
v___x_4234_ = l_List_appendTR___redArg(v___y_4228_, v_a_4233_);
v___y_3811_ = v___y_4226_;
v___y_3812_ = v___y_4227_;
v___y_3813_ = v___y_4229_;
v_a_3814_ = v___x_4234_;
goto v___jp_3810_;
}
else
{
lean_dec(v___y_4228_);
v___y_3881_ = v___y_4226_;
v___y_3882_ = v___y_4227_;
v___y_3883_ = v___y_4229_;
v___y_3884_ = v___x_4232_;
goto v___jp_3880_;
}
}
else
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
lean_dec(v___y_4228_);
lean_dec(v___y_4225_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_4235_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4236_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4235_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_3881_ = v___y_4226_;
v___y_3882_ = v___y_4227_;
v___y_3883_ = v___y_4229_;
v___y_3884_ = v___x_4236_;
goto v___jp_3880_;
}
}
v___jp_4237_:
{
uint8_t v_commitIndependentGoals_4244_; lean_object* v___x_4245_; 
v_commitIndependentGoals_4244_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_4241_);
v___x_4245_ = l_List_appendTR___redArg(v_a_4243_, v___y_4241_);
if (v_commitIndependentGoals_4244_ == 0)
{
v___y_4224_ = v___y_4238_;
v___y_4225_ = v___x_4245_;
v___y_4226_ = v___y_4239_;
v___y_4227_ = v___y_4240_;
v___y_4228_ = v___y_4241_;
v___y_4229_ = v___y_4242_;
goto v___jp_4223_;
}
else
{
uint8_t v___x_4246_; uint8_t v___x_4247_; 
v___x_4246_ = l_List_isEmpty___redArg(v___y_4241_);
v___x_4247_ = lean_bool_not(v___x_4246_);
if (v___x_4247_ == 0)
{
v___y_4224_ = v___y_4238_;
v___y_4225_ = v___x_4245_;
v___y_4226_ = v___y_4239_;
v___y_4227_ = v___y_4240_;
v___y_4228_ = v___y_4241_;
v___y_4229_ = v___y_4242_;
goto v___jp_4223_;
}
else
{
lean_object* v___x_4248_; 
v___x_4248_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; lean_object* v___x_4250_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_a_4249_);
lean_dec_ref_known(v___x_4248_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_4250_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_4245_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_dec(v_a_4249_);
lean_dec(v_snd_3421_);
v___y_3861_ = v___y_4238_;
v___y_3862_ = v___y_4239_;
v___y_3863_ = v___y_4240_;
v___y_3864_ = v___y_4241_;
v___y_3865_ = v___y_4242_;
v___y_3866_ = v___x_4250_;
goto v___jp_3860_;
}
else
{
lean_object* v_a_4251_; uint8_t v___x_4252_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
lean_inc(v_a_4251_);
v___x_4252_ = l_Lean_Exception_isInterrupt(v_a_4251_);
if (v___x_4252_ == 0)
{
uint8_t v___x_4253_; 
v___x_4253_ = l_Lean_Exception_isRuntime(v_a_4251_);
v___y_3870_ = v___y_4238_;
v___y_3871_ = v_a_4249_;
v___y_3872_ = v___x_4250_;
v___y_3873_ = v___y_4239_;
v___y_3874_ = v___y_4240_;
v___y_3875_ = v___y_4241_;
v___y_3876_ = v___y_4242_;
v___y_3877_ = v___x_4253_;
goto v___jp_3869_;
}
else
{
lean_dec(v_a_4251_);
v___y_3870_ = v___y_4238_;
v___y_3871_ = v_a_4249_;
v___y_3872_ = v___x_4250_;
v___y_3873_ = v___y_4239_;
v___y_3874_ = v___y_4240_;
v___y_3875_ = v___y_4241_;
v___y_3876_ = v___y_4242_;
v___y_3877_ = v___x_4252_;
goto v___jp_3869_;
}
}
}
else
{
lean_object* v_a_4254_; 
lean_dec(v___x_4245_);
lean_dec(v___y_4241_);
lean_dec(v___y_4238_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4254_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4248_, 1);
v___y_3835_ = v___y_4239_;
v___y_3836_ = v___y_4240_;
v___y_3837_ = v___y_4242_;
v_a_3838_ = v_a_4254_;
goto v___jp_3834_;
}
}
}
}
v___jp_4255_:
{
lean_object* v___x_4260_; double v___x_4261_; double v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4260_ = lean_io_get_num_heartbeats();
v___x_4261_ = lean_float_of_nat(v___y_4256_);
v___x_4262_ = lean_float_of_nat(v___x_4260_);
v___x_4263_ = lean_box_float(v___x_4261_);
v___x_4264_ = lean_box_float(v___x_4262_);
v___x_4265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4263_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
v___x_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4266_, 0, v_a_4259_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3380_, v___x_3540_, v___x_3543_, v_options_3536_, v___y_4257_, v___y_4258_, v___f_3542_, v___x_4266_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_4267_;
}
v___jp_4268_:
{
lean_object* v___x_4273_; 
v___x_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4273_, 0, v_a_4272_);
v___y_4256_ = v___y_4269_;
v___y_4257_ = v___y_4270_;
v___y_4258_ = v___y_4271_;
v_a_4259_ = v___x_4273_;
goto v___jp_4255_;
}
v___jp_4274_:
{
lean_object* v___x_4279_; 
v___x_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4279_, 0, v_a_4278_);
v___y_4256_ = v___y_4275_;
v___y_4257_ = v___y_4276_;
v___y_4258_ = v___y_4277_;
v_a_4259_ = v___x_4279_;
goto v___jp_4255_;
}
v___jp_4280_:
{
if (lean_obj_tag(v___y_4284_) == 0)
{
lean_object* v_a_4285_; 
v_a_4285_ = lean_ctor_get(v___y_4284_, 0);
lean_inc(v_a_4285_);
lean_dec_ref_known(v___y_4284_, 1);
v___y_4275_ = v___y_4281_;
v___y_4276_ = v___y_4282_;
v___y_4277_ = v___y_4283_;
v_a_4278_ = v_a_4285_;
goto v___jp_4274_;
}
else
{
lean_object* v_a_4286_; 
v_a_4286_ = lean_ctor_get(v___y_4284_, 0);
lean_inc(v_a_4286_);
lean_dec_ref_known(v___y_4284_, 1);
v___y_4269_ = v___y_4281_;
v___y_4270_ = v___y_4282_;
v___y_4271_ = v___y_4283_;
v_a_4272_ = v_a_4286_;
goto v___jp_4268_;
}
}
v___jp_4287_:
{
lean_object* v___x_4296_; double v___x_4297_; double v___x_4298_; double v___x_4299_; double v___x_4300_; double v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4296_ = lean_io_mono_nanos_now();
v___x_4297_ = lean_float_of_nat(v___y_4294_);
v___x_4298_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_4299_ = lean_float_div(v___x_4297_, v___x_4298_);
v___x_4300_ = lean_float_of_nat(v___x_4296_);
v___x_4301_ = lean_float_div(v___x_4300_, v___x_4298_);
v___x_4302_ = lean_box_float(v___x_4299_);
v___x_4303_ = lean_box_float(v___x_4301_);
v___x_4304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4302_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
v___x_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4305_, 0, v_a_4295_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
lean_inc(v_trace_3380_);
v___x_4306_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3380_, v___x_3540_, v___x_3543_, v_options_3536_, v___y_4292_, v___y_4291_, v___y_4288_, v___x_4305_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_4281_ = v___y_4289_;
v___y_4282_ = v___y_4290_;
v___y_4283_ = v___y_4293_;
v___y_4284_ = v___x_4306_;
goto v___jp_4280_;
}
v___jp_4307_:
{
lean_object* v___x_4316_; 
v___x_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4316_, 0, v_a_4315_);
v___y_4288_ = v___y_4308_;
v___y_4289_ = v___y_4309_;
v___y_4290_ = v___y_4310_;
v___y_4291_ = v___y_4311_;
v___y_4292_ = v___y_4312_;
v___y_4293_ = v___y_4314_;
v___y_4294_ = v___y_4313_;
v_a_4295_ = v___x_4316_;
goto v___jp_4287_;
}
v___jp_4317_:
{
lean_object* v___x_4326_; 
v___x_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4326_, 0, v_a_4325_);
v___y_4288_ = v___y_4318_;
v___y_4289_ = v___y_4319_;
v___y_4290_ = v___y_4320_;
v___y_4291_ = v___y_4321_;
v___y_4292_ = v___y_4322_;
v___y_4293_ = v___y_4324_;
v___y_4294_ = v___y_4323_;
v_a_4295_ = v___x_4326_;
goto v___jp_4287_;
}
v___jp_4327_:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4338_ = l_List_appendTR___redArg(v___y_4332_, v___y_4330_);
v___x_4339_ = l_List_appendTR___redArg(v___x_4338_, v_a_4337_);
v___y_4318_ = v___y_4328_;
v___y_4319_ = v___y_4329_;
v___y_4320_ = v___y_4331_;
v___y_4321_ = v___y_4333_;
v___y_4322_ = v___y_4334_;
v___y_4323_ = v___y_4336_;
v___y_4324_ = v___y_4335_;
v_a_4325_ = v___x_4339_;
goto v___jp_4317_;
}
v___jp_4340_:
{
if (lean_obj_tag(v___y_4350_) == 0)
{
lean_object* v_a_4351_; 
v_a_4351_ = lean_ctor_get(v___y_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___y_4350_, 1);
v___y_4328_ = v___y_4341_;
v___y_4329_ = v___y_4343_;
v___y_4330_ = v___y_4342_;
v___y_4331_ = v___y_4345_;
v___y_4332_ = v___y_4344_;
v___y_4333_ = v___y_4346_;
v___y_4334_ = v___y_4347_;
v___y_4335_ = v___y_4349_;
v___y_4336_ = v___y_4348_;
v_a_4337_ = v_a_4351_;
goto v___jp_4327_;
}
else
{
lean_object* v_a_4352_; 
lean_dec(v___y_4344_);
lean_dec(v___y_4342_);
v_a_4352_ = lean_ctor_get(v___y_4350_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___y_4350_, 1);
v___y_4308_ = v___y_4341_;
v___y_4309_ = v___y_4343_;
v___y_4310_ = v___y_4345_;
v___y_4311_ = v___y_4346_;
v___y_4312_ = v___y_4347_;
v___y_4313_ = v___y_4348_;
v___y_4314_ = v___y_4349_;
v_a_4315_ = v_a_4352_;
goto v___jp_4307_;
}
}
v___jp_4353_:
{
if (v___y_4365_ == 0)
{
lean_object* v___x_4366_; 
lean_dec_ref(v___y_4364_);
v___x_4366_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4357_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_4357_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_dec_ref_known(v___x_4366_, 1);
v___y_4328_ = v___y_4354_;
v___y_4329_ = v___y_4356_;
v___y_4330_ = v___y_4355_;
v___y_4331_ = v___y_4359_;
v___y_4332_ = v___y_4358_;
v___y_4333_ = v___y_4360_;
v___y_4334_ = v___y_4361_;
v___y_4335_ = v___y_4363_;
v___y_4336_ = v___y_4362_;
v_a_4337_ = v_snd_3421_;
goto v___jp_4327_;
}
else
{
lean_object* v_a_4367_; 
lean_dec(v___y_4358_);
lean_dec(v___y_4355_);
lean_dec(v_snd_3421_);
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
lean_inc(v_a_4367_);
lean_dec_ref_known(v___x_4366_, 1);
v___y_4308_ = v___y_4354_;
v___y_4309_ = v___y_4356_;
v___y_4310_ = v___y_4359_;
v___y_4311_ = v___y_4360_;
v___y_4312_ = v___y_4361_;
v___y_4313_ = v___y_4362_;
v___y_4314_ = v___y_4363_;
v_a_4315_ = v_a_4367_;
goto v___jp_4307_;
}
}
else
{
lean_dec_ref(v___y_4357_);
lean_dec(v_snd_3421_);
v___y_4341_ = v___y_4354_;
v___y_4342_ = v___y_4355_;
v___y_4343_ = v___y_4356_;
v___y_4344_ = v___y_4358_;
v___y_4345_ = v___y_4359_;
v___y_4346_ = v___y_4360_;
v___y_4347_ = v___y_4361_;
v___y_4348_ = v___y_4362_;
v___y_4349_ = v___y_4363_;
v___y_4350_ = v___y_4364_;
goto v___jp_4340_;
}
}
v___jp_4368_:
{
if (lean_obj_tag(v___y_4376_) == 0)
{
lean_object* v_a_4377_; 
v_a_4377_ = lean_ctor_get(v___y_4376_, 0);
lean_inc(v_a_4377_);
lean_dec_ref_known(v___y_4376_, 1);
v___y_4318_ = v___y_4369_;
v___y_4319_ = v___y_4370_;
v___y_4320_ = v___y_4371_;
v___y_4321_ = v___y_4372_;
v___y_4322_ = v___y_4373_;
v___y_4323_ = v___y_4375_;
v___y_4324_ = v___y_4374_;
v_a_4325_ = v_a_4377_;
goto v___jp_4317_;
}
else
{
lean_object* v_a_4378_; 
v_a_4378_ = lean_ctor_get(v___y_4376_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___y_4376_, 1);
v___y_4308_ = v___y_4369_;
v___y_4309_ = v___y_4370_;
v___y_4310_ = v___y_4371_;
v___y_4311_ = v___y_4372_;
v___y_4312_ = v___y_4373_;
v___y_4313_ = v___y_4375_;
v___y_4314_ = v___y_4374_;
v_a_4315_ = v_a_4378_;
goto v___jp_4307_;
}
}
v___jp_4379_:
{
uint8_t v___x_4390_; uint8_t v___x_4391_; 
v___x_4390_ = l_List_isEmpty___redArg(v___y_4382_);
lean_dec(v___y_4382_);
v___x_4391_ = lean_bool_not(v___x_4390_);
if (v___x_4391_ == 0)
{
lean_object* v___x_4392_; 
lean_inc(v_trace_3380_);
v___x_4392_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_4386_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4394_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_a_4393_);
lean_dec_ref_known(v___x_4392_, 1);
v___x_4394_ = l_List_appendTR___redArg(v___y_4384_, v_a_4393_);
v___y_4318_ = v___y_4380_;
v___y_4319_ = v___y_4381_;
v___y_4320_ = v___y_4383_;
v___y_4321_ = v___y_4385_;
v___y_4322_ = v___y_4387_;
v___y_4323_ = v___y_4389_;
v___y_4324_ = v___y_4388_;
v_a_4325_ = v___x_4394_;
goto v___jp_4317_;
}
else
{
lean_dec(v___y_4384_);
v___y_4369_ = v___y_4380_;
v___y_4370_ = v___y_4381_;
v___y_4371_ = v___y_4383_;
v___y_4372_ = v___y_4385_;
v___y_4373_ = v___y_4387_;
v___y_4374_ = v___y_4388_;
v___y_4375_ = v___y_4389_;
v___y_4376_ = v___x_4392_;
goto v___jp_4368_;
}
}
else
{
lean_object* v___x_4395_; lean_object* v___x_4396_; 
lean_dec(v___y_4386_);
lean_dec(v___y_4384_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_4395_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4396_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4395_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_4369_ = v___y_4380_;
v___y_4370_ = v___y_4381_;
v___y_4371_ = v___y_4383_;
v___y_4372_ = v___y_4385_;
v___y_4373_ = v___y_4387_;
v___y_4374_ = v___y_4388_;
v___y_4375_ = v___y_4389_;
v___y_4376_ = v___x_4396_;
goto v___jp_4368_;
}
}
v___jp_4397_:
{
uint8_t v_commitIndependentGoals_4408_; lean_object* v___x_4409_; 
v_commitIndependentGoals_4408_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_4402_);
v___x_4409_ = l_List_appendTR___redArg(v_a_4407_, v___y_4402_);
if (v_commitIndependentGoals_4408_ == 0)
{
v___y_4380_ = v___y_4398_;
v___y_4381_ = v___y_4400_;
v___y_4382_ = v___y_4399_;
v___y_4383_ = v___y_4401_;
v___y_4384_ = v___y_4402_;
v___y_4385_ = v___y_4403_;
v___y_4386_ = v___x_4409_;
v___y_4387_ = v___y_4404_;
v___y_4388_ = v___y_4406_;
v___y_4389_ = v___y_4405_;
goto v___jp_4379_;
}
else
{
uint8_t v___x_4410_; uint8_t v___x_4411_; 
v___x_4410_ = l_List_isEmpty___redArg(v___y_4402_);
v___x_4411_ = lean_bool_not(v___x_4410_);
if (v___x_4411_ == 0)
{
v___y_4380_ = v___y_4398_;
v___y_4381_ = v___y_4400_;
v___y_4382_ = v___y_4399_;
v___y_4383_ = v___y_4401_;
v___y_4384_ = v___y_4402_;
v___y_4385_ = v___y_4403_;
v___y_4386_ = v___x_4409_;
v___y_4387_ = v___y_4404_;
v___y_4388_ = v___y_4406_;
v___y_4389_ = v___y_4405_;
goto v___jp_4379_;
}
else
{
lean_object* v___x_4412_; 
v___x_4412_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4414_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_4414_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_4409_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_dec(v_a_4413_);
lean_dec(v_snd_3421_);
v___y_4341_ = v___y_4398_;
v___y_4342_ = v___y_4399_;
v___y_4343_ = v___y_4400_;
v___y_4344_ = v___y_4402_;
v___y_4345_ = v___y_4401_;
v___y_4346_ = v___y_4403_;
v___y_4347_ = v___y_4404_;
v___y_4348_ = v___y_4405_;
v___y_4349_ = v___y_4406_;
v___y_4350_ = v___x_4414_;
goto v___jp_4340_;
}
else
{
lean_object* v_a_4415_; uint8_t v___x_4416_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_a_4415_);
v___x_4416_ = l_Lean_Exception_isInterrupt(v_a_4415_);
if (v___x_4416_ == 0)
{
uint8_t v___x_4417_; 
v___x_4417_ = l_Lean_Exception_isRuntime(v_a_4415_);
v___y_4354_ = v___y_4398_;
v___y_4355_ = v___y_4399_;
v___y_4356_ = v___y_4400_;
v___y_4357_ = v_a_4413_;
v___y_4358_ = v___y_4402_;
v___y_4359_ = v___y_4401_;
v___y_4360_ = v___y_4403_;
v___y_4361_ = v___y_4404_;
v___y_4362_ = v___y_4405_;
v___y_4363_ = v___y_4406_;
v___y_4364_ = v___x_4414_;
v___y_4365_ = v___x_4417_;
goto v___jp_4353_;
}
else
{
lean_dec(v_a_4415_);
v___y_4354_ = v___y_4398_;
v___y_4355_ = v___y_4399_;
v___y_4356_ = v___y_4400_;
v___y_4357_ = v_a_4413_;
v___y_4358_ = v___y_4402_;
v___y_4359_ = v___y_4401_;
v___y_4360_ = v___y_4403_;
v___y_4361_ = v___y_4404_;
v___y_4362_ = v___y_4405_;
v___y_4363_ = v___y_4406_;
v___y_4364_ = v___x_4414_;
v___y_4365_ = v___x_4416_;
goto v___jp_4353_;
}
}
}
else
{
lean_object* v_a_4418_; 
lean_dec(v___x_4409_);
lean_dec(v___y_4402_);
lean_dec(v___y_4399_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4418_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4412_, 1);
v___y_4308_ = v___y_4398_;
v___y_4309_ = v___y_4400_;
v___y_4310_ = v___y_4401_;
v___y_4311_ = v___y_4403_;
v___y_4312_ = v___y_4404_;
v___y_4313_ = v___y_4405_;
v___y_4314_ = v___y_4406_;
v_a_4315_ = v_a_4418_;
goto v___jp_4307_;
}
}
}
}
v___jp_4419_:
{
lean_object* v___x_4428_; double v___x_4429_; double v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4428_ = lean_io_get_num_heartbeats();
v___x_4429_ = lean_float_of_nat(v___y_4425_);
v___x_4430_ = lean_float_of_nat(v___x_4428_);
v___x_4431_ = lean_box_float(v___x_4429_);
v___x_4432_ = lean_box_float(v___x_4430_);
v___x_4433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4431_);
lean_ctor_set(v___x_4433_, 1, v___x_4432_);
v___x_4434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4434_, 0, v_a_4427_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
lean_inc(v_trace_3380_);
v___x_4435_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3380_, v___x_3540_, v___x_3543_, v_options_3536_, v___y_4424_, v___y_4423_, v___y_4420_, v___x_4434_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_4281_ = v___y_4421_;
v___y_4282_ = v___y_4422_;
v___y_4283_ = v___y_4426_;
v___y_4284_ = v___x_4435_;
goto v___jp_4280_;
}
v___jp_4436_:
{
lean_object* v___x_4445_; 
v___x_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4445_, 0, v_a_4444_);
v___y_4420_ = v___y_4437_;
v___y_4421_ = v___y_4438_;
v___y_4422_ = v___y_4439_;
v___y_4423_ = v___y_4440_;
v___y_4424_ = v___y_4442_;
v___y_4425_ = v___y_4441_;
v___y_4426_ = v___y_4443_;
v_a_4427_ = v___x_4445_;
goto v___jp_4419_;
}
v___jp_4446_:
{
lean_object* v___x_4455_; 
v___x_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4455_, 0, v_a_4454_);
v___y_4420_ = v___y_4447_;
v___y_4421_ = v___y_4448_;
v___y_4422_ = v___y_4449_;
v___y_4423_ = v___y_4450_;
v___y_4424_ = v___y_4452_;
v___y_4425_ = v___y_4451_;
v___y_4426_ = v___y_4453_;
v_a_4427_ = v___x_4455_;
goto v___jp_4419_;
}
v___jp_4456_:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = l_List_appendTR___redArg(v___y_4461_, v___y_4459_);
v___x_4468_ = l_List_appendTR___redArg(v___x_4467_, v_a_4466_);
v___y_4447_ = v___y_4457_;
v___y_4448_ = v___y_4458_;
v___y_4449_ = v___y_4460_;
v___y_4450_ = v___y_4462_;
v___y_4451_ = v___y_4464_;
v___y_4452_ = v___y_4463_;
v___y_4453_ = v___y_4465_;
v_a_4454_ = v___x_4468_;
goto v___jp_4446_;
}
v___jp_4469_:
{
if (lean_obj_tag(v___y_4479_) == 0)
{
lean_object* v_a_4480_; 
v_a_4480_ = lean_ctor_get(v___y_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref_known(v___y_4479_, 1);
v___y_4457_ = v___y_4470_;
v___y_4458_ = v___y_4472_;
v___y_4459_ = v___y_4471_;
v___y_4460_ = v___y_4474_;
v___y_4461_ = v___y_4473_;
v___y_4462_ = v___y_4475_;
v___y_4463_ = v___y_4477_;
v___y_4464_ = v___y_4476_;
v___y_4465_ = v___y_4478_;
v_a_4466_ = v_a_4480_;
goto v___jp_4456_;
}
else
{
lean_object* v_a_4481_; 
lean_dec(v___y_4473_);
lean_dec(v___y_4471_);
v_a_4481_ = lean_ctor_get(v___y_4479_, 0);
lean_inc(v_a_4481_);
lean_dec_ref_known(v___y_4479_, 1);
v___y_4437_ = v___y_4470_;
v___y_4438_ = v___y_4472_;
v___y_4439_ = v___y_4474_;
v___y_4440_ = v___y_4475_;
v___y_4441_ = v___y_4476_;
v___y_4442_ = v___y_4477_;
v___y_4443_ = v___y_4478_;
v_a_4444_ = v_a_4481_;
goto v___jp_4436_;
}
}
v___jp_4482_:
{
if (v___y_4494_ == 0)
{
lean_object* v___x_4495_; 
lean_dec_ref(v___y_4486_);
v___x_4495_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4493_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_4493_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_dec_ref_known(v___x_4495_, 1);
v___y_4457_ = v___y_4483_;
v___y_4458_ = v___y_4485_;
v___y_4459_ = v___y_4484_;
v___y_4460_ = v___y_4488_;
v___y_4461_ = v___y_4487_;
v___y_4462_ = v___y_4489_;
v___y_4463_ = v___y_4491_;
v___y_4464_ = v___y_4490_;
v___y_4465_ = v___y_4492_;
v_a_4466_ = v_snd_3421_;
goto v___jp_4456_;
}
else
{
lean_object* v_a_4496_; 
lean_dec(v___y_4487_);
lean_dec(v___y_4484_);
lean_dec(v_snd_3421_);
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref_known(v___x_4495_, 1);
v___y_4437_ = v___y_4483_;
v___y_4438_ = v___y_4485_;
v___y_4439_ = v___y_4488_;
v___y_4440_ = v___y_4489_;
v___y_4441_ = v___y_4490_;
v___y_4442_ = v___y_4491_;
v___y_4443_ = v___y_4492_;
v_a_4444_ = v_a_4496_;
goto v___jp_4436_;
}
}
else
{
lean_dec_ref(v___y_4493_);
lean_dec(v_snd_3421_);
v___y_4470_ = v___y_4483_;
v___y_4471_ = v___y_4484_;
v___y_4472_ = v___y_4485_;
v___y_4473_ = v___y_4487_;
v___y_4474_ = v___y_4488_;
v___y_4475_ = v___y_4489_;
v___y_4476_ = v___y_4490_;
v___y_4477_ = v___y_4491_;
v___y_4478_ = v___y_4492_;
v___y_4479_ = v___y_4486_;
goto v___jp_4469_;
}
}
v___jp_4497_:
{
if (lean_obj_tag(v___y_4505_) == 0)
{
lean_object* v_a_4506_; 
v_a_4506_ = lean_ctor_get(v___y_4505_, 0);
lean_inc(v_a_4506_);
lean_dec_ref_known(v___y_4505_, 1);
v___y_4447_ = v___y_4498_;
v___y_4448_ = v___y_4499_;
v___y_4449_ = v___y_4500_;
v___y_4450_ = v___y_4501_;
v___y_4451_ = v___y_4503_;
v___y_4452_ = v___y_4502_;
v___y_4453_ = v___y_4504_;
v_a_4454_ = v_a_4506_;
goto v___jp_4446_;
}
else
{
lean_object* v_a_4507_; 
v_a_4507_ = lean_ctor_get(v___y_4505_, 0);
lean_inc(v_a_4507_);
lean_dec_ref_known(v___y_4505_, 1);
v___y_4437_ = v___y_4498_;
v___y_4438_ = v___y_4499_;
v___y_4439_ = v___y_4500_;
v___y_4440_ = v___y_4501_;
v___y_4441_ = v___y_4503_;
v___y_4442_ = v___y_4502_;
v___y_4443_ = v___y_4504_;
v_a_4444_ = v_a_4507_;
goto v___jp_4436_;
}
}
v___jp_4508_:
{
uint8_t v___x_4519_; uint8_t v___x_4520_; 
v___x_4519_ = l_List_isEmpty___redArg(v___y_4512_);
lean_dec(v___y_4512_);
v___x_4520_ = lean_bool_not(v___x_4519_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; 
lean_inc(v_trace_3380_);
v___x_4521_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_4510_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v___x_4523_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4522_);
lean_dec_ref_known(v___x_4521_, 1);
v___x_4523_ = l_List_appendTR___redArg(v___y_4514_, v_a_4522_);
v___y_4447_ = v___y_4509_;
v___y_4448_ = v___y_4511_;
v___y_4449_ = v___y_4513_;
v___y_4450_ = v___y_4515_;
v___y_4451_ = v___y_4517_;
v___y_4452_ = v___y_4516_;
v___y_4453_ = v___y_4518_;
v_a_4454_ = v___x_4523_;
goto v___jp_4446_;
}
else
{
lean_dec(v___y_4514_);
v___y_4498_ = v___y_4509_;
v___y_4499_ = v___y_4511_;
v___y_4500_ = v___y_4513_;
v___y_4501_ = v___y_4515_;
v___y_4502_ = v___y_4516_;
v___y_4503_ = v___y_4517_;
v___y_4504_ = v___y_4518_;
v___y_4505_ = v___x_4521_;
goto v___jp_4497_;
}
}
else
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
lean_dec(v___y_4514_);
lean_dec(v___y_4510_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_4524_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4525_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4524_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_4498_ = v___y_4509_;
v___y_4499_ = v___y_4511_;
v___y_4500_ = v___y_4513_;
v___y_4501_ = v___y_4515_;
v___y_4502_ = v___y_4516_;
v___y_4503_ = v___y_4517_;
v___y_4504_ = v___y_4518_;
v___y_4505_ = v___x_4525_;
goto v___jp_4497_;
}
}
v___jp_4526_:
{
uint8_t v_commitIndependentGoals_4537_; lean_object* v___x_4538_; 
v_commitIndependentGoals_4537_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_4531_);
v___x_4538_ = l_List_appendTR___redArg(v_a_4536_, v___y_4531_);
if (v_commitIndependentGoals_4537_ == 0)
{
v___y_4509_ = v___y_4527_;
v___y_4510_ = v___x_4538_;
v___y_4511_ = v___y_4529_;
v___y_4512_ = v___y_4528_;
v___y_4513_ = v___y_4530_;
v___y_4514_ = v___y_4531_;
v___y_4515_ = v___y_4532_;
v___y_4516_ = v___y_4534_;
v___y_4517_ = v___y_4533_;
v___y_4518_ = v___y_4535_;
goto v___jp_4508_;
}
else
{
uint8_t v___x_4539_; uint8_t v___x_4540_; 
v___x_4539_ = l_List_isEmpty___redArg(v___y_4531_);
v___x_4540_ = lean_bool_not(v___x_4539_);
if (v___x_4540_ == 0)
{
v___y_4509_ = v___y_4527_;
v___y_4510_ = v___x_4538_;
v___y_4511_ = v___y_4529_;
v___y_4512_ = v___y_4528_;
v___y_4513_ = v___y_4530_;
v___y_4514_ = v___y_4531_;
v___y_4515_ = v___y_4532_;
v___y_4516_ = v___y_4534_;
v___y_4517_ = v___y_4533_;
v___y_4518_ = v___y_4535_;
goto v___jp_4508_;
}
else
{
lean_object* v___x_4541_; 
v___x_4541_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4543_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4542_);
lean_dec_ref_known(v___x_4541_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_4543_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_4538_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_dec(v_a_4542_);
lean_dec(v_snd_3421_);
v___y_4470_ = v___y_4527_;
v___y_4471_ = v___y_4528_;
v___y_4472_ = v___y_4529_;
v___y_4473_ = v___y_4531_;
v___y_4474_ = v___y_4530_;
v___y_4475_ = v___y_4532_;
v___y_4476_ = v___y_4533_;
v___y_4477_ = v___y_4534_;
v___y_4478_ = v___y_4535_;
v___y_4479_ = v___x_4543_;
goto v___jp_4469_;
}
else
{
lean_object* v_a_4544_; uint8_t v___x_4545_; 
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
lean_inc(v_a_4544_);
v___x_4545_ = l_Lean_Exception_isInterrupt(v_a_4544_);
if (v___x_4545_ == 0)
{
uint8_t v___x_4546_; 
v___x_4546_ = l_Lean_Exception_isRuntime(v_a_4544_);
v___y_4483_ = v___y_4527_;
v___y_4484_ = v___y_4528_;
v___y_4485_ = v___y_4529_;
v___y_4486_ = v___x_4543_;
v___y_4487_ = v___y_4531_;
v___y_4488_ = v___y_4530_;
v___y_4489_ = v___y_4532_;
v___y_4490_ = v___y_4533_;
v___y_4491_ = v___y_4534_;
v___y_4492_ = v___y_4535_;
v___y_4493_ = v_a_4542_;
v___y_4494_ = v___x_4546_;
goto v___jp_4482_;
}
else
{
lean_dec(v_a_4544_);
v___y_4483_ = v___y_4527_;
v___y_4484_ = v___y_4528_;
v___y_4485_ = v___y_4529_;
v___y_4486_ = v___x_4543_;
v___y_4487_ = v___y_4531_;
v___y_4488_ = v___y_4530_;
v___y_4489_ = v___y_4532_;
v___y_4490_ = v___y_4533_;
v___y_4491_ = v___y_4534_;
v___y_4492_ = v___y_4535_;
v___y_4493_ = v_a_4542_;
v___y_4494_ = v___x_4545_;
goto v___jp_4482_;
}
}
}
else
{
lean_object* v_a_4547_; 
lean_dec(v___x_4538_);
lean_dec(v___y_4531_);
lean_dec(v___y_4528_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4547_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4547_);
lean_dec_ref_known(v___x_4541_, 1);
v___y_4437_ = v___y_4527_;
v___y_4438_ = v___y_4529_;
v___y_4439_ = v___y_4530_;
v___y_4440_ = v___y_4532_;
v___y_4441_ = v___y_4533_;
v___y_4442_ = v___y_4534_;
v___y_4443_ = v___y_4535_;
v_a_4444_ = v_a_4547_;
goto v___jp_4436_;
}
}
}
}
v___jp_4548_:
{
lean_object* v___x_4558_; 
v___x_4558_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3388_);
if (lean_obj_tag(v___x_4558_) == 0)
{
if (v___y_4553_ == 0)
{
lean_object* v_a_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_a_4559_);
lean_dec_ref_known(v___x_4558_, 1);
v___x_4560_ = lean_io_mono_nanos_now();
v___x_4561_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___y_4550_, v_a_3386_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_a_4562_; lean_object* v___x_4563_; 
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_a_4562_);
lean_dec_ref_known(v___x_4561_, 1);
v___x_4563_ = l_List_reverse___redArg(v_a_4562_);
v___y_4398_ = v___y_4549_;
v___y_4399_ = v___y_4551_;
v___y_4400_ = v___y_4552_;
v___y_4401_ = v___y_4555_;
v___y_4402_ = v___y_4554_;
v___y_4403_ = v_a_4559_;
v___y_4404_ = v___y_4556_;
v___y_4405_ = v___x_4560_;
v___y_4406_ = v___y_4557_;
v_a_4407_ = v___x_4563_;
goto v___jp_4397_;
}
else
{
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_a_4564_; 
v_a_4564_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_a_4564_);
lean_dec_ref_known(v___x_4561_, 1);
v___y_4398_ = v___y_4549_;
v___y_4399_ = v___y_4551_;
v___y_4400_ = v___y_4552_;
v___y_4401_ = v___y_4555_;
v___y_4402_ = v___y_4554_;
v___y_4403_ = v_a_4559_;
v___y_4404_ = v___y_4556_;
v___y_4405_ = v___x_4560_;
v___y_4406_ = v___y_4557_;
v_a_4407_ = v_a_4564_;
goto v___jp_4397_;
}
else
{
lean_object* v_a_4565_; 
lean_dec(v___y_4554_);
lean_dec(v___y_4551_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4565_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_a_4565_);
lean_dec_ref_known(v___x_4561_, 1);
v___y_4308_ = v___y_4549_;
v___y_4309_ = v___y_4552_;
v___y_4310_ = v___y_4555_;
v___y_4311_ = v_a_4559_;
v___y_4312_ = v___y_4556_;
v___y_4313_ = v___x_4560_;
v___y_4314_ = v___y_4557_;
v_a_4315_ = v_a_4565_;
goto v___jp_4307_;
}
}
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v_a_4566_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v___x_4558_, 1);
v___x_4567_ = lean_io_get_num_heartbeats();
v___x_4568_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___y_4550_, v_a_3386_);
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_object* v_a_4569_; lean_object* v___x_4570_; 
v_a_4569_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_a_4569_);
lean_dec_ref_known(v___x_4568_, 1);
v___x_4570_ = l_List_reverse___redArg(v_a_4569_);
v___y_4527_ = v___y_4549_;
v___y_4528_ = v___y_4551_;
v___y_4529_ = v___y_4552_;
v___y_4530_ = v___y_4555_;
v___y_4531_ = v___y_4554_;
v___y_4532_ = v_a_4566_;
v___y_4533_ = v___x_4567_;
v___y_4534_ = v___y_4556_;
v___y_4535_ = v___y_4557_;
v_a_4536_ = v___x_4570_;
goto v___jp_4526_;
}
else
{
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_object* v_a_4571_; 
v_a_4571_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_a_4571_);
lean_dec_ref_known(v___x_4568_, 1);
v___y_4527_ = v___y_4549_;
v___y_4528_ = v___y_4551_;
v___y_4529_ = v___y_4552_;
v___y_4530_ = v___y_4555_;
v___y_4531_ = v___y_4554_;
v___y_4532_ = v_a_4566_;
v___y_4533_ = v___x_4567_;
v___y_4534_ = v___y_4556_;
v___y_4535_ = v___y_4557_;
v_a_4536_ = v_a_4571_;
goto v___jp_4526_;
}
else
{
lean_object* v_a_4572_; 
lean_dec(v___y_4554_);
lean_dec(v___y_4551_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4572_ = lean_ctor_get(v___x_4568_, 0);
lean_inc(v_a_4572_);
lean_dec_ref_known(v___x_4568_, 1);
v___y_4437_ = v___y_4549_;
v___y_4438_ = v___y_4552_;
v___y_4439_ = v___y_4555_;
v___y_4440_ = v_a_4566_;
v___y_4441_ = v___x_4567_;
v___y_4442_ = v___y_4556_;
v___y_4443_ = v___y_4557_;
v_a_4444_ = v_a_4572_;
goto v___jp_4436_;
}
}
}
}
else
{
lean_object* v_a_4573_; 
lean_dec(v___y_4554_);
lean_dec(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v_snd_3421_);
lean_dec(v_goals_3383_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4573_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_a_4573_);
lean_dec_ref_known(v___x_4558_, 1);
v___y_4269_ = v___y_4552_;
v___y_4270_ = v___y_4555_;
v___y_4271_ = v___y_4557_;
v_a_4272_ = v_a_4573_;
goto v___jp_4268_;
}
}
v___jp_4574_:
{
uint8_t v___x_4581_; uint8_t v___x_4582_; 
v___x_4581_ = l_List_isEmpty___redArg(v___y_4576_);
lean_dec(v___y_4576_);
v___x_4582_ = lean_bool_not(v___x_4581_);
if (v___x_4582_ == 0)
{
lean_object* v___x_4583_; 
lean_inc(v_trace_3380_);
v___x_4583_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_4577_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4585_; 
v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
lean_inc(v_a_4584_);
lean_dec_ref_known(v___x_4583_, 1);
v___x_4585_ = l_List_appendTR___redArg(v___y_4579_, v_a_4584_);
v___y_4275_ = v___y_4575_;
v___y_4276_ = v___y_4578_;
v___y_4277_ = v___y_4580_;
v_a_4278_ = v___x_4585_;
goto v___jp_4274_;
}
else
{
lean_dec(v___y_4579_);
v___y_4281_ = v___y_4575_;
v___y_4282_ = v___y_4578_;
v___y_4283_ = v___y_4580_;
v___y_4284_ = v___x_4583_;
goto v___jp_4280_;
}
}
else
{
lean_object* v___x_4586_; lean_object* v___x_4587_; 
lean_dec(v___y_4579_);
lean_dec(v___y_4577_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_4586_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4587_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4586_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_4281_ = v___y_4575_;
v___y_4282_ = v___y_4578_;
v___y_4283_ = v___y_4580_;
v___y_4284_ = v___x_4587_;
goto v___jp_4280_;
}
}
v___jp_4588_:
{
uint8_t v___x_4595_; uint8_t v___x_4596_; 
v___x_4595_ = l_List_isEmpty___redArg(v___y_4590_);
lean_dec(v___y_4590_);
v___x_4596_ = lean_bool_not(v___x_4595_);
if (v___x_4596_ == 0)
{
lean_object* v___x_4597_; 
lean_inc(v_trace_3380_);
v___x_4597_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_4593_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4599_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref_known(v___x_4597_, 1);
v___x_4599_ = l_List_appendTR___redArg(v___y_4592_, v_a_4598_);
v___y_4275_ = v___y_4589_;
v___y_4276_ = v___y_4591_;
v___y_4277_ = v___y_4594_;
v_a_4278_ = v___x_4599_;
goto v___jp_4274_;
}
else
{
lean_dec(v___y_4592_);
v___y_4281_ = v___y_4589_;
v___y_4282_ = v___y_4591_;
v___y_4283_ = v___y_4594_;
v___y_4284_ = v___x_4597_;
goto v___jp_4280_;
}
}
else
{
lean_object* v___x_4600_; lean_object* v___x_4601_; 
lean_dec(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_4600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4601_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4600_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_4281_ = v___y_4589_;
v___y_4282_ = v___y_4591_;
v___y_4283_ = v___y_4594_;
v___y_4284_ = v___x_4601_;
goto v___jp_4280_;
}
}
v___jp_4602_:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
v___x_4609_ = l_List_appendTR___redArg(v___y_4606_, v___y_4604_);
v___x_4610_ = l_List_appendTR___redArg(v___x_4609_, v_a_4608_);
v___y_4275_ = v___y_4603_;
v___y_4276_ = v___y_4605_;
v___y_4277_ = v___y_4607_;
v_a_4278_ = v___x_4610_;
goto v___jp_4274_;
}
v___jp_4611_:
{
if (lean_obj_tag(v___y_4617_) == 0)
{
lean_object* v_a_4618_; 
v_a_4618_ = lean_ctor_get(v___y_4617_, 0);
lean_inc(v_a_4618_);
lean_dec_ref_known(v___y_4617_, 1);
v___y_4603_ = v___y_4613_;
v___y_4604_ = v___y_4612_;
v___y_4605_ = v___y_4615_;
v___y_4606_ = v___y_4614_;
v___y_4607_ = v___y_4616_;
v_a_4608_ = v_a_4618_;
goto v___jp_4602_;
}
else
{
lean_object* v_a_4619_; 
lean_dec(v___y_4614_);
lean_dec(v___y_4612_);
v_a_4619_ = lean_ctor_get(v___y_4617_, 0);
lean_inc(v_a_4619_);
lean_dec_ref_known(v___y_4617_, 1);
v___y_4269_ = v___y_4613_;
v___y_4270_ = v___y_4615_;
v___y_4271_ = v___y_4616_;
v_a_4272_ = v_a_4619_;
goto v___jp_4268_;
}
}
v___jp_4620_:
{
if (v___y_4628_ == 0)
{
lean_object* v___x_4629_; 
lean_dec_ref(v___y_4621_);
v___x_4629_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4626_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_4626_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_dec_ref_known(v___x_4629_, 1);
v___y_4603_ = v___y_4623_;
v___y_4604_ = v___y_4622_;
v___y_4605_ = v___y_4625_;
v___y_4606_ = v___y_4624_;
v___y_4607_ = v___y_4627_;
v_a_4608_ = v_snd_3421_;
goto v___jp_4602_;
}
else
{
lean_object* v_a_4630_; 
lean_dec(v___y_4624_);
lean_dec(v___y_4622_);
lean_dec(v_snd_3421_);
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
lean_inc(v_a_4630_);
lean_dec_ref_known(v___x_4629_, 1);
v___y_4269_ = v___y_4623_;
v___y_4270_ = v___y_4625_;
v___y_4271_ = v___y_4627_;
v_a_4272_ = v_a_4630_;
goto v___jp_4268_;
}
}
else
{
lean_dec_ref(v___y_4626_);
lean_dec(v_snd_3421_);
v___y_4612_ = v___y_4622_;
v___y_4613_ = v___y_4623_;
v___y_4614_ = v___y_4624_;
v___y_4615_ = v___y_4625_;
v___y_4616_ = v___y_4627_;
v___y_4617_ = v___y_4621_;
goto v___jp_4611_;
}
}
v___jp_4631_:
{
uint8_t v_commitIndependentGoals_4638_; lean_object* v___x_4639_; 
v_commitIndependentGoals_4638_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_4635_);
v___x_4639_ = l_List_appendTR___redArg(v_a_4637_, v___y_4635_);
if (v_commitIndependentGoals_4638_ == 0)
{
v___y_4575_ = v___y_4633_;
v___y_4576_ = v___y_4632_;
v___y_4577_ = v___x_4639_;
v___y_4578_ = v___y_4634_;
v___y_4579_ = v___y_4635_;
v___y_4580_ = v___y_4636_;
goto v___jp_4574_;
}
else
{
uint8_t v___x_4640_; uint8_t v___x_4641_; 
v___x_4640_ = l_List_isEmpty___redArg(v___y_4635_);
v___x_4641_ = lean_bool_not(v___x_4640_);
if (v___x_4641_ == 0)
{
v___y_4575_ = v___y_4633_;
v___y_4576_ = v___y_4632_;
v___y_4577_ = v___x_4639_;
v___y_4578_ = v___y_4634_;
v___y_4579_ = v___y_4635_;
v___y_4580_ = v___y_4636_;
goto v___jp_4574_;
}
else
{
lean_object* v___x_4642_; 
v___x_4642_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; lean_object* v___x_4644_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_a_4643_);
lean_dec_ref_known(v___x_4642_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_4644_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_4639_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_dec(v_a_4643_);
lean_dec(v_snd_3421_);
v___y_4612_ = v___y_4632_;
v___y_4613_ = v___y_4633_;
v___y_4614_ = v___y_4635_;
v___y_4615_ = v___y_4634_;
v___y_4616_ = v___y_4636_;
v___y_4617_ = v___x_4644_;
goto v___jp_4611_;
}
else
{
lean_object* v_a_4645_; uint8_t v___x_4646_; 
v_a_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc(v_a_4645_);
v___x_4646_ = l_Lean_Exception_isInterrupt(v_a_4645_);
if (v___x_4646_ == 0)
{
uint8_t v___x_4647_; 
v___x_4647_ = l_Lean_Exception_isRuntime(v_a_4645_);
v___y_4621_ = v___x_4644_;
v___y_4622_ = v___y_4632_;
v___y_4623_ = v___y_4633_;
v___y_4624_ = v___y_4635_;
v___y_4625_ = v___y_4634_;
v___y_4626_ = v_a_4643_;
v___y_4627_ = v___y_4636_;
v___y_4628_ = v___x_4647_;
goto v___jp_4620_;
}
else
{
lean_dec(v_a_4645_);
v___y_4621_ = v___x_4644_;
v___y_4622_ = v___y_4632_;
v___y_4623_ = v___y_4633_;
v___y_4624_ = v___y_4635_;
v___y_4625_ = v___y_4634_;
v___y_4626_ = v_a_4643_;
v___y_4627_ = v___y_4636_;
v___y_4628_ = v___x_4646_;
goto v___jp_4620_;
}
}
}
else
{
lean_object* v_a_4648_; 
lean_dec(v___x_4639_);
lean_dec(v___y_4635_);
lean_dec(v___y_4632_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4648_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_a_4648_);
lean_dec_ref_known(v___x_4642_, 1);
v___y_4269_ = v___y_4633_;
v___y_4270_ = v___y_4634_;
v___y_4271_ = v___y_4636_;
v_a_4272_ = v_a_4648_;
goto v___jp_4268_;
}
}
}
}
v___jp_4649_:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = l_List_appendTR___redArg(v___y_4653_, v___y_4651_);
v___x_4657_ = l_List_appendTR___redArg(v___x_4656_, v_a_4655_);
v___y_4275_ = v___y_4650_;
v___y_4276_ = v___y_4652_;
v___y_4277_ = v___y_4654_;
v_a_4278_ = v___x_4657_;
goto v___jp_4274_;
}
v___jp_4658_:
{
if (lean_obj_tag(v___y_4664_) == 0)
{
lean_object* v_a_4665_; 
v_a_4665_ = lean_ctor_get(v___y_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v___y_4664_, 1);
v___y_4650_ = v___y_4660_;
v___y_4651_ = v___y_4659_;
v___y_4652_ = v___y_4662_;
v___y_4653_ = v___y_4661_;
v___y_4654_ = v___y_4663_;
v_a_4655_ = v_a_4665_;
goto v___jp_4649_;
}
else
{
lean_object* v_a_4666_; 
lean_dec(v___y_4661_);
lean_dec(v___y_4659_);
v_a_4666_ = lean_ctor_get(v___y_4664_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___y_4664_, 1);
v___y_4269_ = v___y_4660_;
v___y_4270_ = v___y_4662_;
v___y_4271_ = v___y_4663_;
v_a_4272_ = v_a_4666_;
goto v___jp_4268_;
}
}
v___jp_4667_:
{
if (v___y_4675_ == 0)
{
lean_object* v___x_4676_; 
lean_dec_ref(v___y_4672_);
v___x_4676_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4674_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_4674_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_dec_ref_known(v___x_4676_, 1);
v___y_4650_ = v___y_4669_;
v___y_4651_ = v___y_4668_;
v___y_4652_ = v___y_4671_;
v___y_4653_ = v___y_4670_;
v___y_4654_ = v___y_4673_;
v_a_4655_ = v_snd_3421_;
goto v___jp_4649_;
}
else
{
lean_object* v_a_4677_; 
lean_dec(v___y_4670_);
lean_dec(v___y_4668_);
lean_dec(v_snd_3421_);
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v___x_4676_, 1);
v___y_4269_ = v___y_4669_;
v___y_4270_ = v___y_4671_;
v___y_4271_ = v___y_4673_;
v_a_4272_ = v_a_4677_;
goto v___jp_4268_;
}
}
else
{
lean_dec_ref(v___y_4674_);
lean_dec(v_snd_3421_);
v___y_4659_ = v___y_4668_;
v___y_4660_ = v___y_4669_;
v___y_4661_ = v___y_4670_;
v___y_4662_ = v___y_4671_;
v___y_4663_ = v___y_4673_;
v___y_4664_ = v___y_4672_;
goto v___jp_4658_;
}
}
v___jp_4678_:
{
uint8_t v_commitIndependentGoals_4685_; lean_object* v___x_4686_; 
v_commitIndependentGoals_4685_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_4682_);
v___x_4686_ = l_List_appendTR___redArg(v_a_4684_, v___y_4682_);
if (v_commitIndependentGoals_4685_ == 0)
{
v___y_4589_ = v___y_4680_;
v___y_4590_ = v___y_4679_;
v___y_4591_ = v___y_4681_;
v___y_4592_ = v___y_4682_;
v___y_4593_ = v___x_4686_;
v___y_4594_ = v___y_4683_;
goto v___jp_4588_;
}
else
{
uint8_t v___x_4687_; uint8_t v___x_4688_; 
v___x_4687_ = l_List_isEmpty___redArg(v___y_4682_);
v___x_4688_ = lean_bool_not(v___x_4687_);
if (v___x_4688_ == 0)
{
v___y_4589_ = v___y_4680_;
v___y_4590_ = v___y_4679_;
v___y_4591_ = v___y_4681_;
v___y_4592_ = v___y_4682_;
v___y_4593_ = v___x_4686_;
v___y_4594_ = v___y_4683_;
goto v___jp_4588_;
}
else
{
lean_object* v___x_4689_; 
v___x_4689_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_object* v_a_4690_; lean_object* v___x_4691_; 
v_a_4690_ = lean_ctor_get(v___x_4689_, 0);
lean_inc(v_a_4690_);
lean_dec_ref_known(v___x_4689_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_4691_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_4686_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_dec(v_a_4690_);
lean_dec(v_snd_3421_);
v___y_4659_ = v___y_4679_;
v___y_4660_ = v___y_4680_;
v___y_4661_ = v___y_4682_;
v___y_4662_ = v___y_4681_;
v___y_4663_ = v___y_4683_;
v___y_4664_ = v___x_4691_;
goto v___jp_4658_;
}
else
{
lean_object* v_a_4692_; uint8_t v___x_4693_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
lean_inc(v_a_4692_);
v___x_4693_ = l_Lean_Exception_isInterrupt(v_a_4692_);
if (v___x_4693_ == 0)
{
uint8_t v___x_4694_; 
v___x_4694_ = l_Lean_Exception_isRuntime(v_a_4692_);
v___y_4668_ = v___y_4679_;
v___y_4669_ = v___y_4680_;
v___y_4670_ = v___y_4682_;
v___y_4671_ = v___y_4681_;
v___y_4672_ = v___x_4691_;
v___y_4673_ = v___y_4683_;
v___y_4674_ = v_a_4690_;
v___y_4675_ = v___x_4694_;
goto v___jp_4667_;
}
else
{
lean_dec(v_a_4692_);
v___y_4668_ = v___y_4679_;
v___y_4669_ = v___y_4680_;
v___y_4670_ = v___y_4682_;
v___y_4671_ = v___y_4681_;
v___y_4672_ = v___x_4691_;
v___y_4673_ = v___y_4683_;
v___y_4674_ = v_a_4690_;
v___y_4675_ = v___x_4693_;
goto v___jp_4667_;
}
}
}
else
{
lean_object* v_a_4695_; 
lean_dec(v___x_4686_);
lean_dec(v___y_4682_);
lean_dec(v___y_4679_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4695_ = lean_ctor_get(v___x_4689_, 0);
lean_inc(v_a_4695_);
lean_dec_ref_known(v___x_4689_, 1);
v___y_4269_ = v___y_4680_;
v___y_4270_ = v___y_4681_;
v___y_4271_ = v___y_4683_;
v_a_4272_ = v_a_4695_;
goto v___jp_4268_;
}
}
}
}
v___jp_4696_:
{
lean_object* v___x_4706_; uint8_t v___x_4707_; 
v___x_4706_ = l_Lean_trace_profiler;
v___x_4707_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3536_, v___x_4706_);
if (v___x_4707_ == 0)
{
lean_object* v___x_4708_; 
lean_dec_ref(v___y_4697_);
v___x_4708_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___y_4698_, v_a_3386_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4710_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_a_4709_);
lean_dec_ref_known(v___x_4708_, 1);
v___x_4710_ = l_List_reverse___redArg(v_a_4709_);
v___y_4679_ = v___y_4700_;
v___y_4680_ = v___y_4699_;
v___y_4681_ = v___y_4702_;
v___y_4682_ = v___y_4703_;
v___y_4683_ = v___y_4704_;
v_a_4684_ = v___x_4710_;
goto v___jp_4678_;
}
else
{
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4711_; 
v_a_4711_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_a_4711_);
lean_dec_ref_known(v___x_4708_, 1);
v___y_4679_ = v___y_4700_;
v___y_4680_ = v___y_4699_;
v___y_4681_ = v___y_4702_;
v___y_4682_ = v___y_4703_;
v___y_4683_ = v___y_4704_;
v_a_4684_ = v_a_4711_;
goto v___jp_4678_;
}
else
{
lean_object* v_a_4712_; 
lean_dec(v___y_4703_);
lean_dec(v___y_4700_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4712_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_a_4712_);
lean_dec_ref_known(v___x_4708_, 1);
v___y_4269_ = v___y_4699_;
v___y_4270_ = v___y_4702_;
v___y_4271_ = v___y_4704_;
v_a_4272_ = v_a_4712_;
goto v___jp_4268_;
}
}
}
else
{
v___y_4549_ = v___y_4697_;
v___y_4550_ = v___y_4698_;
v___y_4551_ = v___y_4700_;
v___y_4552_ = v___y_4699_;
v___y_4553_ = v___y_4701_;
v___y_4554_ = v___y_4703_;
v___y_4555_ = v___y_4702_;
v___y_4556_ = v_a_4705_;
v___y_4557_ = v___y_4704_;
goto v___jp_4548_;
}
}
v___jp_4713_:
{
lean_object* v___x_4715_; 
v___x_4715_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3388_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; lean_object* v___x_4717_; uint8_t v___x_4718_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_a_4716_);
lean_dec_ref_known(v___x_4715_, 1);
v___x_4717_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4718_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3536_, v___x_4717_);
if (v___x_4718_ == 0)
{
lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4719_ = lean_io_mono_nanos_now();
v___x_4720_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3420_, v___f_3539_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v_fst_4722_; lean_object* v_snd_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4721_);
lean_dec_ref_known(v___x_4720_, 1);
v_fst_4722_ = lean_ctor_get(v_a_4721_, 0);
lean_inc(v_fst_4722_);
v_snd_4723_ = lean_ctor_get(v_a_4721_, 1);
lean_inc(v_snd_4723_);
lean_dec(v_a_4721_);
v___x_4724_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_4723_, v___x_3414_);
v___x_4725_ = lean_box(0);
if (v___x_3541_ == 0)
{
lean_object* v___f_4726_; 
lean_inc(v___x_4724_);
lean_inc(v_fst_4722_);
v___f_4726_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_4726_, 0, v_fst_4722_);
lean_closure_set(v___f_4726_, 1, v___x_4724_);
if (v_hasTrace_3538_ == 0)
{
v___y_4207_ = v_fst_4722_;
v___y_4208_ = v___x_4718_;
v___y_4209_ = v___x_4725_;
v___y_4210_ = v___y_4714_;
v___y_4211_ = v___x_4719_;
v___y_4212_ = v___x_4724_;
v___y_4213_ = v_a_4716_;
v___y_4214_ = v___f_4726_;
v_a_4215_ = v_hasTrace_3538_;
goto v___jp_4206_;
}
else
{
lean_object* v___x_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; 
v___x_4727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_3380_);
v___x_4728_ = l_Lean_Name_append(v___x_4727_, v_trace_3380_);
v___x_4729_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3537_, v_options_3536_, v___x_4728_);
lean_dec(v___x_4728_);
if (v___x_4729_ == 0)
{
v___y_4207_ = v_fst_4722_;
v___y_4208_ = v___x_4718_;
v___y_4209_ = v___x_4725_;
v___y_4210_ = v___y_4714_;
v___y_4211_ = v___x_4719_;
v___y_4212_ = v___x_4724_;
v___y_4213_ = v_a_4716_;
v___y_4214_ = v___f_4726_;
v_a_4215_ = v___x_4729_;
goto v___jp_4206_;
}
else
{
v___y_4149_ = v_fst_4722_;
v___y_4150_ = v___x_4725_;
v___y_4151_ = v___x_4718_;
v___y_4152_ = v___x_4729_;
v___y_4153_ = v___y_4714_;
v___y_4154_ = v___x_4719_;
v___y_4155_ = v___x_4724_;
v___y_4156_ = v_a_4716_;
v___y_4157_ = v___f_4726_;
goto v___jp_4148_;
}
}
}
else
{
lean_object* v___x_4730_; 
v___x_4730_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___x_4725_, v_a_3386_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4732_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v___x_4730_, 1);
v___x_4732_ = l_List_reverse___redArg(v_a_4731_);
v___y_4238_ = v_fst_4722_;
v___y_4239_ = v___y_4714_;
v___y_4240_ = v___x_4719_;
v___y_4241_ = v___x_4724_;
v___y_4242_ = v_a_4716_;
v_a_4243_ = v___x_4732_;
goto v___jp_4237_;
}
else
{
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4733_; 
v_a_4733_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4733_);
lean_dec_ref_known(v___x_4730_, 1);
v___y_4238_ = v_fst_4722_;
v___y_4239_ = v___y_4714_;
v___y_4240_ = v___x_4719_;
v___y_4241_ = v___x_4724_;
v___y_4242_ = v_a_4716_;
v_a_4243_ = v_a_4733_;
goto v___jp_4237_;
}
else
{
lean_object* v_a_4734_; 
lean_dec(v___x_4724_);
lean_dec(v_fst_4722_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4734_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___x_4730_, 1);
v___y_3835_ = v___y_4714_;
v___y_3836_ = v___x_4719_;
v___y_3837_ = v_a_4716_;
v_a_3838_ = v_a_4734_;
goto v___jp_3834_;
}
}
}
}
else
{
lean_object* v_a_4735_; 
lean_dec(v_snd_3421_);
lean_dec(v_goals_3383_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4735_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4735_);
lean_dec_ref_known(v___x_4720_, 1);
v___y_3835_ = v___y_4714_;
v___y_3836_ = v___x_4719_;
v___y_3837_ = v_a_4716_;
v_a_3838_ = v_a_4735_;
goto v___jp_3834_;
}
}
else
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = lean_io_get_num_heartbeats();
v___x_4737_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3420_, v___f_3539_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v_fst_4739_; lean_object* v_snd_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4738_);
lean_dec_ref_known(v___x_4737_, 1);
v_fst_4739_ = lean_ctor_get(v_a_4738_, 0);
lean_inc(v_fst_4739_);
v_snd_4740_ = lean_ctor_get(v_a_4738_, 1);
lean_inc(v_snd_4740_);
lean_dec(v_a_4738_);
v___x_4741_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_4740_, v___x_3414_);
v___x_4742_ = lean_box(0);
if (v___x_3541_ == 0)
{
lean_object* v___f_4743_; 
lean_inc(v___x_4741_);
lean_inc(v_fst_4739_);
v___f_4743_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_4743_, 0, v_fst_4739_);
lean_closure_set(v___f_4743_, 1, v___x_4741_);
if (v_hasTrace_3538_ == 0)
{
v___y_4697_ = v___f_4743_;
v___y_4698_ = v___x_4742_;
v___y_4699_ = v___x_4736_;
v___y_4700_ = v_fst_4739_;
v___y_4701_ = v___x_4718_;
v___y_4702_ = v___y_4714_;
v___y_4703_ = v___x_4741_;
v___y_4704_ = v_a_4716_;
v_a_4705_ = v_hasTrace_3538_;
goto v___jp_4696_;
}
else
{
lean_object* v___x_4744_; lean_object* v___x_4745_; uint8_t v___x_4746_; 
v___x_4744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_3380_);
v___x_4745_ = l_Lean_Name_append(v___x_4744_, v_trace_3380_);
v___x_4746_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3537_, v_options_3536_, v___x_4745_);
lean_dec(v___x_4745_);
if (v___x_4746_ == 0)
{
v___y_4697_ = v___f_4743_;
v___y_4698_ = v___x_4742_;
v___y_4699_ = v___x_4736_;
v___y_4700_ = v_fst_4739_;
v___y_4701_ = v___x_4718_;
v___y_4702_ = v___y_4714_;
v___y_4703_ = v___x_4741_;
v___y_4704_ = v_a_4716_;
v_a_4705_ = v___x_4746_;
goto v___jp_4696_;
}
else
{
v___y_4549_ = v___f_4743_;
v___y_4550_ = v___x_4742_;
v___y_4551_ = v_fst_4739_;
v___y_4552_ = v___x_4736_;
v___y_4553_ = v___x_4718_;
v___y_4554_ = v___x_4741_;
v___y_4555_ = v___y_4714_;
v___y_4556_ = v___x_4746_;
v___y_4557_ = v_a_4716_;
goto v___jp_4548_;
}
}
}
else
{
lean_object* v___x_4747_; 
v___x_4747_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___x_4742_, v_a_3386_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; lean_object* v___x_4749_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref_known(v___x_4747_, 1);
v___x_4749_ = l_List_reverse___redArg(v_a_4748_);
v___y_4632_ = v_fst_4739_;
v___y_4633_ = v___x_4736_;
v___y_4634_ = v___y_4714_;
v___y_4635_ = v___x_4741_;
v___y_4636_ = v_a_4716_;
v_a_4637_ = v___x_4749_;
goto v___jp_4631_;
}
else
{
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4750_; 
v_a_4750_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4750_);
lean_dec_ref_known(v___x_4747_, 1);
v___y_4632_ = v_fst_4739_;
v___y_4633_ = v___x_4736_;
v___y_4634_ = v___y_4714_;
v___y_4635_ = v___x_4741_;
v___y_4636_ = v_a_4716_;
v_a_4637_ = v_a_4750_;
goto v___jp_4631_;
}
else
{
lean_object* v_a_4751_; 
lean_dec(v___x_4741_);
lean_dec(v_fst_4739_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4751_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4751_);
lean_dec_ref_known(v___x_4747_, 1);
v___y_4269_ = v___x_4736_;
v___y_4270_ = v___y_4714_;
v___y_4271_ = v_a_4716_;
v_a_4272_ = v_a_4751_;
goto v___jp_4268_;
}
}
}
}
else
{
lean_object* v_a_4752_; 
lean_dec(v_snd_3421_);
lean_dec(v_goals_3383_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_4752_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4752_);
lean_dec_ref_known(v___x_4737_, 1);
v___y_4269_ = v___x_4736_;
v___y_4270_ = v___y_4714_;
v___y_4271_ = v_a_4716_;
v_a_4272_ = v_a_4752_;
goto v___jp_4268_;
}
}
}
else
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4760_; 
lean_dec_ref(v___f_3542_);
lean_dec_ref(v___f_3539_);
lean_dec(v_snd_3421_);
lean_dec(v_fst_3420_);
lean_dec(v_goals_3383_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v_a_4753_ = lean_ctor_get(v___x_4715_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4755_ = v___x_4715_;
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4715_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
v___jp_4761_:
{
lean_object* v___x_4763_; uint8_t v___x_4764_; 
v___x_4763_ = l_Lean_trace_profiler;
v___x_4764_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3536_, v___x_4763_);
if (v___x_4764_ == 0)
{
lean_object* v___x_4765_; 
lean_dec_ref(v___f_3542_);
v___x_4765_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3420_, v___f_3539_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v_fst_4767_; lean_object* v_snd_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
lean_inc(v_a_4766_);
lean_dec_ref_known(v___x_4765_, 1);
v_fst_4767_ = lean_ctor_get(v_a_4766_, 0);
lean_inc(v_fst_4767_);
v_snd_4768_ = lean_ctor_get(v_a_4766_, 1);
lean_inc(v_snd_4768_);
lean_dec(v_a_4766_);
v___x_4769_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_4768_, v___x_3414_);
v___x_4770_ = lean_box(0);
if (v___x_3541_ == 0)
{
lean_object* v___f_4771_; 
lean_inc(v___x_4769_);
lean_inc(v_fst_4767_);
v___f_4771_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_4771_, 0, v_fst_4767_);
lean_closure_set(v___f_4771_, 1, v___x_4769_);
if (v_hasTrace_3538_ == 0)
{
v___y_3784_ = v___x_4764_;
v___y_3785_ = v___x_4769_;
v___y_3786_ = v___f_4771_;
v___y_3787_ = v_fst_4767_;
v___y_3788_ = v___x_4770_;
v_a_3789_ = v_hasTrace_3538_;
goto v___jp_3783_;
}
else
{
lean_object* v___x_4772_; lean_object* v___x_4773_; uint8_t v___x_4774_; 
v___x_4772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_3380_);
v___x_4773_ = l_Lean_Name_append(v___x_4772_, v_trace_3380_);
v___x_4774_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3537_, v_options_3536_, v___x_4773_);
lean_dec(v___x_4773_);
if (v___x_4774_ == 0)
{
v___y_3784_ = v___x_4764_;
v___y_3785_ = v___x_4769_;
v___y_3786_ = v___f_4771_;
v___y_3787_ = v_fst_4767_;
v___y_3788_ = v___x_4770_;
v_a_3789_ = v___x_4774_;
goto v___jp_3783_;
}
else
{
v___y_3754_ = v___x_4769_;
v___y_3755_ = v___x_4774_;
v___y_3756_ = v___f_4771_;
v___y_3757_ = v_fst_4767_;
v___y_3758_ = v___x_4770_;
goto v___jp_3753_;
}
}
}
else
{
lean_object* v___x_4775_; 
lean_del_object(v___x_3423_);
v___x_4775_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___x_4770_, v_a_3386_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v_a_4776_; lean_object* v___x_4777_; 
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_a_4776_);
lean_dec_ref_known(v___x_4775_, 1);
v___x_4777_ = l_List_reverse___redArg(v_a_4776_);
v___y_3514_ = v___x_4769_;
v___y_3515_ = v_fst_4767_;
v_a_3516_ = v___x_4777_;
goto v___jp_3513_;
}
else
{
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v_a_4778_; 
v_a_4778_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_a_4778_);
lean_dec_ref_known(v___x_4775_, 1);
v___y_3514_ = v___x_4769_;
v___y_3515_ = v_fst_4767_;
v_a_3516_ = v_a_4778_;
goto v___jp_3513_;
}
else
{
lean_dec(v___x_4769_);
lean_dec(v_fst_4767_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
return v___x_4775_;
}
}
}
}
else
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4786_; 
lean_del_object(v___x_3423_);
lean_dec(v_snd_3421_);
lean_dec(v_goals_3383_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v_a_4779_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4781_ = v___x_4765_;
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v___x_4765_);
v___x_4781_ = lean_box(0);
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
v_resetjp_4780_:
{
lean_object* v___x_4784_; 
if (v_isShared_4782_ == 0)
{
v___x_4784_ = v___x_4781_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_a_4779_);
v___x_4784_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
return v___x_4784_;
}
}
}
}
else
{
lean_del_object(v___x_3423_);
v___y_4714_ = v_a_4762_;
goto v___jp_4713_;
}
}
}
else
{
lean_object* v___x_4790_; 
v___x_4790_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_3420_, v___f_3539_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_5137_; 
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_4793_ = v___x_4790_;
v_isShared_4794_ = v_isSharedCheck_5137_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4790_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_5137_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v_fst_4795_; lean_object* v_snd_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_5136_; 
v_fst_4795_ = lean_ctor_get(v_a_4791_, 0);
v_snd_4796_ = lean_ctor_get(v_a_4791_, 1);
v_isSharedCheck_5136_ = !lean_is_exclusive(v_a_4791_);
if (v_isSharedCheck_5136_ == 0)
{
v___x_4798_ = v_a_4791_;
v_isShared_4799_ = v_isSharedCheck_5136_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_snd_4796_);
lean_inc(v_fst_4795_);
lean_dec(v_a_4791_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_5136_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4800_; lean_object* v___y_4802_; lean_object* v_a_4818_; lean_object* v___y_4825_; lean_object* v___y_4828_; lean_object* v___y_4829_; uint8_t v___y_4830_; lean_object* v_a_4841_; lean_object* v_a_4861_; lean_object* v___y_4868_; lean_object* v___y_4871_; lean_object* v___y_4872_; uint8_t v___y_4873_; lean_object* v___y_4884_; lean_object* v_a_4900_; lean_object* v___x_4919_; 
v___x_4800_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_4796_, v___x_3414_);
v___x_4919_ = lean_box(0);
if (v___x_3541_ == 0)
{
lean_object* v___f_4920_; lean_object* v___x_4921_; lean_object* v___y_4923_; lean_object* v___y_4924_; uint8_t v___y_4925_; lean_object* v_a_4926_; lean_object* v___y_4943_; lean_object* v___y_4944_; uint8_t v___y_4945_; lean_object* v_a_4946_; lean_object* v___y_4949_; lean_object* v___y_4950_; uint8_t v___y_4951_; lean_object* v_a_4952_; lean_object* v___y_4955_; lean_object* v___y_4956_; uint8_t v___y_4957_; lean_object* v_a_4958_; lean_object* v___y_4962_; lean_object* v___y_4963_; uint8_t v___y_4964_; lean_object* v___y_4965_; lean_object* v___y_4969_; lean_object* v___y_4970_; lean_object* v___y_4971_; lean_object* v___y_4972_; uint8_t v___y_4973_; uint8_t v___y_4974_; lean_object* v___y_4978_; lean_object* v___y_4979_; uint8_t v___y_4980_; lean_object* v___y_4981_; lean_object* v___y_4985_; lean_object* v___y_4986_; lean_object* v___y_4987_; uint8_t v___y_4988_; lean_object* v___y_4997_; lean_object* v___y_4998_; uint8_t v___y_4999_; lean_object* v_a_5000_; lean_object* v___y_5013_; uint8_t v___y_5014_; lean_object* v___y_5015_; lean_object* v_a_5016_; lean_object* v___y_5026_; lean_object* v___y_5027_; uint8_t v___y_5028_; lean_object* v_a_5029_; lean_object* v___y_5032_; lean_object* v___y_5033_; uint8_t v___y_5034_; lean_object* v_a_5035_; lean_object* v___y_5038_; uint8_t v___y_5039_; lean_object* v___y_5040_; lean_object* v_a_5041_; lean_object* v___y_5045_; lean_object* v___y_5046_; uint8_t v___y_5047_; lean_object* v___y_5048_; lean_object* v___y_5052_; lean_object* v___y_5053_; lean_object* v___y_5054_; uint8_t v___y_5055_; lean_object* v___y_5056_; uint8_t v___y_5057_; lean_object* v___y_5061_; uint8_t v___y_5062_; lean_object* v___y_5063_; lean_object* v___y_5064_; lean_object* v___y_5068_; uint8_t v___y_5069_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5080_; lean_object* v___y_5081_; uint8_t v___y_5082_; lean_object* v_a_5083_; uint8_t v___y_5096_; uint8_t v_a_5122_; 
lean_del_object(v___x_4793_);
lean_inc(v___x_4800_);
lean_inc(v_fst_4795_);
v___f_4920_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_4920_, 0, v_fst_4795_);
lean_closure_set(v___f_4920_, 1, v___x_4800_);
v___x_4921_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
if (v_hasTrace_3538_ == 0)
{
v_a_5122_ = v_hasTrace_3538_;
goto v___jp_5121_;
}
else
{
lean_object* v___x_5129_; lean_object* v___x_5130_; uint8_t v___x_5131_; 
v___x_5129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
lean_inc(v_trace_3380_);
v___x_5130_ = l_Lean_Name_append(v___x_5129_, v_trace_3380_);
v___x_5131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3537_, v_options_3536_, v___x_5130_);
lean_dec(v___x_5130_);
if (v___x_5131_ == 0)
{
v_a_5122_ = v___x_5131_;
goto v___jp_5121_;
}
else
{
lean_del_object(v___x_3418_);
v___y_5096_ = v___x_5131_;
goto v___jp_5095_;
}
}
v___jp_4922_:
{
lean_object* v___x_4927_; double v___x_4928_; double v___x_4929_; double v___x_4930_; double v___x_4931_; double v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4936_; 
v___x_4927_ = lean_io_mono_nanos_now();
v___x_4928_ = lean_float_of_nat(v___y_4924_);
v___x_4929_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_4930_ = lean_float_div(v___x_4928_, v___x_4929_);
v___x_4931_ = lean_float_of_nat(v___x_4927_);
v___x_4932_ = lean_float_div(v___x_4931_, v___x_4929_);
v___x_4933_ = lean_box_float(v___x_4930_);
v___x_4934_ = lean_box_float(v___x_4932_);
if (v_isShared_4799_ == 0)
{
lean_ctor_set(v___x_4798_, 1, v___x_4934_);
lean_ctor_set(v___x_4798_, 0, v___x_4933_);
v___x_4936_ = v___x_4798_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4933_);
lean_ctor_set(v_reuseFailAlloc_4941_, 1, v___x_4934_);
v___x_4936_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
lean_object* v___x_4938_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 1, v___x_4936_);
lean_ctor_set(v___x_3423_, 0, v_a_4926_);
v___x_4938_ = v___x_3423_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_a_4926_);
lean_ctor_set(v_reuseFailAlloc_4940_, 1, v___x_4936_);
v___x_4938_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
lean_object* v___x_4939_; 
v___x_4939_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3380_, v___x_3540_, v___x_4921_, v_options_3536_, v___y_4925_, v___y_4923_, v___f_4920_, v___x_4938_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_4939_;
}
}
}
v___jp_4942_:
{
lean_object* v___x_4947_; 
v___x_4947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4947_, 0, v_a_4946_);
v___y_4923_ = v___y_4944_;
v___y_4924_ = v___y_4943_;
v___y_4925_ = v___y_4945_;
v_a_4926_ = v___x_4947_;
goto v___jp_4922_;
}
v___jp_4948_:
{
lean_object* v___x_4953_; 
v___x_4953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4953_, 0, v_a_4952_);
v___y_4923_ = v___y_4950_;
v___y_4924_ = v___y_4949_;
v___y_4925_ = v___y_4951_;
v_a_4926_ = v___x_4953_;
goto v___jp_4922_;
}
v___jp_4954_:
{
lean_object* v___x_4959_; lean_object* v___x_4960_; 
v___x_4959_ = l_List_appendTR___redArg(v___x_4800_, v_fst_4795_);
v___x_4960_ = l_List_appendTR___redArg(v___x_4959_, v_a_4958_);
v___y_4949_ = v___y_4956_;
v___y_4950_ = v___y_4955_;
v___y_4951_ = v___y_4957_;
v_a_4952_ = v___x_4960_;
goto v___jp_4948_;
}
v___jp_4961_:
{
if (lean_obj_tag(v___y_4965_) == 0)
{
lean_object* v_a_4966_; 
v_a_4966_ = lean_ctor_get(v___y_4965_, 0);
lean_inc(v_a_4966_);
lean_dec_ref_known(v___y_4965_, 1);
v___y_4955_ = v___y_4963_;
v___y_4956_ = v___y_4962_;
v___y_4957_ = v___y_4964_;
v_a_4958_ = v_a_4966_;
goto v___jp_4954_;
}
else
{
lean_object* v_a_4967_; 
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
v_a_4967_ = lean_ctor_get(v___y_4965_, 0);
lean_inc(v_a_4967_);
lean_dec_ref_known(v___y_4965_, 1);
v___y_4943_ = v___y_4962_;
v___y_4944_ = v___y_4963_;
v___y_4945_ = v___y_4964_;
v_a_4946_ = v_a_4967_;
goto v___jp_4942_;
}
}
v___jp_4968_:
{
if (v___y_4974_ == 0)
{
lean_object* v___x_4975_; 
lean_dec_ref(v___y_4969_);
v___x_4975_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4970_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_4970_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_dec_ref_known(v___x_4975_, 1);
v___y_4955_ = v___y_4972_;
v___y_4956_ = v___y_4971_;
v___y_4957_ = v___y_4973_;
v_a_4958_ = v_snd_3421_;
goto v___jp_4954_;
}
else
{
lean_object* v_a_4976_; 
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_dec(v_snd_3421_);
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
lean_inc(v_a_4976_);
lean_dec_ref_known(v___x_4975_, 1);
v___y_4943_ = v___y_4971_;
v___y_4944_ = v___y_4972_;
v___y_4945_ = v___y_4973_;
v_a_4946_ = v_a_4976_;
goto v___jp_4942_;
}
}
else
{
lean_dec_ref(v___y_4970_);
lean_dec(v_snd_3421_);
v___y_4962_ = v___y_4971_;
v___y_4963_ = v___y_4972_;
v___y_4964_ = v___y_4973_;
v___y_4965_ = v___y_4969_;
goto v___jp_4961_;
}
}
v___jp_4977_:
{
if (lean_obj_tag(v___y_4981_) == 0)
{
lean_object* v_a_4982_; 
v_a_4982_ = lean_ctor_get(v___y_4981_, 0);
lean_inc(v_a_4982_);
lean_dec_ref_known(v___y_4981_, 1);
v___y_4949_ = v___y_4979_;
v___y_4950_ = v___y_4978_;
v___y_4951_ = v___y_4980_;
v_a_4952_ = v_a_4982_;
goto v___jp_4948_;
}
else
{
lean_object* v_a_4983_; 
v_a_4983_ = lean_ctor_get(v___y_4981_, 0);
lean_inc(v_a_4983_);
lean_dec_ref_known(v___y_4981_, 1);
v___y_4943_ = v___y_4979_;
v___y_4944_ = v___y_4978_;
v___y_4945_ = v___y_4980_;
v_a_4946_ = v_a_4983_;
goto v___jp_4942_;
}
}
v___jp_4984_:
{
uint8_t v___x_4989_; uint8_t v___x_4990_; 
v___x_4989_ = l_List_isEmpty___redArg(v_fst_4795_);
lean_dec(v_fst_4795_);
v___x_4990_ = lean_bool_not(v___x_4989_);
if (v___x_4990_ == 0)
{
lean_object* v___x_4991_; 
lean_inc(v_trace_3380_);
v___x_4991_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_4985_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4991_) == 0)
{
lean_object* v_a_4992_; lean_object* v___x_4993_; 
v_a_4992_ = lean_ctor_get(v___x_4991_, 0);
lean_inc(v_a_4992_);
lean_dec_ref_known(v___x_4991_, 1);
v___x_4993_ = l_List_appendTR___redArg(v___x_4800_, v_a_4992_);
v___y_4949_ = v___y_4987_;
v___y_4950_ = v___y_4986_;
v___y_4951_ = v___y_4988_;
v_a_4952_ = v___x_4993_;
goto v___jp_4948_;
}
else
{
lean_dec(v___x_4800_);
v___y_4978_ = v___y_4986_;
v___y_4979_ = v___y_4987_;
v___y_4980_ = v___y_4988_;
v___y_4981_ = v___x_4991_;
goto v___jp_4977_;
}
}
else
{
lean_object* v___x_4994_; lean_object* v___x_4995_; 
lean_dec(v___y_4985_);
lean_dec(v___x_4800_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_4994_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4995_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4994_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_4978_ = v___y_4986_;
v___y_4979_ = v___y_4987_;
v___y_4980_ = v___y_4988_;
v___y_4981_ = v___x_4995_;
goto v___jp_4977_;
}
}
v___jp_4996_:
{
uint8_t v_commitIndependentGoals_5001_; lean_object* v___x_5002_; 
v_commitIndependentGoals_5001_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___x_4800_);
v___x_5002_ = l_List_appendTR___redArg(v_a_5000_, v___x_4800_);
if (v_commitIndependentGoals_5001_ == 0)
{
v___y_4985_ = v___x_5002_;
v___y_4986_ = v___y_4998_;
v___y_4987_ = v___y_4997_;
v___y_4988_ = v___y_4999_;
goto v___jp_4984_;
}
else
{
uint8_t v___x_5003_; uint8_t v___x_5004_; 
v___x_5003_ = l_List_isEmpty___redArg(v___x_4800_);
v___x_5004_ = lean_bool_not(v___x_5003_);
if (v___x_5004_ == 0)
{
v___y_4985_ = v___x_5002_;
v___y_4986_ = v___y_4998_;
v___y_4987_ = v___y_4997_;
v___y_4988_ = v___y_4999_;
goto v___jp_4984_;
}
else
{
lean_object* v___x_5005_; 
v___x_5005_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5007_; 
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
lean_inc(v_a_5006_);
lean_dec_ref_known(v___x_5005_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_5007_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_5002_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_5007_) == 0)
{
lean_dec(v_a_5006_);
lean_dec(v_snd_3421_);
v___y_4962_ = v___y_4997_;
v___y_4963_ = v___y_4998_;
v___y_4964_ = v___y_4999_;
v___y_4965_ = v___x_5007_;
goto v___jp_4961_;
}
else
{
lean_object* v_a_5008_; uint8_t v___x_5009_; 
v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
lean_inc(v_a_5008_);
v___x_5009_ = l_Lean_Exception_isInterrupt(v_a_5008_);
if (v___x_5009_ == 0)
{
uint8_t v___x_5010_; 
v___x_5010_ = l_Lean_Exception_isRuntime(v_a_5008_);
v___y_4969_ = v___x_5007_;
v___y_4970_ = v_a_5006_;
v___y_4971_ = v___y_4997_;
v___y_4972_ = v___y_4998_;
v___y_4973_ = v___y_4999_;
v___y_4974_ = v___x_5010_;
goto v___jp_4968_;
}
else
{
lean_dec(v_a_5008_);
v___y_4969_ = v___x_5007_;
v___y_4970_ = v_a_5006_;
v___y_4971_ = v___y_4997_;
v___y_4972_ = v___y_4998_;
v___y_4973_ = v___y_4999_;
v___y_4974_ = v___x_5009_;
goto v___jp_4968_;
}
}
}
else
{
lean_object* v_a_5011_; 
lean_dec(v___x_5002_);
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_5011_ = lean_ctor_get(v___x_5005_, 0);
lean_inc(v_a_5011_);
lean_dec_ref_known(v___x_5005_, 1);
v___y_4943_ = v___y_4997_;
v___y_4944_ = v___y_4998_;
v___y_4945_ = v___y_4999_;
v_a_4946_ = v_a_5011_;
goto v___jp_4942_;
}
}
}
}
v___jp_5012_:
{
lean_object* v___x_5017_; double v___x_5018_; double v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; 
v___x_5017_ = lean_io_get_num_heartbeats();
v___x_5018_ = lean_float_of_nat(v___y_5015_);
v___x_5019_ = lean_float_of_nat(v___x_5017_);
v___x_5020_ = lean_box_float(v___x_5018_);
v___x_5021_ = lean_box_float(v___x_5019_);
v___x_5022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5020_);
lean_ctor_set(v___x_5022_, 1, v___x_5021_);
v___x_5023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5023_, 0, v_a_5016_);
lean_ctor_set(v___x_5023_, 1, v___x_5022_);
v___x_5024_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_3380_, v___x_3540_, v___x_4921_, v_options_3536_, v___y_5014_, v___y_5013_, v___f_4920_, v___x_5023_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_5024_;
}
v___jp_5025_:
{
lean_object* v___x_5030_; 
v___x_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5030_, 0, v_a_5029_);
v___y_5013_ = v___y_5026_;
v___y_5014_ = v___y_5028_;
v___y_5015_ = v___y_5027_;
v_a_5016_ = v___x_5030_;
goto v___jp_5012_;
}
v___jp_5031_:
{
lean_object* v___x_5036_; 
v___x_5036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5036_, 0, v_a_5035_);
v___y_5013_ = v___y_5032_;
v___y_5014_ = v___y_5034_;
v___y_5015_ = v___y_5033_;
v_a_5016_ = v___x_5036_;
goto v___jp_5012_;
}
v___jp_5037_:
{
lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5042_ = l_List_appendTR___redArg(v___x_4800_, v_fst_4795_);
v___x_5043_ = l_List_appendTR___redArg(v___x_5042_, v_a_5041_);
v___y_5032_ = v___y_5038_;
v___y_5033_ = v___y_5040_;
v___y_5034_ = v___y_5039_;
v_a_5035_ = v___x_5043_;
goto v___jp_5031_;
}
v___jp_5044_:
{
if (lean_obj_tag(v___y_5048_) == 0)
{
lean_object* v_a_5049_; 
v_a_5049_ = lean_ctor_get(v___y_5048_, 0);
lean_inc(v_a_5049_);
lean_dec_ref_known(v___y_5048_, 1);
v___y_5038_ = v___y_5045_;
v___y_5039_ = v___y_5047_;
v___y_5040_ = v___y_5046_;
v_a_5041_ = v_a_5049_;
goto v___jp_5037_;
}
else
{
lean_object* v_a_5050_; 
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
v_a_5050_ = lean_ctor_get(v___y_5048_, 0);
lean_inc(v_a_5050_);
lean_dec_ref_known(v___y_5048_, 1);
v___y_5026_ = v___y_5045_;
v___y_5027_ = v___y_5046_;
v___y_5028_ = v___y_5047_;
v_a_5029_ = v_a_5050_;
goto v___jp_5025_;
}
}
v___jp_5051_:
{
if (v___y_5057_ == 0)
{
lean_object* v___x_5058_; 
lean_dec_ref(v___y_5056_);
v___x_5058_ = l_Lean_Meta_SavedState_restore___redArg(v___y_5052_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_5052_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_dec_ref_known(v___x_5058_, 1);
v___y_5038_ = v___y_5053_;
v___y_5039_ = v___y_5055_;
v___y_5040_ = v___y_5054_;
v_a_5041_ = v_snd_3421_;
goto v___jp_5037_;
}
else
{
lean_object* v_a_5059_; 
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_dec(v_snd_3421_);
v_a_5059_ = lean_ctor_get(v___x_5058_, 0);
lean_inc(v_a_5059_);
lean_dec_ref_known(v___x_5058_, 1);
v___y_5026_ = v___y_5053_;
v___y_5027_ = v___y_5054_;
v___y_5028_ = v___y_5055_;
v_a_5029_ = v_a_5059_;
goto v___jp_5025_;
}
}
else
{
lean_dec_ref(v___y_5052_);
lean_dec(v_snd_3421_);
v___y_5045_ = v___y_5053_;
v___y_5046_ = v___y_5054_;
v___y_5047_ = v___y_5055_;
v___y_5048_ = v___y_5056_;
goto v___jp_5044_;
}
}
v___jp_5060_:
{
if (lean_obj_tag(v___y_5064_) == 0)
{
lean_object* v_a_5065_; 
v_a_5065_ = lean_ctor_get(v___y_5064_, 0);
lean_inc(v_a_5065_);
lean_dec_ref_known(v___y_5064_, 1);
v___y_5032_ = v___y_5061_;
v___y_5033_ = v___y_5063_;
v___y_5034_ = v___y_5062_;
v_a_5035_ = v_a_5065_;
goto v___jp_5031_;
}
else
{
lean_object* v_a_5066_; 
v_a_5066_ = lean_ctor_get(v___y_5064_, 0);
lean_inc(v_a_5066_);
lean_dec_ref_known(v___y_5064_, 1);
v___y_5026_ = v___y_5061_;
v___y_5027_ = v___y_5063_;
v___y_5028_ = v___y_5062_;
v_a_5029_ = v_a_5066_;
goto v___jp_5025_;
}
}
v___jp_5067_:
{
uint8_t v___x_5072_; uint8_t v___x_5073_; 
v___x_5072_ = l_List_isEmpty___redArg(v_fst_4795_);
lean_dec(v_fst_4795_);
v___x_5073_ = lean_bool_not(v___x_5072_);
if (v___x_5073_ == 0)
{
lean_object* v___x_5074_; 
lean_inc(v_trace_3380_);
v___x_5074_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_5071_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_5074_) == 0)
{
lean_object* v_a_5075_; lean_object* v___x_5076_; 
v_a_5075_ = lean_ctor_get(v___x_5074_, 0);
lean_inc(v_a_5075_);
lean_dec_ref_known(v___x_5074_, 1);
v___x_5076_ = l_List_appendTR___redArg(v___x_4800_, v_a_5075_);
v___y_5032_ = v___y_5068_;
v___y_5033_ = v___y_5070_;
v___y_5034_ = v___y_5069_;
v_a_5035_ = v___x_5076_;
goto v___jp_5031_;
}
else
{
lean_dec(v___x_4800_);
v___y_5061_ = v___y_5068_;
v___y_5062_ = v___y_5069_;
v___y_5063_ = v___y_5070_;
v___y_5064_ = v___x_5074_;
goto v___jp_5060_;
}
}
else
{
lean_object* v___x_5077_; lean_object* v___x_5078_; 
lean_dec(v___y_5071_);
lean_dec(v___x_4800_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v___x_5077_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_5078_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_5077_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_5061_ = v___y_5068_;
v___y_5062_ = v___y_5069_;
v___y_5063_ = v___y_5070_;
v___y_5064_ = v___x_5078_;
goto v___jp_5060_;
}
}
v___jp_5079_:
{
uint8_t v_commitIndependentGoals_5084_; lean_object* v___x_5085_; 
v_commitIndependentGoals_5084_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___x_4800_);
v___x_5085_ = l_List_appendTR___redArg(v_a_5083_, v___x_4800_);
if (v_commitIndependentGoals_5084_ == 0)
{
v___y_5068_ = v___y_5080_;
v___y_5069_ = v___y_5082_;
v___y_5070_ = v___y_5081_;
v___y_5071_ = v___x_5085_;
goto v___jp_5067_;
}
else
{
uint8_t v___x_5086_; uint8_t v___x_5087_; 
v___x_5086_ = l_List_isEmpty___redArg(v___x_4800_);
v___x_5087_ = lean_bool_not(v___x_5086_);
if (v___x_5087_ == 0)
{
v___y_5068_ = v___y_5080_;
v___y_5069_ = v___y_5082_;
v___y_5070_ = v___y_5081_;
v___y_5071_ = v___x_5085_;
goto v___jp_5067_;
}
else
{
lean_object* v___x_5088_; 
v___x_5088_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_5088_) == 0)
{
lean_object* v_a_5089_; lean_object* v___x_5090_; 
v_a_5089_ = lean_ctor_get(v___x_5088_, 0);
lean_inc(v_a_5089_);
lean_dec_ref_known(v___x_5088_, 1);
lean_inc(v_snd_3421_);
lean_inc(v_trace_3380_);
v___x_5090_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_5085_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_5090_) == 0)
{
lean_dec(v_a_5089_);
lean_dec(v_snd_3421_);
v___y_5045_ = v___y_5080_;
v___y_5046_ = v___y_5081_;
v___y_5047_ = v___y_5082_;
v___y_5048_ = v___x_5090_;
goto v___jp_5044_;
}
else
{
lean_object* v_a_5091_; uint8_t v___x_5092_; 
v_a_5091_ = lean_ctor_get(v___x_5090_, 0);
lean_inc(v_a_5091_);
v___x_5092_ = l_Lean_Exception_isInterrupt(v_a_5091_);
if (v___x_5092_ == 0)
{
uint8_t v___x_5093_; 
v___x_5093_ = l_Lean_Exception_isRuntime(v_a_5091_);
v___y_5052_ = v_a_5089_;
v___y_5053_ = v___y_5080_;
v___y_5054_ = v___y_5081_;
v___y_5055_ = v___y_5082_;
v___y_5056_ = v___x_5090_;
v___y_5057_ = v___x_5093_;
goto v___jp_5051_;
}
else
{
lean_dec(v_a_5091_);
v___y_5052_ = v_a_5089_;
v___y_5053_ = v___y_5080_;
v___y_5054_ = v___y_5081_;
v___y_5055_ = v___y_5082_;
v___y_5056_ = v___x_5090_;
v___y_5057_ = v___x_5092_;
goto v___jp_5051_;
}
}
}
else
{
lean_object* v_a_5094_; 
lean_dec(v___x_5085_);
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_5094_ = lean_ctor_get(v___x_5088_, 0);
lean_inc(v_a_5094_);
lean_dec_ref_known(v___x_5088_, 1);
v___y_5026_ = v___y_5080_;
v___y_5027_ = v___y_5081_;
v___y_5028_ = v___y_5082_;
v_a_5029_ = v_a_5094_;
goto v___jp_5025_;
}
}
}
}
v___jp_5095_:
{
lean_object* v___x_5097_; 
v___x_5097_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_3388_);
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_object* v_a_5098_; lean_object* v___x_5099_; uint8_t v___x_5100_; 
v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_a_5098_);
lean_dec_ref_known(v___x_5097_, 1);
v___x_5099_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5100_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3536_, v___x_5099_);
if (v___x_5100_ == 0)
{
lean_object* v___x_5101_; lean_object* v___x_5102_; 
v___x_5101_ = lean_io_mono_nanos_now();
v___x_5102_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___x_4919_, v_a_3386_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v_a_5103_; lean_object* v___x_5104_; 
v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
lean_inc(v_a_5103_);
lean_dec_ref_known(v___x_5102_, 1);
v___x_5104_ = l_List_reverse___redArg(v_a_5103_);
v___y_4997_ = v___x_5101_;
v___y_4998_ = v_a_5098_;
v___y_4999_ = v___y_5096_;
v_a_5000_ = v___x_5104_;
goto v___jp_4996_;
}
else
{
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v_a_5105_; 
v_a_5105_ = lean_ctor_get(v___x_5102_, 0);
lean_inc(v_a_5105_);
lean_dec_ref_known(v___x_5102_, 1);
v___y_4997_ = v___x_5101_;
v___y_4998_ = v_a_5098_;
v___y_4999_ = v___y_5096_;
v_a_5000_ = v_a_5105_;
goto v___jp_4996_;
}
else
{
lean_object* v_a_5106_; 
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_5106_ = lean_ctor_get(v___x_5102_, 0);
lean_inc(v_a_5106_);
lean_dec_ref_known(v___x_5102_, 1);
v___y_4943_ = v___x_5101_;
v___y_4944_ = v_a_5098_;
v___y_4945_ = v___y_5096_;
v_a_4946_ = v_a_5106_;
goto v___jp_4942_;
}
}
}
else
{
lean_object* v___x_5107_; lean_object* v___x_5108_; 
lean_del_object(v___x_4798_);
lean_del_object(v___x_3423_);
v___x_5107_ = lean_io_get_num_heartbeats();
v___x_5108_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___x_4919_, v_a_3386_);
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5109_; lean_object* v___x_5110_; 
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5109_);
lean_dec_ref_known(v___x_5108_, 1);
v___x_5110_ = l_List_reverse___redArg(v_a_5109_);
v___y_5080_ = v_a_5098_;
v___y_5081_ = v___x_5107_;
v___y_5082_ = v___y_5096_;
v_a_5083_ = v___x_5110_;
goto v___jp_5079_;
}
else
{
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5111_; 
v_a_5111_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5111_);
lean_dec_ref_known(v___x_5108_, 1);
v___y_5080_ = v_a_5098_;
v___y_5081_ = v___x_5107_;
v___y_5082_ = v___y_5096_;
v_a_5083_ = v_a_5111_;
goto v___jp_5079_;
}
else
{
lean_object* v_a_5112_; 
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec_ref(v_cfg_3379_);
v_a_5112_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5112_);
lean_dec_ref_known(v___x_5108_, 1);
v___y_5026_ = v_a_5098_;
v___y_5027_ = v___x_5107_;
v___y_5028_ = v___y_5096_;
v_a_5029_ = v_a_5112_;
goto v___jp_5025_;
}
}
}
}
else
{
lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5120_; 
lean_dec_ref(v___f_4920_);
lean_dec(v___x_4800_);
lean_del_object(v___x_4798_);
lean_dec(v_fst_4795_);
lean_del_object(v___x_3423_);
lean_dec(v_snd_3421_);
lean_dec(v_goals_3383_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v_a_5113_ = lean_ctor_get(v___x_5097_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5115_ = v___x_5097_;
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_dec(v___x_5097_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_a_5113_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
return v___x_5118_;
}
}
}
}
v___jp_5121_:
{
lean_object* v___x_5123_; uint8_t v___x_5124_; 
v___x_5123_ = l_Lean_trace_profiler;
v___x_5124_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_3536_, v___x_5123_);
if (v___x_5124_ == 0)
{
lean_object* v___x_5125_; 
lean_dec_ref(v___f_4920_);
lean_del_object(v___x_4798_);
lean_del_object(v___x_3423_);
v___x_5125_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___x_4919_, v_a_3386_);
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5126_; lean_object* v___x_5127_; 
v_a_5126_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5126_);
lean_dec_ref_known(v___x_5125_, 1);
v___x_5127_ = l_List_reverse___redArg(v_a_5126_);
v_a_4900_ = v___x_5127_;
goto v___jp_4899_;
}
else
{
if (lean_obj_tag(v___x_5125_) == 0)
{
lean_object* v_a_5128_; 
v_a_5128_ = lean_ctor_get(v___x_5125_, 0);
lean_inc(v_a_5128_);
lean_dec_ref_known(v___x_5125_, 1);
v_a_4900_ = v_a_5128_;
goto v___jp_4899_;
}
else
{
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_dec(v_snd_3421_);
lean_del_object(v___x_3418_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
return v___x_5125_;
}
}
}
else
{
lean_del_object(v___x_3418_);
v___y_5096_ = v_a_5122_;
goto v___jp_5095_;
}
}
}
else
{
lean_object* v___x_5132_; 
lean_del_object(v___x_4798_);
lean_del_object(v___x_3423_);
lean_del_object(v___x_3418_);
v___x_5132_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_goals_3383_, v___x_4919_, v_a_3386_);
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_a_5133_; lean_object* v___x_5134_; 
v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_a_5133_);
lean_dec_ref_known(v___x_5132_, 1);
v___x_5134_ = l_List_reverse___redArg(v_a_5133_);
v_a_4841_ = v___x_5134_;
goto v___jp_4840_;
}
else
{
if (lean_obj_tag(v___x_5132_) == 0)
{
lean_object* v_a_5135_; 
v_a_5135_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5132_, 1);
v_a_4841_ = v_a_5135_;
goto v___jp_4840_;
}
else
{
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_del_object(v___x_4793_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
return v___x_5132_;
}
}
}
v___jp_4801_:
{
uint8_t v___x_4803_; uint8_t v___x_4804_; 
v___x_4803_ = l_List_isEmpty___redArg(v_fst_4795_);
lean_dec(v_fst_4795_);
v___x_4804_ = lean_bool_not(v___x_4803_);
if (v___x_4804_ == 0)
{
lean_object* v___x_4805_; 
v___x_4805_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_4802_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4805_) == 0)
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4814_; 
v_a_4806_ = lean_ctor_get(v___x_4805_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4808_ = v___x_4805_;
v_isShared_4809_ = v_isSharedCheck_4814_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4805_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4814_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4810_; lean_object* v___x_4812_; 
v___x_4810_ = l_List_appendTR___redArg(v___x_4800_, v_a_4806_);
if (v_isShared_4809_ == 0)
{
lean_ctor_set(v___x_4808_, 0, v___x_4810_);
v___x_4812_ = v___x_4808_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4810_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
else
{
lean_dec(v___x_4800_);
return v___x_4805_;
}
}
else
{
lean_object* v___x_4815_; lean_object* v___x_4816_; 
lean_dec(v___y_4802_);
lean_dec(v___x_4800_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v___x_4815_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4816_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4815_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_4816_;
}
}
v___jp_4817_:
{
lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4822_; 
v___x_4819_ = l_List_appendTR___redArg(v___x_4800_, v_fst_4795_);
v___x_4820_ = l_List_appendTR___redArg(v___x_4819_, v_a_4818_);
if (v_isShared_4794_ == 0)
{
lean_ctor_set(v___x_4793_, 0, v___x_4820_);
v___x_4822_ = v___x_4793_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4820_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
v___jp_4824_:
{
if (lean_obj_tag(v___y_4825_) == 0)
{
lean_object* v_a_4826_; 
v_a_4826_ = lean_ctor_get(v___y_4825_, 0);
lean_inc(v_a_4826_);
lean_dec_ref_known(v___y_4825_, 1);
v_a_4818_ = v_a_4826_;
goto v___jp_4817_;
}
else
{
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_del_object(v___x_4793_);
return v___y_4825_;
}
}
v___jp_4827_:
{
if (v___y_4830_ == 0)
{
lean_object* v___x_4831_; 
lean_dec_ref(v___y_4828_);
v___x_4831_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4829_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_4829_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_dec_ref_known(v___x_4831_, 1);
v_a_4818_ = v_snd_3421_;
goto v___jp_4817_;
}
else
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4839_; 
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_del_object(v___x_4793_);
lean_dec(v_snd_3421_);
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4834_ = v___x_4831_;
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4831_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4837_; 
if (v_isShared_4835_ == 0)
{
v___x_4837_ = v___x_4834_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
return v___x_4837_;
}
}
}
}
else
{
lean_dec_ref(v___y_4829_);
lean_dec(v_snd_3421_);
v___y_4825_ = v___y_4828_;
goto v___jp_4824_;
}
}
v___jp_4840_:
{
uint8_t v_commitIndependentGoals_4842_; lean_object* v___x_4843_; 
v_commitIndependentGoals_4842_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___x_4800_);
v___x_4843_ = l_List_appendTR___redArg(v_a_4841_, v___x_4800_);
if (v_commitIndependentGoals_4842_ == 0)
{
lean_del_object(v___x_4793_);
v___y_4802_ = v___x_4843_;
goto v___jp_4801_;
}
else
{
uint8_t v___x_4844_; uint8_t v___x_4845_; 
v___x_4844_ = l_List_isEmpty___redArg(v___x_4800_);
v___x_4845_ = lean_bool_not(v___x_4844_);
if (v___x_4845_ == 0)
{
lean_del_object(v___x_4793_);
v___y_4802_ = v___x_4843_;
goto v___jp_4801_;
}
else
{
lean_object* v___x_4846_; 
v___x_4846_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_a_4847_; lean_object* v___x_4848_; 
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
lean_inc(v_a_4847_);
lean_dec_ref_known(v___x_4846_, 1);
lean_inc(v_snd_3421_);
v___x_4848_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_4843_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_dec(v_a_4847_);
lean_dec(v_snd_3421_);
v___y_4825_ = v___x_4848_;
goto v___jp_4824_;
}
else
{
lean_object* v_a_4849_; uint8_t v___x_4850_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
lean_inc(v_a_4849_);
v___x_4850_ = l_Lean_Exception_isInterrupt(v_a_4849_);
if (v___x_4850_ == 0)
{
uint8_t v___x_4851_; 
v___x_4851_ = l_Lean_Exception_isRuntime(v_a_4849_);
v___y_4828_ = v___x_4848_;
v___y_4829_ = v_a_4847_;
v___y_4830_ = v___x_4851_;
goto v___jp_4827_;
}
else
{
lean_dec(v_a_4849_);
v___y_4828_ = v___x_4848_;
v___y_4829_ = v_a_4847_;
v___y_4830_ = v___x_4850_;
goto v___jp_4827_;
}
}
}
else
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4859_; 
lean_dec(v___x_4843_);
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_del_object(v___x_4793_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v_a_4852_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4854_ = v___x_4846_;
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4846_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v___x_4857_; 
if (v_isShared_4855_ == 0)
{
v___x_4857_ = v___x_4854_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
}
}
}
v___jp_4860_:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4865_; 
v___x_4862_ = l_List_appendTR___redArg(v___x_4800_, v_fst_4795_);
v___x_4863_ = l_List_appendTR___redArg(v___x_4862_, v_a_4861_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_4863_);
v___x_4865_ = v___x_3418_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v___x_4863_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
v___jp_4867_:
{
if (lean_obj_tag(v___y_4868_) == 0)
{
lean_object* v_a_4869_; 
v_a_4869_ = lean_ctor_get(v___y_4868_, 0);
lean_inc(v_a_4869_);
lean_dec_ref_known(v___y_4868_, 1);
v_a_4861_ = v_a_4869_;
goto v___jp_4860_;
}
else
{
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_del_object(v___x_3418_);
return v___y_4868_;
}
}
v___jp_4870_:
{
if (v___y_4873_ == 0)
{
lean_object* v___x_4874_; 
lean_dec_ref(v___y_4872_);
v___x_4874_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4871_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_4871_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_dec_ref_known(v___x_4874_, 1);
v_a_4861_ = v_snd_3421_;
goto v___jp_4860_;
}
else
{
lean_object* v_a_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4882_; 
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_dec(v_snd_3421_);
lean_del_object(v___x_3418_);
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4877_ = v___x_4874_;
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_a_4875_);
lean_dec(v___x_4874_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v___x_4880_; 
if (v_isShared_4878_ == 0)
{
v___x_4880_ = v___x_4877_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_a_4875_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
}
}
else
{
lean_dec_ref(v___y_4871_);
lean_dec(v_snd_3421_);
v___y_4868_ = v___y_4872_;
goto v___jp_4867_;
}
}
v___jp_4883_:
{
uint8_t v___x_4885_; uint8_t v___x_4886_; 
v___x_4885_ = l_List_isEmpty___redArg(v_fst_4795_);
lean_dec(v_fst_4795_);
v___x_4886_ = lean_bool_not(v___x_4885_);
if (v___x_4886_ == 0)
{
lean_object* v___x_4887_; 
v___x_4887_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_4884_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4896_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4890_ = v___x_4887_;
v_isShared_4891_ = v_isSharedCheck_4896_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4887_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4896_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4892_; lean_object* v___x_4894_; 
v___x_4892_ = l_List_appendTR___redArg(v___x_4800_, v_a_4888_);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 0, v___x_4892_);
v___x_4894_ = v___x_4890_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4892_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
}
else
{
lean_dec(v___x_4800_);
return v___x_4887_;
}
}
else
{
lean_object* v___x_4897_; lean_object* v___x_4898_; 
lean_dec(v___y_4884_);
lean_dec(v___x_4800_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v___x_4897_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_4898_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_4897_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_4898_;
}
}
v___jp_4899_:
{
uint8_t v_commitIndependentGoals_4901_; lean_object* v___x_4902_; 
v_commitIndependentGoals_4901_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___x_4800_);
v___x_4902_ = l_List_appendTR___redArg(v_a_4900_, v___x_4800_);
if (v_commitIndependentGoals_4901_ == 0)
{
lean_del_object(v___x_3418_);
v___y_4884_ = v___x_4902_;
goto v___jp_4883_;
}
else
{
uint8_t v___x_4903_; uint8_t v___x_4904_; 
v___x_4903_ = l_List_isEmpty___redArg(v___x_4800_);
v___x_4904_ = lean_bool_not(v___x_4903_);
if (v___x_4904_ == 0)
{
lean_del_object(v___x_3418_);
v___y_4884_ = v___x_4902_;
goto v___jp_4883_;
}
else
{
lean_object* v___x_4905_; 
v___x_4905_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_4905_) == 0)
{
lean_object* v_a_4906_; lean_object* v___x_4907_; 
v_a_4906_ = lean_ctor_get(v___x_4905_, 0);
lean_inc(v_a_4906_);
lean_dec_ref_known(v___x_4905_, 1);
lean_inc(v_snd_3421_);
v___x_4907_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_4902_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_dec(v_a_4906_);
lean_dec(v_snd_3421_);
v___y_4868_ = v___x_4907_;
goto v___jp_4867_;
}
else
{
lean_object* v_a_4908_; uint8_t v___x_4909_; 
v_a_4908_ = lean_ctor_get(v___x_4907_, 0);
lean_inc(v_a_4908_);
v___x_4909_ = l_Lean_Exception_isInterrupt(v_a_4908_);
if (v___x_4909_ == 0)
{
uint8_t v___x_4910_; 
v___x_4910_ = l_Lean_Exception_isRuntime(v_a_4908_);
v___y_4871_ = v_a_4906_;
v___y_4872_ = v___x_4907_;
v___y_4873_ = v___x_4910_;
goto v___jp_4870_;
}
else
{
lean_dec(v_a_4908_);
v___y_4871_ = v_a_4906_;
v___y_4872_ = v___x_4907_;
v___y_4873_ = v___x_4909_;
goto v___jp_4870_;
}
}
}
else
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4918_; 
lean_dec(v___x_4902_);
lean_dec(v___x_4800_);
lean_dec(v_fst_4795_);
lean_dec(v_snd_3421_);
lean_del_object(v___x_3418_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v_a_4911_ = lean_ctor_get(v___x_4905_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4913_ = v___x_4905_;
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4905_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4916_; 
if (v_isShared_4914_ == 0)
{
v___x_4916_ = v___x_4913_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4911_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5145_; 
lean_del_object(v___x_3423_);
lean_dec(v_snd_3421_);
lean_del_object(v___x_3418_);
lean_dec(v_goals_3383_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v_a_5138_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5140_ = v___x_4790_;
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_4790_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5143_; 
if (v_isShared_5141_ == 0)
{
v___x_5143_ = v___x_5140_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
}
}
else
{
lean_object* v_maxDepth_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
lean_del_object(v___x_3423_);
lean_dec(v_snd_3421_);
lean_dec(v_fst_3420_);
lean_del_object(v___x_3418_);
lean_dec(v_goals_3383_);
v_maxDepth_5146_ = lean_ctor_get(v_cfg_3379_, 0);
lean_inc(v_maxDepth_5146_);
v___x_5147_ = lean_box(0);
v___x_5148_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v_maxDepth_5146_, v_remaining_3384_, v___x_5147_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_5148_;
}
v___jp_3425_:
{
if (v___y_3430_ == 0)
{
lean_object* v___x_3431_; 
lean_dec_ref(v___y_3426_);
v___x_3431_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3428_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_3428_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_dec_ref_known(v___x_3431_, 1);
v___y_3391_ = v___y_3427_;
v___y_3392_ = v___y_3429_;
v_a_3393_ = v_snd_3421_;
goto v___jp_3390_;
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec(v___y_3429_);
lean_dec(v___y_3427_);
lean_dec(v_snd_3421_);
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
else
{
lean_dec_ref(v___y_3428_);
lean_dec(v_snd_3421_);
v___y_3398_ = v___y_3427_;
v___y_3399_ = v___y_3429_;
v___y_3400_ = v___y_3426_;
goto v___jp_3397_;
}
}
v___jp_3440_:
{
uint8_t v___x_3444_; uint8_t v___x_3445_; 
v___x_3444_ = l_List_isEmpty___redArg(v___y_3443_);
lean_dec(v___y_3443_);
v___x_3445_ = lean_bool_not(v___x_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; 
v___x_3446_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_3442_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3455_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3449_ = v___x_3446_;
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3446_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3451_ = l_List_appendTR___redArg(v___y_3441_, v_a_3447_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3451_);
v___x_3453_ = v___x_3449_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
else
{
lean_dec(v___y_3441_);
return v___x_3446_;
}
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v___x_3456_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3457_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3456_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_3457_;
}
}
v___jp_3458_:
{
uint8_t v_commitIndependentGoals_3462_; lean_object* v___x_3463_; 
v_commitIndependentGoals_3462_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_3459_);
v___x_3463_ = l_List_appendTR___redArg(v_a_3461_, v___y_3459_);
if (v_commitIndependentGoals_3462_ == 0)
{
v___y_3441_ = v___y_3459_;
v___y_3442_ = v___x_3463_;
v___y_3443_ = v___y_3460_;
goto v___jp_3440_;
}
else
{
uint8_t v___x_3464_; uint8_t v___x_3465_; 
v___x_3464_ = l_List_isEmpty___redArg(v___y_3459_);
v___x_3465_ = lean_bool_not(v___x_3464_);
if (v___x_3465_ == 0)
{
v___y_3441_ = v___y_3459_;
v___y_3442_ = v___x_3463_;
v___y_3443_ = v___y_3460_;
goto v___jp_3440_;
}
else
{
lean_object* v___x_3466_; 
v___x_3466_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3468_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3467_);
lean_dec_ref_known(v___x_3466_, 1);
lean_inc(v_snd_3421_);
v___x_3468_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_3463_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_dec(v_a_3467_);
lean_dec(v_snd_3421_);
v___y_3398_ = v___y_3459_;
v___y_3399_ = v___y_3460_;
v___y_3400_ = v___x_3468_;
goto v___jp_3397_;
}
else
{
lean_object* v_a_3469_; uint8_t v___x_3470_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_a_3469_);
v___x_3470_ = l_Lean_Exception_isInterrupt(v_a_3469_);
if (v___x_3470_ == 0)
{
uint8_t v___x_3471_; 
v___x_3471_ = l_Lean_Exception_isRuntime(v_a_3469_);
v___y_3426_ = v___x_3468_;
v___y_3427_ = v___y_3459_;
v___y_3428_ = v_a_3467_;
v___y_3429_ = v___y_3460_;
v___y_3430_ = v___x_3471_;
goto v___jp_3425_;
}
else
{
lean_dec(v_a_3469_);
v___y_3426_ = v___x_3468_;
v___y_3427_ = v___y_3459_;
v___y_3428_ = v_a_3467_;
v___y_3429_ = v___y_3460_;
v___y_3430_ = v___x_3470_;
goto v___jp_3425_;
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec(v___x_3463_);
lean_dec(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v_a_3472_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3466_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3466_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
}
}
v___jp_3480_:
{
if (v___y_3485_ == 0)
{
lean_object* v___x_3486_; 
lean_dec_ref(v___y_3482_);
v___x_3486_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3483_, v_a_3386_, v_a_3388_);
lean_dec_ref(v___y_3483_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_dec_ref_known(v___x_3486_, 1);
v___y_3403_ = v___y_3481_;
v___y_3404_ = v___y_3484_;
v_a_3405_ = v_snd_3421_;
goto v___jp_3402_;
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec(v___y_3484_);
lean_dec(v___y_3481_);
lean_dec(v_snd_3421_);
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_dec_ref(v___y_3483_);
lean_dec(v_snd_3421_);
v___y_3410_ = v___y_3481_;
v___y_3411_ = v___y_3484_;
v___y_3412_ = v___y_3482_;
goto v___jp_3409_;
}
}
v___jp_3495_:
{
uint8_t v___x_3499_; uint8_t v___x_3500_; 
v___x_3499_ = l_List_isEmpty___redArg(v___y_3498_);
lean_dec(v___y_3498_);
v___x_3500_ = lean_bool_not(v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
v___x_3501_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___y_3497_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3510_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3510_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3510_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
v___x_3506_ = l_List_appendTR___redArg(v___y_3496_, v_a_3502_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v___x_3506_);
v___x_3508_ = v___x_3504_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
else
{
lean_dec(v___y_3496_);
return v___x_3501_;
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v___x_3511_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3512_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3511_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
return v___x_3512_;
}
}
v___jp_3513_:
{
uint8_t v_commitIndependentGoals_3517_; lean_object* v___x_3518_; 
v_commitIndependentGoals_3517_ = lean_ctor_get_uint8(v_cfg_3379_, sizeof(void*)*4);
lean_inc(v___y_3514_);
v___x_3518_ = l_List_appendTR___redArg(v_a_3516_, v___y_3514_);
if (v_commitIndependentGoals_3517_ == 0)
{
v___y_3496_ = v___y_3514_;
v___y_3497_ = v___x_3518_;
v___y_3498_ = v___y_3515_;
goto v___jp_3495_;
}
else
{
uint8_t v___x_3519_; uint8_t v___x_3520_; 
v___x_3519_ = l_List_isEmpty___redArg(v___y_3514_);
v___x_3520_ = lean_bool_not(v___x_3519_);
if (v___x_3520_ == 0)
{
v___y_3496_ = v___y_3514_;
v___y_3497_ = v___x_3518_;
v___y_3498_ = v___y_3515_;
goto v___jp_3495_;
}
else
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_Meta_saveState___redArg(v_a_3386_, v_a_3388_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3523_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
lean_inc(v_snd_3421_);
v___x_3523_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3379_, v_trace_3380_, v_next_3381_, v_orig_3382_, v___x_3518_, v_snd_3421_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_dec(v_a_3522_);
lean_dec(v_snd_3421_);
v___y_3410_ = v___y_3514_;
v___y_3411_ = v___y_3515_;
v___y_3412_ = v___x_3523_;
goto v___jp_3409_;
}
else
{
lean_object* v_a_3524_; uint8_t v___x_3525_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
v___x_3525_ = l_Lean_Exception_isInterrupt(v_a_3524_);
if (v___x_3525_ == 0)
{
uint8_t v___x_3526_; 
v___x_3526_ = l_Lean_Exception_isRuntime(v_a_3524_);
v___y_3481_ = v___y_3514_;
v___y_3482_ = v___x_3523_;
v___y_3483_ = v_a_3522_;
v___y_3484_ = v___y_3515_;
v___y_3485_ = v___x_3526_;
goto v___jp_3480_;
}
else
{
lean_dec(v_a_3524_);
v___y_3481_ = v___y_3514_;
v___y_3482_ = v___x_3523_;
v___y_3483_ = v_a_3522_;
v___y_3484_ = v___y_3515_;
v___y_3485_ = v___x_3525_;
goto v___jp_3480_;
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec(v___x_3518_);
lean_dec(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec(v_snd_3421_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v_a_3527_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3521_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3521_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_5151_; lean_object* v___x_5153_; uint8_t v_isShared_5154_; uint8_t v_isSharedCheck_5158_; 
lean_dec(v_remaining_3384_);
lean_dec(v_goals_3383_);
lean_dec(v_orig_3382_);
lean_dec_ref(v_next_3381_);
lean_dec(v_trace_3380_);
lean_dec_ref(v_cfg_3379_);
v_a_5151_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5153_ = v___x_3415_;
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
else
{
lean_inc(v_a_5151_);
lean_dec(v___x_3415_);
v___x_5153_ = lean_box(0);
v_isShared_5154_ = v_isSharedCheck_5158_;
goto v_resetjp_5152_;
}
v_resetjp_5152_:
{
lean_object* v___x_5156_; 
if (v_isShared_5154_ == 0)
{
v___x_5156_ = v___x_5153_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5151_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
return v___x_5156_;
}
}
}
v___jp_3390_:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = l_List_appendTR___redArg(v___y_3391_, v___y_3392_);
v___x_3395_ = l_List_appendTR___redArg(v___x_3394_, v_a_3393_);
v___x_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
return v___x_3396_;
}
v___jp_3397_:
{
if (lean_obj_tag(v___y_3400_) == 0)
{
lean_object* v_a_3401_; 
v_a_3401_ = lean_ctor_get(v___y_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___y_3400_, 1);
v___y_3391_ = v___y_3398_;
v___y_3392_ = v___y_3399_;
v_a_3393_ = v_a_3401_;
goto v___jp_3390_;
}
else
{
lean_dec(v___y_3399_);
lean_dec(v___y_3398_);
return v___y_3400_;
}
}
v___jp_3402_:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3406_ = l_List_appendTR___redArg(v___y_3403_, v___y_3404_);
v___x_3407_ = l_List_appendTR___redArg(v___x_3406_, v_a_3405_);
v___x_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
return v___x_3408_;
}
v___jp_3409_:
{
if (lean_obj_tag(v___y_3412_) == 0)
{
lean_object* v_a_3413_; 
v_a_3413_ = lean_ctor_get(v___y_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___y_3412_, 1);
v___y_3403_ = v___y_3410_;
v___y_3404_ = v___y_3411_;
v_a_3405_ = v_a_3413_;
goto v___jp_3402_;
}
else
{
lean_dec(v___y_3411_);
lean_dec(v___y_3410_);
return v___y_3412_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_5159_, lean_object* v_trace_5160_, lean_object* v_next_5161_, lean_object* v_orig_5162_, lean_object* v_goals_5163_, lean_object* v_remaining_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_, lean_object* v_a_5169_){
_start:
{
lean_object* v_res_5170_; 
v_res_5170_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_5159_, v_trace_5160_, v_next_5161_, v_orig_5162_, v_goals_5163_, v_remaining_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
lean_dec(v_a_5168_);
lean_dec_ref(v_a_5167_);
lean_dec(v_a_5166_);
lean_dec_ref(v_a_5165_);
return v_res_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_5171_, lean_object* v_00_u03b2_5172_, lean_object* v_L_5173_, lean_object* v_f_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_){
_start:
{
lean_object* v___x_5180_; 
v___x_5180_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_5173_, v_f_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_);
return v___x_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_5181_, lean_object* v_00_u03b2_5182_, lean_object* v_L_5183_, lean_object* v_f_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_){
_start:
{
lean_object* v_res_5190_; 
v_res_5190_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_5181_, v_00_u03b2_5182_, v_L_5183_, v_f_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
return v_res_5190_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(lean_object* v_x_5191_, lean_object* v_x_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_){
_start:
{
lean_object* v___x_5198_; 
v___x_5198_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v_x_5191_, v_x_5192_, v___y_5194_);
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v_x_5199_, lean_object* v_x_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v_x_5199_, v_x_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_5207_, lean_object* v_00_u03b2_5208_, lean_object* v_f_5209_, lean_object* v_x_5210_, lean_object* v_x_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
lean_object* v___x_5217_; 
v___x_5217_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_5209_, v_x_5210_, v_x_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_);
return v___x_5217_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_5218_, lean_object* v_00_u03b2_5219_, lean_object* v_f_5220_, lean_object* v_x_5221_, lean_object* v_x_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
lean_object* v_res_5228_; 
v_res_5228_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_5218_, v_00_u03b2_5219_, v_f_5220_, v_x_5221_, v_x_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_);
lean_dec(v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
return v_res_5228_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_5229_, lean_object* v_00_u03b2_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_5231_, v_a_5232_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_5234_, lean_object* v_00_u03b2_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_){
_start:
{
lean_object* v___x_5238_; 
v___x_5238_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_5236_, v_a_5237_);
return v___x_5238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_5239_, lean_object* v_g_5240_, lean_object* v_f_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v___x_5247_; 
lean_inc(v___y_5245_);
lean_inc_ref(v___y_5244_);
lean_inc(v___y_5243_);
lean_inc_ref(v___y_5242_);
v___x_5247_ = lean_apply_6(v_next_5239_, v_g_5240_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, lean_box(0));
if (lean_obj_tag(v___x_5247_) == 0)
{
lean_object* v_a_5248_; lean_object* v___x_5249_; 
v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
lean_inc(v_a_5248_);
lean_dec_ref_known(v___x_5247_, 1);
v___x_5249_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_5248_, v_f_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_);
return v___x_5249_;
}
else
{
lean_object* v_a_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5257_; 
lean_dec_ref(v_f_5241_);
v_a_5250_ = lean_ctor_get(v___x_5247_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5247_);
if (v_isSharedCheck_5257_ == 0)
{
v___x_5252_ = v___x_5247_;
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_a_5250_);
lean_dec(v___x_5247_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5257_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v___x_5255_; 
if (v_isShared_5253_ == 0)
{
v___x_5255_ = v___x_5252_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_a_5250_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_5258_, lean_object* v_g_5259_, lean_object* v_f_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_){
_start:
{
lean_object* v_res_5266_; 
v_res_5266_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_5258_, v_g_5259_, v_f_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_);
lean_dec(v___y_5264_);
lean_dec_ref(v___y_5263_);
lean_dec(v___y_5262_);
lean_dec_ref(v___y_5261_);
return v_res_5266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_5267_, lean_object* v_trace_5268_, lean_object* v_next_5269_, lean_object* v_goals_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_){
_start:
{
lean_object* v_resolve_5276_; lean_object* v___x_5277_; 
v_resolve_5276_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_5276_, 0, v_next_5269_);
lean_inc_n(v_goals_5270_, 2);
v___x_5277_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_5267_, v_trace_5268_, v_resolve_5276_, v_goals_5270_, v_goals_5270_, v_goals_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_);
return v___x_5277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_5278_, lean_object* v_trace_5279_, lean_object* v_next_5280_, lean_object* v_goals_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_){
_start:
{
lean_object* v_res_5287_; 
v_res_5287_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_5278_, v_trace_5279_, v_next_5280_, v_goals_5281_, v_a_5282_, v_a_5283_, v_a_5284_, v_a_5285_);
lean_dec(v_a_5285_);
lean_dec_ref(v_a_5284_);
lean_dec(v_a_5283_);
lean_dec_ref(v_a_5282_);
return v_res_5287_;
}
}
lean_object* runtime_initialize_Lean_Meta_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_IndependentOf(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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

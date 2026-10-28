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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 35, .m_data = "⏬ discharger generated new subgoals"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 42, .m_data = "⏭️ deemed acceptable, returning as subgoal"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 45, .m_data = "⏸️ suspending search and returning as subgoal"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "working on: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_275_; 
v_a_245_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_275_ == 0)
{
v___x_247_ = v___x_235_;
v_isShared_248_ = v_isSharedCheck_275_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_235_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_275_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
uint8_t v___x_249_; 
v___x_249_ = l_Lean_Exception_isInterrupt(v_a_245_);
if (v___x_249_ == 0)
{
uint8_t v___x_250_; 
lean_inc(v_a_245_);
v___x_250_ = l_Lean_Exception_isRuntime(v_a_245_);
if (v___x_250_ == 0)
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
else
{
lean_object* v___x_273_; 
lean_dec(v_a_234_);
if (v_isShared_248_ == 0)
{
v___x_273_ = v___x_247_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_245_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_x_227_);
v_a_276_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_233_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_233_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___boxed(lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v_x_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object* v_00_u03b1_291_, lean_object* v_x_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v_x_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object* v_00_u03b1_299_, lean_object* v_x_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(v_00_u03b1_299_, v_x_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(lean_object* v_msgData_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; lean_object* v_env_314_; uint8_t v___x_315_; lean_object* v_env_316_; lean_object* v___x_317_; lean_object* v_toCold_318_; lean_object* v_mctx_319_; lean_object* v_lctx_320_; lean_object* v_options_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_313_ = lean_st_ref_get(v___y_311_);
v_env_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_env_314_);
lean_dec(v___x_313_);
v___x_315_ = 0;
v_env_316_ = l_Lean_Environment_setRecordingDeps(v_env_314_, v___x_315_);
v___x_317_ = lean_st_ref_get(v___y_309_);
v_toCold_318_ = lean_ctor_get(v___y_310_, 0);
v_mctx_319_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_mctx_319_);
lean_dec(v___x_317_);
v_lctx_320_ = lean_ctor_get(v___y_308_, 2);
v_options_321_ = lean_ctor_get(v_toCold_318_, 2);
lean_inc_ref(v_options_321_);
lean_inc_ref(v_lctx_320_);
v___x_322_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_322_, 0, v_env_316_);
lean_ctor_set(v___x_322_, 1, v_mctx_319_);
lean_ctor_set(v___x_322_, 2, v_lctx_320_);
lean_ctor_set(v___x_322_, 3, v_options_321_);
v___x_323_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_msgData_307_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___boxed(lean_object* v_msgData_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msgData_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_331_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0));
v___x_334_ = l_Lean_stringToMessageData(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object* v_x_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object* v_x_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(v_x_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec_ref(v_x_343_);
return v_res_349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0));
v___x_352_ = l_Lean_stringToMessageData(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object* v_x_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object* v_x_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(v_x_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec_ref(v_x_361_);
return v_res_367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0));
v___x_370_ = l_Lean_stringToMessageData(v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* v_x_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* v_x_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(v_x_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec_ref(v_x_379_);
return v_res_385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object* v_x_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object* v_x_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(v_x_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec_ref(v_x_397_);
return v_res_403_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0));
v___x_406_ = l_Lean_stringToMessageData(v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object* v_head_407_, lean_object* v_x_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_425_; 
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v_head_407_);
v___x_415_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v___x_414_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_425_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1);
v___x_421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v_a_416_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_421_);
v___x_423_ = v___x_418_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object* v_head_426_, lean_object* v_x_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(v_head_426_, v_x_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec_ref(v_x_427_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(lean_object* v_opts_434_, lean_object* v_opt_435_){
_start:
{
lean_object* v_name_436_; lean_object* v_defValue_437_; lean_object* v_map_438_; lean_object* v___x_439_; 
v_name_436_ = lean_ctor_get(v_opt_435_, 0);
v_defValue_437_ = lean_ctor_get(v_opt_435_, 1);
v_map_438_ = lean_ctor_get(v_opts_434_, 0);
v___x_439_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_438_, v_name_436_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_inc(v_defValue_437_);
return v_defValue_437_;
}
else
{
lean_object* v_val_440_; 
v_val_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v___x_439_, 1);
if (lean_obj_tag(v_val_440_) == 3)
{
lean_object* v_v_441_; 
v_v_441_ = lean_ctor_get(v_val_440_, 0);
lean_inc(v_v_441_);
lean_dec_ref_known(v_val_440_, 1);
return v_v_441_;
}
else
{
lean_dec(v_val_440_);
lean_inc(v_defValue_437_);
return v_defValue_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6___boxed(lean_object* v_opts_442_, lean_object* v_opt_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_442_, v_opt_443_);
lean_dec_ref(v_opt_443_);
lean_dec_ref(v_opts_442_);
return v_res_444_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(lean_object* v_e_445_){
_start:
{
if (lean_obj_tag(v_e_445_) == 0)
{
uint8_t v___x_446_; 
v___x_446_ = 2;
return v___x_446_;
}
else
{
lean_object* v_a_447_; 
v_a_447_ = lean_ctor_get(v_e_445_, 0);
if (lean_obj_tag(v_a_447_) == 0)
{
uint8_t v___x_448_; 
v___x_448_ = 1;
return v___x_448_;
}
else
{
uint8_t v___x_449_; 
v___x_449_ = 0;
return v___x_449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12___boxed(lean_object* v_e_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_e_450_);
lean_dec_ref(v_e_450_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(lean_object* v_x_453_){
_start:
{
if (lean_obj_tag(v_x_453_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_455_ = lean_ctor_get(v_x_453_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_x_453_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v_x_453_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v_x_453_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
lean_ctor_set_tag(v___x_457_, 1);
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
v_a_463_ = lean_ctor_get(v_x_453_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v_x_453_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v_x_453_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v_x_453_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set_tag(v___x_465_, 0);
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg___boxed(lean_object* v_x_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(size_t v_sz_474_, size_t v_i_475_, lean_object* v_bs_476_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = lean_usize_dec_lt(v_i_475_, v_sz_474_);
if (v___x_477_ == 0)
{
return v_bs_476_;
}
else
{
lean_object* v_v_478_; lean_object* v_msg_479_; lean_object* v___x_480_; lean_object* v_bs_x27_481_; size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
v_v_478_ = lean_array_uget_borrowed(v_bs_476_, v_i_475_);
v_msg_479_ = lean_ctor_get(v_v_478_, 1);
lean_inc_ref(v_msg_479_);
v___x_480_ = lean_unsigned_to_nat(0u);
v_bs_x27_481_ = lean_array_uset(v_bs_476_, v_i_475_, v___x_480_);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_add(v_i_475_, v___x_482_);
v___x_484_ = lean_array_uset(v_bs_x27_481_, v_i_475_, v_msg_479_);
v_i_475_ = v___x_483_;
v_bs_476_ = v___x_484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6___boxed(lean_object* v_sz_486_, lean_object* v_i_487_, lean_object* v_bs_488_){
_start:
{
size_t v_sz_boxed_489_; size_t v_i_boxed_490_; lean_object* v_res_491_; 
v_sz_boxed_489_ = lean_unbox_usize(v_sz_486_);
lean_dec(v_sz_486_);
v_i_boxed_490_ = lean_unbox_usize(v_i_487_);
lean_dec(v_i_487_);
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_boxed_489_, v_i_boxed_490_, v_bs_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(lean_object* v_oldTraces_492_, lean_object* v_data_493_, lean_object* v_ref_494_, lean_object* v_msg_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_toCold_501_; lean_object* v_currRecDepth_502_; lean_object* v_ref_503_; uint16_t v_optionFlags_504_; uint8_t v_suppressElabErrors_505_; uint8_t v_checkDeprecated_506_; uint8_t v_isRecordingDeps_507_; lean_object* v_ref_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_traceState_511_; lean_object* v_traces_512_; lean_object* v___x_513_; size_t v_sz_514_; size_t v___x_515_; lean_object* v___x_516_; lean_object* v_msg_517_; lean_object* v___x_518_; lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_557_; 
v_toCold_501_ = lean_ctor_get(v___y_498_, 0);
v_currRecDepth_502_ = lean_ctor_get(v___y_498_, 1);
v_ref_503_ = lean_ctor_get(v___y_498_, 2);
v_optionFlags_504_ = lean_ctor_get_uint16(v___y_498_, sizeof(void*)*3);
v_suppressElabErrors_505_ = lean_ctor_get_uint8(v___y_498_, sizeof(void*)*3 + 2);
v_checkDeprecated_506_ = lean_ctor_get_uint8(v___y_498_, sizeof(void*)*3 + 3);
v_isRecordingDeps_507_ = lean_ctor_get_uint8(v___y_498_, sizeof(void*)*3 + 4);
v_ref_508_ = l_Lean_replaceRef(v_ref_494_, v_ref_503_);
lean_inc(v_currRecDepth_502_);
lean_inc_ref(v_toCold_501_);
v___x_509_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_509_, 0, v_toCold_501_);
lean_ctor_set(v___x_509_, 1, v_currRecDepth_502_);
lean_ctor_set(v___x_509_, 2, v_ref_508_);
lean_ctor_set_uint16(v___x_509_, sizeof(void*)*3, v_optionFlags_504_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*3 + 2, v_suppressElabErrors_505_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*3 + 3, v_checkDeprecated_506_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*3 + 4, v_isRecordingDeps_507_);
v___x_510_ = lean_st_ref_get(v___y_499_);
v_traceState_511_ = lean_ctor_get(v___x_510_, 4);
lean_inc_ref(v_traceState_511_);
lean_dec(v___x_510_);
v_traces_512_ = lean_ctor_get(v_traceState_511_, 0);
lean_inc_ref(v_traces_512_);
lean_dec_ref(v_traceState_511_);
v___x_513_ = l_Lean_PersistentArray_toArray___redArg(v_traces_512_);
lean_dec_ref(v_traces_512_);
v_sz_514_ = lean_array_size(v___x_513_);
v___x_515_ = ((size_t)0ULL);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_514_, v___x_515_, v___x_513_);
v_msg_517_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_517_, 0, v_data_493_);
lean_ctor_set(v_msg_517_, 1, v_msg_495_);
lean_ctor_set(v_msg_517_, 2, v___x_516_);
v___x_518_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_517_, v___y_496_, v___y_497_, v___x_509_, v___y_499_);
lean_dec_ref_known(v___x_509_, 3);
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_557_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_557_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_557_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v_traceState_524_; lean_object* v_env_525_; lean_object* v_nextMacroScope_526_; lean_object* v_ngen_527_; lean_object* v_auxDeclNGen_528_; lean_object* v_cache_529_; lean_object* v_recordedDeps_530_; lean_object* v_messages_531_; lean_object* v_infoState_532_; lean_object* v_snapshotTasks_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_556_; 
v___x_523_ = lean_st_ref_take(v___y_499_);
v_traceState_524_ = lean_ctor_get(v___x_523_, 4);
v_env_525_ = lean_ctor_get(v___x_523_, 0);
v_nextMacroScope_526_ = lean_ctor_get(v___x_523_, 1);
v_ngen_527_ = lean_ctor_get(v___x_523_, 2);
v_auxDeclNGen_528_ = lean_ctor_get(v___x_523_, 3);
v_cache_529_ = lean_ctor_get(v___x_523_, 5);
v_recordedDeps_530_ = lean_ctor_get(v___x_523_, 6);
v_messages_531_ = lean_ctor_get(v___x_523_, 7);
v_infoState_532_ = lean_ctor_get(v___x_523_, 8);
v_snapshotTasks_533_ = lean_ctor_get(v___x_523_, 9);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_556_ == 0)
{
v___x_535_ = v___x_523_;
v_isShared_536_ = v_isSharedCheck_556_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_snapshotTasks_533_);
lean_inc(v_infoState_532_);
lean_inc(v_messages_531_);
lean_inc(v_recordedDeps_530_);
lean_inc(v_cache_529_);
lean_inc(v_traceState_524_);
lean_inc(v_auxDeclNGen_528_);
lean_inc(v_ngen_527_);
lean_inc(v_nextMacroScope_526_);
lean_inc(v_env_525_);
lean_dec(v___x_523_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_556_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
uint64_t v_tid_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_554_; 
v_tid_537_ = lean_ctor_get_uint64(v_traceState_524_, sizeof(void*)*1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_traceState_524_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v_traceState_524_, 0);
lean_dec(v_unused_555_);
v___x_539_ = v_traceState_524_;
v_isShared_540_ = v_isSharedCheck_554_;
goto v_resetjp_538_;
}
else
{
lean_dec(v_traceState_524_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_554_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_541_ = lean_box(0);
v___x_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_542_, 0, v_ref_494_);
lean_ctor_set(v___x_542_, 1, v_a_519_);
v___x_543_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_492_, v___x_542_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_543_);
v___x_545_ = v___x_539_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_543_);
lean_ctor_set_uint64(v_reuseFailAlloc_553_, sizeof(void*)*1, v_tid_537_);
v___x_545_ = v_reuseFailAlloc_553_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 4, v___x_545_);
v___x_547_ = v___x_535_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_env_525_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_nextMacroScope_526_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_ngen_527_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_auxDeclNGen_528_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_552_, 5, v_cache_529_);
lean_ctor_set(v_reuseFailAlloc_552_, 6, v_recordedDeps_530_);
lean_ctor_set(v_reuseFailAlloc_552_, 7, v_messages_531_);
lean_ctor_set(v_reuseFailAlloc_552_, 8, v_infoState_532_);
lean_ctor_set(v_reuseFailAlloc_552_, 9, v_snapshotTasks_533_);
v___x_547_ = v_reuseFailAlloc_552_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_st_ref_put(v___y_499_, v___x_547_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_541_);
v___x_550_ = v___x_521_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_541_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object* v_oldTraces_558_, lean_object* v_data_559_, lean_object* v_ref_560_, lean_object* v_msg_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_558_, v_data_559_, v_ref_560_, v_msg_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
return v_res_567_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0(void){
_start:
{
lean_object* v___x_568_; double v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_float_of_nat(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3(void){
_start:
{
lean_object* v___x_573_; double v___x_574_; 
v___x_573_ = lean_unsigned_to_nat(1000u);
v___x_574_ = lean_float_of_nat(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_cls_575_, uint8_t v_collapsed_576_, lean_object* v_tag_577_, lean_object* v_opts_578_, uint8_t v_clsEnabled_579_, lean_object* v_oldTraces_580_, lean_object* v_msg_581_, lean_object* v_resStartStop_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_fst_588_; lean_object* v_snd_589_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v_data_593_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___y_609_; lean_object* v_a_610_; uint8_t v___y_625_; double v___y_657_; 
v_fst_588_ = lean_ctor_get(v_resStartStop_582_, 0);
lean_inc(v_fst_588_);
v_snd_589_ = lean_ctor_get(v_resStartStop_582_, 1);
lean_inc(v_snd_589_);
lean_dec_ref(v_resStartStop_582_);
v_fst_604_ = lean_ctor_get(v_snd_589_, 0);
lean_inc(v_fst_604_);
v_snd_605_ = lean_ctor_get(v_snd_589_, 1);
lean_inc(v_snd_605_);
lean_dec(v_snd_589_);
v___x_606_ = l_Lean_trace_profiler;
v___x_607_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_578_, v___x_606_);
if (v___x_607_ == 0)
{
v___y_625_ = v___x_607_;
goto v___jp_624_;
}
else
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = l_Lean_trace_profiler_useHeartbeats;
v___x_663_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_578_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; double v___x_666_; double v___x_667_; double v___x_668_; 
v___x_664_ = l_Lean_trace_profiler_threshold;
v___x_665_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_578_, v___x_664_);
v___x_666_ = lean_float_of_nat(v___x_665_);
v___x_667_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_668_ = lean_float_div(v___x_666_, v___x_667_);
v___y_657_ = v___x_668_;
goto v___jp_656_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; double v___x_671_; 
v___x_669_ = l_Lean_trace_profiler_threshold;
v___x_670_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_578_, v___x_669_);
v___x_671_ = lean_float_of_nat(v___x_670_);
v___y_657_ = v___x_671_;
goto v___jp_656_;
}
}
v___jp_590_:
{
lean_object* v___x_594_; 
lean_inc(v___y_591_);
v___x_594_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_580_, v_data_593_, v___y_591_, v___y_592_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v___x_595_; 
lean_dec_ref_known(v___x_594_, 1);
v___x_595_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_588_);
return v___x_595_;
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_fst_588_);
v_a_596_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_594_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_594_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
v___jp_608_:
{
uint8_t v_result_611_; lean_object* v___x_612_; lean_object* v___x_613_; double v___x_614_; lean_object* v_data_615_; 
v_result_611_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_fst_588_);
v___x_612_ = lean_box(v_result_611_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
v___x_614_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_577_);
lean_inc_ref(v___x_613_);
lean_inc(v_cls_575_);
v_data_615_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_615_, 0, v_cls_575_);
lean_ctor_set(v_data_615_, 1, v___x_613_);
lean_ctor_set(v_data_615_, 2, v_tag_577_);
lean_ctor_set_float(v_data_615_, sizeof(void*)*3, v___x_614_);
lean_ctor_set_float(v_data_615_, sizeof(void*)*3 + 8, v___x_614_);
lean_ctor_set_uint8(v_data_615_, sizeof(void*)*3 + 16, v_collapsed_576_);
if (v___x_607_ == 0)
{
lean_dec_ref_known(v___x_613_, 1);
lean_dec(v_snd_605_);
lean_dec(v_fst_604_);
lean_dec_ref(v_tag_577_);
lean_dec(v_cls_575_);
v___y_591_ = v___y_609_;
v___y_592_ = v_a_610_;
v_data_593_ = v_data_615_;
goto v___jp_590_;
}
else
{
lean_object* v_data_616_; double v___x_617_; double v___x_618_; 
lean_dec_ref_known(v_data_615_, 3);
v_data_616_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_616_, 0, v_cls_575_);
lean_ctor_set(v_data_616_, 1, v___x_613_);
lean_ctor_set(v_data_616_, 2, v_tag_577_);
v___x_617_ = lean_unbox_float(v_fst_604_);
lean_dec(v_fst_604_);
lean_ctor_set_float(v_data_616_, sizeof(void*)*3, v___x_617_);
v___x_618_ = lean_unbox_float(v_snd_605_);
lean_dec(v_snd_605_);
lean_ctor_set_float(v_data_616_, sizeof(void*)*3 + 8, v___x_618_);
lean_ctor_set_uint8(v_data_616_, sizeof(void*)*3 + 16, v_collapsed_576_);
v___y_591_ = v___y_609_;
v___y_592_ = v_a_610_;
v_data_593_ = v_data_616_;
goto v___jp_590_;
}
}
v___jp_619_:
{
lean_object* v_ref_620_; lean_object* v___x_621_; 
v_ref_620_ = lean_ctor_get(v___y_585_, 2);
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc(v___y_584_);
lean_inc_ref(v___y_583_);
lean_inc(v_fst_588_);
v___x_621_ = lean_apply_6(v_msg_581_, v_fst_588_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, lean_box(0));
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v___y_609_ = v_ref_620_;
v_a_610_ = v_a_622_;
goto v___jp_608_;
}
else
{
lean_object* v___x_623_; 
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_609_ = v_ref_620_;
v_a_610_ = v___x_623_;
goto v___jp_608_;
}
}
v___jp_624_:
{
if (v_clsEnabled_579_ == 0)
{
if (v___y_625_ == 0)
{
lean_object* v___x_626_; lean_object* v_traceState_627_; lean_object* v_env_628_; lean_object* v_nextMacroScope_629_; lean_object* v_ngen_630_; lean_object* v_auxDeclNGen_631_; lean_object* v_cache_632_; lean_object* v_recordedDeps_633_; lean_object* v_messages_634_; lean_object* v_infoState_635_; lean_object* v_snapshotTasks_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_snd_605_);
lean_dec(v_fst_604_);
lean_dec_ref(v_msg_581_);
lean_dec_ref(v_tag_577_);
lean_dec(v_cls_575_);
v___x_626_ = lean_st_ref_take(v___y_586_);
v_traceState_627_ = lean_ctor_get(v___x_626_, 4);
v_env_628_ = lean_ctor_get(v___x_626_, 0);
v_nextMacroScope_629_ = lean_ctor_get(v___x_626_, 1);
v_ngen_630_ = lean_ctor_get(v___x_626_, 2);
v_auxDeclNGen_631_ = lean_ctor_get(v___x_626_, 3);
v_cache_632_ = lean_ctor_get(v___x_626_, 5);
v_recordedDeps_633_ = lean_ctor_get(v___x_626_, 6);
v_messages_634_ = lean_ctor_get(v___x_626_, 7);
v_infoState_635_ = lean_ctor_get(v___x_626_, 8);
v_snapshotTasks_636_ = lean_ctor_get(v___x_626_, 9);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_655_ == 0)
{
v___x_638_ = v___x_626_;
v_isShared_639_ = v_isSharedCheck_655_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_snapshotTasks_636_);
lean_inc(v_infoState_635_);
lean_inc(v_messages_634_);
lean_inc(v_recordedDeps_633_);
lean_inc(v_cache_632_);
lean_inc(v_traceState_627_);
lean_inc(v_auxDeclNGen_631_);
lean_inc(v_ngen_630_);
lean_inc(v_nextMacroScope_629_);
lean_inc(v_env_628_);
lean_dec(v___x_626_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_655_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
uint64_t v_tid_640_; lean_object* v_traces_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_654_; 
v_tid_640_ = lean_ctor_get_uint64(v_traceState_627_, sizeof(void*)*1);
v_traces_641_ = lean_ctor_get(v_traceState_627_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_traceState_627_);
if (v_isSharedCheck_654_ == 0)
{
v___x_643_ = v_traceState_627_;
v_isShared_644_ = v_isSharedCheck_654_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_traces_641_);
lean_dec(v_traceState_627_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_654_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_580_, v_traces_641_);
lean_dec_ref(v_traces_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_645_);
v___x_647_ = v___x_643_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_645_);
lean_ctor_set_uint64(v_reuseFailAlloc_653_, sizeof(void*)*1, v_tid_640_);
v___x_647_ = v_reuseFailAlloc_653_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 4, v___x_647_);
v___x_649_ = v___x_638_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_env_628_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_nextMacroScope_629_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_ngen_630_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v_auxDeclNGen_631_);
lean_ctor_set(v_reuseFailAlloc_652_, 4, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_652_, 5, v_cache_632_);
lean_ctor_set(v_reuseFailAlloc_652_, 6, v_recordedDeps_633_);
lean_ctor_set(v_reuseFailAlloc_652_, 7, v_messages_634_);
lean_ctor_set(v_reuseFailAlloc_652_, 8, v_infoState_635_);
lean_ctor_set(v_reuseFailAlloc_652_, 9, v_snapshotTasks_636_);
v___x_649_ = v_reuseFailAlloc_652_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_st_ref_put(v___y_586_, v___x_649_);
v___x_651_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_588_);
return v___x_651_;
}
}
}
}
}
else
{
goto v___jp_619_;
}
}
else
{
goto v___jp_619_;
}
}
v___jp_656_:
{
double v___x_658_; double v___x_659_; double v___x_660_; uint8_t v___x_661_; 
v___x_658_ = lean_unbox_float(v_snd_605_);
v___x_659_ = lean_unbox_float(v_fst_604_);
v___x_660_ = lean_float_sub(v___x_658_, v___x_659_);
v___x_661_ = lean_float_decLt(v___y_657_, v___x_660_);
v___y_625_ = v___x_661_;
goto v___jp_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_cls_672_, lean_object* v_collapsed_673_, lean_object* v_tag_674_, lean_object* v_opts_675_, lean_object* v_clsEnabled_676_, lean_object* v_oldTraces_677_, lean_object* v_msg_678_, lean_object* v_resStartStop_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
uint8_t v_collapsed_boxed_685_; uint8_t v_clsEnabled_boxed_686_; lean_object* v_res_687_; 
v_collapsed_boxed_685_ = lean_unbox(v_collapsed_673_);
v_clsEnabled_boxed_686_ = lean_unbox(v_clsEnabled_676_);
v_res_687_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_cls_672_, v_collapsed_boxed_685_, v_tag_674_, v_opts_675_, v_clsEnabled_boxed_686_, v_oldTraces_677_, v_msg_678_, v_resStartStop_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec_ref(v_opts_675_);
return v_res_687_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object* v_keys_688_, lean_object* v_i_689_, lean_object* v_k_690_){
_start:
{
lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_691_ = lean_array_get_size(v_keys_688_);
v___x_692_ = lean_nat_dec_lt(v_i_689_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec(v_i_689_);
return v___x_692_;
}
else
{
lean_object* v_k_x27_693_; uint8_t v___x_694_; 
v_k_x27_693_ = lean_array_fget_borrowed(v_keys_688_, v_i_689_);
v___x_694_ = l_Lean_instBEqMVarId_beq(v_k_690_, v_k_x27_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_nat_add(v_i_689_, v___x_695_);
lean_dec(v_i_689_);
v_i_689_ = v___x_696_;
goto _start;
}
else
{
lean_dec(v_i_689_);
return v___x_692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object* v_keys_698_, lean_object* v_i_699_, lean_object* v_k_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_698_, v_i_699_, v_k_700_);
lean_dec(v_k_700_);
lean_dec_ref(v_keys_698_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_703_, size_t v_x_704_, lean_object* v_x_705_){
_start:
{
if (lean_obj_tag(v_x_703_) == 0)
{
lean_object* v_es_706_; lean_object* v___x_707_; size_t v___x_708_; size_t v___x_709_; lean_object* v_j_710_; lean_object* v___x_711_; 
v_es_706_ = lean_ctor_get(v_x_703_, 0);
v___x_707_ = lean_box(2);
v___x_708_ = ((size_t)31ULL);
v___x_709_ = lean_usize_land(v_x_704_, v___x_708_);
v_j_710_ = lean_usize_to_nat(v___x_709_);
v___x_711_ = lean_array_get_borrowed(v___x_707_, v_es_706_, v_j_710_);
lean_dec(v_j_710_);
switch(lean_obj_tag(v___x_711_))
{
case 0:
{
lean_object* v_key_712_; uint8_t v___x_713_; 
v_key_712_ = lean_ctor_get(v___x_711_, 0);
v___x_713_ = l_Lean_instBEqMVarId_beq(v_x_705_, v_key_712_);
return v___x_713_;
}
case 1:
{
lean_object* v_node_714_; size_t v___x_715_; size_t v___x_716_; 
v_node_714_ = lean_ctor_get(v___x_711_, 0);
v___x_715_ = ((size_t)5ULL);
v___x_716_ = lean_usize_shift_right(v_x_704_, v___x_715_);
v_x_703_ = v_node_714_;
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
size_t v_x_73995__boxed_725_; uint8_t v_res_726_; lean_object* v_r_727_; 
v_x_73995__boxed_725_ = lean_unbox_usize(v_x_723_);
lean_dec(v_x_723_);
v_res_726_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_722_, v_x_73995__boxed_725_, v_x_724_);
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
v_ref_756_ = lean_ctor_get(v___y_753_, 2);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_a_777_, lean_object* v_x_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_784_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_785_ = l_Lean_Exception_toMessageData(v_a_777_);
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_a_788_, lean_object* v_x_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_a_788_, v_x_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec_ref(v_x_789_);
return v_res_795_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_e_796_){
_start:
{
if (lean_obj_tag(v_e_796_) == 0)
{
uint8_t v___x_797_; 
v___x_797_ = 2;
return v___x_797_;
}
else
{
uint8_t v___x_798_; 
v___x_798_ = 0;
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_e_799_){
_start:
{
uint8_t v_res_800_; lean_object* v_r_801_; 
v_res_800_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_e_799_);
lean_dec_ref(v_e_799_);
v_r_801_ = lean_box(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_802_, uint8_t v_collapsed_803_, lean_object* v_tag_804_, lean_object* v_opts_805_, uint8_t v_clsEnabled_806_, lean_object* v_oldTraces_807_, lean_object* v_msg_808_, lean_object* v_resStartStop_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_fst_815_; lean_object* v_snd_816_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v_data_820_; lean_object* v_fst_831_; lean_object* v_snd_832_; lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___y_836_; lean_object* v_a_837_; uint8_t v___y_852_; double v___y_884_; 
v_fst_815_ = lean_ctor_get(v_resStartStop_809_, 0);
lean_inc(v_fst_815_);
v_snd_816_ = lean_ctor_get(v_resStartStop_809_, 1);
lean_inc(v_snd_816_);
lean_dec_ref(v_resStartStop_809_);
v_fst_831_ = lean_ctor_get(v_snd_816_, 0);
lean_inc(v_fst_831_);
v_snd_832_ = lean_ctor_get(v_snd_816_, 1);
lean_inc(v_snd_832_);
lean_dec(v_snd_816_);
v___x_833_ = l_Lean_trace_profiler;
v___x_834_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_805_, v___x_833_);
if (v___x_834_ == 0)
{
v___y_852_ = v___x_834_;
goto v___jp_851_;
}
else
{
lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_889_ = l_Lean_trace_profiler_useHeartbeats;
v___x_890_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_805_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; double v___x_893_; double v___x_894_; double v___x_895_; 
v___x_891_ = l_Lean_trace_profiler_threshold;
v___x_892_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_805_, v___x_891_);
v___x_893_ = lean_float_of_nat(v___x_892_);
v___x_894_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_895_ = lean_float_div(v___x_893_, v___x_894_);
v___y_884_ = v___x_895_;
goto v___jp_883_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; double v___x_898_; 
v___x_896_ = l_Lean_trace_profiler_threshold;
v___x_897_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_805_, v___x_896_);
v___x_898_ = lean_float_of_nat(v___x_897_);
v___y_884_ = v___x_898_;
goto v___jp_883_;
}
}
v___jp_817_:
{
lean_object* v___x_821_; 
lean_inc(v___y_819_);
v___x_821_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_807_, v_data_820_, v___y_819_, v___y_818_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v___x_822_; 
lean_dec_ref_known(v___x_821_, 1);
v___x_822_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_815_);
return v___x_822_;
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_fst_815_);
v_a_823_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_821_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_821_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
v___jp_835_:
{
uint8_t v_result_838_; lean_object* v___x_839_; lean_object* v___x_840_; double v___x_841_; lean_object* v_data_842_; 
v_result_838_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_fst_815_);
v___x_839_ = lean_box(v_result_838_);
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
v___x_841_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_804_);
lean_inc_ref(v___x_840_);
lean_inc(v_cls_802_);
v_data_842_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_842_, 0, v_cls_802_);
lean_ctor_set(v_data_842_, 1, v___x_840_);
lean_ctor_set(v_data_842_, 2, v_tag_804_);
lean_ctor_set_float(v_data_842_, sizeof(void*)*3, v___x_841_);
lean_ctor_set_float(v_data_842_, sizeof(void*)*3 + 8, v___x_841_);
lean_ctor_set_uint8(v_data_842_, sizeof(void*)*3 + 16, v_collapsed_803_);
if (v___x_834_ == 0)
{
lean_dec_ref_known(v___x_840_, 1);
lean_dec(v_snd_832_);
lean_dec(v_fst_831_);
lean_dec_ref(v_tag_804_);
lean_dec(v_cls_802_);
v___y_818_ = v_a_837_;
v___y_819_ = v___y_836_;
v_data_820_ = v_data_842_;
goto v___jp_817_;
}
else
{
lean_object* v_data_843_; double v___x_844_; double v___x_845_; 
lean_dec_ref_known(v_data_842_, 3);
v_data_843_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_843_, 0, v_cls_802_);
lean_ctor_set(v_data_843_, 1, v___x_840_);
lean_ctor_set(v_data_843_, 2, v_tag_804_);
v___x_844_ = lean_unbox_float(v_fst_831_);
lean_dec(v_fst_831_);
lean_ctor_set_float(v_data_843_, sizeof(void*)*3, v___x_844_);
v___x_845_ = lean_unbox_float(v_snd_832_);
lean_dec(v_snd_832_);
lean_ctor_set_float(v_data_843_, sizeof(void*)*3 + 8, v___x_845_);
lean_ctor_set_uint8(v_data_843_, sizeof(void*)*3 + 16, v_collapsed_803_);
v___y_818_ = v_a_837_;
v___y_819_ = v___y_836_;
v_data_820_ = v_data_843_;
goto v___jp_817_;
}
}
v___jp_846_:
{
lean_object* v_ref_847_; lean_object* v___x_848_; 
v_ref_847_ = lean_ctor_get(v___y_812_, 2);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v_fst_815_);
v___x_848_ = lean_apply_6(v_msg_808_, v_fst_815_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, lean_box(0));
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___y_836_ = v_ref_847_;
v_a_837_ = v_a_849_;
goto v___jp_835_;
}
else
{
lean_object* v___x_850_; 
lean_dec_ref_known(v___x_848_, 1);
v___x_850_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_836_ = v_ref_847_;
v_a_837_ = v___x_850_;
goto v___jp_835_;
}
}
v___jp_851_:
{
if (v_clsEnabled_806_ == 0)
{
if (v___y_852_ == 0)
{
lean_object* v___x_853_; lean_object* v_traceState_854_; lean_object* v_env_855_; lean_object* v_nextMacroScope_856_; lean_object* v_ngen_857_; lean_object* v_auxDeclNGen_858_; lean_object* v_cache_859_; lean_object* v_recordedDeps_860_; lean_object* v_messages_861_; lean_object* v_infoState_862_; lean_object* v_snapshotTasks_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_snd_832_);
lean_dec(v_fst_831_);
lean_dec_ref(v_msg_808_);
lean_dec_ref(v_tag_804_);
lean_dec(v_cls_802_);
v___x_853_ = lean_st_ref_take(v___y_813_);
v_traceState_854_ = lean_ctor_get(v___x_853_, 4);
v_env_855_ = lean_ctor_get(v___x_853_, 0);
v_nextMacroScope_856_ = lean_ctor_get(v___x_853_, 1);
v_ngen_857_ = lean_ctor_get(v___x_853_, 2);
v_auxDeclNGen_858_ = lean_ctor_get(v___x_853_, 3);
v_cache_859_ = lean_ctor_get(v___x_853_, 5);
v_recordedDeps_860_ = lean_ctor_get(v___x_853_, 6);
v_messages_861_ = lean_ctor_get(v___x_853_, 7);
v_infoState_862_ = lean_ctor_get(v___x_853_, 8);
v_snapshotTasks_863_ = lean_ctor_get(v___x_853_, 9);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_882_ == 0)
{
v___x_865_ = v___x_853_;
v_isShared_866_ = v_isSharedCheck_882_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_snapshotTasks_863_);
lean_inc(v_infoState_862_);
lean_inc(v_messages_861_);
lean_inc(v_recordedDeps_860_);
lean_inc(v_cache_859_);
lean_inc(v_traceState_854_);
lean_inc(v_auxDeclNGen_858_);
lean_inc(v_ngen_857_);
lean_inc(v_nextMacroScope_856_);
lean_inc(v_env_855_);
lean_dec(v___x_853_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_882_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint64_t v_tid_867_; lean_object* v_traces_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_881_; 
v_tid_867_ = lean_ctor_get_uint64(v_traceState_854_, sizeof(void*)*1);
v_traces_868_ = lean_ctor_get(v_traceState_854_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_traceState_854_);
if (v_isSharedCheck_881_ == 0)
{
v___x_870_ = v_traceState_854_;
v_isShared_871_ = v_isSharedCheck_881_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_traces_868_);
lean_dec(v_traceState_854_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_881_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_807_, v_traces_868_);
lean_dec_ref(v_traces_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_872_);
lean_ctor_set_uint64(v_reuseFailAlloc_880_, sizeof(void*)*1, v_tid_867_);
v___x_874_ = v_reuseFailAlloc_880_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_876_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 4, v___x_874_);
v___x_876_ = v___x_865_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_env_855_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_nextMacroScope_856_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_ngen_857_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_auxDeclNGen_858_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_879_, 5, v_cache_859_);
lean_ctor_set(v_reuseFailAlloc_879_, 6, v_recordedDeps_860_);
lean_ctor_set(v_reuseFailAlloc_879_, 7, v_messages_861_);
lean_ctor_set(v_reuseFailAlloc_879_, 8, v_infoState_862_);
lean_ctor_set(v_reuseFailAlloc_879_, 9, v_snapshotTasks_863_);
v___x_876_ = v_reuseFailAlloc_879_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_st_ref_put(v___y_813_, v___x_876_);
v___x_878_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_815_);
return v___x_878_;
}
}
}
}
}
else
{
goto v___jp_846_;
}
}
else
{
goto v___jp_846_;
}
}
v___jp_883_:
{
double v___x_885_; double v___x_886_; double v___x_887_; uint8_t v___x_888_; 
v___x_885_ = lean_unbox_float(v_snd_832_);
v___x_886_ = lean_unbox_float(v_fst_831_);
v___x_887_ = lean_float_sub(v___x_885_, v___x_886_);
v___x_888_ = lean_float_decLt(v___y_884_, v___x_887_);
v___y_852_ = v___x_888_;
goto v___jp_851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_899_, lean_object* v_collapsed_900_, lean_object* v_tag_901_, lean_object* v_opts_902_, lean_object* v_clsEnabled_903_, lean_object* v_oldTraces_904_, lean_object* v_msg_905_, lean_object* v_resStartStop_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
uint8_t v_collapsed_boxed_912_; uint8_t v_clsEnabled_boxed_913_; lean_object* v_res_914_; 
v_collapsed_boxed_912_ = lean_unbox(v_collapsed_900_);
v_clsEnabled_boxed_913_ = lean_unbox(v_clsEnabled_903_);
v_res_914_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_899_, v_collapsed_boxed_912_, v_tag_901_, v_opts_902_, v_clsEnabled_boxed_913_, v_oldTraces_904_, v_msg_905_, v_resStartStop_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec_ref(v_opts_902_);
return v_res_914_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__0));
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(lean_object* v_head_918_, lean_object* v_x_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_925_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1);
v___x_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_926_, 0, v_head_918_);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___boxed(lean_object* v_head_929_, lean_object* v_x_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(v_head_929_, v_x_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec_ref(v_x_930_);
return v_res_936_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_937_; double v___x_938_; 
v___x_937_ = lean_unsigned_to_nat(1000000000u);
v___x_938_ = lean_float_of_nat(v___x_937_);
return v___x_938_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__8___boxed(lean_object* v_tail_950_, lean_object* v_cfg_951_, lean_object* v_trace_952_, lean_object* v_next_953_, lean_object* v_goals_954_, lean_object* v_n_955_, lean_object* v_acc_956_, lean_object* v_r_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__8(v_tail_950_, v_cfg_951_, v_trace_952_, v_next_953_, v_goals_954_, v_n_955_, v_acc_956_, v_r_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_964_, lean_object* v_trace_965_, lean_object* v_next_966_, lean_object* v_goals_967_, lean_object* v_n_968_, lean_object* v_curr_969_, lean_object* v_acc_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
uint8_t v___y_977_; uint8_t v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v_a_984_; uint8_t v___y_994_; uint8_t v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v_a_1001_; uint8_t v___y_1014_; uint8_t v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; uint8_t v___y_1062_; lean_object* v___y_1063_; uint8_t v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v_a_1069_; uint8_t v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; uint8_t v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v_a_1086_; uint8_t v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; uint8_t v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v_a_1096_; uint8_t v___y_1099_; lean_object* v___y_1100_; uint8_t v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; uint8_t v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; uint8_t v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v_a_1117_; uint8_t v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; uint8_t v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v_a_1137_; uint8_t v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; uint8_t v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v_a_1147_; uint8_t v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; uint8_t v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v_zero_1160_; uint8_t v_isZero_1161_; 
v_zero_1160_ = lean_unsigned_to_nat(0u);
v_isZero_1161_ = lean_nat_dec_eq(v_n_968_, v_zero_1160_);
if (v_isZero_1161_ == 1)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_dec(v_acc_970_);
lean_dec(v_curr_969_);
lean_dec(v_n_968_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
v___x_1162_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1163_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1162_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1163_;
}
else
{
lean_object* v_proc_1164_; lean_object* v_suspend_1165_; lean_object* v_discharge_1166_; lean_object* v___f_1167_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; uint8_t v___y_1172_; uint8_t v___y_1173_; lean_object* v___f_1209_; uint8_t v___y_1211_; uint8_t v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v_a_1217_; uint8_t v___y_1230_; uint8_t v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v_a_1236_; uint8_t v___y_1246_; uint8_t v___y_1247_; lean_object* v___y_1248_; uint8_t v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v_a_1256_; uint8_t v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; uint8_t v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; uint8_t v___y_1275_; lean_object* v_a_1276_; lean_object* v___f_1288_; uint8_t v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; uint8_t v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; uint8_t v___y_1299_; lean_object* v_a_1300_; lean_object* v___y_1313_; uint8_t v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; uint8_t v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; uint8_t v___y_1323_; lean_object* v___f_1344_; uint8_t v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; uint8_t v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; lean_object* v___y_1355_; lean_object* v_a_1356_; uint8_t v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; uint8_t v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; uint8_t v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1401_; lean_object* v___y_1402_; uint8_t v___y_1403_; lean_object* v___y_1404_; uint8_t v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; uint8_t v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v_a_1411_; lean_object* v___y_1421_; uint8_t v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; uint8_t v___y_1425_; uint8_t v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1453_; lean_object* v___y_1454_; uint8_t v___y_1455_; lean_object* v___y_1456_; uint8_t v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; uint8_t v___y_1462_; lean_object* v_a_1463_; uint8_t v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; uint8_t v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; uint8_t v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; uint8_t v___y_1505_; lean_object* v___y_1506_; uint8_t v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v_a_1511_; uint8_t v___y_1521_; lean_object* v___y_1522_; uint8_t v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v_a_1527_; uint8_t v___y_1540_; uint8_t v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v_a_1546_; uint8_t v___y_1559_; uint8_t v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v_a_1565_; lean_object* v_one_1574_; lean_object* v_n_1575_; lean_object* v___y_1577_; uint8_t v___y_1578_; uint8_t v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; uint8_t v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; uint8_t v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; uint8_t v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; uint8_t v___y_1615_; uint8_t v___y_1637_; lean_object* v___y_1638_; uint8_t v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v_a_1728_; lean_object* v___y_1977_; lean_object* v___x_1987_; 
v_proc_1164_ = lean_ctor_get(v_cfg_964_, 1);
v_suspend_1165_ = lean_ctor_get(v_cfg_964_, 2);
v_discharge_1166_ = lean_ctor_get(v_cfg_964_, 3);
v___f_1167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1574_ = lean_unsigned_to_nat(1u);
v_n_1575_ = lean_nat_sub(v_n_968_, v_one_1574_);
lean_dec(v_n_968_);
lean_inc_ref(v_proc_1164_);
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_curr_969_);
lean_inc(v_goals_967_);
v___x_1987_ = lean_apply_7(v_proc_1164_, v_goals_967_, v_curr_969_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v_a_1728_ = v_a_1988_;
goto v___jp_1727_;
}
else
{
lean_object* v_a_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2054_; 
v_a_1989_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_1991_ = v___x_1987_;
v_isShared_1992_ = v_isSharedCheck_2054_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_a_1989_);
lean_dec(v___x_1987_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2054_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_Exception_isInterrupt(v_a_1989_);
if (v___x_1993_ == 0)
{
uint8_t v___x_1994_; 
lean_inc(v_a_1989_);
v___x_1994_ = l_Lean_Exception_isRuntime(v_a_1989_);
if (v___x_1994_ == 0)
{
lean_object* v_toCold_1995_; lean_object* v_options_1996_; uint8_t v_hasTrace_1997_; 
v_toCold_1995_ = lean_ctor_get(v_a_973_, 0);
v_options_1996_ = lean_ctor_get(v_toCold_1995_, 2);
v_hasTrace_1997_ = lean_ctor_get_uint8(v_options_1996_, sizeof(void*)*1);
if (v_hasTrace_1997_ == 0)
{
lean_object* v___x_1999_; 
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_curr_969_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
if (v_isShared_1992_ == 0)
{
v___x_1999_ = v___x_1991_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1989_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2001_; lean_object* v___f_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v_inheritedTraceOptions_2001_ = lean_ctor_get(v_toCold_1995_, 11);
lean_inc(v_a_1989_);
v___f_2002_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2002_, 0, v_a_1989_);
v___x_2003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_965_);
v___x_2005_ = l_Lean_Name_append(v___x_2004_, v_trace_965_);
v___x_2006_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2001_, v_options_1996_, v___x_2005_);
lean_dec(v___x_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = l_Lean_trace_profiler;
v___x_2044_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1996_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2046_; 
lean_dec_ref(v___f_2002_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_curr_969_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
if (v_isShared_1992_ == 0)
{
v___x_2046_ = v___x_1991_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_1989_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
else
{
lean_del_object(v___x_1991_);
goto v___jp_2007_;
}
}
else
{
lean_del_object(v___x_1991_);
goto v___jp_2007_;
}
v___jp_2007_:
{
lean_object* v___x_2008_; lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2042_; 
v___x_2008_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2042_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2042_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2014_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1996_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = lean_io_mono_nanos_now();
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v_a_1989_);
v___x_2017_ = v___x_2011_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_1989_);
v___x_2017_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; double v___x_2019_; double v___x_2020_; double v___x_2021_; double v___x_2022_; double v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2018_ = lean_io_mono_nanos_now();
v___x_2019_ = lean_float_of_nat(v___x_2015_);
v___x_2020_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2021_ = lean_float_div(v___x_2019_, v___x_2020_);
v___x_2022_ = lean_float_of_nat(v___x_2018_);
v___x_2023_ = lean_float_div(v___x_2022_, v___x_2020_);
v___x_2024_ = lean_box_float(v___x_2021_);
v___x_2025_ = lean_box_float(v___x_2023_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2024_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2017_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
lean_inc(v_trace_965_);
v___x_2028_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_965_, v_hasTrace_1997_, v___x_2003_, v_options_1996_, v___x_2006_, v_a_2009_, v___f_2002_, v___x_2027_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1977_ = v___x_2028_;
goto v___jp_1976_;
}
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2030_ = lean_io_get_num_heartbeats();
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v_a_1989_);
v___x_2032_ = v___x_2011_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_1989_);
v___x_2032_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; double v___x_2034_; double v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2033_ = lean_io_get_num_heartbeats();
v___x_2034_ = lean_float_of_nat(v___x_2030_);
v___x_2035_ = lean_float_of_nat(v___x_2033_);
v___x_2036_ = lean_box_float(v___x_2034_);
v___x_2037_ = lean_box_float(v___x_2035_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2032_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
lean_inc(v_trace_965_);
v___x_2040_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_965_, v_hasTrace_1997_, v___x_2003_, v_options_1996_, v___x_2006_, v_a_2009_, v___f_2002_, v___x_2039_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1977_ = v___x_2040_;
goto v___jp_1976_;
}
}
}
}
}
}
else
{
lean_object* v___x_2049_; 
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_curr_969_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
if (v_isShared_1992_ == 0)
{
v___x_2049_ = v___x_1991_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_1989_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
lean_object* v___x_2052_; 
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_curr_969_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
if (v_isShared_1992_ == 0)
{
v___x_2052_ = v___x_1991_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_1989_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
v___jp_1168_:
{
lean_object* v___x_1174_; lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1208_; 
v___x_1174_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1208_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1208_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1180_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1170_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = lean_io_mono_nanos_now();
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 1);
lean_ctor_set(v___x_1177_, 0, v___y_1171_);
v___x_1183_ = v___x_1177_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___y_1171_);
v___x_1183_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; double v___x_1185_; double v___x_1186_; double v___x_1187_; double v___x_1188_; double v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1184_ = lean_io_mono_nanos_now();
v___x_1185_ = lean_float_of_nat(v___x_1181_);
v___x_1186_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1187_ = lean_float_div(v___x_1185_, v___x_1186_);
v___x_1188_ = lean_float_of_nat(v___x_1184_);
v___x_1189_ = lean_float_div(v___x_1188_, v___x_1186_);
v___x_1190_ = lean_box_float(v___x_1187_);
v___x_1191_ = lean_box_float(v___x_1189_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1183_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
lean_inc_ref(v___y_1169_);
v___x_1194_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1173_, v___y_1169_, v___y_1170_, v___y_1172_, v_a_1175_, v___f_1167_, v___x_1193_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1194_;
}
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = lean_io_get_num_heartbeats();
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 1);
lean_ctor_set(v___x_1177_, 0, v___y_1171_);
v___x_1198_ = v___x_1177_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___y_1171_);
v___x_1198_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; double v___x_1200_; double v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1199_ = lean_io_get_num_heartbeats();
v___x_1200_ = lean_float_of_nat(v___x_1196_);
v___x_1201_ = lean_float_of_nat(v___x_1199_);
v___x_1202_ = lean_box_float(v___x_1200_);
v___x_1203_ = lean_box_float(v___x_1201_);
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1198_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
lean_inc_ref(v___y_1169_);
v___x_1206_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1173_, v___y_1169_, v___y_1170_, v___y_1172_, v_a_1175_, v___f_1167_, v___x_1205_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1206_;
}
}
}
}
v___jp_1210_:
{
lean_object* v___x_1218_; double v___x_1219_; double v___x_1220_; double v___x_1221_; double v___x_1222_; double v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1218_ = lean_io_mono_nanos_now();
v___x_1219_ = lean_float_of_nat(v___y_1216_);
v___x_1220_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1221_ = lean_float_div(v___x_1219_, v___x_1220_);
v___x_1222_ = lean_float_of_nat(v___x_1218_);
v___x_1223_ = lean_float_div(v___x_1222_, v___x_1220_);
v___x_1224_ = lean_box_float(v___x_1221_);
v___x_1225_ = lean_box_float(v___x_1223_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_a_1217_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
lean_inc_ref(v___y_1213_);
v___x_1228_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1212_, v___y_1213_, v___y_1215_, v___y_1211_, v___y_1214_, v___f_1209_, v___x_1227_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1228_;
}
v___jp_1229_:
{
lean_object* v___x_1237_; double v___x_1238_; double v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1237_ = lean_io_get_num_heartbeats();
v___x_1238_ = lean_float_of_nat(v___y_1235_);
v___x_1239_ = lean_float_of_nat(v___x_1237_);
v___x_1240_ = lean_box_float(v___x_1238_);
v___x_1241_ = lean_box_float(v___x_1239_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_a_1236_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
lean_inc_ref(v___y_1232_);
v___x_1244_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1231_, v___y_1232_, v___y_1234_, v___y_1230_, v___y_1233_, v___f_1209_, v___x_1243_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1244_;
}
v___jp_1245_:
{
lean_object* v___x_1257_; double v___x_1258_; double v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1257_ = lean_io_get_num_heartbeats();
v___x_1258_ = lean_float_of_nat(v___y_1251_);
v___x_1259_ = lean_float_of_nat(v___x_1257_);
v___x_1260_ = lean_box_float(v___x_1258_);
v___x_1261_ = lean_box_float(v___x_1259_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_a_1256_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
lean_inc_ref(v___y_1250_);
lean_inc(v_trace_965_);
v___x_1264_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1247_, v___y_1250_, v___y_1253_, v___y_1246_, v___y_1255_, v___f_1209_, v___x_1263_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1099_ = v___y_1247_;
v___y_1100_ = v___y_1248_;
v___y_1101_ = v___y_1249_;
v___y_1102_ = v___y_1250_;
v___y_1103_ = v___y_1252_;
v___y_1104_ = v___y_1253_;
v___y_1105_ = v___y_1254_;
v___y_1106_ = v___x_1264_;
goto v___jp_1098_;
}
v___jp_1265_:
{
lean_object* v___x_1277_; double v___x_1278_; double v___x_1279_; double v___x_1280_; double v___x_1281_; double v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1277_ = lean_io_mono_nanos_now();
v___x_1278_ = lean_float_of_nat(v___y_1274_);
v___x_1279_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1280_ = lean_float_div(v___x_1278_, v___x_1279_);
v___x_1281_ = lean_float_of_nat(v___x_1277_);
v___x_1282_ = lean_float_div(v___x_1281_, v___x_1279_);
v___x_1283_ = lean_box_float(v___x_1280_);
v___x_1284_ = lean_box_float(v___x_1282_);
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_a_1276_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
lean_inc_ref(v___y_1270_);
lean_inc(v_trace_965_);
v___x_1287_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1266_, v___y_1270_, v___y_1272_, v___y_1275_, v___y_1271_, v___f_1209_, v___x_1286_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1150_ = v___y_1266_;
v___y_1151_ = v___y_1268_;
v___y_1152_ = v___y_1267_;
v___y_1153_ = v___y_1269_;
v___y_1154_ = v___y_1270_;
v___y_1155_ = v___y_1272_;
v___y_1156_ = v___y_1273_;
v___y_1157_ = v___x_1287_;
goto v___jp_1149_;
}
v___jp_1289_:
{
lean_object* v___x_1301_; double v___x_1302_; double v___x_1303_; double v___x_1304_; double v___x_1305_; double v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1301_ = lean_io_mono_nanos_now();
v___x_1302_ = lean_float_of_nat(v___y_1297_);
v___x_1303_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1304_ = lean_float_div(v___x_1302_, v___x_1303_);
v___x_1305_ = lean_float_of_nat(v___x_1301_);
v___x_1306_ = lean_float_div(v___x_1305_, v___x_1303_);
v___x_1307_ = lean_box_float(v___x_1304_);
v___x_1308_ = lean_box_float(v___x_1306_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v_a_1300_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
lean_inc_ref(v___y_1295_);
lean_inc(v_trace_965_);
v___x_1311_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1290_, v___y_1295_, v___y_1296_, v___y_1299_, v___y_1293_, v___f_1288_, v___x_1310_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1150_ = v___y_1290_;
v___y_1151_ = v___y_1292_;
v___y_1152_ = v___y_1291_;
v___y_1153_ = v___y_1294_;
v___y_1154_ = v___y_1295_;
v___y_1155_ = v___y_1296_;
v___y_1156_ = v___y_1298_;
v___y_1157_ = v___x_1311_;
goto v___jp_1149_;
}
v___jp_1312_:
{
lean_object* v___x_1324_; lean_object* v_a_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1324_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref(v___x_1324_);
v___x_1326_ = lean_io_mono_nanos_now();
lean_inc(v_trace_965_);
v___x_1327_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___y_1313_, v___y_1320_, v___y_1319_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set_tag(v___x_1330_, 1);
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
v___y_1290_ = v___y_1314_;
v___y_1291_ = v___y_1316_;
v___y_1292_ = v___y_1315_;
v___y_1293_ = v_a_1325_;
v___y_1294_ = v___y_1318_;
v___y_1295_ = v___y_1317_;
v___y_1296_ = v___y_1321_;
v___y_1297_ = v___x_1326_;
v___y_1298_ = v___y_1322_;
v___y_1299_ = v___y_1323_;
v_a_1300_ = v___x_1333_;
goto v___jp_1289_;
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
v_a_1336_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1327_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1327_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
lean_ctor_set_tag(v___x_1338_, 0);
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
v___y_1290_ = v___y_1314_;
v___y_1291_ = v___y_1316_;
v___y_1292_ = v___y_1315_;
v___y_1293_ = v_a_1325_;
v___y_1294_ = v___y_1318_;
v___y_1295_ = v___y_1317_;
v___y_1296_ = v___y_1321_;
v___y_1297_ = v___x_1326_;
v___y_1298_ = v___y_1322_;
v___y_1299_ = v___y_1323_;
v_a_1300_ = v___x_1341_;
goto v___jp_1289_;
}
}
}
}
v___jp_1345_:
{
lean_object* v___x_1357_; double v___x_1358_; double v___x_1359_; double v___x_1360_; double v___x_1361_; double v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1357_ = lean_io_mono_nanos_now();
v___x_1358_ = lean_float_of_nat(v___y_1352_);
v___x_1359_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1360_ = lean_float_div(v___x_1358_, v___x_1359_);
v___x_1361_ = lean_float_of_nat(v___x_1357_);
v___x_1362_ = lean_float_div(v___x_1361_, v___x_1359_);
v___x_1363_ = lean_box_float(v___x_1360_);
v___x_1364_ = lean_box_float(v___x_1362_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1363_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1356_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
lean_inc_ref(v___y_1350_);
lean_inc(v_trace_965_);
v___x_1367_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1346_, v___y_1350_, v___y_1351_, v___y_1354_, v___y_1355_, v___f_1344_, v___x_1366_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1150_ = v___y_1346_;
v___y_1151_ = v___y_1348_;
v___y_1152_ = v___y_1347_;
v___y_1153_ = v___y_1349_;
v___y_1154_ = v___y_1350_;
v___y_1155_ = v___y_1351_;
v___y_1156_ = v___y_1353_;
v___y_1157_ = v___x_1367_;
goto v___jp_1149_;
}
v___jp_1368_:
{
lean_object* v___x_1380_; lean_object* v_a_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1380_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = lean_io_mono_nanos_now();
lean_inc(v_trace_965_);
v___x_1383_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___y_1375_, v___y_1374_, v___y_1379_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set_tag(v___x_1386_, 1);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
v___y_1346_ = v___y_1369_;
v___y_1347_ = v___y_1371_;
v___y_1348_ = v___y_1370_;
v___y_1349_ = v___y_1373_;
v___y_1350_ = v___y_1372_;
v___y_1351_ = v___y_1376_;
v___y_1352_ = v___x_1382_;
v___y_1353_ = v___y_1378_;
v___y_1354_ = v___y_1377_;
v___y_1355_ = v_a_1381_;
v_a_1356_ = v___x_1389_;
goto v___jp_1345_;
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
v_a_1392_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1383_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1383_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 0);
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
v___y_1346_ = v___y_1369_;
v___y_1347_ = v___y_1371_;
v___y_1348_ = v___y_1370_;
v___y_1349_ = v___y_1373_;
v___y_1350_ = v___y_1372_;
v___y_1351_ = v___y_1376_;
v___y_1352_ = v___x_1382_;
v___y_1353_ = v___y_1378_;
v___y_1354_ = v___y_1377_;
v___y_1355_ = v_a_1381_;
v_a_1356_ = v___x_1397_;
goto v___jp_1345_;
}
}
}
}
v___jp_1400_:
{
lean_object* v___x_1412_; double v___x_1413_; double v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1412_ = lean_io_get_num_heartbeats();
v___x_1413_ = lean_float_of_nat(v___y_1402_);
v___x_1414_ = lean_float_of_nat(v___x_1412_);
v___x_1415_ = lean_box_float(v___x_1413_);
v___x_1416_ = lean_box_float(v___x_1414_);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_a_1411_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
lean_inc_ref(v___y_1406_);
lean_inc(v_trace_965_);
v___x_1419_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1403_, v___y_1406_, v___y_1409_, v___y_1408_, v___y_1401_, v___f_1288_, v___x_1418_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1099_ = v___y_1403_;
v___y_1100_ = v___y_1404_;
v___y_1101_ = v___y_1405_;
v___y_1102_ = v___y_1406_;
v___y_1103_ = v___y_1407_;
v___y_1104_ = v___y_1409_;
v___y_1105_ = v___y_1410_;
v___y_1106_ = v___x_1419_;
goto v___jp_1098_;
}
v___jp_1420_:
{
lean_object* v___x_1432_; lean_object* v_a_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1432_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref(v___x_1432_);
v___x_1434_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_965_);
v___x_1435_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___y_1430_, v___y_1428_, v___y_1421_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set_tag(v___x_1438_, 1);
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
v___y_1401_ = v_a_1433_;
v___y_1402_ = v___x_1434_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1425_;
v___y_1406_ = v___y_1424_;
v___y_1407_ = v___y_1427_;
v___y_1408_ = v___y_1426_;
v___y_1409_ = v___y_1429_;
v___y_1410_ = v___y_1431_;
v_a_1411_ = v___x_1441_;
goto v___jp_1400_;
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
v_a_1444_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1435_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1435_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set_tag(v___x_1446_, 0);
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
v___y_1401_ = v_a_1433_;
v___y_1402_ = v___x_1434_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1425_;
v___y_1406_ = v___y_1424_;
v___y_1407_ = v___y_1427_;
v___y_1408_ = v___y_1426_;
v___y_1409_ = v___y_1429_;
v___y_1410_ = v___y_1431_;
v_a_1411_ = v___x_1449_;
goto v___jp_1400_;
}
}
}
}
v___jp_1452_:
{
lean_object* v___x_1464_; double v___x_1465_; double v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1464_ = lean_io_get_num_heartbeats();
v___x_1465_ = lean_float_of_nat(v___y_1453_);
v___x_1466_ = lean_float_of_nat(v___x_1464_);
v___x_1467_ = lean_box_float(v___x_1465_);
v___x_1468_ = lean_box_float(v___x_1466_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v_a_1463_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
lean_inc_ref(v___y_1458_);
lean_inc(v_trace_965_);
v___x_1471_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1455_, v___y_1458_, v___y_1460_, v___y_1462_, v___y_1454_, v___f_1344_, v___x_1470_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1099_ = v___y_1455_;
v___y_1100_ = v___y_1456_;
v___y_1101_ = v___y_1457_;
v___y_1102_ = v___y_1458_;
v___y_1103_ = v___y_1459_;
v___y_1104_ = v___y_1460_;
v___y_1105_ = v___y_1461_;
v___y_1106_ = v___x_1471_;
goto v___jp_1098_;
}
v___jp_1472_:
{
lean_object* v___x_1484_; lean_object* v_a_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1484_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
lean_dec_ref(v___x_1484_);
v___x_1486_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_965_);
v___x_1487_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___y_1483_, v___y_1479_, v___y_1475_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set_tag(v___x_1490_, 1);
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
v___y_1453_ = v___x_1486_;
v___y_1454_ = v_a_1485_;
v___y_1455_ = v___y_1473_;
v___y_1456_ = v___y_1474_;
v___y_1457_ = v___y_1477_;
v___y_1458_ = v___y_1476_;
v___y_1459_ = v___y_1478_;
v___y_1460_ = v___y_1480_;
v___y_1461_ = v___y_1482_;
v___y_1462_ = v___y_1481_;
v_a_1463_ = v___x_1493_;
goto v___jp_1452_;
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v_a_1496_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1487_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1487_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set_tag(v___x_1498_, 0);
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
v___y_1453_ = v___x_1486_;
v___y_1454_ = v_a_1485_;
v___y_1455_ = v___y_1473_;
v___y_1456_ = v___y_1474_;
v___y_1457_ = v___y_1477_;
v___y_1458_ = v___y_1476_;
v___y_1459_ = v___y_1478_;
v___y_1460_ = v___y_1480_;
v___y_1461_ = v___y_1482_;
v___y_1462_ = v___y_1481_;
v_a_1463_ = v___x_1501_;
goto v___jp_1452_;
}
}
}
}
v___jp_1504_:
{
lean_object* v___x_1512_; double v___x_1513_; double v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1512_ = lean_io_get_num_heartbeats();
v___x_1513_ = lean_float_of_nat(v___y_1510_);
v___x_1514_ = lean_float_of_nat(v___x_1512_);
v___x_1515_ = lean_box_float(v___x_1513_);
v___x_1516_ = lean_box_float(v___x_1514_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1515_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_a_1511_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
lean_inc_ref(v___y_1508_);
v___x_1519_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1505_, v___y_1508_, v___y_1509_, v___y_1507_, v___y_1506_, v___f_1288_, v___x_1518_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1519_;
}
v___jp_1520_:
{
lean_object* v___x_1528_; double v___x_1529_; double v___x_1530_; double v___x_1531_; double v___x_1532_; double v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1528_ = lean_io_mono_nanos_now();
v___x_1529_ = lean_float_of_nat(v___y_1525_);
v___x_1530_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1531_ = lean_float_div(v___x_1529_, v___x_1530_);
v___x_1532_ = lean_float_of_nat(v___x_1528_);
v___x_1533_ = lean_float_div(v___x_1532_, v___x_1530_);
v___x_1534_ = lean_box_float(v___x_1531_);
v___x_1535_ = lean_box_float(v___x_1533_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1534_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_a_1527_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
lean_inc_ref(v___y_1524_);
v___x_1538_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1521_, v___y_1524_, v___y_1526_, v___y_1523_, v___y_1522_, v___f_1288_, v___x_1537_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1538_;
}
v___jp_1539_:
{
lean_object* v___x_1547_; double v___x_1548_; double v___x_1549_; double v___x_1550_; double v___x_1551_; double v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1547_ = lean_io_mono_nanos_now();
v___x_1548_ = lean_float_of_nat(v___y_1544_);
v___x_1549_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1550_ = lean_float_div(v___x_1548_, v___x_1549_);
v___x_1551_ = lean_float_of_nat(v___x_1547_);
v___x_1552_ = lean_float_div(v___x_1551_, v___x_1549_);
v___x_1553_ = lean_box_float(v___x_1550_);
v___x_1554_ = lean_box_float(v___x_1552_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_a_1546_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
lean_inc_ref(v___y_1542_);
v___x_1557_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1540_, v___y_1545_, v___f_1344_, v___x_1556_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1557_;
}
v___jp_1558_:
{
lean_object* v___x_1566_; double v___x_1567_; double v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1566_ = lean_io_get_num_heartbeats();
v___x_1567_ = lean_float_of_nat(v___y_1564_);
v___x_1568_ = lean_float_of_nat(v___x_1566_);
v___x_1569_ = lean_box_float(v___x_1567_);
v___x_1570_ = lean_box_float(v___x_1568_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_a_1565_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
lean_inc_ref(v___y_1561_);
v___x_1573_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1559_, v___y_1563_, v___f_1344_, v___x_1572_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1573_;
}
v___jp_1576_:
{
lean_object* v___x_1586_; lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1586_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1586_);
v___x_1588_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_965_);
v___x_1589_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v_n_1575_, v___y_1577_, v_acc_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 1);
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
v___y_1246_ = v___y_1578_;
v___y_1247_ = v___y_1579_;
v___y_1248_ = v___y_1580_;
v___y_1249_ = v___y_1582_;
v___y_1250_ = v___y_1581_;
v___y_1251_ = v___x_1588_;
v___y_1252_ = v___y_1583_;
v___y_1253_ = v___y_1584_;
v___y_1254_ = v___y_1585_;
v___y_1255_ = v_a_1587_;
v_a_1256_ = v___x_1595_;
goto v___jp_1245_;
}
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_a_1598_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1589_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1589_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 0);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
v___y_1246_ = v___y_1578_;
v___y_1247_ = v___y_1579_;
v___y_1248_ = v___y_1580_;
v___y_1249_ = v___y_1582_;
v___y_1250_ = v___y_1581_;
v___y_1251_ = v___x_1588_;
v___y_1252_ = v___y_1583_;
v___y_1253_ = v___y_1584_;
v___y_1254_ = v___y_1585_;
v___y_1255_ = v_a_1587_;
v_a_1256_ = v___x_1603_;
goto v___jp_1245_;
}
}
}
}
v___jp_1606_:
{
lean_object* v___x_1616_; lean_object* v_a_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1616_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = lean_io_mono_nanos_now();
lean_inc(v_trace_965_);
v___x_1619_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v_n_1575_, v___y_1614_, v_acc_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
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
v___y_1266_ = v___y_1607_;
v___y_1267_ = v___y_1609_;
v___y_1268_ = v___y_1608_;
v___y_1269_ = v___y_1611_;
v___y_1270_ = v___y_1610_;
v___y_1271_ = v_a_1617_;
v___y_1272_ = v___y_1612_;
v___y_1273_ = v___y_1613_;
v___y_1274_ = v___x_1618_;
v___y_1275_ = v___y_1615_;
v_a_1276_ = v___x_1625_;
goto v___jp_1265_;
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
v___y_1266_ = v___y_1607_;
v___y_1267_ = v___y_1609_;
v___y_1268_ = v___y_1608_;
v___y_1269_ = v___y_1611_;
v___y_1270_ = v___y_1610_;
v___y_1271_ = v_a_1617_;
v___y_1272_ = v___y_1612_;
v___y_1273_ = v___y_1613_;
v___y_1274_ = v___x_1618_;
v___y_1275_ = v___y_1615_;
v_a_1276_ = v___x_1633_;
goto v___jp_1265_;
}
}
}
}
v___jp_1636_:
{
lean_object* v___x_1649_; lean_object* v_a_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1649_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1652_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1642_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_dec_ref(v___y_1638_);
v___x_1653_ = lean_io_mono_nanos_now();
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v___y_1644_);
v___x_1654_ = lean_apply_6(v___y_1641_, v___y_1644_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; uint8_t v___x_1656_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1654_, 1);
v___x_1656_ = lean_unbox(v_a_1655_);
lean_dec(v_a_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
lean_inc_ref(v_next_966_);
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v___y_1644_);
v___x_1657_ = lean_apply_7(v_next_966_, v___y_1644_, v___y_1645_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; 
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1644_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec_ref(v_cfg_964_);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___y_1140_ = v___y_1637_;
v___y_1141_ = v___x_1653_;
v___y_1142_ = v_a_1650_;
v___y_1143_ = v___y_1640_;
v___y_1144_ = v___y_1639_;
v___y_1145_ = v___y_1642_;
v___y_1146_ = v___y_1643_;
v_a_1147_ = v_a_1658_;
goto v___jp_1139_;
}
else
{
lean_object* v_a_1659_; uint8_t v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1660_ = l_Lean_Exception_isInterrupt(v_a_1659_);
if (v___x_1660_ == 0)
{
uint8_t v___x_1661_; 
lean_inc(v_a_1659_);
v___x_1661_ = l_Lean_Exception_isRuntime(v_a_1659_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
lean_dec(v_a_1659_);
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v___y_1644_);
v___x_1662_ = lean_apply_6(v___y_1646_, v___y_1644_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1663_);
lean_dec_ref_known(v___x_1662_, 1);
if (lean_obj_tag(v_a_1663_) == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1664_ = lean_nat_add(v_n_1575_, v_one_1574_);
lean_dec(v_n_1575_);
v___x_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___y_1644_);
lean_ctor_set(v___x_1665_, 1, v_acc_970_);
v___x_1666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_965_);
v___x_1667_ = l_Lean_Name_append(v___x_1666_, v_trace_965_);
v___x_1668_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1648_, v___y_1642_, v___x_1667_);
lean_dec(v___x_1667_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = l_Lean_trace_profiler;
v___x_1670_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1642_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; 
lean_inc(v_trace_965_);
v___x_1671_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___x_1664_, v___y_1647_, v___x_1665_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1150_ = v___y_1637_;
v___y_1151_ = v_a_1650_;
v___y_1152_ = v___x_1653_;
v___y_1153_ = v___y_1639_;
v___y_1154_ = v___y_1640_;
v___y_1155_ = v___y_1642_;
v___y_1156_ = v___y_1643_;
v___y_1157_ = v___x_1671_;
goto v___jp_1149_;
}
else
{
v___y_1313_ = v___x_1664_;
v___y_1314_ = v___y_1637_;
v___y_1315_ = v_a_1650_;
v___y_1316_ = v___x_1653_;
v___y_1317_ = v___y_1640_;
v___y_1318_ = v___y_1639_;
v___y_1319_ = v___x_1665_;
v___y_1320_ = v___y_1647_;
v___y_1321_ = v___y_1642_;
v___y_1322_ = v___y_1643_;
v___y_1323_ = v___x_1668_;
goto v___jp_1312_;
}
}
else
{
v___y_1313_ = v___x_1664_;
v___y_1314_ = v___y_1637_;
v___y_1315_ = v_a_1650_;
v___y_1316_ = v___x_1653_;
v___y_1317_ = v___y_1640_;
v___y_1318_ = v___y_1639_;
v___y_1319_ = v___x_1665_;
v___y_1320_ = v___y_1647_;
v___y_1321_ = v___y_1642_;
v___y_1322_ = v___y_1643_;
v___y_1323_ = v___x_1668_;
goto v___jp_1312_;
}
}
else
{
lean_object* v_val_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
lean_dec(v___y_1644_);
v_val_1672_ = lean_ctor_get(v_a_1663_, 0);
lean_inc(v_val_1672_);
lean_dec_ref_known(v_a_1663_, 1);
v___x_1673_ = l_List_appendTR___redArg(v_val_1672_, v___y_1647_);
v___x_1674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_965_);
v___x_1675_ = l_Lean_Name_append(v___x_1674_, v_trace_965_);
v___x_1676_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1648_, v___y_1642_, v___x_1675_);
lean_dec(v___x_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1677_ = l_Lean_trace_profiler;
v___x_1678_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1642_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
lean_inc(v_trace_965_);
v___x_1679_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v_n_1575_, v___x_1673_, v_acc_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1150_ = v___y_1637_;
v___y_1151_ = v_a_1650_;
v___y_1152_ = v___x_1653_;
v___y_1153_ = v___y_1639_;
v___y_1154_ = v___y_1640_;
v___y_1155_ = v___y_1642_;
v___y_1156_ = v___y_1643_;
v___y_1157_ = v___x_1679_;
goto v___jp_1149_;
}
else
{
v___y_1607_ = v___y_1637_;
v___y_1608_ = v_a_1650_;
v___y_1609_ = v___x_1653_;
v___y_1610_ = v___y_1640_;
v___y_1611_ = v___y_1639_;
v___y_1612_ = v___y_1642_;
v___y_1613_ = v___y_1643_;
v___y_1614_ = v___x_1673_;
v___y_1615_ = v___x_1676_;
goto v___jp_1606_;
}
}
else
{
v___y_1607_ = v___y_1637_;
v___y_1608_ = v_a_1650_;
v___y_1609_ = v___x_1653_;
v___y_1610_ = v___y_1640_;
v___y_1611_ = v___y_1639_;
v___y_1612_ = v___y_1642_;
v___y_1613_ = v___y_1643_;
v___y_1614_ = v___x_1673_;
v___y_1615_ = v___x_1676_;
goto v___jp_1606_;
}
}
}
else
{
lean_object* v_a_1680_; 
lean_dec(v___y_1647_);
lean_dec(v___y_1644_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec_ref(v_cfg_964_);
v_a_1680_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1662_, 1);
v___y_1130_ = v___y_1637_;
v___y_1131_ = v___x_1653_;
v___y_1132_ = v_a_1650_;
v___y_1133_ = v___y_1640_;
v___y_1134_ = v___y_1639_;
v___y_1135_ = v___y_1642_;
v___y_1136_ = v___y_1643_;
v_a_1137_ = v_a_1680_;
goto v___jp_1129_;
}
}
else
{
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1644_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec_ref(v_cfg_964_);
v___y_1130_ = v___y_1637_;
v___y_1131_ = v___x_1653_;
v___y_1132_ = v_a_1650_;
v___y_1133_ = v___y_1640_;
v___y_1134_ = v___y_1639_;
v___y_1135_ = v___y_1642_;
v___y_1136_ = v___y_1643_;
v_a_1137_ = v_a_1659_;
goto v___jp_1129_;
}
}
else
{
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1644_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec_ref(v_cfg_964_);
v___y_1130_ = v___y_1637_;
v___y_1131_ = v___x_1653_;
v___y_1132_ = v_a_1650_;
v___y_1133_ = v___y_1640_;
v___y_1134_ = v___y_1639_;
v___y_1135_ = v___y_1642_;
v___y_1136_ = v___y_1643_;
v_a_1137_ = v_a_1659_;
goto v___jp_1129_;
}
}
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
lean_dec_ref(v___y_1646_);
lean_dec_ref(v___y_1645_);
v___x_1681_ = lean_nat_add(v_n_1575_, v_one_1574_);
lean_dec(v_n_1575_);
v___x_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___y_1644_);
lean_ctor_set(v___x_1682_, 1, v_acc_970_);
v___x_1683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_965_);
v___x_1684_ = l_Lean_Name_append(v___x_1683_, v_trace_965_);
v___x_1685_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1648_, v___y_1642_, v___x_1684_);
lean_dec(v___x_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = l_Lean_trace_profiler;
v___x_1687_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1642_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; 
lean_inc(v_trace_965_);
v___x_1688_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___x_1681_, v___y_1647_, v___x_1682_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1150_ = v___y_1637_;
v___y_1151_ = v_a_1650_;
v___y_1152_ = v___x_1653_;
v___y_1153_ = v___y_1639_;
v___y_1154_ = v___y_1640_;
v___y_1155_ = v___y_1642_;
v___y_1156_ = v___y_1643_;
v___y_1157_ = v___x_1688_;
goto v___jp_1149_;
}
else
{
v___y_1369_ = v___y_1637_;
v___y_1370_ = v_a_1650_;
v___y_1371_ = v___x_1653_;
v___y_1372_ = v___y_1640_;
v___y_1373_ = v___y_1639_;
v___y_1374_ = v___y_1647_;
v___y_1375_ = v___x_1681_;
v___y_1376_ = v___y_1642_;
v___y_1377_ = v___x_1685_;
v___y_1378_ = v___y_1643_;
v___y_1379_ = v___x_1682_;
goto v___jp_1368_;
}
}
else
{
v___y_1369_ = v___y_1637_;
v___y_1370_ = v_a_1650_;
v___y_1371_ = v___x_1653_;
v___y_1372_ = v___y_1640_;
v___y_1373_ = v___y_1639_;
v___y_1374_ = v___y_1647_;
v___y_1375_ = v___x_1681_;
v___y_1376_ = v___y_1642_;
v___y_1377_ = v___x_1685_;
v___y_1378_ = v___y_1643_;
v___y_1379_ = v___x_1682_;
goto v___jp_1368_;
}
}
}
else
{
lean_object* v_a_1689_; 
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec_ref(v_cfg_964_);
v_a_1689_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1654_, 1);
v___y_1130_ = v___y_1637_;
v___y_1131_ = v___x_1653_;
v___y_1132_ = v_a_1650_;
v___y_1133_ = v___y_1640_;
v___y_1134_ = v___y_1639_;
v___y_1135_ = v___y_1642_;
v___y_1136_ = v___y_1643_;
v_a_1137_ = v_a_1689_;
goto v___jp_1129_;
}
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec_ref(v___y_1645_);
v___x_1690_ = lean_io_get_num_heartbeats();
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v___y_1644_);
v___x_1691_ = lean_apply_6(v___y_1641_, v___y_1644_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; uint8_t v___x_1693_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1693_ = lean_unbox(v_a_1692_);
lean_dec(v_a_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; 
lean_inc_ref(v_next_966_);
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v___y_1644_);
v___x_1694_ = lean_apply_7(v_next_966_, v___y_1644_, v___y_1638_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; 
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1644_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec_ref(v_cfg_964_);
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
v___y_1089_ = v___y_1637_;
v___y_1090_ = v_a_1650_;
v___y_1091_ = v___y_1640_;
v___y_1092_ = v___y_1639_;
v___y_1093_ = v___x_1690_;
v___y_1094_ = v___y_1642_;
v___y_1095_ = v___y_1643_;
v_a_1096_ = v_a_1695_;
goto v___jp_1088_;
}
else
{
lean_object* v_a_1696_; uint8_t v___x_1697_; 
v_a_1696_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1694_, 1);
v___x_1697_ = l_Lean_Exception_isInterrupt(v_a_1696_);
if (v___x_1697_ == 0)
{
uint8_t v___x_1698_; 
lean_inc(v_a_1696_);
v___x_1698_ = l_Lean_Exception_isRuntime(v_a_1696_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; 
lean_dec(v_a_1696_);
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v___y_1644_);
v___x_1699_ = lean_apply_6(v___y_1646_, v___y_1644_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 1);
if (lean_obj_tag(v_a_1700_) == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1701_ = lean_nat_add(v_n_1575_, v_one_1574_);
lean_dec(v_n_1575_);
v___x_1702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___y_1644_);
lean_ctor_set(v___x_1702_, 1, v_acc_970_);
v___x_1703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_965_);
v___x_1704_ = l_Lean_Name_append(v___x_1703_, v_trace_965_);
v___x_1705_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1648_, v___y_1642_, v___x_1704_);
lean_dec(v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = l_Lean_trace_profiler;
v___x_1707_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1642_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; 
lean_inc(v_trace_965_);
v___x_1708_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___x_1701_, v___y_1647_, v___x_1702_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1099_ = v___y_1637_;
v___y_1100_ = v_a_1650_;
v___y_1101_ = v___y_1639_;
v___y_1102_ = v___y_1640_;
v___y_1103_ = v___x_1690_;
v___y_1104_ = v___y_1642_;
v___y_1105_ = v___y_1643_;
v___y_1106_ = v___x_1708_;
goto v___jp_1098_;
}
else
{
v___y_1421_ = v___x_1702_;
v___y_1422_ = v___y_1637_;
v___y_1423_ = v_a_1650_;
v___y_1424_ = v___y_1640_;
v___y_1425_ = v___y_1639_;
v___y_1426_ = v___x_1705_;
v___y_1427_ = v___x_1690_;
v___y_1428_ = v___y_1647_;
v___y_1429_ = v___y_1642_;
v___y_1430_ = v___x_1701_;
v___y_1431_ = v___y_1643_;
goto v___jp_1420_;
}
}
else
{
v___y_1421_ = v___x_1702_;
v___y_1422_ = v___y_1637_;
v___y_1423_ = v_a_1650_;
v___y_1424_ = v___y_1640_;
v___y_1425_ = v___y_1639_;
v___y_1426_ = v___x_1705_;
v___y_1427_ = v___x_1690_;
v___y_1428_ = v___y_1647_;
v___y_1429_ = v___y_1642_;
v___y_1430_ = v___x_1701_;
v___y_1431_ = v___y_1643_;
goto v___jp_1420_;
}
}
else
{
lean_object* v_val_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
lean_dec(v___y_1644_);
v_val_1709_ = lean_ctor_get(v_a_1700_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v_a_1700_, 1);
v___x_1710_ = l_List_appendTR___redArg(v_val_1709_, v___y_1647_);
v___x_1711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_965_);
v___x_1712_ = l_Lean_Name_append(v___x_1711_, v_trace_965_);
v___x_1713_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1648_, v___y_1642_, v___x_1712_);
lean_dec(v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = l_Lean_trace_profiler;
v___x_1715_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1642_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; 
lean_inc(v_trace_965_);
v___x_1716_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v_n_1575_, v___x_1710_, v_acc_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1099_ = v___y_1637_;
v___y_1100_ = v_a_1650_;
v___y_1101_ = v___y_1639_;
v___y_1102_ = v___y_1640_;
v___y_1103_ = v___x_1690_;
v___y_1104_ = v___y_1642_;
v___y_1105_ = v___y_1643_;
v___y_1106_ = v___x_1716_;
goto v___jp_1098_;
}
else
{
v___y_1577_ = v___x_1710_;
v___y_1578_ = v___x_1713_;
v___y_1579_ = v___y_1637_;
v___y_1580_ = v_a_1650_;
v___y_1581_ = v___y_1640_;
v___y_1582_ = v___y_1639_;
v___y_1583_ = v___x_1690_;
v___y_1584_ = v___y_1642_;
v___y_1585_ = v___y_1643_;
goto v___jp_1576_;
}
}
else
{
v___y_1577_ = v___x_1710_;
v___y_1578_ = v___x_1713_;
v___y_1579_ = v___y_1637_;
v___y_1580_ = v_a_1650_;
v___y_1581_ = v___y_1640_;
v___y_1582_ = v___y_1639_;
v___y_1583_ = v___x_1690_;
v___y_1584_ = v___y_1642_;
v___y_1585_ = v___y_1643_;
goto v___jp_1576_;
}
}
}
else
{
lean_object* v_a_1717_; 
lean_dec(v___y_1647_);
lean_dec(v___y_1644_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec_ref(v_cfg_964_);
v_a_1717_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1699_, 1);
v___y_1079_ = v___y_1637_;
v___y_1080_ = v_a_1650_;
v___y_1081_ = v___y_1640_;
v___y_1082_ = v___y_1639_;
v___y_1083_ = v___x_1690_;
v___y_1084_ = v___y_1642_;
v___y_1085_ = v___y_1643_;
v_a_1086_ = v_a_1717_;
goto v___jp_1078_;
}
}
else
{
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1644_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec_ref(v_cfg_964_);
v___y_1079_ = v___y_1637_;
v___y_1080_ = v_a_1650_;
v___y_1081_ = v___y_1640_;
v___y_1082_ = v___y_1639_;
v___y_1083_ = v___x_1690_;
v___y_1084_ = v___y_1642_;
v___y_1085_ = v___y_1643_;
v_a_1086_ = v_a_1696_;
goto v___jp_1078_;
}
}
else
{
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1644_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec_ref(v_cfg_964_);
v___y_1079_ = v___y_1637_;
v___y_1080_ = v_a_1650_;
v___y_1081_ = v___y_1640_;
v___y_1082_ = v___y_1639_;
v___y_1083_ = v___x_1690_;
v___y_1084_ = v___y_1642_;
v___y_1085_ = v___y_1643_;
v_a_1086_ = v_a_1696_;
goto v___jp_1078_;
}
}
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
lean_dec_ref(v___y_1646_);
lean_dec_ref(v___y_1638_);
v___x_1718_ = lean_nat_add(v_n_1575_, v_one_1574_);
lean_dec(v_n_1575_);
v___x_1719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___y_1644_);
lean_ctor_set(v___x_1719_, 1, v_acc_970_);
v___x_1720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_965_);
v___x_1721_ = l_Lean_Name_append(v___x_1720_, v_trace_965_);
v___x_1722_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1648_, v___y_1642_, v___x_1721_);
lean_dec(v___x_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = l_Lean_trace_profiler;
v___x_1724_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1642_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; 
lean_inc(v_trace_965_);
v___x_1725_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___x_1718_, v___y_1647_, v___x_1719_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
v___y_1099_ = v___y_1637_;
v___y_1100_ = v_a_1650_;
v___y_1101_ = v___y_1639_;
v___y_1102_ = v___y_1640_;
v___y_1103_ = v___x_1690_;
v___y_1104_ = v___y_1642_;
v___y_1105_ = v___y_1643_;
v___y_1106_ = v___x_1725_;
goto v___jp_1098_;
}
else
{
v___y_1473_ = v___y_1637_;
v___y_1474_ = v_a_1650_;
v___y_1475_ = v___x_1719_;
v___y_1476_ = v___y_1640_;
v___y_1477_ = v___y_1639_;
v___y_1478_ = v___x_1690_;
v___y_1479_ = v___y_1647_;
v___y_1480_ = v___y_1642_;
v___y_1481_ = v___x_1722_;
v___y_1482_ = v___y_1643_;
v___y_1483_ = v___x_1718_;
goto v___jp_1472_;
}
}
else
{
v___y_1473_ = v___y_1637_;
v___y_1474_ = v_a_1650_;
v___y_1475_ = v___x_1719_;
v___y_1476_ = v___y_1640_;
v___y_1477_ = v___y_1639_;
v___y_1478_ = v___x_1690_;
v___y_1479_ = v___y_1647_;
v___y_1480_ = v___y_1642_;
v___y_1481_ = v___x_1722_;
v___y_1482_ = v___y_1643_;
v___y_1483_ = v___x_1718_;
goto v___jp_1472_;
}
}
}
else
{
lean_object* v_a_1726_; 
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1638_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec_ref(v_cfg_964_);
v_a_1726_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1691_, 1);
v___y_1079_ = v___y_1637_;
v___y_1080_ = v_a_1650_;
v___y_1081_ = v___y_1640_;
v___y_1082_ = v___y_1639_;
v___y_1083_ = v___x_1690_;
v___y_1084_ = v___y_1642_;
v___y_1085_ = v___y_1643_;
v_a_1086_ = v_a_1726_;
goto v___jp_1078_;
}
}
}
v___jp_1727_:
{
if (lean_obj_tag(v_a_1728_) == 0)
{
if (lean_obj_tag(v_curr_969_) == 0)
{
lean_object* v_toCold_1729_; lean_object* v_options_1730_; lean_object* v_inheritedTraceOptions_1731_; uint8_t v_hasTrace_1732_; lean_object* v___x_1733_; 
lean_dec(v_n_1575_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec_ref(v_cfg_964_);
v_toCold_1729_ = lean_ctor_get(v_a_973_, 0);
v_options_1730_ = lean_ctor_get(v_toCold_1729_, 2);
v_inheritedTraceOptions_1731_ = lean_ctor_get(v_toCold_1729_, 11);
v_hasTrace_1732_ = lean_ctor_get_uint8(v_options_1730_, sizeof(void*)*1);
v___x_1733_ = l_List_reverse___redArg(v_acc_970_);
if (v_hasTrace_1732_ == 0)
{
lean_object* v___x_1734_; 
lean_dec(v_trace_965_);
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1733_);
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_965_);
v___x_1737_ = l_Lean_Name_append(v___x_1736_, v_trace_965_);
v___x_1738_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1731_, v_options_1730_, v___x_1737_);
lean_dec(v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = l_Lean_trace_profiler;
v___x_1740_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1730_, v___x_1739_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
lean_dec(v_trace_965_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1733_);
return v___x_1741_;
}
else
{
v___y_1169_ = v___x_1735_;
v___y_1170_ = v_options_1730_;
v___y_1171_ = v___x_1733_;
v___y_1172_ = v___x_1738_;
v___y_1173_ = v_hasTrace_1732_;
goto v___jp_1168_;
}
}
else
{
v___y_1169_ = v___x_1735_;
v___y_1170_ = v_options_1730_;
v___y_1171_ = v___x_1733_;
v___y_1172_ = v___x_1738_;
v___y_1173_ = v_hasTrace_1732_;
goto v___jp_1168_;
}
}
}
else
{
lean_object* v_head_1742_; lean_object* v_tail_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1973_; 
v_head_1742_ = lean_ctor_get(v_curr_969_, 0);
v_tail_1743_ = lean_ctor_get(v_curr_969_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_curr_969_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1745_ = v_curr_969_;
v_isShared_1746_ = v_isSharedCheck_1973_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_tail_1743_);
lean_inc(v_head_1742_);
lean_dec(v_curr_969_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1973_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___f_1747_; lean_object* v___f_1748_; lean_object* v___f_1749_; lean_object* v___x_1750_; lean_object* v_a_1751_; uint8_t v___x_1752_; uint8_t v___x_1753_; 
lean_inc(v_acc_970_);
lean_inc(v_n_1575_);
lean_inc(v_goals_967_);
lean_inc_ref(v_next_966_);
lean_inc(v_trace_965_);
lean_inc_ref(v_cfg_964_);
lean_inc(v_tail_1743_);
v___f_1747_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__8___boxed), 13, 7);
lean_closure_set(v___f_1747_, 0, v_tail_1743_);
lean_closure_set(v___f_1747_, 1, v_cfg_964_);
lean_closure_set(v___f_1747_, 2, v_trace_965_);
lean_closure_set(v___f_1747_, 3, v_next_966_);
lean_closure_set(v___f_1747_, 4, v_goals_967_);
lean_closure_set(v___f_1747_, 5, v_n_1575_);
lean_closure_set(v___f_1747_, 6, v_acc_970_);
lean_inc_n(v_head_1742_, 2);
v___f_1748_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___boxed), 7, 1);
lean_closure_set(v___f_1748_, 0, v_head_1742_);
v___f_1749_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed), 7, 1);
lean_closure_set(v___f_1749_, 0, v_head_1742_);
v___x_1750_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_1742_, v_a_972_);
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = 1;
v___x_1753_ = lean_unbox(v_a_1751_);
lean_dec(v_a_1751_);
if (v___x_1753_ == 0)
{
lean_object* v_toCold_1754_; lean_object* v_options_1755_; uint8_t v_hasTrace_1756_; 
lean_dec_ref(v___f_1748_);
v_toCold_1754_ = lean_ctor_get(v_a_973_, 0);
v_options_1755_ = lean_ctor_get(v_toCold_1754_, 2);
v_hasTrace_1756_ = lean_ctor_get_uint8(v_options_1755_, sizeof(void*)*1);
if (v_hasTrace_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v___f_1749_);
lean_inc_ref(v_suspend_1165_);
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_head_1742_);
v___x_1757_ = lean_apply_6(v_suspend_1165_, v_head_1742_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; uint8_t v___x_1759_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = lean_unbox(v_a_1758_);
lean_dec(v_a_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_inc_ref(v_next_966_);
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_head_1742_);
v___x_1760_ = lean_apply_7(v_next_966_, v_head_1742_, v___f_1747_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_del_object(v___x_1745_);
lean_dec(v_tail_1743_);
lean_dec(v_head_1742_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
return v___x_1760_;
}
else
{
lean_object* v_a_1761_; uint8_t v___x_1762_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
v___x_1762_ = l_Lean_Exception_isInterrupt(v_a_1761_);
if (v___x_1762_ == 0)
{
uint8_t v___x_1763_; 
v___x_1763_ = l_Lean_Exception_isRuntime(v_a_1761_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_dec_ref_known(v___x_1760_, 1);
lean_inc_ref(v_discharge_1166_);
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_head_1742_);
v___x_1764_ = lean_apply_6(v_discharge_1166_, v_head_1742_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
if (lean_obj_tag(v_a_1765_) == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
v___x_1766_ = lean_nat_add(v_n_1575_, v_one_1574_);
lean_dec(v_n_1575_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_acc_970_);
v___x_1768_ = v___x_1745_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_head_1742_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_acc_970_);
v___x_1768_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
v_n_968_ = v___x_1766_;
v_curr_969_ = v_tail_1743_;
v_acc_970_ = v___x_1768_;
goto _start;
}
}
else
{
lean_object* v_val_1771_; lean_object* v___x_1772_; 
lean_del_object(v___x_1745_);
lean_dec(v_head_1742_);
v_val_1771_ = lean_ctor_get(v_a_1765_, 0);
lean_inc(v_val_1771_);
lean_dec_ref_known(v_a_1765_, 1);
v___x_1772_ = l_List_appendTR___redArg(v_val_1771_, v_tail_1743_);
v_n_968_ = v_n_1575_;
v_curr_969_ = v___x_1772_;
goto _start;
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_del_object(v___x_1745_);
lean_dec(v_tail_1743_);
lean_dec(v_head_1742_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
v_a_1774_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1764_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1764_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
else
{
lean_del_object(v___x_1745_);
lean_dec(v_tail_1743_);
lean_dec(v_head_1742_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
return v___x_1760_;
}
}
else
{
lean_dec(v_a_1761_);
lean_del_object(v___x_1745_);
lean_dec(v_tail_1743_);
lean_dec(v_head_1742_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
return v___x_1760_;
}
}
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
lean_dec_ref(v___f_1747_);
v___x_1782_ = lean_nat_add(v_n_1575_, v_one_1574_);
lean_dec(v_n_1575_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_acc_970_);
v___x_1784_ = v___x_1745_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_head_1742_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_acc_970_);
v___x_1784_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
v_n_968_ = v___x_1782_;
v_curr_969_ = v_tail_1743_;
v_acc_970_ = v___x_1784_;
goto _start;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v___f_1747_);
lean_del_object(v___x_1745_);
lean_dec(v_tail_1743_);
lean_dec(v_head_1742_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
v_a_1787_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1757_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1757_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
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
return v___x_1792_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_inheritedTraceOptions_1795_ = lean_ctor_get(v_toCold_1754_, 11);
v___x_1796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_1797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_965_);
v___x_1798_ = l_Lean_Name_append(v___x_1797_, v_trace_965_);
v___x_1799_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1795_, v_options_1755_, v___x_1798_);
lean_dec(v___x_1798_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = l_Lean_trace_profiler;
v___x_1801_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1755_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; 
lean_dec_ref(v___f_1749_);
lean_inc_ref(v_suspend_1165_);
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_head_1742_);
v___x_1802_ = lean_apply_6(v_suspend_1165_, v_head_1742_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; uint8_t v___x_1804_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v___x_1804_ = lean_unbox(v_a_1803_);
lean_dec(v_a_1803_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
lean_inc_ref(v_next_966_);
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_head_1742_);
v___x_1805_ = lean_apply_7(v_next_966_, v_head_1742_, v___f_1747_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_del_object(v___x_1745_);
lean_dec(v_tail_1743_);
lean_dec(v_head_1742_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
return v___x_1805_;
}
else
{
lean_object* v_a_1806_; uint8_t v___x_1807_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
v___x_1807_ = l_Lean_Exception_isInterrupt(v_a_1806_);
if (v___x_1807_ == 0)
{
uint8_t v___x_1808_; 
v___x_1808_ = l_Lean_Exception_isRuntime(v_a_1806_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; 
lean_dec_ref_known(v___x_1805_, 1);
lean_inc_ref(v_discharge_1166_);
lean_inc(v_a_974_);
lean_inc_ref(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
lean_inc(v_head_1742_);
v___x_1809_ = lean_apply_6(v_discharge_1166_, v_head_1742_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, lean_box(0));
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
if (lean_obj_tag(v_a_1810_) == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_nat_add(v_n_1575_, v_one_1574_);
lean_dec(v_n_1575_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_acc_970_);
v___x_1813_ = v___x_1745_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_head_1742_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_acc_970_);
v___x_1813_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
if (v___x_1799_ == 0)
{
v_n_968_ = v___x_1811_;
v_curr_969_ = v_tail_1743_;
v_acc_970_ = v___x_1813_;
goto _start;
}
else
{
lean_object* v___x_1815_; lean_object* v_a_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1815_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1818_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1755_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_io_mono_nanos_now();
lean_inc(v_trace_965_);
v___x_1820_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___x_1811_, v_tail_1743_, v___x_1813_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set_tag(v___x_1823_, 1);
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
v___y_1521_ = v___x_1752_;
v___y_1522_ = v_a_1816_;
v___y_1523_ = v___x_1799_;
v___y_1524_ = v___x_1796_;
v___y_1525_ = v___x_1819_;
v___y_1526_ = v_options_1755_;
v_a_1527_ = v___x_1826_;
goto v___jp_1520_;
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_a_1829_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1820_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1820_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set_tag(v___x_1831_, 0);
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
v___y_1521_ = v___x_1752_;
v___y_1522_ = v_a_1816_;
v___y_1523_ = v___x_1799_;
v___y_1524_ = v___x_1796_;
v___y_1525_ = v___x_1819_;
v___y_1526_ = v_options_1755_;
v_a_1527_ = v___x_1834_;
goto v___jp_1520_;
}
}
}
}
else
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_965_);
v___x_1838_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___x_1811_, v_tail_1743_, v___x_1813_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set_tag(v___x_1841_, 1);
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
v___y_1505_ = v___x_1752_;
v___y_1506_ = v_a_1816_;
v___y_1507_ = v___x_1799_;
v___y_1508_ = v___x_1796_;
v___y_1509_ = v_options_1755_;
v___y_1510_ = v___x_1837_;
v_a_1511_ = v___x_1844_;
goto v___jp_1504_;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
v_a_1847_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1838_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1838_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set_tag(v___x_1849_, 0);
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
v___y_1505_ = v___x_1752_;
v___y_1506_ = v_a_1816_;
v___y_1507_ = v___x_1799_;
v___y_1508_ = v___x_1796_;
v___y_1509_ = v_options_1755_;
v___y_1510_ = v___x_1837_;
v_a_1511_ = v___x_1852_;
goto v___jp_1504_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_1856_; lean_object* v___x_1857_; 
lean_del_object(v___x_1745_);
lean_dec(v_head_1742_);
v_val_1856_ = lean_ctor_get(v_a_1810_, 0);
lean_inc(v_val_1856_);
lean_dec_ref_known(v_a_1810_, 1);
v___x_1857_ = l_List_appendTR___redArg(v_val_1856_, v_tail_1743_);
if (v___x_1799_ == 0)
{
v_n_968_ = v_n_1575_;
v_curr_969_ = v___x_1857_;
goto _start;
}
else
{
lean_object* v___x_1859_; lean_object* v_a_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1859_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1862_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1755_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_io_mono_nanos_now();
lean_inc(v_trace_965_);
v___x_1864_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v_n_1575_, v___x_1857_, v_acc_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set_tag(v___x_1867_, 1);
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
v___y_1211_ = v___x_1799_;
v___y_1212_ = v___x_1752_;
v___y_1213_ = v___x_1796_;
v___y_1214_ = v_a_1860_;
v___y_1215_ = v_options_1755_;
v___y_1216_ = v___x_1863_;
v_a_1217_ = v___x_1870_;
goto v___jp_1210_;
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_a_1873_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1864_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1864_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set_tag(v___x_1875_, 0);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
v___y_1211_ = v___x_1799_;
v___y_1212_ = v___x_1752_;
v___y_1213_ = v___x_1796_;
v___y_1214_ = v_a_1860_;
v___y_1215_ = v_options_1755_;
v___y_1216_ = v___x_1863_;
v_a_1217_ = v___x_1878_;
goto v___jp_1210_;
}
}
}
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_965_);
v___x_1882_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v_n_1575_, v___x_1857_, v_acc_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set_tag(v___x_1885_, 1);
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
v___y_1230_ = v___x_1799_;
v___y_1231_ = v___x_1752_;
v___y_1232_ = v___x_1796_;
v___y_1233_ = v_a_1860_;
v___y_1234_ = v_options_1755_;
v___y_1235_ = v___x_1881_;
v_a_1236_ = v___x_1888_;
goto v___jp_1229_;
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_a_1891_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1882_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1882_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set_tag(v___x_1893_, 0);
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
v___y_1230_ = v___x_1799_;
v___y_1231_ = v___x_1752_;
v___y_1232_ = v___x_1796_;
v___y_1233_ = v_a_1860_;
v___y_1234_ = v_options_1755_;
v___y_1235_ = v___x_1881_;
v_a_1236_ = v___x_1896_;
goto v___jp_1229_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_del_object(v___x_1745_);
lean_dec(v_tail_1743_);
lean_dec(v_head_1742_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
v_a_1899_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1809_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1809_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
else
{
lean_del_object(v___x_1745_);
lean_dec(v_tail_1743_);
lean_dec(v_head_1742_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
return v___x_1805_;
}
}
else
{
lean_dec(v_a_1806_);
lean_del_object(v___x_1745_);
lean_dec(v_tail_1743_);
lean_dec(v_head_1742_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
return v___x_1805_;
}
}
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
lean_dec_ref(v___f_1747_);
v___x_1907_ = lean_nat_add(v_n_1575_, v_one_1574_);
lean_dec(v_n_1575_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_acc_970_);
v___x_1909_ = v___x_1745_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_head_1742_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_acc_970_);
v___x_1909_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
if (v___x_1799_ == 0)
{
v_n_968_ = v___x_1907_;
v_curr_969_ = v_tail_1743_;
v_acc_970_ = v___x_1909_;
goto _start;
}
else
{
lean_object* v___x_1911_; lean_object* v_a_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1911_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1914_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1755_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_io_mono_nanos_now();
lean_inc(v_trace_965_);
v___x_1916_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___x_1907_, v_tail_1743_, v___x_1909_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 1);
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
v___y_1540_ = v___x_1799_;
v___y_1541_ = v___x_1752_;
v___y_1542_ = v___x_1796_;
v___y_1543_ = v_options_1755_;
v___y_1544_ = v___x_1915_;
v___y_1545_ = v_a_1912_;
v_a_1546_ = v___x_1922_;
goto v___jp_1539_;
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
v_a_1925_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1916_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1916_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set_tag(v___x_1927_, 0);
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
v___y_1540_ = v___x_1799_;
v___y_1541_ = v___x_1752_;
v___y_1542_ = v___x_1796_;
v___y_1543_ = v_options_1755_;
v___y_1544_ = v___x_1915_;
v___y_1545_ = v_a_1912_;
v_a_1546_ = v___x_1930_;
goto v___jp_1539_;
}
}
}
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_965_);
v___x_1934_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___x_1907_, v_tail_1743_, v___x_1909_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set_tag(v___x_1937_, 1);
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
v___y_1559_ = v___x_1799_;
v___y_1560_ = v___x_1752_;
v___y_1561_ = v___x_1796_;
v___y_1562_ = v_options_1755_;
v___y_1563_ = v_a_1912_;
v___y_1564_ = v___x_1933_;
v_a_1565_ = v___x_1940_;
goto v___jp_1558_;
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
v_a_1943_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1934_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1934_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set_tag(v___x_1945_, 0);
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
v___y_1559_ = v___x_1799_;
v___y_1560_ = v___x_1752_;
v___y_1561_ = v___x_1796_;
v___y_1562_ = v_options_1755_;
v___y_1563_ = v_a_1912_;
v___y_1564_ = v___x_1933_;
v_a_1565_ = v___x_1948_;
goto v___jp_1558_;
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
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v___f_1747_);
lean_del_object(v___x_1745_);
lean_dec(v_tail_1743_);
lean_dec(v_head_1742_);
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
v_a_1952_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1802_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1802_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_del_object(v___x_1745_);
lean_inc_ref(v_discharge_1166_);
lean_inc_ref(v_suspend_1165_);
lean_inc_ref(v___f_1747_);
v___y_1637_ = v___x_1752_;
v___y_1638_ = v___f_1747_;
v___y_1639_ = v___x_1799_;
v___y_1640_ = v___x_1796_;
v___y_1641_ = v_suspend_1165_;
v___y_1642_ = v_options_1755_;
v___y_1643_ = v___f_1749_;
v___y_1644_ = v_head_1742_;
v___y_1645_ = v___f_1747_;
v___y_1646_ = v_discharge_1166_;
v___y_1647_ = v_tail_1743_;
v___y_1648_ = v_inheritedTraceOptions_1795_;
goto v___jp_1636_;
}
}
else
{
lean_del_object(v___x_1745_);
lean_inc_ref(v_discharge_1166_);
lean_inc_ref(v_suspend_1165_);
lean_inc_ref(v___f_1747_);
v___y_1637_ = v___x_1752_;
v___y_1638_ = v___f_1747_;
v___y_1639_ = v___x_1799_;
v___y_1640_ = v___x_1796_;
v___y_1641_ = v_suspend_1165_;
v___y_1642_ = v_options_1755_;
v___y_1643_ = v___f_1749_;
v___y_1644_ = v_head_1742_;
v___y_1645_ = v___f_1747_;
v___y_1646_ = v_discharge_1166_;
v___y_1647_ = v_tail_1743_;
v___y_1648_ = v_inheritedTraceOptions_1795_;
goto v___jp_1636_;
}
}
}
else
{
lean_object* v_toCold_1960_; lean_object* v_options_1961_; lean_object* v_inheritedTraceOptions_1962_; uint8_t v_hasTrace_1963_; lean_object* v___x_1964_; 
lean_dec_ref(v___f_1749_);
lean_dec_ref(v___f_1747_);
lean_del_object(v___x_1745_);
lean_dec(v_head_1742_);
v_toCold_1960_ = lean_ctor_get(v_a_973_, 0);
v_options_1961_ = lean_ctor_get(v_toCold_1960_, 2);
v_inheritedTraceOptions_1962_ = lean_ctor_get(v_toCold_1960_, 11);
v_hasTrace_1963_ = lean_ctor_get_uint8(v_options_1961_, sizeof(void*)*1);
v___x_1964_ = lean_nat_add(v_n_1575_, v_one_1574_);
lean_dec(v_n_1575_);
if (v_hasTrace_1963_ == 0)
{
lean_dec_ref(v___f_1748_);
v_n_968_ = v___x_1964_;
v_curr_969_ = v_tail_1743_;
goto _start;
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_1967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_965_);
v___x_1968_ = l_Lean_Name_append(v___x_1967_, v_trace_965_);
v___x_1969_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1962_, v_options_1961_, v___x_1968_);
lean_dec(v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1970_ = l_Lean_trace_profiler;
v___x_1971_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1961_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_dec_ref(v___f_1748_);
v_n_968_ = v___x_1964_;
v_curr_969_ = v_tail_1743_;
goto _start;
}
else
{
v___y_1014_ = v___x_1752_;
v___y_1015_ = v___x_1969_;
v___y_1016_ = v_options_1961_;
v___y_1017_ = v_tail_1743_;
v___y_1018_ = v___x_1964_;
v___y_1019_ = v___x_1966_;
v___y_1020_ = v___f_1748_;
goto v___jp_1013_;
}
}
else
{
v___y_1014_ = v___x_1752_;
v___y_1015_ = v___x_1969_;
v___y_1016_ = v_options_1961_;
v___y_1017_ = v_tail_1743_;
v___y_1018_ = v___x_1964_;
v___y_1019_ = v___x_1966_;
v___y_1020_ = v___f_1748_;
goto v___jp_1013_;
}
}
}
}
}
}
else
{
lean_object* v_val_1974_; 
lean_dec(v_curr_969_);
v_val_1974_ = lean_ctor_get(v_a_1728_, 0);
lean_inc(v_val_1974_);
lean_dec_ref_known(v_a_1728_, 1);
v_n_968_ = v_n_1575_;
v_curr_969_ = v_val_1974_;
goto _start;
}
}
v___jp_1976_:
{
if (lean_obj_tag(v___y_1977_) == 0)
{
lean_object* v_a_1978_; 
v_a_1978_ = lean_ctor_get(v___y_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___y_1977_, 1);
v_a_1728_ = v_a_1978_;
goto v___jp_1727_;
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec(v_n_1575_);
lean_dec(v_acc_970_);
lean_dec(v_curr_969_);
lean_dec(v_goals_967_);
lean_dec_ref(v_next_966_);
lean_dec(v_trace_965_);
lean_dec_ref(v_cfg_964_);
v_a_1979_ = lean_ctor_get(v___y_1977_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___y_1977_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___y_1977_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___y_1977_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
v___jp_976_:
{
lean_object* v___x_985_; double v___x_986_; double v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_985_ = lean_io_get_num_heartbeats();
v___x_986_ = lean_float_of_nat(v___y_980_);
v___x_987_ = lean_float_of_nat(v___x_985_);
v___x_988_ = lean_box_float(v___x_986_);
v___x_989_ = lean_box_float(v___x_987_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_a_984_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
lean_inc_ref(v___y_982_);
v___x_992_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_978_, v___y_982_, v___y_979_, v___y_977_, v___y_981_, v___y_983_, v___x_991_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_992_;
}
v___jp_993_:
{
lean_object* v___x_1002_; double v___x_1003_; double v___x_1004_; double v___x_1005_; double v___x_1006_; double v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1002_ = lean_io_mono_nanos_now();
v___x_1003_ = lean_float_of_nat(v___y_997_);
v___x_1004_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1005_ = lean_float_div(v___x_1003_, v___x_1004_);
v___x_1006_ = lean_float_of_nat(v___x_1002_);
v___x_1007_ = lean_float_div(v___x_1006_, v___x_1004_);
v___x_1008_ = lean_box_float(v___x_1005_);
v___x_1009_ = lean_box_float(v___x_1007_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1011_, 0, v_a_1001_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
lean_inc_ref(v___y_999_);
v___x_1012_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_995_, v___y_999_, v___y_996_, v___y_994_, v___y_998_, v___y_1000_, v___x_1011_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1012_;
}
v___jp_1013_:
{
lean_object* v___x_1021_; lean_object* v_a_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1021_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_974_);
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1024_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1016_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_io_mono_nanos_now();
lean_inc(v_trace_965_);
v___x_1026_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___y_1018_, v___y_1017_, v_acc_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set_tag(v___x_1029_, 1);
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
v___y_994_ = v___y_1015_;
v___y_995_ = v___y_1014_;
v___y_996_ = v___y_1016_;
v___y_997_ = v___x_1025_;
v___y_998_ = v_a_1022_;
v___y_999_ = v___y_1019_;
v___y_1000_ = v___y_1020_;
v_a_1001_ = v___x_1032_;
goto v___jp_993_;
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
v_a_1035_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1026_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1026_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 0);
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
v___y_994_ = v___y_1015_;
v___y_995_ = v___y_1014_;
v___y_996_ = v___y_1016_;
v___y_997_ = v___x_1025_;
v___y_998_ = v_a_1022_;
v___y_999_ = v___y_1019_;
v___y_1000_ = v___y_1020_;
v_a_1001_ = v___x_1040_;
goto v___jp_993_;
}
}
}
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_965_);
v___x_1044_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_964_, v_trace_965_, v_next_966_, v_goals_967_, v___y_1018_, v___y_1017_, v_acc_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 1);
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
v___y_977_ = v___y_1015_;
v___y_978_ = v___y_1014_;
v___y_979_ = v___y_1016_;
v___y_980_ = v___x_1043_;
v___y_981_ = v_a_1022_;
v___y_982_ = v___y_1019_;
v___y_983_ = v___y_1020_;
v_a_984_ = v___x_1050_;
goto v___jp_976_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1044_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1044_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 0);
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
v___y_977_ = v___y_1015_;
v___y_978_ = v___y_1014_;
v___y_979_ = v___y_1016_;
v___y_980_ = v___x_1043_;
v___y_981_ = v_a_1022_;
v___y_982_ = v___y_1019_;
v___y_983_ = v___y_1020_;
v_a_984_ = v___x_1058_;
goto v___jp_976_;
}
}
}
}
}
v___jp_1061_:
{
lean_object* v___x_1070_; double v___x_1071_; double v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1070_ = lean_io_get_num_heartbeats();
v___x_1071_ = lean_float_of_nat(v___y_1066_);
v___x_1072_ = lean_float_of_nat(v___x_1070_);
v___x_1073_ = lean_box_float(v___x_1071_);
v___x_1074_ = lean_box_float(v___x_1072_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_a_1069_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
lean_inc_ref(v___y_1065_);
v___x_1077_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1062_, v___y_1065_, v___y_1067_, v___y_1064_, v___y_1063_, v___y_1068_, v___x_1076_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1077_;
}
v___jp_1078_:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_a_1086_);
v___y_1062_ = v___y_1079_;
v___y_1063_ = v___y_1080_;
v___y_1064_ = v___y_1082_;
v___y_1065_ = v___y_1081_;
v___y_1066_ = v___y_1083_;
v___y_1067_ = v___y_1084_;
v___y_1068_ = v___y_1085_;
v_a_1069_ = v___x_1087_;
goto v___jp_1061_;
}
v___jp_1088_:
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_a_1096_);
v___y_1062_ = v___y_1089_;
v___y_1063_ = v___y_1090_;
v___y_1064_ = v___y_1092_;
v___y_1065_ = v___y_1091_;
v___y_1066_ = v___y_1093_;
v___y_1067_ = v___y_1094_;
v___y_1068_ = v___y_1095_;
v_a_1069_ = v___x_1097_;
goto v___jp_1061_;
}
v___jp_1098_:
{
if (lean_obj_tag(v___y_1106_) == 0)
{
lean_object* v_a_1107_; 
v_a_1107_ = lean_ctor_get(v___y_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___y_1106_, 1);
v___y_1089_ = v___y_1099_;
v___y_1090_ = v___y_1100_;
v___y_1091_ = v___y_1102_;
v___y_1092_ = v___y_1101_;
v___y_1093_ = v___y_1103_;
v___y_1094_ = v___y_1104_;
v___y_1095_ = v___y_1105_;
v_a_1096_ = v_a_1107_;
goto v___jp_1088_;
}
else
{
lean_object* v_a_1108_; 
v_a_1108_ = lean_ctor_get(v___y_1106_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___y_1106_, 1);
v___y_1079_ = v___y_1099_;
v___y_1080_ = v___y_1100_;
v___y_1081_ = v___y_1102_;
v___y_1082_ = v___y_1101_;
v___y_1083_ = v___y_1103_;
v___y_1084_ = v___y_1104_;
v___y_1085_ = v___y_1105_;
v_a_1086_ = v_a_1108_;
goto v___jp_1078_;
}
}
v___jp_1109_:
{
lean_object* v___x_1118_; double v___x_1119_; double v___x_1120_; double v___x_1121_; double v___x_1122_; double v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1118_ = lean_io_mono_nanos_now();
v___x_1119_ = lean_float_of_nat(v___y_1112_);
v___x_1120_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1121_ = lean_float_div(v___x_1119_, v___x_1120_);
v___x_1122_ = lean_float_of_nat(v___x_1118_);
v___x_1123_ = lean_float_div(v___x_1122_, v___x_1120_);
v___x_1124_ = lean_box_float(v___x_1121_);
v___x_1125_ = lean_box_float(v___x_1123_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1127_, 0, v_a_1117_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
lean_inc_ref(v___y_1114_);
v___x_1128_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_965_, v___y_1110_, v___y_1114_, v___y_1115_, v___y_1113_, v___y_1111_, v___y_1116_, v___x_1127_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1128_;
}
v___jp_1129_:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_a_1137_);
v___y_1110_ = v___y_1130_;
v___y_1111_ = v___y_1132_;
v___y_1112_ = v___y_1131_;
v___y_1113_ = v___y_1134_;
v___y_1114_ = v___y_1133_;
v___y_1115_ = v___y_1135_;
v___y_1116_ = v___y_1136_;
v_a_1117_ = v___x_1138_;
goto v___jp_1109_;
}
v___jp_1139_:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v_a_1147_);
v___y_1110_ = v___y_1140_;
v___y_1111_ = v___y_1142_;
v___y_1112_ = v___y_1141_;
v___y_1113_ = v___y_1144_;
v___y_1114_ = v___y_1143_;
v___y_1115_ = v___y_1145_;
v___y_1116_ = v___y_1146_;
v_a_1117_ = v___x_1148_;
goto v___jp_1109_;
}
v___jp_1149_:
{
if (lean_obj_tag(v___y_1157_) == 0)
{
lean_object* v_a_1158_; 
v_a_1158_ = lean_ctor_get(v___y_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___y_1157_, 1);
v___y_1140_ = v___y_1150_;
v___y_1141_ = v___y_1152_;
v___y_1142_ = v___y_1151_;
v___y_1143_ = v___y_1154_;
v___y_1144_ = v___y_1153_;
v___y_1145_ = v___y_1155_;
v___y_1146_ = v___y_1156_;
v_a_1147_ = v_a_1158_;
goto v___jp_1139_;
}
else
{
lean_object* v_a_1159_; 
v_a_1159_ = lean_ctor_get(v___y_1157_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___y_1157_, 1);
v___y_1130_ = v___y_1150_;
v___y_1131_ = v___y_1152_;
v___y_1132_ = v___y_1151_;
v___y_1133_ = v___y_1154_;
v___y_1134_ = v___y_1153_;
v___y_1135_ = v___y_1155_;
v___y_1136_ = v___y_1156_;
v_a_1137_ = v_a_1159_;
goto v___jp_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2055_, lean_object* v_trace_2056_, lean_object* v_next_2057_, lean_object* v_goals_2058_, lean_object* v_n_2059_, lean_object* v_curr_2060_, lean_object* v_acc_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2055_, v_trace_2056_, v_next_2057_, v_goals_2058_, v_n_2059_, v_curr_2060_, v_acc_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__8(lean_object* v_tail_2068_, lean_object* v_cfg_2069_, lean_object* v_trace_2070_, lean_object* v_next_2071_, lean_object* v_goals_2072_, lean_object* v_n_2073_, lean_object* v_acc_2074_, lean_object* v_r_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = l_List_appendTR___redArg(v_r_2075_, v_tail_2068_);
v___x_2082_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2082_, 0, v_cfg_2069_);
lean_closure_set(v___x_2082_, 1, v_trace_2070_);
lean_closure_set(v___x_2082_, 2, v_next_2071_);
lean_closure_set(v___x_2082_, 3, v_goals_2072_);
lean_closure_set(v___x_2082_, 4, v_n_2073_);
lean_closure_set(v___x_2082_, 5, v___x_2081_);
lean_closure_set(v___x_2082_, 6, v_acc_2074_);
v___x_2083_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v___x_2082_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2084_, lean_object* v_msg_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2092_, lean_object* v_msg_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2092_, v_msg_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object* v_00_u03b1_2100_, lean_object* v_x_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_2101_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2108_, lean_object* v_x_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_00_u03b1_2108_, v_x_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* v_mvarId_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_2116_, v___y_2118_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* v_mvarId_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_mvarId_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v_mvarId_2123_);
return v_res_2129_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_object* v_00_u03b2_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_){
_start:
{
uint8_t v___x_2133_; 
v___x_2133_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_2131_, v_x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2134_, lean_object* v_x_2135_, lean_object* v_x_2136_){
_start:
{
uint8_t v_res_2137_; lean_object* v_r_2138_; 
v_res_2137_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(v_00_u03b2_2134_, v_x_2135_, v_x_2136_);
lean_dec(v_x_2136_);
lean_dec_ref(v_x_2135_);
v_r_2138_ = lean_box(v_res_2137_);
return v_r_2138_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_2139_, lean_object* v_x_2140_, size_t v_x_2141_, lean_object* v_x_2142_){
_start:
{
uint8_t v___x_2143_; 
v___x_2143_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_2140_, v_x_2141_, v_x_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___boxed(lean_object* v_00_u03b2_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_){
_start:
{
size_t v_x_76650__boxed_2148_; uint8_t v_res_2149_; lean_object* v_r_2150_; 
v_x_76650__boxed_2148_ = lean_unbox_usize(v_x_2146_);
lean_dec(v_x_2146_);
v_res_2149_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2144_, v_x_2145_, v_x_76650__boxed_2148_, v_x_2147_);
lean_dec(v_x_2147_);
lean_dec_ref(v_x_2145_);
v_r_2150_ = lean_box(v_res_2149_);
return v_r_2150_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_object* v_00_u03b2_2151_, lean_object* v_keys_2152_, lean_object* v_vals_2153_, lean_object* v_heq_2154_, lean_object* v_i_2155_, lean_object* v_k_2156_){
_start:
{
uint8_t v___x_2157_; 
v___x_2157_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_2152_, v_i_2155_, v_k_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2158_, lean_object* v_keys_2159_, lean_object* v_vals_2160_, lean_object* v_heq_2161_, lean_object* v_i_2162_, lean_object* v_k_2163_){
_start:
{
uint8_t v_res_2164_; lean_object* v_r_2165_; 
v_res_2164_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(v_00_u03b2_2158_, v_keys_2159_, v_vals_2160_, v_heq_2161_, v_i_2162_, v_k_2163_);
lean_dec(v_k_2163_);
lean_dec_ref(v_vals_2160_);
lean_dec_ref(v_keys_2159_);
v_r_2165_ = lean_box(v_res_2164_);
return v_r_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2166_, lean_object* v_h__1_2167_, lean_object* v_h__2_2168_){
_start:
{
lean_object* v_zero_2169_; uint8_t v_isZero_2170_; 
v_zero_2169_ = lean_unsigned_to_nat(0u);
v_isZero_2170_ = lean_nat_dec_eq(v_n_2166_, v_zero_2169_);
if (v_isZero_2170_ == 1)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec(v_h__2_2168_);
v___x_2171_ = lean_box(0);
v___x_2172_ = lean_apply_1(v_h__1_2167_, v___x_2171_);
return v___x_2172_;
}
else
{
lean_object* v_one_2173_; lean_object* v_n_2174_; lean_object* v___x_2175_; 
lean_dec(v_h__1_2167_);
v_one_2173_ = lean_unsigned_to_nat(1u);
v_n_2174_ = lean_nat_sub(v_n_2166_, v_one_2173_);
v___x_2175_ = lean_apply_1(v_h__2_2168_, v_n_2174_);
return v___x_2175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2176_, lean_object* v_h__1_2177_, lean_object* v_h__2_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2176_, v_h__1_2177_, v_h__2_2178_);
lean_dec(v_n_2176_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2180_, lean_object* v_n_2181_, lean_object* v_h__1_2182_, lean_object* v_h__2_2183_){
_start:
{
lean_object* v_zero_2184_; uint8_t v_isZero_2185_; 
v_zero_2184_ = lean_unsigned_to_nat(0u);
v_isZero_2185_ = lean_nat_dec_eq(v_n_2181_, v_zero_2184_);
if (v_isZero_2185_ == 1)
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
lean_dec(v_h__2_2183_);
v___x_2186_ = lean_box(0);
v___x_2187_ = lean_apply_1(v_h__1_2182_, v___x_2186_);
return v___x_2187_;
}
else
{
lean_object* v_one_2188_; lean_object* v_n_2189_; lean_object* v___x_2190_; 
lean_dec(v_h__1_2182_);
v_one_2188_ = lean_unsigned_to_nat(1u);
v_n_2189_ = lean_nat_sub(v_n_2181_, v_one_2188_);
v___x_2190_ = lean_apply_1(v_h__2_2183_, v_n_2189_);
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* v_motive_2191_, lean_object* v_n_2192_, lean_object* v_h__1_2193_, lean_object* v_h__2_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(v_motive_2191_, v_n_2192_, v_h__1_2193_, v_h__2_2194_);
lean_dec(v_n_2192_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* v_procResult_x3f_2196_, lean_object* v_h__1_2197_, lean_object* v_h__2_2198_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2196_) == 0)
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec(v_h__1_2197_);
v___x_2199_ = lean_box(0);
v___x_2200_ = lean_apply_1(v_h__2_2198_, v___x_2199_);
return v___x_2200_;
}
else
{
lean_object* v_val_2201_; lean_object* v___x_2202_; 
lean_dec(v_h__2_2198_);
v_val_2201_ = lean_ctor_get(v_procResult_x3f_2196_, 0);
lean_inc(v_val_2201_);
lean_dec_ref_known(v_procResult_x3f_2196_, 1);
v___x_2202_ = lean_apply_1(v_h__1_2197_, v_val_2201_);
return v___x_2202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* v_motive_2203_, lean_object* v_procResult_x3f_2204_, lean_object* v_h__1_2205_, lean_object* v_h__2_2206_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2204_) == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec(v_h__1_2205_);
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_apply_1(v_h__2_2206_, v___x_2207_);
return v___x_2208_;
}
else
{
lean_object* v_val_2209_; lean_object* v___x_2210_; 
lean_dec(v_h__2_2206_);
v_val_2209_ = lean_ctor_get(v_procResult_x3f_2204_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v_procResult_x3f_2204_, 1);
v___x_2210_ = lean_apply_1(v_h__1_2205_, v_val_2209_);
return v___x_2210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2211_, lean_object* v_h__1_2212_, lean_object* v_h__2_2213_){
_start:
{
if (lean_obj_tag(v_curr_2211_) == 0)
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_dec(v_h__2_2213_);
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_apply_1(v_h__1_2212_, v___x_2214_);
return v___x_2215_;
}
else
{
lean_object* v_head_2216_; lean_object* v_tail_2217_; lean_object* v___x_2218_; 
lean_dec(v_h__1_2212_);
v_head_2216_ = lean_ctor_get(v_curr_2211_, 0);
lean_inc(v_head_2216_);
v_tail_2217_ = lean_ctor_get(v_curr_2211_, 1);
lean_inc(v_tail_2217_);
lean_dec_ref_known(v_curr_2211_, 2);
v___x_2218_ = lean_apply_2(v_h__2_2213_, v_head_2216_, v_tail_2217_);
return v___x_2218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2219_, lean_object* v_curr_2220_, lean_object* v_h__1_2221_, lean_object* v_h__2_2222_){
_start:
{
if (lean_obj_tag(v_curr_2220_) == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_dec(v_h__2_2222_);
v___x_2223_ = lean_box(0);
v___x_2224_ = lean_apply_1(v_h__1_2221_, v___x_2223_);
return v___x_2224_;
}
else
{
lean_object* v_head_2225_; lean_object* v_tail_2226_; lean_object* v___x_2227_; 
lean_dec(v_h__1_2221_);
v_head_2225_ = lean_ctor_get(v_curr_2220_, 0);
lean_inc(v_head_2225_);
v_tail_2226_ = lean_ctor_get(v_curr_2220_, 1);
lean_inc(v_tail_2226_);
lean_dec_ref_known(v_curr_2220_, 2);
v___x_2227_ = lean_apply_2(v_h__2_2222_, v_head_2225_, v_tail_2226_);
return v___x_2227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2228_, lean_object* v_h__1_2229_, lean_object* v_h__2_2230_){
_start:
{
if (lean_obj_tag(v_____do__lift_2228_) == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_dec(v_h__2_2230_);
v___x_2231_ = lean_box(0);
v___x_2232_ = lean_apply_1(v_h__1_2229_, v___x_2231_);
return v___x_2232_;
}
else
{
lean_object* v_val_2233_; lean_object* v___x_2234_; 
lean_dec(v_h__1_2229_);
v_val_2233_ = lean_ctor_get(v_____do__lift_2228_, 0);
lean_inc(v_val_2233_);
lean_dec_ref_known(v_____do__lift_2228_, 1);
v___x_2234_ = lean_apply_1(v_h__2_2230_, v_val_2233_);
return v___x_2234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_2235_, lean_object* v_____do__lift_2236_, lean_object* v_h__1_2237_, lean_object* v_h__2_2238_){
_start:
{
if (lean_obj_tag(v_____do__lift_2236_) == 0)
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec(v_h__2_2238_);
v___x_2239_ = lean_box(0);
v___x_2240_ = lean_apply_1(v_h__1_2237_, v___x_2239_);
return v___x_2240_;
}
else
{
lean_object* v_val_2241_; lean_object* v___x_2242_; 
lean_dec(v_h__1_2237_);
v_val_2241_ = lean_ctor_get(v_____do__lift_2236_, 0);
lean_inc(v_val_2241_);
lean_dec_ref_known(v_____do__lift_2236_, 1);
v___x_2242_ = lean_apply_1(v_h__2_2238_, v_val_2241_);
return v___x_2242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_2243_, lean_object* v_trace_2244_, lean_object* v_next_2245_, lean_object* v_orig_2246_, lean_object* v_g_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_maxDepth_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v_maxDepth_2253_ = lean_ctor_get(v_cfg_2243_, 0);
lean_inc(v_maxDepth_2253_);
v___x_2254_ = lean_box(0);
v___x_2255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2255_, 0, v_g_2247_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2243_, v_trace_2244_, v_next_2245_, v_orig_2246_, v_maxDepth_2253_, v___x_2255_, v___x_2254_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_2257_, lean_object* v_trace_2258_, lean_object* v_next_2259_, lean_object* v_orig_2260_, lean_object* v_g_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2257_, v_trace_2258_, v_next_2259_, v_orig_2260_, v_g_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
if (lean_obj_tag(v_a_2268_) == 0)
{
lean_object* v___x_2270_; 
v___x_2270_ = l_List_reverse___redArg(v_a_2269_);
return v___x_2270_;
}
else
{
lean_object* v_head_2271_; lean_object* v_tail_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2281_; 
v_head_2271_ = lean_ctor_get(v_a_2268_, 0);
v_tail_2272_ = lean_ctor_get(v_a_2268_, 1);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_a_2268_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2274_ = v_a_2268_;
v_isShared_2275_ = v_isSharedCheck_2281_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_tail_2272_);
lean_inc(v_head_2271_);
lean_dec(v_a_2268_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2281_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = l_Lean_MessageData_ofFormat(v_head_2271_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 1, v_a_2269_);
lean_ctor_set(v___x_2274_, 0, v___x_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_a_2269_);
v___x_2278_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
v_a_2268_ = v_tail_2272_;
v_a_2269_ = v___x_2278_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_2284_ = l_Lean_stringToMessageData(v___x_2283_);
return v___x_2284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_2287_ = l_Lean_stringToMessageData(v___x_2286_);
return v___x_2287_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_2290_ = l_Lean_stringToMessageData(v___x_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_2291_, lean_object* v_snd_2292_, lean_object* v_x_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2291_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_2292_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2321_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2321_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2321_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_2307_ = lean_box(0);
v___x_2308_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2300_, v___x_2307_);
v___x_2309_ = l_Lean_MessageData_ofList(v___x_2308_);
v___x_2310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2306_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_2314_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2302_, v___x_2307_);
v___x_2315_ = l_Lean_MessageData_ofList(v___x_2314_);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2313_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2312_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2317_);
v___x_2319_ = v___x_2304_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_a_2300_);
v_a_2322_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2301_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2301_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v_snd_2292_);
v_a_2330_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2299_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2299_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_2338_, lean_object* v_snd_2339_, lean_object* v_x_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2338_, v_snd_2339_, v_x_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec_ref(v_x_2340_);
return v_res_2346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_2349_ = l_Lean_stringToMessageData(v___x_2348_);
return v___x_2349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_2352_ = l_Lean_stringToMessageData(v___x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_2353_, lean_object* v___x_2354_, lean_object* v_x_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2353_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_2354_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2381_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2381_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2381_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2368_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_2369_ = lean_box(0);
v___x_2370_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2362_, v___x_2369_);
v___x_2371_ = l_Lean_MessageData_ofList(v___x_2370_);
v___x_2372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2368_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2364_, v___x_2369_);
v___x_2376_ = l_Lean_MessageData_ofList(v___x_2375_);
v___x_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2374_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2377_);
v___x_2379_ = v___x_2366_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v_a_2362_);
v_a_2382_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2363_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2363_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v___x_2354_);
v_a_2390_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2361_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2361_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_2398_, lean_object* v___x_2399_, lean_object* v_x_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2398_, v___x_2399_, v_x_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec_ref(v_x_2400_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t v___x_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_, lean_object* v___y_2410_){
_start:
{
if (lean_obj_tag(v_x_2408_) == 0)
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2412_, 0, v_x_2409_);
return v___x_2412_;
}
else
{
lean_object* v_head_2413_; lean_object* v_tail_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2427_; 
v_head_2413_ = lean_ctor_get(v_x_2408_, 0);
v_tail_2414_ = lean_ctor_get(v_x_2408_, 1);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_x_2408_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2416_ = v_x_2408_;
v_isShared_2417_ = v_isSharedCheck_2427_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_tail_2414_);
lean_inc(v_head_2413_);
lean_dec(v_x_2408_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2427_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2423_; lean_object* v_a_2424_; uint8_t v___x_2425_; 
v___x_2423_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2413_, v___y_2410_);
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref(v___x_2423_);
v___x_2425_ = lean_unbox(v_a_2424_);
lean_dec(v_a_2424_);
if (v___x_2425_ == 0)
{
goto v___jp_2418_;
}
else
{
if (v___x_2407_ == 0)
{
lean_del_object(v___x_2416_);
lean_dec(v_head_2413_);
v_x_2408_ = v_tail_2414_;
goto _start;
}
else
{
goto v___jp_2418_;
}
}
v___jp_2418_:
{
lean_object* v___x_2420_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v_x_2409_);
v___x_2420_ = v___x_2416_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_head_2413_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_x_2409_);
v___x_2420_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
v_x_2408_ = v_tail_2414_;
v_x_2409_ = v___x_2420_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v___x_2428_, lean_object* v_x_2429_, lean_object* v_x_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
uint8_t v___x_46397__boxed_2433_; lean_object* v_res_2434_; 
v___x_46397__boxed_2433_ = lean_unbox(v___x_2428_);
v_res_2434_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_46397__boxed_2433_, v_x_2429_, v_x_2430_, v___y_2431_);
lean_dec(v___y_2431_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
if (lean_obj_tag(v_a_2435_) == 0)
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_array_to_list(v_a_2436_);
return v___x_2437_;
}
else
{
lean_object* v_head_2438_; lean_object* v_tail_2439_; lean_object* v___x_2440_; 
v_head_2438_ = lean_ctor_get(v_a_2435_, 0);
lean_inc(v_head_2438_);
v_tail_2439_ = lean_ctor_get(v_a_2435_, 1);
lean_inc(v_tail_2439_);
lean_dec_ref_known(v_a_2435_, 2);
v___x_2440_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2436_, v_head_2438_);
v_a_2435_ = v_tail_2439_;
v_a_2436_ = v___x_2440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
if (lean_obj_tag(v_a_2443_) == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
lean_dec(v_goals_2442_);
v___x_2451_ = lean_array_to_list(v_a_2444_);
v___x_2452_ = lean_array_to_list(v_a_2445_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2451_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
return v___x_2454_;
}
else
{
lean_object* v_head_2455_; lean_object* v_tail_2456_; lean_object* v___x_2457_; 
v_head_2455_ = lean_ctor_get(v_a_2443_, 0);
lean_inc_n(v_head_2455_, 2);
v_tail_2456_ = lean_ctor_get(v_a_2443_, 1);
lean_inc(v_tail_2456_);
lean_dec_ref_known(v_a_2443_, 2);
lean_inc(v_goals_2442_);
v___x_2457_ = l_Lean_MVarId_isIndependentOf(v_goals_2442_, v_head_2455_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; uint8_t v___x_2459_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___x_2459_ = lean_unbox(v_a_2458_);
lean_dec(v_a_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_array_push(v_a_2445_, v_head_2455_);
v_a_2443_ = v_tail_2456_;
v_a_2445_ = v___x_2460_;
goto _start;
}
else
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_array_push(v_a_2444_, v_head_2455_);
v_a_2443_ = v_tail_2456_;
v_a_2444_ = v___x_2462_;
goto _start;
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_tail_2456_);
lean_dec(v_head_2455_);
lean_dec_ref(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_goals_2442_);
v_a_2464_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2457_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2457_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
if (lean_obj_tag(v_a_2482_) == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_array_to_list(v_a_2483_);
return v___x_2484_;
}
else
{
lean_object* v_head_2485_; 
v_head_2485_ = lean_ctor_get(v_a_2482_, 0);
if (lean_obj_tag(v_head_2485_) == 0)
{
lean_object* v_tail_2486_; lean_object* v_val_2487_; lean_object* v___x_2488_; 
lean_inc_ref(v_head_2485_);
v_tail_2486_ = lean_ctor_get(v_a_2482_, 1);
lean_inc(v_tail_2486_);
lean_dec_ref_known(v_a_2482_, 2);
v_val_2487_ = lean_ctor_get(v_head_2485_, 0);
lean_inc(v_val_2487_);
lean_dec_ref_known(v_head_2485_, 1);
v___x_2488_ = lean_array_push(v_a_2483_, v_val_2487_);
v_a_2482_ = v_tail_2486_;
v_a_2483_ = v___x_2488_;
goto _start;
}
else
{
lean_object* v_tail_2490_; 
v_tail_2490_ = lean_ctor_get(v_a_2482_, 1);
lean_inc(v_tail_2490_);
lean_dec_ref_known(v_a_2482_, 2);
v_a_2482_ = v_tail_2490_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_2492_, lean_object* v_x_2493_, lean_object* v_x_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
if (lean_obj_tag(v_x_2493_) == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_dec_ref(v_f_2492_);
v___x_2500_ = l_List_reverse___redArg(v_x_2494_);
v___x_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
return v___x_2501_;
}
else
{
lean_object* v_head_2502_; lean_object* v_tail_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2549_; 
v_head_2502_ = lean_ctor_get(v_x_2493_, 0);
v_tail_2503_ = lean_ctor_get(v_x_2493_, 1);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_x_2493_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2505_ = v_x_2493_;
v_isShared_2506_ = v_isSharedCheck_2549_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_tail_2503_);
lean_inc(v_head_2502_);
lean_dec(v_x_2493_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2549_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v_a_2508_; lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_Meta_saveState___redArg(v___y_2496_, v___y_2498_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2515_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2513_, 1);
lean_inc_ref(v_f_2492_);
lean_inc(v___y_2498_);
lean_inc_ref(v___y_2497_);
lean_inc(v___y_2496_);
lean_inc_ref(v___y_2495_);
lean_inc(v_head_2502_);
v___x_2515_ = lean_apply_6(v_f_2492_, v_head_2502_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, lean_box(0));
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2517_; 
lean_dec(v_a_2514_);
lean_dec(v_head_2502_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2517_, 0, v_a_2516_);
v_a_2508_ = v___x_2517_;
goto v___jp_2507_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2540_; 
v_a_2518_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2520_ = v___x_2515_;
v_isShared_2521_ = v_isSharedCheck_2540_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2515_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2540_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
uint8_t v___x_2522_; 
v___x_2522_ = l_Lean_Exception_isInterrupt(v_a_2518_);
if (v___x_2522_ == 0)
{
uint8_t v___x_2523_; 
lean_inc(v_a_2518_);
v___x_2523_ = l_Lean_Exception_isRuntime(v_a_2518_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
lean_del_object(v___x_2520_);
lean_dec(v_a_2518_);
v___x_2524_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2514_, v___y_2496_, v___y_2498_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v___x_2525_; 
lean_dec_ref_known(v___x_2524_, 1);
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_head_2502_);
v_a_2508_ = v___x_2525_;
goto v___jp_2507_;
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_del_object(v___x_2505_);
lean_dec(v_tail_2503_);
lean_dec(v_head_2502_);
lean_dec(v_x_2494_);
lean_dec_ref(v_f_2492_);
v_a_2526_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2524_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2524_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_object* v___x_2535_; 
lean_dec(v_a_2514_);
lean_del_object(v___x_2505_);
lean_dec(v_tail_2503_);
lean_dec(v_head_2502_);
lean_dec(v_x_2494_);
lean_dec_ref(v_f_2492_);
if (v_isShared_2521_ == 0)
{
v___x_2535_ = v___x_2520_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2518_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
else
{
lean_object* v___x_2538_; 
lean_dec(v_a_2514_);
lean_del_object(v___x_2505_);
lean_dec(v_tail_2503_);
lean_dec(v_head_2502_);
lean_dec(v_x_2494_);
lean_dec_ref(v_f_2492_);
if (v_isShared_2521_ == 0)
{
v___x_2538_ = v___x_2520_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2518_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_del_object(v___x_2505_);
lean_dec(v_tail_2503_);
lean_dec(v_head_2502_);
lean_dec(v_x_2494_);
lean_dec_ref(v_f_2492_);
v_a_2541_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2513_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2513_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
v___jp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 1, v_x_2494_);
lean_ctor_set(v___x_2505_, 0, v_a_2508_);
v___x_2510_ = v___x_2505_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2508_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_x_2494_);
v___x_2510_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
v_x_2493_ = v_tail_2503_;
v_x_2494_ = v___x_2510_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_2550_, lean_object* v_x_2551_, lean_object* v_x_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2550_, v_x_2551_, v_x_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
if (lean_obj_tag(v_a_2559_) == 0)
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_array_to_list(v_a_2560_);
return v___x_2561_;
}
else
{
lean_object* v_head_2562_; 
v_head_2562_ = lean_ctor_get(v_a_2559_, 0);
if (lean_obj_tag(v_head_2562_) == 1)
{
lean_object* v_tail_2563_; lean_object* v_val_2564_; lean_object* v___x_2565_; 
lean_inc_ref(v_head_2562_);
v_tail_2563_ = lean_ctor_get(v_a_2559_, 1);
lean_inc(v_tail_2563_);
lean_dec_ref_known(v_a_2559_, 2);
v_val_2564_ = lean_ctor_get(v_head_2562_, 0);
lean_inc(v_val_2564_);
lean_dec_ref_known(v_head_2562_, 1);
v___x_2565_ = lean_array_push(v_a_2560_, v_val_2564_);
v_a_2559_ = v_tail_2563_;
v_a_2560_ = v___x_2565_;
goto _start;
}
else
{
lean_object* v_tail_2567_; 
v_tail_2567_ = lean_ctor_get(v_a_2559_, 1);
lean_inc(v_tail_2567_);
lean_dec_ref_known(v_a_2559_, 2);
v_a_2559_ = v_tail_2567_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_2569_, lean_object* v_f_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_box(0);
v___x_2577_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2570_, v_L_2569_, v___x_2576_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2589_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2589_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2589_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2582_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_2578_);
v___x_2583_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_2578_, v___x_2582_);
v___x_2584_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_2578_, v___x_2582_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2583_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2585_);
v___x_2587_ = v___x_2580_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
v_a_2590_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2577_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2577_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* v_L_2598_, lean_object* v_f_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_2598_, v_f_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t v___x_2606_, uint8_t v___x_2607_, lean_object* v_x_2608_, lean_object* v_x_2609_, lean_object* v___y_2610_){
_start:
{
if (lean_obj_tag(v_x_2608_) == 0)
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v_x_2609_);
return v___x_2612_;
}
else
{
lean_object* v_head_2613_; lean_object* v_tail_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2628_; 
v_head_2613_ = lean_ctor_get(v_x_2608_, 0);
v_tail_2614_ = lean_ctor_get(v_x_2608_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_x_2608_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2616_ = v_x_2608_;
v_isShared_2617_ = v_isSharedCheck_2628_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_tail_2614_);
lean_inc(v_head_2613_);
lean_dec(v_x_2608_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2628_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
uint8_t v_a_2619_; lean_object* v___x_2625_; lean_object* v_a_2626_; uint8_t v___x_2627_; 
v___x_2625_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2613_, v___y_2610_);
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref(v___x_2625_);
v___x_2627_ = lean_unbox(v_a_2626_);
lean_dec(v_a_2626_);
if (v___x_2627_ == 0)
{
v_a_2619_ = v___x_2606_;
goto v___jp_2618_;
}
else
{
v_a_2619_ = v___x_2607_;
goto v___jp_2618_;
}
v___jp_2618_:
{
if (v_a_2619_ == 0)
{
lean_del_object(v___x_2616_);
lean_dec(v_head_2613_);
v_x_2608_ = v_tail_2614_;
goto _start;
}
else
{
lean_object* v___x_2622_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 1, v_x_2609_);
v___x_2622_ = v___x_2616_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_head_2613_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_x_2609_);
v___x_2622_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
v_x_2608_ = v_tail_2614_;
v_x_2609_ = v___x_2622_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* v___x_2629_, lean_object* v___x_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
uint8_t v___x_46749__boxed_2635_; uint8_t v___x_46750__boxed_2636_; lean_object* v_res_2637_; 
v___x_46749__boxed_2635_ = lean_unbox(v___x_2629_);
v___x_46750__boxed_2636_ = lean_unbox(v___x_2630_);
v_res_2637_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_46749__boxed_2635_, v___x_46750__boxed_2636_, v_x_2631_, v_x_2632_, v___y_2633_);
lean_dec(v___y_2633_);
return v_res_2637_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1));
v___x_2642_ = l_Lean_stringToMessageData(v___x_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_2643_, lean_object* v_trace_2644_, lean_object* v_next_2645_, lean_object* v_orig_2646_, lean_object* v_goals_2647_, lean_object* v_remaining_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v___f_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_inc(v_orig_2646_);
lean_inc_ref(v_next_2645_);
lean_inc(v_trace_2644_);
lean_inc_ref(v_cfg_2643_);
v___f_2654_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2654_, 0, v_cfg_2643_);
lean_closure_set(v___f_2654_, 1, v_trace_2644_);
lean_closure_set(v___f_2654_, 2, v_next_2645_);
lean_closure_set(v___f_2654_, 3, v_orig_2646_);
v___x_2655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
lean_inc(v_remaining_2648_);
lean_inc(v_goals_2647_);
v___x_2656_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2647_, v_remaining_2648_, v___x_2655_, v___x_2655_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_3300_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v_fst_2658_ = lean_ctor_get(v_a_2657_, 0);
v_snd_2659_ = lean_ctor_get(v_a_2657_, 1);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_a_2657_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_2661_ = v_a_2657_;
v_isShared_2662_ = v_isSharedCheck_3300_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_snd_2659_);
lean_inc(v_fst_2658_);
lean_dec(v_a_2657_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_3300_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
uint8_t v___x_2663_; 
v___x_2663_ = l_List_isEmpty___redArg(v_fst_2658_);
if (v___x_2663_ == 0)
{
lean_object* v_toCold_2664_; lean_object* v_options_2665_; uint8_t v_hasTrace_2666_; 
lean_dec(v_remaining_2648_);
v_toCold_2664_ = lean_ctor_get(v_a_2651_, 0);
v_options_2665_ = lean_ctor_get(v_toCold_2664_, 2);
v_hasTrace_2666_ = lean_ctor_get_uint8(v_options_2665_, sizeof(void*)*1);
if (v_hasTrace_2666_ == 0)
{
lean_object* v___x_2667_; 
lean_del_object(v___x_2661_);
v___x_2667_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2658_, v___f_2654_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2727_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2727_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2727_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_fst_2672_; lean_object* v_snd_2673_; lean_object* v___x_2674_; lean_object* v_a_2676_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v_fst_2672_ = lean_ctor_get(v_a_2668_, 0);
lean_inc(v_fst_2672_);
v_snd_2673_ = lean_ctor_get(v_a_2668_, 1);
lean_inc(v_snd_2673_);
lean_dec(v_a_2668_);
v___x_2674_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_2673_, v___x_2655_);
v___x_2682_ = lean_box(0);
v___x_2683_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_2663_, v_goals_2647_, v___x_2682_, v_a_2650_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; uint8_t v_commitIndependentGoals_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v___x_2683_, 1);
v_commitIndependentGoals_2685_ = lean_ctor_get_uint8(v_cfg_2643_, sizeof(void*)*4);
v___x_2686_ = l_List_reverse___redArg(v_a_2684_);
lean_inc(v___x_2674_);
v___x_2687_ = l_List_appendTR___redArg(v___x_2686_, v___x_2674_);
if (v_commitIndependentGoals_2685_ == 0)
{
lean_del_object(v___x_2670_);
goto v___jp_2688_;
}
else
{
uint8_t v___x_2702_; 
v___x_2702_ = l_List_isEmpty___redArg(v___x_2674_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_Meta_saveState___redArg(v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2705_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
lean_inc(v_snd_2659_);
v___x_2705_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_2687_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v_a_2706_; 
lean_dec(v_a_2704_);
lean_dec(v_snd_2659_);
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2705_, 1);
v_a_2676_ = v_a_2706_;
goto v___jp_2675_;
}
else
{
lean_object* v_a_2707_; uint8_t v___x_2708_; 
v_a_2707_ = lean_ctor_get(v___x_2705_, 0);
v___x_2708_ = l_Lean_Exception_isInterrupt(v_a_2707_);
if (v___x_2708_ == 0)
{
uint8_t v___x_2709_; 
lean_inc(v_a_2707_);
v___x_2709_ = l_Lean_Exception_isRuntime(v_a_2707_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; 
lean_dec_ref_known(v___x_2705_, 1);
v___x_2710_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2704_, v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_dec_ref_known(v___x_2710_, 1);
v_a_2676_ = v_snd_2659_;
goto v___jp_2675_;
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v___x_2674_);
lean_dec(v_fst_2672_);
lean_del_object(v___x_2670_);
lean_dec(v_snd_2659_);
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
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
else
{
lean_dec(v_a_2704_);
lean_dec(v___x_2674_);
lean_dec(v_fst_2672_);
lean_del_object(v___x_2670_);
lean_dec(v_snd_2659_);
return v___x_2705_;
}
}
else
{
lean_dec(v_a_2704_);
lean_dec(v___x_2674_);
lean_dec(v_fst_2672_);
lean_del_object(v___x_2670_);
lean_dec(v_snd_2659_);
return v___x_2705_;
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v___x_2687_);
lean_dec(v___x_2674_);
lean_dec(v_fst_2672_);
lean_del_object(v___x_2670_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec(v_trace_2644_);
lean_dec_ref(v_cfg_2643_);
v_a_2719_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2703_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2703_);
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
else
{
lean_del_object(v___x_2670_);
goto v___jp_2688_;
}
}
v___jp_2688_:
{
uint8_t v___x_2689_; 
v___x_2689_ = l_List_isEmpty___redArg(v_fst_2672_);
lean_dec(v_fst_2672_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
lean_dec(v___x_2687_);
lean_dec(v___x_2674_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec(v_trace_2644_);
lean_dec_ref(v_cfg_2643_);
v___x_2690_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_2691_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_2690_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
return v___x_2691_;
}
else
{
lean_object* v___x_2692_; 
v___x_2692_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_2687_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2701_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2695_ = v___x_2692_;
v_isShared_2696_ = v_isSharedCheck_2701_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2692_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2701_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = l_List_appendTR___redArg(v___x_2674_, v_a_2693_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set(v___x_2695_, 0, v___x_2697_);
v___x_2699_ = v___x_2695_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
else
{
lean_dec(v___x_2674_);
return v___x_2692_;
}
}
}
}
else
{
lean_dec(v___x_2674_);
lean_dec(v_fst_2672_);
lean_del_object(v___x_2670_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec(v_trace_2644_);
lean_dec_ref(v_cfg_2643_);
return v___x_2683_;
}
v___jp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2677_ = l_List_appendTR___redArg(v___x_2674_, v_fst_2672_);
v___x_2678_ = l_List_appendTR___redArg(v___x_2677_, v_a_2676_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2678_);
v___x_2680_ = v___x_2670_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_snd_2659_);
lean_dec(v_goals_2647_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec(v_trace_2644_);
lean_dec_ref(v_cfg_2643_);
v_a_2728_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2667_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2667_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2736_; lean_object* v___f_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; lean_object* v___y_2743_; lean_object* v___y_2744_; lean_object* v_a_2745_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v_a_2759_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v_a_2766_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v_a_2772_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2781_; lean_object* v___y_2782_; uint8_t v___y_2783_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v_a_2787_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; uint8_t v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v_a_2803_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; uint8_t v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v_a_2812_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; uint8_t v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; uint8_t v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v_a_2842_; lean_object* v___y_2846_; lean_object* v___y_2847_; uint8_t v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; uint8_t v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v_a_2891_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v_a_2906_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v_a_2911_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v_a_2918_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; uint8_t v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v_a_2947_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; uint8_t v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v_a_2966_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; uint8_t v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v_a_2975_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; uint8_t v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v_a_2986_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; uint8_t v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; uint8_t v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; 
v_inheritedTraceOptions_2736_ = lean_ctor_get(v_toCold_2664_, 11);
lean_inc(v_snd_2659_);
lean_inc(v_fst_2658_);
v___f_2737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_2737_, 0, v_fst_2658_);
lean_closure_set(v___f_2737_, 1, v_snd_2659_);
v___x_2738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_2644_);
v___x_2740_ = l_Lean_Name_append(v___x_2739_, v_trace_2644_);
v___x_2741_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2736_, v_options_2665_, v___x_2740_);
lean_dec(v___x_2740_);
if (v___x_2741_ == 0)
{
lean_object* v___x_3106_; uint8_t v___x_3107_; 
v___x_3106_ = l_Lean_trace_profiler;
v___x_3107_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2665_, v___x_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; 
lean_dec_ref(v___f_2737_);
lean_del_object(v___x_2661_);
v___x_3108_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2658_, v___f_2654_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3288_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3111_ = v___x_3108_;
v_isShared_3112_ = v_isSharedCheck_3288_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3288_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v_fst_3113_; lean_object* v_snd_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3287_; 
v_fst_3113_ = lean_ctor_get(v_a_3109_, 0);
v_snd_3114_ = lean_ctor_get(v_a_3109_, 1);
v_isSharedCheck_3287_ = !lean_is_exclusive(v_a_3109_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3116_ = v_a_3109_;
v_isShared_3117_ = v_isSharedCheck_3287_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_snd_3114_);
lean_inc(v_fst_3113_);
lean_dec(v_a_3109_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3287_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v_a_3120_; lean_object* v___x_3126_; 
v___x_3118_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3114_, v___x_2655_);
v___x_3126_ = lean_box(0);
if (v___x_2741_ == 0)
{
lean_object* v___x_3127_; 
lean_del_object(v___x_3116_);
v___x_3127_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2666_, v___x_2663_, v_goals_2647_, v___x_3126_, v_a_2650_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; uint8_t v_commitIndependentGoals_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3127_, 1);
v_commitIndependentGoals_3129_ = lean_ctor_get_uint8(v_cfg_2643_, sizeof(void*)*4);
v___x_3130_ = l_List_reverse___redArg(v_a_3128_);
lean_inc(v___x_3118_);
v___x_3131_ = l_List_appendTR___redArg(v___x_3130_, v___x_3118_);
if (v_commitIndependentGoals_3129_ == 0)
{
lean_del_object(v___x_3111_);
goto v___jp_3132_;
}
else
{
uint8_t v___x_3146_; 
v___x_3146_ = l_List_isEmpty___redArg(v___x_3118_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
v___x_3147_ = l_Lean_Meta_saveState___redArg(v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3149_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3147_, 1);
lean_inc(v_snd_2659_);
v___x_3149_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_3131_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; 
lean_dec(v_a_3148_);
lean_dec(v_snd_2659_);
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc(v_a_3150_);
lean_dec_ref_known(v___x_3149_, 1);
v_a_3120_ = v_a_3150_;
goto v___jp_3119_;
}
else
{
lean_object* v_a_3151_; uint8_t v___x_3152_; 
v_a_3151_ = lean_ctor_get(v___x_3149_, 0);
v___x_3152_ = l_Lean_Exception_isInterrupt(v_a_3151_);
if (v___x_3152_ == 0)
{
uint8_t v___x_3153_; 
lean_inc(v_a_3151_);
v___x_3153_ = l_Lean_Exception_isRuntime(v_a_3151_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; 
lean_dec_ref_known(v___x_3149_, 1);
v___x_3154_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3148_, v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_dec_ref_known(v___x_3154_, 1);
v_a_3120_ = v_snd_2659_;
goto v___jp_3119_;
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_del_object(v___x_3111_);
lean_dec(v_snd_2659_);
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3154_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_dec(v_a_3148_);
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_del_object(v___x_3111_);
lean_dec(v_snd_2659_);
return v___x_3149_;
}
}
else
{
lean_dec(v_a_3148_);
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_del_object(v___x_3111_);
lean_dec(v_snd_2659_);
return v___x_3149_;
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v___x_3131_);
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_del_object(v___x_3111_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec(v_trace_2644_);
lean_dec_ref(v_cfg_2643_);
v_a_3163_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3147_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3147_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_del_object(v___x_3111_);
goto v___jp_3132_;
}
}
v___jp_3132_:
{
uint8_t v___x_3133_; 
v___x_3133_ = l_List_isEmpty___redArg(v_fst_3113_);
lean_dec(v_fst_3113_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec(v___x_3131_);
lean_dec(v___x_3118_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec(v_trace_2644_);
lean_dec_ref(v_cfg_2643_);
v___x_3134_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3135_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3134_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
return v___x_3135_;
}
else
{
lean_object* v___x_3136_; 
v___x_3136_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_3131_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3145_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3139_ = v___x_3136_;
v_isShared_3140_ = v_isSharedCheck_3145_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3136_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3145_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3141_; lean_object* v___x_3143_; 
v___x_3141_ = l_List_appendTR___redArg(v___x_3118_, v_a_3137_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 0, v___x_3141_);
v___x_3143_ = v___x_3139_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
else
{
lean_dec(v___x_3118_);
return v___x_3136_;
}
}
}
}
else
{
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_del_object(v___x_3111_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec(v_trace_2644_);
lean_dec_ref(v_cfg_2643_);
return v___x_3127_;
}
}
else
{
lean_object* v___f_3171_; lean_object* v___x_3172_; 
lean_del_object(v___x_3111_);
lean_inc(v___x_3118_);
lean_inc(v_fst_3113_);
v___f_3171_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3171_, 0, v_fst_3113_);
lean_closure_set(v___f_3171_, 1, v___x_3118_);
v___x_3172_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2652_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3172_, 1);
v___x_3174_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3175_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2665_, v___x_3174_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v_a_3178_; lean_object* v_a_3193_; lean_object* v_a_3196_; lean_object* v_a_3200_; lean_object* v___x_3202_; 
v___x_3176_ = lean_io_mono_nanos_now();
v___x_3202_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2666_, v___x_2663_, v_goals_2647_, v___x_3126_, v_a_2650_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; uint8_t v_commitIndependentGoals_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref_known(v___x_3202_, 1);
v_commitIndependentGoals_3204_ = lean_ctor_get_uint8(v_cfg_2643_, sizeof(void*)*4);
v___x_3205_ = l_List_reverse___redArg(v_a_3203_);
lean_inc(v___x_3118_);
v___x_3206_ = l_List_appendTR___redArg(v___x_3205_, v___x_3118_);
if (v_commitIndependentGoals_3204_ == 0)
{
goto v___jp_3207_;
}
else
{
uint8_t v___x_3217_; 
v___x_3217_ = l_List_isEmpty___redArg(v___x_3118_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_Meta_saveState___redArg(v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3220_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
lean_inc(v_snd_2659_);
lean_inc(v_trace_2644_);
v___x_3220_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_3206_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; 
lean_dec(v_a_3219_);
lean_dec(v_snd_2659_);
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3220_, 1);
v_a_3196_ = v_a_3221_;
goto v___jp_3195_;
}
else
{
lean_object* v_a_3222_; uint8_t v___x_3223_; 
v_a_3222_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3220_, 1);
v___x_3223_ = l_Lean_Exception_isInterrupt(v_a_3222_);
if (v___x_3223_ == 0)
{
uint8_t v___x_3224_; 
lean_inc(v_a_3222_);
v___x_3224_ = l_Lean_Exception_isRuntime(v_a_3222_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
lean_dec(v_a_3222_);
v___x_3225_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3219_, v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_dec_ref_known(v___x_3225_, 1);
v_a_3196_ = v_snd_2659_;
goto v___jp_3195_;
}
else
{
lean_object* v_a_3226_; 
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_dec(v_snd_2659_);
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3225_, 1);
v_a_3200_ = v_a_3226_;
goto v___jp_3199_;
}
}
else
{
lean_dec(v_a_3219_);
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_dec(v_snd_2659_);
v_a_3200_ = v_a_3222_;
goto v___jp_3199_;
}
}
else
{
lean_dec(v_a_3219_);
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_dec(v_snd_2659_);
v_a_3200_ = v_a_3222_;
goto v___jp_3199_;
}
}
}
else
{
lean_object* v_a_3227_; 
lean_dec(v___x_3206_);
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3227_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3218_, 1);
v_a_3200_ = v_a_3227_;
goto v___jp_3199_;
}
}
else
{
goto v___jp_3207_;
}
}
v___jp_3207_:
{
uint8_t v___x_3208_; 
v___x_3208_ = l_List_isEmpty___redArg(v_fst_3113_);
lean_dec(v_fst_3113_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_dec(v___x_3206_);
lean_dec(v___x_3118_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v___x_3209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3210_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3209_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v_a_3193_ = v_a_3211_;
goto v___jp_3192_;
}
else
{
lean_object* v_a_3212_; 
v_a_3212_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3210_, 1);
v_a_3200_ = v_a_3212_;
goto v___jp_3199_;
}
}
else
{
lean_object* v___x_3213_; 
lean_inc(v_trace_2644_);
v___x_3213_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_3206_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3215_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v___x_3215_ = l_List_appendTR___redArg(v___x_3118_, v_a_3214_);
v_a_3193_ = v___x_3215_;
goto v___jp_3192_;
}
else
{
lean_object* v_a_3216_; 
lean_dec(v___x_3118_);
v_a_3216_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3213_, 1);
v_a_3200_ = v_a_3216_;
goto v___jp_3199_;
}
}
}
}
else
{
lean_object* v_a_3228_; 
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3228_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___x_3202_, 1);
v_a_3200_ = v_a_3228_;
goto v___jp_3199_;
}
v___jp_3177_:
{
lean_object* v___x_3179_; double v___x_3180_; double v___x_3181_; double v___x_3182_; double v___x_3183_; double v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3188_; 
v___x_3179_ = lean_io_mono_nanos_now();
v___x_3180_ = lean_float_of_nat(v___x_3176_);
v___x_3181_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3182_ = lean_float_div(v___x_3180_, v___x_3181_);
v___x_3183_ = lean_float_of_nat(v___x_3179_);
v___x_3184_ = lean_float_div(v___x_3183_, v___x_3181_);
v___x_3185_ = lean_box_float(v___x_3182_);
v___x_3186_ = lean_box_float(v___x_3184_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 1, v___x_3186_);
lean_ctor_set(v___x_3116_, 0, v___x_3185_);
v___x_3188_ = v___x_3116_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3185_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v___x_3186_);
v___x_3188_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3189_, 0, v_a_3178_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2644_, v_hasTrace_2666_, v___x_2738_, v_options_2665_, v___x_2741_, v_a_3173_, v___f_3171_, v___x_3189_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
return v___x_3190_;
}
}
v___jp_3192_:
{
lean_object* v___x_3194_; 
v___x_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3194_, 0, v_a_3193_);
v_a_3178_ = v___x_3194_;
goto v___jp_3177_;
}
v___jp_3195_:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = l_List_appendTR___redArg(v___x_3118_, v_fst_3113_);
v___x_3198_ = l_List_appendTR___redArg(v___x_3197_, v_a_3196_);
v_a_3193_ = v___x_3198_;
goto v___jp_3192_;
}
v___jp_3199_:
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3201_, 0, v_a_3200_);
v_a_3178_ = v___x_3201_;
goto v___jp_3177_;
}
}
else
{
lean_object* v___x_3229_; lean_object* v_a_3231_; lean_object* v_a_3243_; lean_object* v_a_3246_; lean_object* v_a_3250_; lean_object* v___x_3252_; 
v___x_3229_ = lean_io_get_num_heartbeats();
v___x_3252_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2666_, v___x_2663_, v_goals_2647_, v___x_3126_, v_a_2650_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; uint8_t v_commitIndependentGoals_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref_known(v___x_3252_, 1);
v_commitIndependentGoals_3254_ = lean_ctor_get_uint8(v_cfg_2643_, sizeof(void*)*4);
v___x_3255_ = l_List_reverse___redArg(v_a_3253_);
lean_inc(v___x_3118_);
v___x_3256_ = l_List_appendTR___redArg(v___x_3255_, v___x_3118_);
if (v_commitIndependentGoals_3254_ == 0)
{
goto v___jp_3257_;
}
else
{
uint8_t v___x_3267_; 
v___x_3267_ = l_List_isEmpty___redArg(v___x_3118_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = l_Lean_Meta_saveState___redArg(v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
lean_inc(v_snd_2659_);
lean_inc(v_trace_2644_);
v___x_3270_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_3256_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; 
lean_dec(v_a_3269_);
lean_dec(v_snd_2659_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v_a_3246_ = v_a_3271_;
goto v___jp_3245_;
}
else
{
lean_object* v_a_3272_; uint8_t v___x_3273_; 
v_a_3272_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3273_ = l_Lean_Exception_isInterrupt(v_a_3272_);
if (v___x_3273_ == 0)
{
uint8_t v___x_3274_; 
lean_inc(v_a_3272_);
v___x_3274_ = l_Lean_Exception_isRuntime(v_a_3272_);
if (v___x_3274_ == 0)
{
lean_object* v___x_3275_; 
lean_dec(v_a_3272_);
v___x_3275_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3269_, v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_dec_ref_known(v___x_3275_, 1);
v_a_3246_ = v_snd_2659_;
goto v___jp_3245_;
}
else
{
lean_object* v_a_3276_; 
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_dec(v_snd_2659_);
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3275_, 1);
v_a_3250_ = v_a_3276_;
goto v___jp_3249_;
}
}
else
{
lean_dec(v_a_3269_);
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_dec(v_snd_2659_);
v_a_3250_ = v_a_3272_;
goto v___jp_3249_;
}
}
else
{
lean_dec(v_a_3269_);
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_dec(v_snd_2659_);
v_a_3250_ = v_a_3272_;
goto v___jp_3249_;
}
}
}
else
{
lean_object* v_a_3277_; 
lean_dec(v___x_3256_);
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3277_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3268_, 1);
v_a_3250_ = v_a_3277_;
goto v___jp_3249_;
}
}
else
{
goto v___jp_3257_;
}
}
v___jp_3257_:
{
uint8_t v___x_3258_; 
v___x_3258_ = l_List_isEmpty___redArg(v_fst_3113_);
lean_dec(v_fst_3113_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_dec(v___x_3256_);
lean_dec(v___x_3118_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v___x_3259_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3260_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3259_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v_a_3243_ = v_a_3261_;
goto v___jp_3242_;
}
else
{
lean_object* v_a_3262_; 
v_a_3262_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3262_);
lean_dec_ref_known(v___x_3260_, 1);
v_a_3250_ = v_a_3262_;
goto v___jp_3249_;
}
}
else
{
lean_object* v___x_3263_; 
lean_inc(v_trace_2644_);
v___x_3263_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_3256_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3265_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref_known(v___x_3263_, 1);
v___x_3265_ = l_List_appendTR___redArg(v___x_3118_, v_a_3264_);
v_a_3243_ = v___x_3265_;
goto v___jp_3242_;
}
else
{
lean_object* v_a_3266_; 
lean_dec(v___x_3118_);
v_a_3266_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3263_, 1);
v_a_3250_ = v_a_3266_;
goto v___jp_3249_;
}
}
}
}
else
{
lean_object* v_a_3278_; 
lean_dec(v___x_3118_);
lean_dec(v_fst_3113_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3278_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3252_, 1);
v_a_3250_ = v_a_3278_;
goto v___jp_3249_;
}
v___jp_3230_:
{
lean_object* v___x_3232_; double v___x_3233_; double v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3232_ = lean_io_get_num_heartbeats();
v___x_3233_ = lean_float_of_nat(v___x_3229_);
v___x_3234_ = lean_float_of_nat(v___x_3232_);
v___x_3235_ = lean_box_float(v___x_3233_);
v___x_3236_ = lean_box_float(v___x_3234_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 1, v___x_3236_);
lean_ctor_set(v___x_3116_, 0, v___x_3235_);
v___x_3238_ = v___x_3116_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3239_, 0, v_a_3231_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2644_, v_hasTrace_2666_, v___x_2738_, v_options_2665_, v___x_2741_, v_a_3173_, v___f_3171_, v___x_3239_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
return v___x_3240_;
}
}
v___jp_3242_:
{
lean_object* v___x_3244_; 
v___x_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3244_, 0, v_a_3243_);
v_a_3231_ = v___x_3244_;
goto v___jp_3230_;
}
v___jp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = l_List_appendTR___redArg(v___x_3118_, v_fst_3113_);
v___x_3248_ = l_List_appendTR___redArg(v___x_3247_, v_a_3246_);
v_a_3243_ = v___x_3248_;
goto v___jp_3242_;
}
v___jp_3249_:
{
lean_object* v___x_3251_; 
v___x_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3251_, 0, v_a_3250_);
v_a_3231_ = v___x_3251_;
goto v___jp_3230_;
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec_ref(v___f_3171_);
lean_dec(v___x_3118_);
lean_del_object(v___x_3116_);
lean_dec(v_fst_3113_);
lean_dec(v_snd_2659_);
lean_dec(v_goals_2647_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec(v_trace_2644_);
lean_dec_ref(v_cfg_2643_);
v_a_3279_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3172_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3172_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
v___jp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3121_ = l_List_appendTR___redArg(v___x_3118_, v_fst_3113_);
v___x_3122_ = l_List_appendTR___redArg(v___x_3121_, v_a_3120_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3122_);
v___x_3124_ = v___x_3111_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec(v_snd_2659_);
lean_dec(v_goals_2647_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec(v_trace_2644_);
lean_dec_ref(v_cfg_2643_);
v_a_3289_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3108_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3108_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
else
{
goto v___jp_3037_;
}
}
else
{
goto v___jp_3037_;
}
v___jp_2742_:
{
lean_object* v___x_2746_; double v___x_2747_; double v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2746_ = lean_io_get_num_heartbeats();
v___x_2747_ = lean_float_of_nat(v___y_2744_);
v___x_2748_ = lean_float_of_nat(v___x_2746_);
v___x_2749_ = lean_box_float(v___x_2747_);
v___x_2750_ = lean_box_float(v___x_2748_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2750_);
lean_ctor_set(v___x_2661_, 0, v___x_2749_);
v___x_2752_ = v___x_2661_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v___x_2750_);
v___x_2752_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v_a_2745_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2644_, v_hasTrace_2666_, v___x_2738_, v_options_2665_, v___x_2741_, v___y_2743_, v___f_2737_, v___x_2753_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
return v___x_2754_;
}
}
v___jp_2756_:
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2760_, 0, v_a_2759_);
v___y_2743_ = v___y_2757_;
v___y_2744_ = v___y_2758_;
v_a_2745_ = v___x_2760_;
goto v___jp_2742_;
}
v___jp_2761_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = l_List_appendTR___redArg(v___y_2765_, v___y_2762_);
v___x_2768_ = l_List_appendTR___redArg(v___x_2767_, v_a_2766_);
v___y_2757_ = v___y_2763_;
v___y_2758_ = v___y_2764_;
v_a_2759_ = v___x_2768_;
goto v___jp_2756_;
}
v___jp_2769_:
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2773_, 0, v_a_2772_);
v___y_2743_ = v___y_2770_;
v___y_2744_ = v___y_2771_;
v_a_2745_ = v___x_2773_;
goto v___jp_2742_;
}
v___jp_2774_:
{
if (lean_obj_tag(v___y_2777_) == 0)
{
lean_object* v_a_2778_; 
v_a_2778_ = lean_ctor_get(v___y_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___y_2777_, 1);
v___y_2757_ = v___y_2775_;
v___y_2758_ = v___y_2776_;
v_a_2759_ = v_a_2778_;
goto v___jp_2756_;
}
else
{
lean_object* v_a_2779_; 
v_a_2779_ = lean_ctor_get(v___y_2777_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___y_2777_, 1);
v___y_2770_ = v___y_2775_;
v___y_2771_ = v___y_2776_;
v_a_2772_ = v_a_2779_;
goto v___jp_2769_;
}
}
v___jp_2780_:
{
lean_object* v___x_2788_; double v___x_2789_; double v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2788_ = lean_io_get_num_heartbeats();
v___x_2789_ = lean_float_of_nat(v___y_2784_);
v___x_2790_ = lean_float_of_nat(v___x_2788_);
v___x_2791_ = lean_box_float(v___x_2789_);
v___x_2792_ = lean_box_float(v___x_2790_);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v_a_2787_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
lean_inc(v_trace_2644_);
v___x_2795_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2644_, v_hasTrace_2666_, v___x_2738_, v_options_2665_, v___y_2783_, v___y_2781_, v___y_2782_, v___x_2794_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
v___y_2775_ = v___y_2785_;
v___y_2776_ = v___y_2786_;
v___y_2777_ = v___x_2795_;
goto v___jp_2774_;
}
v___jp_2796_:
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_a_2803_);
v___y_2781_ = v___y_2797_;
v___y_2782_ = v___y_2798_;
v___y_2783_ = v___y_2800_;
v___y_2784_ = v___y_2799_;
v___y_2785_ = v___y_2801_;
v___y_2786_ = v___y_2802_;
v_a_2787_ = v___x_2804_;
goto v___jp_2780_;
}
v___jp_2805_:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2813_, 0, v_a_2812_);
v___y_2781_ = v___y_2806_;
v___y_2782_ = v___y_2807_;
v___y_2783_ = v___y_2809_;
v___y_2784_ = v___y_2808_;
v___y_2785_ = v___y_2810_;
v___y_2786_ = v___y_2811_;
v_a_2787_ = v___x_2813_;
goto v___jp_2780_;
}
v___jp_2814_:
{
uint8_t v___x_2824_; 
v___x_2824_ = l_List_isEmpty___redArg(v___y_2816_);
lean_dec(v___y_2816_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec(v___y_2822_);
lean_dec(v___y_2818_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v___x_2825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_2826_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_2825_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
v___y_2806_ = v___y_2815_;
v___y_2807_ = v___y_2817_;
v___y_2808_ = v___y_2820_;
v___y_2809_ = v___y_2819_;
v___y_2810_ = v___y_2821_;
v___y_2811_ = v___y_2823_;
v_a_2812_ = v_a_2827_;
goto v___jp_2805_;
}
else
{
lean_object* v_a_2828_; 
v_a_2828_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2826_, 1);
v___y_2797_ = v___y_2815_;
v___y_2798_ = v___y_2817_;
v___y_2799_ = v___y_2820_;
v___y_2800_ = v___y_2819_;
v___y_2801_ = v___y_2821_;
v___y_2802_ = v___y_2823_;
v_a_2803_ = v_a_2828_;
goto v___jp_2796_;
}
}
else
{
lean_object* v___x_2829_; 
lean_inc(v_trace_2644_);
v___x_2829_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___y_2818_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2831_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2831_ = l_List_appendTR___redArg(v___y_2822_, v_a_2830_);
v___y_2806_ = v___y_2815_;
v___y_2807_ = v___y_2817_;
v___y_2808_ = v___y_2820_;
v___y_2809_ = v___y_2819_;
v___y_2810_ = v___y_2821_;
v___y_2811_ = v___y_2823_;
v_a_2812_ = v___x_2831_;
goto v___jp_2805_;
}
else
{
lean_object* v_a_2832_; 
lean_dec(v___y_2822_);
v_a_2832_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2829_, 1);
v___y_2797_ = v___y_2815_;
v___y_2798_ = v___y_2817_;
v___y_2799_ = v___y_2820_;
v___y_2800_ = v___y_2819_;
v___y_2801_ = v___y_2821_;
v___y_2802_ = v___y_2823_;
v_a_2803_ = v_a_2832_;
goto v___jp_2796_;
}
}
}
v___jp_2833_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = l_List_appendTR___redArg(v___y_2841_, v___y_2835_);
v___x_2844_ = l_List_appendTR___redArg(v___x_2843_, v_a_2842_);
v___y_2806_ = v___y_2834_;
v___y_2807_ = v___y_2836_;
v___y_2808_ = v___y_2838_;
v___y_2809_ = v___y_2837_;
v___y_2810_ = v___y_2839_;
v___y_2811_ = v___y_2840_;
v_a_2812_ = v___x_2844_;
goto v___jp_2805_;
}
v___jp_2845_:
{
lean_object* v___x_2854_; 
v___x_2854_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2652_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2856_ = lean_io_get_num_heartbeats();
v___x_2857_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_2851_, v___x_2663_, v_goals_2647_, v___y_2849_, v_a_2650_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; uint8_t v_commitIndependentGoals_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v_commitIndependentGoals_2859_ = lean_ctor_get_uint8(v_cfg_2643_, sizeof(void*)*4);
v___x_2860_ = l_List_reverse___redArg(v_a_2858_);
lean_inc(v___y_2852_);
v___x_2861_ = l_List_appendTR___redArg(v___x_2860_, v___y_2852_);
if (v_commitIndependentGoals_2859_ == 0)
{
v___y_2815_ = v_a_2855_;
v___y_2816_ = v___y_2846_;
v___y_2817_ = v___y_2847_;
v___y_2818_ = v___x_2861_;
v___y_2819_ = v___y_2848_;
v___y_2820_ = v___x_2856_;
v___y_2821_ = v___y_2850_;
v___y_2822_ = v___y_2852_;
v___y_2823_ = v___y_2853_;
goto v___jp_2814_;
}
else
{
uint8_t v___x_2862_; 
v___x_2862_ = l_List_isEmpty___redArg(v___y_2852_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Lean_Meta_saveState___redArg(v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
lean_inc(v_snd_2659_);
lean_inc(v_trace_2644_);
v___x_2865_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_2861_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; 
lean_dec(v_a_2864_);
lean_dec(v_snd_2659_);
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___y_2834_ = v_a_2855_;
v___y_2835_ = v___y_2846_;
v___y_2836_ = v___y_2847_;
v___y_2837_ = v___y_2848_;
v___y_2838_ = v___x_2856_;
v___y_2839_ = v___y_2850_;
v___y_2840_ = v___y_2853_;
v___y_2841_ = v___y_2852_;
v_a_2842_ = v_a_2866_;
goto v___jp_2833_;
}
else
{
lean_object* v_a_2867_; uint8_t v___x_2868_; 
v_a_2867_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2868_ = l_Lean_Exception_isInterrupt(v_a_2867_);
if (v___x_2868_ == 0)
{
uint8_t v___x_2869_; 
lean_inc(v_a_2867_);
v___x_2869_ = l_Lean_Exception_isRuntime(v_a_2867_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; 
lean_dec(v_a_2867_);
v___x_2870_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2864_, v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_dec_ref_known(v___x_2870_, 1);
v___y_2834_ = v_a_2855_;
v___y_2835_ = v___y_2846_;
v___y_2836_ = v___y_2847_;
v___y_2837_ = v___y_2848_;
v___y_2838_ = v___x_2856_;
v___y_2839_ = v___y_2850_;
v___y_2840_ = v___y_2853_;
v___y_2841_ = v___y_2852_;
v_a_2842_ = v_snd_2659_;
goto v___jp_2833_;
}
else
{
lean_object* v_a_2871_; 
lean_dec(v___y_2852_);
lean_dec(v___y_2846_);
lean_dec(v_snd_2659_);
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___x_2870_, 1);
v___y_2797_ = v_a_2855_;
v___y_2798_ = v___y_2847_;
v___y_2799_ = v___x_2856_;
v___y_2800_ = v___y_2848_;
v___y_2801_ = v___y_2850_;
v___y_2802_ = v___y_2853_;
v_a_2803_ = v_a_2871_;
goto v___jp_2796_;
}
}
else
{
lean_dec(v_a_2864_);
lean_dec(v___y_2852_);
lean_dec(v___y_2846_);
lean_dec(v_snd_2659_);
v___y_2797_ = v_a_2855_;
v___y_2798_ = v___y_2847_;
v___y_2799_ = v___x_2856_;
v___y_2800_ = v___y_2848_;
v___y_2801_ = v___y_2850_;
v___y_2802_ = v___y_2853_;
v_a_2803_ = v_a_2867_;
goto v___jp_2796_;
}
}
else
{
lean_dec(v_a_2864_);
lean_dec(v___y_2852_);
lean_dec(v___y_2846_);
lean_dec(v_snd_2659_);
v___y_2797_ = v_a_2855_;
v___y_2798_ = v___y_2847_;
v___y_2799_ = v___x_2856_;
v___y_2800_ = v___y_2848_;
v___y_2801_ = v___y_2850_;
v___y_2802_ = v___y_2853_;
v_a_2803_ = v_a_2867_;
goto v___jp_2796_;
}
}
}
else
{
lean_object* v_a_2872_; 
lean_dec(v___x_2861_);
lean_dec(v___y_2852_);
lean_dec(v___y_2846_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_2872_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2863_, 1);
v___y_2797_ = v_a_2855_;
v___y_2798_ = v___y_2847_;
v___y_2799_ = v___x_2856_;
v___y_2800_ = v___y_2848_;
v___y_2801_ = v___y_2850_;
v___y_2802_ = v___y_2853_;
v_a_2803_ = v_a_2872_;
goto v___jp_2796_;
}
}
else
{
v___y_2815_ = v_a_2855_;
v___y_2816_ = v___y_2846_;
v___y_2817_ = v___y_2847_;
v___y_2818_ = v___x_2861_;
v___y_2819_ = v___y_2848_;
v___y_2820_ = v___x_2856_;
v___y_2821_ = v___y_2850_;
v___y_2822_ = v___y_2852_;
v___y_2823_ = v___y_2853_;
goto v___jp_2814_;
}
}
}
else
{
lean_object* v_a_2873_; 
lean_dec(v___y_2852_);
lean_dec(v___y_2846_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_2873_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2857_, 1);
v___y_2797_ = v_a_2855_;
v___y_2798_ = v___y_2847_;
v___y_2799_ = v___x_2856_;
v___y_2800_ = v___y_2848_;
v___y_2801_ = v___y_2850_;
v___y_2802_ = v___y_2853_;
v_a_2803_ = v_a_2873_;
goto v___jp_2796_;
}
}
else
{
lean_object* v_a_2874_; 
lean_dec(v___y_2852_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec(v_snd_2659_);
lean_dec(v_goals_2647_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_2874_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2854_, 1);
v___y_2770_ = v___y_2850_;
v___y_2771_ = v___y_2853_;
v_a_2772_ = v_a_2874_;
goto v___jp_2769_;
}
}
v___jp_2875_:
{
uint8_t v___x_2881_; 
v___x_2881_ = l_List_isEmpty___redArg(v___y_2876_);
lean_dec(v___y_2876_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_dec(v___y_2879_);
lean_dec(v___y_2877_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v___x_2882_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_2883_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_2882_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
v___y_2775_ = v___y_2878_;
v___y_2776_ = v___y_2880_;
v___y_2777_ = v___x_2883_;
goto v___jp_2774_;
}
else
{
lean_object* v___x_2884_; 
lean_inc(v_trace_2644_);
v___x_2884_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___y_2877_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2886_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v___x_2886_ = l_List_appendTR___redArg(v___y_2879_, v_a_2885_);
v___y_2757_ = v___y_2878_;
v___y_2758_ = v___y_2880_;
v_a_2759_ = v___x_2886_;
goto v___jp_2756_;
}
else
{
lean_object* v_a_2887_; 
lean_dec(v___y_2879_);
v_a_2887_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2884_, 1);
v___y_2770_ = v___y_2878_;
v___y_2771_ = v___y_2880_;
v_a_2772_ = v_a_2887_;
goto v___jp_2769_;
}
}
}
v___jp_2888_:
{
lean_object* v___x_2892_; double v___x_2893_; double v___x_2894_; double v___x_2895_; double v___x_2896_; double v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2892_ = lean_io_mono_nanos_now();
v___x_2893_ = lean_float_of_nat(v___y_2889_);
v___x_2894_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2895_ = lean_float_div(v___x_2893_, v___x_2894_);
v___x_2896_ = lean_float_of_nat(v___x_2892_);
v___x_2897_ = lean_float_div(v___x_2896_, v___x_2894_);
v___x_2898_ = lean_box_float(v___x_2895_);
v___x_2899_ = lean_box_float(v___x_2897_);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2901_, 0, v_a_2891_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2644_, v_hasTrace_2666_, v___x_2738_, v_options_2665_, v___x_2741_, v___y_2890_, v___f_2737_, v___x_2901_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
return v___x_2902_;
}
v___jp_2903_:
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_a_2906_);
v___y_2889_ = v___y_2904_;
v___y_2890_ = v___y_2905_;
v_a_2891_ = v___x_2907_;
goto v___jp_2888_;
}
v___jp_2908_:
{
lean_object* v___x_2912_; 
v___x_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2911_);
v___y_2889_ = v___y_2909_;
v___y_2890_ = v___y_2910_;
v_a_2891_ = v___x_2912_;
goto v___jp_2888_;
}
v___jp_2913_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = l_List_appendTR___redArg(v___y_2915_, v___y_2914_);
v___x_2920_ = l_List_appendTR___redArg(v___x_2919_, v_a_2918_);
v___y_2909_ = v___y_2916_;
v___y_2910_ = v___y_2917_;
v_a_2911_ = v___x_2920_;
goto v___jp_2908_;
}
v___jp_2921_:
{
if (lean_obj_tag(v___y_2924_) == 0)
{
lean_object* v_a_2925_; 
v_a_2925_ = lean_ctor_get(v___y_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___y_2924_, 1);
v___y_2909_ = v___y_2922_;
v___y_2910_ = v___y_2923_;
v_a_2911_ = v_a_2925_;
goto v___jp_2908_;
}
else
{
lean_object* v_a_2926_; 
v_a_2926_ = lean_ctor_get(v___y_2924_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___y_2924_, 1);
v___y_2904_ = v___y_2922_;
v___y_2905_ = v___y_2923_;
v_a_2906_ = v_a_2926_;
goto v___jp_2903_;
}
}
v___jp_2927_:
{
uint8_t v___x_2933_; 
v___x_2933_ = l_List_isEmpty___redArg(v___y_2928_);
lean_dec(v___y_2928_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v___x_2934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_2935_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_2934_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
v___y_2922_ = v___y_2931_;
v___y_2923_ = v___y_2932_;
v___y_2924_ = v___x_2935_;
goto v___jp_2921_;
}
else
{
lean_object* v___x_2936_; 
lean_inc(v_trace_2644_);
v___x_2936_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___y_2930_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2938_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v___x_2938_ = l_List_appendTR___redArg(v___y_2929_, v_a_2937_);
v___y_2909_ = v___y_2931_;
v___y_2910_ = v___y_2932_;
v_a_2911_ = v___x_2938_;
goto v___jp_2908_;
}
else
{
lean_object* v_a_2939_; 
lean_dec(v___y_2929_);
v_a_2939_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2936_, 1);
v___y_2904_ = v___y_2931_;
v___y_2905_ = v___y_2932_;
v_a_2906_ = v_a_2939_;
goto v___jp_2903_;
}
}
}
v___jp_2940_:
{
lean_object* v___x_2948_; double v___x_2949_; double v___x_2950_; double v___x_2951_; double v___x_2952_; double v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2948_ = lean_io_mono_nanos_now();
v___x_2949_ = lean_float_of_nat(v___y_2941_);
v___x_2950_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2951_ = lean_float_div(v___x_2949_, v___x_2950_);
v___x_2952_ = lean_float_of_nat(v___x_2948_);
v___x_2953_ = lean_float_div(v___x_2952_, v___x_2950_);
v___x_2954_ = lean_box_float(v___x_2951_);
v___x_2955_ = lean_box_float(v___x_2953_);
v___x_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2954_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_2957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2957_, 0, v_a_2947_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
lean_inc(v_trace_2644_);
v___x_2958_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2644_, v_hasTrace_2666_, v___x_2738_, v_options_2665_, v___y_2944_, v___y_2943_, v___y_2942_, v___x_2957_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
v___y_2922_ = v___y_2945_;
v___y_2923_ = v___y_2946_;
v___y_2924_ = v___x_2958_;
goto v___jp_2921_;
}
v___jp_2959_:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2967_, 0, v_a_2966_);
v___y_2941_ = v___y_2960_;
v___y_2942_ = v___y_2961_;
v___y_2943_ = v___y_2962_;
v___y_2944_ = v___y_2963_;
v___y_2945_ = v___y_2964_;
v___y_2946_ = v___y_2965_;
v_a_2947_ = v___x_2967_;
goto v___jp_2940_;
}
v___jp_2968_:
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2976_, 0, v_a_2975_);
v___y_2941_ = v___y_2969_;
v___y_2942_ = v___y_2970_;
v___y_2943_ = v___y_2971_;
v___y_2944_ = v___y_2972_;
v___y_2945_ = v___y_2973_;
v___y_2946_ = v___y_2974_;
v_a_2947_ = v___x_2976_;
goto v___jp_2940_;
}
v___jp_2977_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = l_List_appendTR___redArg(v___y_2982_, v___y_2980_);
v___x_2988_ = l_List_appendTR___redArg(v___x_2987_, v_a_2986_);
v___y_2969_ = v___y_2978_;
v___y_2970_ = v___y_2979_;
v___y_2971_ = v___y_2981_;
v___y_2972_ = v___y_2983_;
v___y_2973_ = v___y_2984_;
v___y_2974_ = v___y_2985_;
v_a_2975_ = v___x_2988_;
goto v___jp_2968_;
}
v___jp_2989_:
{
uint8_t v___x_2999_; 
v___x_2999_ = l_List_isEmpty___redArg(v___y_2992_);
lean_dec(v___y_2992_);
if (v___x_2999_ == 0)
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
lean_dec(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v___x_3000_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3001_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3000_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___y_2969_ = v___y_2990_;
v___y_2970_ = v___y_2991_;
v___y_2971_ = v___y_2993_;
v___y_2972_ = v___y_2996_;
v___y_2973_ = v___y_2997_;
v___y_2974_ = v___y_2998_;
v_a_2975_ = v_a_3002_;
goto v___jp_2968_;
}
else
{
lean_object* v_a_3003_; 
v_a_3003_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3001_, 1);
v___y_2960_ = v___y_2990_;
v___y_2961_ = v___y_2991_;
v___y_2962_ = v___y_2993_;
v___y_2963_ = v___y_2996_;
v___y_2964_ = v___y_2997_;
v___y_2965_ = v___y_2998_;
v_a_2966_ = v_a_3003_;
goto v___jp_2959_;
}
}
else
{
lean_object* v___x_3004_; 
lean_inc(v_trace_2644_);
v___x_3004_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___y_2995_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = l_List_appendTR___redArg(v___y_2994_, v_a_3005_);
v___y_2969_ = v___y_2990_;
v___y_2970_ = v___y_2991_;
v___y_2971_ = v___y_2993_;
v___y_2972_ = v___y_2996_;
v___y_2973_ = v___y_2997_;
v___y_2974_ = v___y_2998_;
v_a_2975_ = v___x_3006_;
goto v___jp_2968_;
}
else
{
lean_object* v_a_3007_; 
lean_dec(v___y_2994_);
v_a_3007_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3004_, 1);
v___y_2960_ = v___y_2990_;
v___y_2961_ = v___y_2991_;
v___y_2962_ = v___y_2993_;
v___y_2963_ = v___y_2996_;
v___y_2964_ = v___y_2997_;
v___y_2965_ = v___y_2998_;
v_a_2966_ = v_a_3007_;
goto v___jp_2959_;
}
}
}
v___jp_3008_:
{
lean_object* v___x_3016_; 
v___x_3016_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2652_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = lean_io_mono_nanos_now();
v___x_3019_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2666_, v___x_2663_, v_goals_2647_, v___y_3012_, v_a_2650_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; uint8_t v_commitIndependentGoals_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v_commitIndependentGoals_3021_ = lean_ctor_get_uint8(v_cfg_2643_, sizeof(void*)*4);
v___x_3022_ = l_List_reverse___redArg(v_a_3020_);
lean_inc(v___y_3011_);
v___x_3023_ = l_List_appendTR___redArg(v___x_3022_, v___y_3011_);
if (v_commitIndependentGoals_3021_ == 0)
{
v___y_2990_ = v___x_3018_;
v___y_2991_ = v___y_3009_;
v___y_2992_ = v___y_3010_;
v___y_2993_ = v_a_3017_;
v___y_2994_ = v___y_3011_;
v___y_2995_ = v___x_3023_;
v___y_2996_ = v___y_3013_;
v___y_2997_ = v___y_3014_;
v___y_2998_ = v___y_3015_;
goto v___jp_2989_;
}
else
{
uint8_t v___x_3024_; 
v___x_3024_ = l_List_isEmpty___redArg(v___y_3011_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Lean_Meta_saveState___redArg(v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3027_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
lean_inc(v_snd_2659_);
lean_inc(v_trace_2644_);
v___x_3027_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_3023_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; 
lean_dec(v_a_3026_);
lean_dec(v_snd_2659_);
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
v___y_2978_ = v___x_3018_;
v___y_2979_ = v___y_3009_;
v___y_2980_ = v___y_3010_;
v___y_2981_ = v_a_3017_;
v___y_2982_ = v___y_3011_;
v___y_2983_ = v___y_3013_;
v___y_2984_ = v___y_3014_;
v___y_2985_ = v___y_3015_;
v_a_2986_ = v_a_3028_;
goto v___jp_2977_;
}
else
{
lean_object* v_a_3029_; uint8_t v___x_3030_; 
v_a_3029_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3027_, 1);
v___x_3030_ = l_Lean_Exception_isInterrupt(v_a_3029_);
if (v___x_3030_ == 0)
{
uint8_t v___x_3031_; 
lean_inc(v_a_3029_);
v___x_3031_ = l_Lean_Exception_isRuntime(v_a_3029_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; 
lean_dec(v_a_3029_);
v___x_3032_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3026_, v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_dec_ref_known(v___x_3032_, 1);
v___y_2978_ = v___x_3018_;
v___y_2979_ = v___y_3009_;
v___y_2980_ = v___y_3010_;
v___y_2981_ = v_a_3017_;
v___y_2982_ = v___y_3011_;
v___y_2983_ = v___y_3013_;
v___y_2984_ = v___y_3014_;
v___y_2985_ = v___y_3015_;
v_a_2986_ = v_snd_2659_;
goto v___jp_2977_;
}
else
{
lean_object* v_a_3033_; 
lean_dec(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec(v_snd_2659_);
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___y_2960_ = v___x_3018_;
v___y_2961_ = v___y_3009_;
v___y_2962_ = v_a_3017_;
v___y_2963_ = v___y_3013_;
v___y_2964_ = v___y_3014_;
v___y_2965_ = v___y_3015_;
v_a_2966_ = v_a_3033_;
goto v___jp_2959_;
}
}
else
{
lean_dec(v_a_3026_);
lean_dec(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec(v_snd_2659_);
v___y_2960_ = v___x_3018_;
v___y_2961_ = v___y_3009_;
v___y_2962_ = v_a_3017_;
v___y_2963_ = v___y_3013_;
v___y_2964_ = v___y_3014_;
v___y_2965_ = v___y_3015_;
v_a_2966_ = v_a_3029_;
goto v___jp_2959_;
}
}
else
{
lean_dec(v_a_3026_);
lean_dec(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec(v_snd_2659_);
v___y_2960_ = v___x_3018_;
v___y_2961_ = v___y_3009_;
v___y_2962_ = v_a_3017_;
v___y_2963_ = v___y_3013_;
v___y_2964_ = v___y_3014_;
v___y_2965_ = v___y_3015_;
v_a_2966_ = v_a_3029_;
goto v___jp_2959_;
}
}
}
else
{
lean_object* v_a_3034_; 
lean_dec(v___x_3023_);
lean_dec(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3034_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3025_, 1);
v___y_2960_ = v___x_3018_;
v___y_2961_ = v___y_3009_;
v___y_2962_ = v_a_3017_;
v___y_2963_ = v___y_3013_;
v___y_2964_ = v___y_3014_;
v___y_2965_ = v___y_3015_;
v_a_2966_ = v_a_3034_;
goto v___jp_2959_;
}
}
else
{
v___y_2990_ = v___x_3018_;
v___y_2991_ = v___y_3009_;
v___y_2992_ = v___y_3010_;
v___y_2993_ = v_a_3017_;
v___y_2994_ = v___y_3011_;
v___y_2995_ = v___x_3023_;
v___y_2996_ = v___y_3013_;
v___y_2997_ = v___y_3014_;
v___y_2998_ = v___y_3015_;
goto v___jp_2989_;
}
}
}
else
{
lean_object* v_a_3035_; 
lean_dec(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3035_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3019_, 1);
v___y_2960_ = v___x_3018_;
v___y_2961_ = v___y_3009_;
v___y_2962_ = v_a_3017_;
v___y_2963_ = v___y_3013_;
v___y_2964_ = v___y_3014_;
v___y_2965_ = v___y_3015_;
v_a_2966_ = v_a_3035_;
goto v___jp_2959_;
}
}
else
{
lean_object* v_a_3036_; 
lean_dec(v___y_3012_);
lean_dec(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v_snd_2659_);
lean_dec(v_goals_2647_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3036_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3016_, 1);
v___y_2904_ = v___y_3014_;
v___y_2905_ = v___y_3015_;
v_a_2906_ = v_a_3036_;
goto v___jp_2903_;
}
}
v___jp_3037_:
{
lean_object* v___x_3038_; 
v___x_3038_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2652_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v___x_3040_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3041_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2665_, v___x_3040_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
lean_del_object(v___x_2661_);
v___x_3042_ = lean_io_mono_nanos_now();
v___x_3043_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2658_, v___f_2654_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v_fst_3045_; lean_object* v_snd_3046_; lean_object* v___x_3047_; lean_object* v___f_3048_; lean_object* v___x_3049_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
v_fst_3045_ = lean_ctor_get(v_a_3044_, 0);
lean_inc_n(v_fst_3045_, 2);
v_snd_3046_ = lean_ctor_get(v_a_3044_, 1);
lean_inc(v_snd_3046_);
lean_dec(v_a_3044_);
v___x_3047_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3046_, v___x_2655_);
lean_inc(v___x_3047_);
v___f_3048_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3048_, 0, v_fst_3045_);
lean_closure_set(v___f_3048_, 1, v___x_3047_);
v___x_3049_ = lean_box(0);
if (v___x_2741_ == 0)
{
lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3050_ = l_Lean_trace_profiler;
v___x_3051_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2665_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; 
lean_dec_ref(v___f_3048_);
v___x_3052_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2666_, v___x_2663_, v_goals_2647_, v___x_3049_, v_a_2650_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; uint8_t v_commitIndependentGoals_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
v_commitIndependentGoals_3054_ = lean_ctor_get_uint8(v_cfg_2643_, sizeof(void*)*4);
v___x_3055_ = l_List_reverse___redArg(v_a_3053_);
lean_inc(v___x_3047_);
v___x_3056_ = l_List_appendTR___redArg(v___x_3055_, v___x_3047_);
if (v_commitIndependentGoals_3054_ == 0)
{
v___y_2928_ = v_fst_3045_;
v___y_2929_ = v___x_3047_;
v___y_2930_ = v___x_3056_;
v___y_2931_ = v___x_3042_;
v___y_2932_ = v_a_3039_;
goto v___jp_2927_;
}
else
{
uint8_t v___x_3057_; 
v___x_3057_ = l_List_isEmpty___redArg(v___x_3047_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_Meta_saveState___redArg(v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
lean_inc(v_snd_2659_);
lean_inc(v_trace_2644_);
v___x_3060_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_3056_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; 
lean_dec(v_a_3059_);
lean_dec(v_snd_2659_);
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
v___y_2914_ = v_fst_3045_;
v___y_2915_ = v___x_3047_;
v___y_2916_ = v___x_3042_;
v___y_2917_ = v_a_3039_;
v_a_2918_ = v_a_3061_;
goto v___jp_2913_;
}
else
{
lean_object* v_a_3062_; uint8_t v___x_3063_; 
v_a_3062_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3062_);
lean_dec_ref_known(v___x_3060_, 1);
v___x_3063_ = l_Lean_Exception_isInterrupt(v_a_3062_);
if (v___x_3063_ == 0)
{
uint8_t v___x_3064_; 
lean_inc(v_a_3062_);
v___x_3064_ = l_Lean_Exception_isRuntime(v_a_3062_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; 
lean_dec(v_a_3062_);
v___x_3065_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3059_, v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_dec_ref_known(v___x_3065_, 1);
v___y_2914_ = v_fst_3045_;
v___y_2915_ = v___x_3047_;
v___y_2916_ = v___x_3042_;
v___y_2917_ = v_a_3039_;
v_a_2918_ = v_snd_2659_;
goto v___jp_2913_;
}
else
{
lean_object* v_a_3066_; 
lean_dec(v___x_3047_);
lean_dec(v_fst_3045_);
lean_dec(v_snd_2659_);
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
v___y_2904_ = v___x_3042_;
v___y_2905_ = v_a_3039_;
v_a_2906_ = v_a_3066_;
goto v___jp_2903_;
}
}
else
{
lean_dec(v_a_3059_);
lean_dec(v___x_3047_);
lean_dec(v_fst_3045_);
lean_dec(v_snd_2659_);
v___y_2904_ = v___x_3042_;
v___y_2905_ = v_a_3039_;
v_a_2906_ = v_a_3062_;
goto v___jp_2903_;
}
}
else
{
lean_dec(v_a_3059_);
lean_dec(v___x_3047_);
lean_dec(v_fst_3045_);
lean_dec(v_snd_2659_);
v___y_2904_ = v___x_3042_;
v___y_2905_ = v_a_3039_;
v_a_2906_ = v_a_3062_;
goto v___jp_2903_;
}
}
}
else
{
lean_object* v_a_3067_; 
lean_dec(v___x_3056_);
lean_dec(v___x_3047_);
lean_dec(v_fst_3045_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3067_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___x_3058_, 1);
v___y_2904_ = v___x_3042_;
v___y_2905_ = v_a_3039_;
v_a_2906_ = v_a_3067_;
goto v___jp_2903_;
}
}
else
{
v___y_2928_ = v_fst_3045_;
v___y_2929_ = v___x_3047_;
v___y_2930_ = v___x_3056_;
v___y_2931_ = v___x_3042_;
v___y_2932_ = v_a_3039_;
goto v___jp_2927_;
}
}
}
else
{
lean_object* v_a_3068_; 
lean_dec(v___x_3047_);
lean_dec(v_fst_3045_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3068_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3052_, 1);
v___y_2904_ = v___x_3042_;
v___y_2905_ = v_a_3039_;
v_a_2906_ = v_a_3068_;
goto v___jp_2903_;
}
}
else
{
v___y_3009_ = v___f_3048_;
v___y_3010_ = v_fst_3045_;
v___y_3011_ = v___x_3047_;
v___y_3012_ = v___x_3049_;
v___y_3013_ = v___x_2741_;
v___y_3014_ = v___x_3042_;
v___y_3015_ = v_a_3039_;
goto v___jp_3008_;
}
}
else
{
v___y_3009_ = v___f_3048_;
v___y_3010_ = v_fst_3045_;
v___y_3011_ = v___x_3047_;
v___y_3012_ = v___x_3049_;
v___y_3013_ = v___x_2741_;
v___y_3014_ = v___x_3042_;
v___y_3015_ = v_a_3039_;
goto v___jp_3008_;
}
}
else
{
lean_object* v_a_3069_; 
lean_dec(v_snd_2659_);
lean_dec(v_goals_2647_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3069_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v___x_3043_, 1);
v___y_2904_ = v___x_3042_;
v___y_2905_ = v_a_3039_;
v_a_2906_ = v_a_3069_;
goto v___jp_2903_;
}
}
else
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = lean_io_get_num_heartbeats();
v___x_3071_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2658_, v___f_2654_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v_fst_3073_; lean_object* v_snd_3074_; lean_object* v___x_3075_; lean_object* v___f_3076_; lean_object* v___x_3077_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v_fst_3073_ = lean_ctor_get(v_a_3072_, 0);
lean_inc_n(v_fst_3073_, 2);
v_snd_3074_ = lean_ctor_get(v_a_3072_, 1);
lean_inc(v_snd_3074_);
lean_dec(v_a_3072_);
v___x_3075_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3074_, v___x_2655_);
lean_inc(v___x_3075_);
v___f_3076_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3076_, 0, v_fst_3073_);
lean_closure_set(v___f_3076_, 1, v___x_3075_);
v___x_3077_ = lean_box(0);
if (v___x_2741_ == 0)
{
lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3078_ = l_Lean_trace_profiler;
v___x_3079_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2665_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; 
lean_dec_ref(v___f_3076_);
v___x_3080_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3041_, v___x_2663_, v_goals_2647_, v___x_3077_, v_a_2650_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; uint8_t v_commitIndependentGoals_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v_commitIndependentGoals_3082_ = lean_ctor_get_uint8(v_cfg_2643_, sizeof(void*)*4);
v___x_3083_ = l_List_reverse___redArg(v_a_3081_);
lean_inc(v___x_3075_);
v___x_3084_ = l_List_appendTR___redArg(v___x_3083_, v___x_3075_);
if (v_commitIndependentGoals_3082_ == 0)
{
v___y_2876_ = v_fst_3073_;
v___y_2877_ = v___x_3084_;
v___y_2878_ = v_a_3039_;
v___y_2879_ = v___x_3075_;
v___y_2880_ = v___x_3070_;
goto v___jp_2875_;
}
else
{
uint8_t v___x_3085_; 
v___x_3085_ = l_List_isEmpty___redArg(v___x_3075_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; 
v___x_3086_ = l_Lean_Meta_saveState___redArg(v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3088_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
lean_inc(v_snd_2659_);
lean_inc(v_trace_2644_);
v___x_3088_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v___x_3084_, v_snd_2659_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; 
lean_dec(v_a_3087_);
lean_dec(v_snd_2659_);
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3088_, 1);
v___y_2762_ = v_fst_3073_;
v___y_2763_ = v_a_3039_;
v___y_2764_ = v___x_3070_;
v___y_2765_ = v___x_3075_;
v_a_2766_ = v_a_3089_;
goto v___jp_2761_;
}
else
{
lean_object* v_a_3090_; uint8_t v___x_3091_; 
v_a_3090_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3090_);
lean_dec_ref_known(v___x_3088_, 1);
v___x_3091_ = l_Lean_Exception_isInterrupt(v_a_3090_);
if (v___x_3091_ == 0)
{
uint8_t v___x_3092_; 
lean_inc(v_a_3090_);
v___x_3092_ = l_Lean_Exception_isRuntime(v_a_3090_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; 
lean_dec(v_a_3090_);
v___x_3093_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3087_, v_a_2650_, v_a_2652_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_dec_ref_known(v___x_3093_, 1);
v___y_2762_ = v_fst_3073_;
v___y_2763_ = v_a_3039_;
v___y_2764_ = v___x_3070_;
v___y_2765_ = v___x_3075_;
v_a_2766_ = v_snd_2659_;
goto v___jp_2761_;
}
else
{
lean_object* v_a_3094_; 
lean_dec(v___x_3075_);
lean_dec(v_fst_3073_);
lean_dec(v_snd_2659_);
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
v___y_2770_ = v_a_3039_;
v___y_2771_ = v___x_3070_;
v_a_2772_ = v_a_3094_;
goto v___jp_2769_;
}
}
else
{
lean_dec(v_a_3087_);
lean_dec(v___x_3075_);
lean_dec(v_fst_3073_);
lean_dec(v_snd_2659_);
v___y_2770_ = v_a_3039_;
v___y_2771_ = v___x_3070_;
v_a_2772_ = v_a_3090_;
goto v___jp_2769_;
}
}
else
{
lean_dec(v_a_3087_);
lean_dec(v___x_3075_);
lean_dec(v_fst_3073_);
lean_dec(v_snd_2659_);
v___y_2770_ = v_a_3039_;
v___y_2771_ = v___x_3070_;
v_a_2772_ = v_a_3090_;
goto v___jp_2769_;
}
}
}
else
{
lean_object* v_a_3095_; 
lean_dec(v___x_3084_);
lean_dec(v___x_3075_);
lean_dec(v_fst_3073_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3095_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3095_);
lean_dec_ref_known(v___x_3086_, 1);
v___y_2770_ = v_a_3039_;
v___y_2771_ = v___x_3070_;
v_a_2772_ = v_a_3095_;
goto v___jp_2769_;
}
}
else
{
v___y_2876_ = v_fst_3073_;
v___y_2877_ = v___x_3084_;
v___y_2878_ = v_a_3039_;
v___y_2879_ = v___x_3075_;
v___y_2880_ = v___x_3070_;
goto v___jp_2875_;
}
}
}
else
{
lean_object* v_a_3096_; 
lean_dec(v___x_3075_);
lean_dec(v_fst_3073_);
lean_dec(v_snd_2659_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3096_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3080_, 1);
v___y_2770_ = v_a_3039_;
v___y_2771_ = v___x_3070_;
v_a_2772_ = v_a_3096_;
goto v___jp_2769_;
}
}
else
{
v___y_2846_ = v_fst_3073_;
v___y_2847_ = v___f_3076_;
v___y_2848_ = v___x_2741_;
v___y_2849_ = v___x_3077_;
v___y_2850_ = v_a_3039_;
v___y_2851_ = v___x_3041_;
v___y_2852_ = v___x_3075_;
v___y_2853_ = v___x_3070_;
goto v___jp_2845_;
}
}
else
{
v___y_2846_ = v_fst_3073_;
v___y_2847_ = v___f_3076_;
v___y_2848_ = v___x_2741_;
v___y_2849_ = v___x_3077_;
v___y_2850_ = v_a_3039_;
v___y_2851_ = v___x_3041_;
v___y_2852_ = v___x_3075_;
v___y_2853_ = v___x_3070_;
goto v___jp_2845_;
}
}
else
{
lean_object* v_a_3097_; 
lean_dec(v_snd_2659_);
lean_dec(v_goals_2647_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec_ref(v_cfg_2643_);
v_a_3097_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3097_);
lean_dec_ref_known(v___x_3071_, 1);
v___y_2770_ = v_a_3039_;
v___y_2771_ = v___x_3070_;
v_a_2772_ = v_a_3097_;
goto v___jp_2769_;
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec_ref(v___f_2737_);
lean_del_object(v___x_2661_);
lean_dec(v_snd_2659_);
lean_dec(v_fst_2658_);
lean_dec_ref(v___f_2654_);
lean_dec(v_goals_2647_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec(v_trace_2644_);
lean_dec_ref(v_cfg_2643_);
v_a_3098_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3038_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3038_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
}
else
{
lean_object* v_maxDepth_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_del_object(v___x_2661_);
lean_dec(v_snd_2659_);
lean_dec(v_fst_2658_);
lean_dec_ref(v___f_2654_);
lean_dec(v_goals_2647_);
v_maxDepth_3297_ = lean_ctor_get(v_cfg_2643_, 0);
lean_inc(v_maxDepth_3297_);
v___x_3298_ = lean_box(0);
v___x_3299_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2643_, v_trace_2644_, v_next_2645_, v_orig_2646_, v_maxDepth_3297_, v_remaining_2648_, v___x_3298_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
return v___x_3299_;
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v___f_2654_);
lean_dec(v_remaining_2648_);
lean_dec(v_goals_2647_);
lean_dec(v_orig_2646_);
lean_dec_ref(v_next_2645_);
lean_dec(v_trace_2644_);
lean_dec_ref(v_cfg_2643_);
v_a_3301_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_2656_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_2656_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_3309_, lean_object* v_trace_3310_, lean_object* v_next_3311_, lean_object* v_orig_3312_, lean_object* v_goals_3313_, lean_object* v_remaining_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3309_, v_trace_3310_, v_next_3311_, v_orig_3312_, v_goals_3313_, v_remaining_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_3321_, lean_object* v_00_u03b2_3322_, lean_object* v_L_3323_, lean_object* v_f_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_3323_, v_f_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_3331_, lean_object* v_00_u03b2_3332_, lean_object* v_L_3333_, lean_object* v_f_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_3331_, v_00_u03b2_3332_, v_L_3333_, v_f_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_3341_, lean_object* v_x_3342_, lean_object* v_x_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_3341_, v_x_3342_, v_x_3343_, v___y_3345_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_3350_, lean_object* v_x_3351_, lean_object* v_x_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
uint8_t v___x_48164__boxed_3358_; lean_object* v_res_3359_; 
v___x_48164__boxed_3358_ = lean_unbox(v___x_3350_);
v_res_3359_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_48164__boxed_3358_, v_x_3351_, v_x_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_3360_, uint8_t v___x_3361_, lean_object* v_x_3362_, lean_object* v_x_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v___x_3369_; 
v___x_3369_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3360_, v___x_3361_, v_x_3362_, v_x_3363_, v___y_3365_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_3370_, lean_object* v___x_3371_, lean_object* v_x_3372_, lean_object* v_x_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
uint8_t v___x_48190__boxed_3379_; uint8_t v___x_48191__boxed_3380_; lean_object* v_res_3381_; 
v___x_48190__boxed_3379_ = lean_unbox(v___x_3370_);
v___x_48191__boxed_3380_ = lean_unbox(v___x_3371_);
v_res_3381_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_48190__boxed_3379_, v___x_48191__boxed_3380_, v_x_3372_, v_x_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_3382_, lean_object* v_00_u03b2_3383_, lean_object* v_f_3384_, lean_object* v_x_3385_, lean_object* v_x_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_3384_, v_x_3385_, v_x_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3393_, lean_object* v_00_u03b2_3394_, lean_object* v_f_3395_, lean_object* v_x_3396_, lean_object* v_x_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_3393_, v_00_u03b2_3394_, v_f_3395_, v_x_3396_, v_x_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_3404_, lean_object* v_00_u03b2_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_3406_, v_a_3407_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_3409_, lean_object* v_00_u03b2_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_3411_, v_a_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_3414_, lean_object* v_g_3415_, lean_object* v_f_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; 
lean_inc(v___y_3420_);
lean_inc_ref(v___y_3419_);
lean_inc(v___y_3418_);
lean_inc_ref(v___y_3417_);
v___x_3422_ = lean_apply_6(v_next_3414_, v_g_3415_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, lean_box(0));
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3424_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref_known(v___x_3422_, 1);
v___x_3424_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_3423_, v_f_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
return v___x_3424_;
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_dec_ref(v_f_3416_);
v_a_3425_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3422_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3422_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_3433_, lean_object* v_g_3434_, lean_object* v_f_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_3433_, v_g_3434_, v_f_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_3442_, lean_object* v_trace_3443_, lean_object* v_next_3444_, lean_object* v_goals_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v_resolve_3451_; lean_object* v___x_3452_; 
v_resolve_3451_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_3451_, 0, v_next_3444_);
lean_inc_n(v_goals_3445_, 2);
v___x_3452_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3442_, v_trace_3443_, v_resolve_3451_, v_goals_3445_, v_goals_3445_, v_goals_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_3453_, lean_object* v_trace_3454_, lean_object* v_next_3455_, lean_object* v_goals_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_3453_, v_trace_3454_, v_next_3455_, v_goals_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
return v_res_3462_;
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

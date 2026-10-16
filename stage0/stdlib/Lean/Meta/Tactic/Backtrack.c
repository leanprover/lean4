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
lean_object* v_toCold_501_; lean_object* v_currRecDepth_502_; lean_object* v_ref_503_; uint16_t v_optionFlags_504_; uint8_t v_suppressElabErrors_505_; uint8_t v_isRecordingDeps_506_; lean_object* v_ref_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_traceState_510_; lean_object* v_traces_511_; lean_object* v___x_512_; size_t v_sz_513_; size_t v___x_514_; lean_object* v___x_515_; lean_object* v_msg_516_; lean_object* v___x_517_; lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_556_; 
v_toCold_501_ = lean_ctor_get(v___y_498_, 0);
v_currRecDepth_502_ = lean_ctor_get(v___y_498_, 1);
v_ref_503_ = lean_ctor_get(v___y_498_, 2);
v_optionFlags_504_ = lean_ctor_get_uint16(v___y_498_, sizeof(void*)*3);
v_suppressElabErrors_505_ = lean_ctor_get_uint8(v___y_498_, sizeof(void*)*3 + 2);
v_isRecordingDeps_506_ = lean_ctor_get_uint8(v___y_498_, sizeof(void*)*3 + 3);
v_ref_507_ = l_Lean_replaceRef(v_ref_494_, v_ref_503_);
lean_inc(v_currRecDepth_502_);
lean_inc_ref(v_toCold_501_);
v___x_508_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_508_, 0, v_toCold_501_);
lean_ctor_set(v___x_508_, 1, v_currRecDepth_502_);
lean_ctor_set(v___x_508_, 2, v_ref_507_);
lean_ctor_set_uint16(v___x_508_, sizeof(void*)*3, v_optionFlags_504_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*3 + 2, v_suppressElabErrors_505_);
lean_ctor_set_uint8(v___x_508_, sizeof(void*)*3 + 3, v_isRecordingDeps_506_);
v___x_509_ = lean_st_ref_get(v___y_499_);
v_traceState_510_ = lean_ctor_get(v___x_509_, 4);
lean_inc_ref(v_traceState_510_);
lean_dec(v___x_509_);
v_traces_511_ = lean_ctor_get(v_traceState_510_, 0);
lean_inc_ref(v_traces_511_);
lean_dec_ref(v_traceState_510_);
v___x_512_ = l_Lean_PersistentArray_toArray___redArg(v_traces_511_);
lean_dec_ref(v_traces_511_);
v_sz_513_ = lean_array_size(v___x_512_);
v___x_514_ = ((size_t)0ULL);
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3_spec__6(v_sz_513_, v___x_514_, v___x_512_);
v_msg_516_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_516_, 0, v_data_493_);
lean_ctor_set(v_msg_516_, 1, v_msg_495_);
lean_ctor_set(v_msg_516_, 2, v___x_515_);
v___x_517_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_516_, v___y_496_, v___y_497_, v___x_508_, v___y_499_);
lean_dec_ref_known(v___x_508_, 3);
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_556_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_556_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_556_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v_traceState_523_; lean_object* v_env_524_; lean_object* v_nextMacroScope_525_; lean_object* v_ngen_526_; lean_object* v_auxDeclNGen_527_; lean_object* v_cache_528_; lean_object* v_recordedDeps_529_; lean_object* v_messages_530_; lean_object* v_infoState_531_; lean_object* v_snapshotTasks_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_555_; 
v___x_522_ = lean_st_ref_take(v___y_499_);
v_traceState_523_ = lean_ctor_get(v___x_522_, 4);
v_env_524_ = lean_ctor_get(v___x_522_, 0);
v_nextMacroScope_525_ = lean_ctor_get(v___x_522_, 1);
v_ngen_526_ = lean_ctor_get(v___x_522_, 2);
v_auxDeclNGen_527_ = lean_ctor_get(v___x_522_, 3);
v_cache_528_ = lean_ctor_get(v___x_522_, 5);
v_recordedDeps_529_ = lean_ctor_get(v___x_522_, 6);
v_messages_530_ = lean_ctor_get(v___x_522_, 7);
v_infoState_531_ = lean_ctor_get(v___x_522_, 8);
v_snapshotTasks_532_ = lean_ctor_get(v___x_522_, 9);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_555_ == 0)
{
v___x_534_ = v___x_522_;
v_isShared_535_ = v_isSharedCheck_555_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_snapshotTasks_532_);
lean_inc(v_infoState_531_);
lean_inc(v_messages_530_);
lean_inc(v_recordedDeps_529_);
lean_inc(v_cache_528_);
lean_inc(v_traceState_523_);
lean_inc(v_auxDeclNGen_527_);
lean_inc(v_ngen_526_);
lean_inc(v_nextMacroScope_525_);
lean_inc(v_env_524_);
lean_dec(v___x_522_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_555_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
uint64_t v_tid_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_553_; 
v_tid_536_ = lean_ctor_get_uint64(v_traceState_523_, sizeof(void*)*1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_traceState_523_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v_traceState_523_, 0);
lean_dec(v_unused_554_);
v___x_538_ = v_traceState_523_;
v_isShared_539_ = v_isSharedCheck_553_;
goto v_resetjp_537_;
}
else
{
lean_dec(v_traceState_523_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_553_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_540_ = lean_box(0);
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v_ref_494_);
lean_ctor_set(v___x_541_, 1, v_a_518_);
v___x_542_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_492_, v___x_541_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_542_);
v___x_544_ = v___x_538_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_542_);
lean_ctor_set_uint64(v_reuseFailAlloc_552_, sizeof(void*)*1, v_tid_536_);
v___x_544_ = v_reuseFailAlloc_552_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 4, v___x_544_);
v___x_546_ = v___x_534_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_env_524_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_nextMacroScope_525_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_ngen_526_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_auxDeclNGen_527_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_551_, 5, v_cache_528_);
lean_ctor_set(v_reuseFailAlloc_551_, 6, v_recordedDeps_529_);
lean_ctor_set(v_reuseFailAlloc_551_, 7, v_messages_530_);
lean_ctor_set(v_reuseFailAlloc_551_, 8, v_infoState_531_);
lean_ctor_set(v_reuseFailAlloc_551_, 9, v_snapshotTasks_532_);
v___x_546_ = v_reuseFailAlloc_551_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_st_ref_put(v___y_499_, v___x_546_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_540_);
v___x_549_ = v___x_520_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_540_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3___boxed(lean_object* v_oldTraces_557_, lean_object* v_data_558_, lean_object* v_ref_559_, lean_object* v_msg_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_557_, v_data_558_, v_ref_559_, v_msg_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
return v_res_566_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0(void){
_start:
{
lean_object* v___x_567_; double v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_float_of_nat(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__1));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3(void){
_start:
{
lean_object* v___x_572_; double v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(1000u);
v___x_573_ = lean_float_of_nat(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* v_cls_574_, uint8_t v_collapsed_575_, lean_object* v_tag_576_, lean_object* v_opts_577_, uint8_t v_clsEnabled_578_, lean_object* v_oldTraces_579_, lean_object* v_msg_580_, lean_object* v_resStartStop_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v_data_592_; lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___x_605_; uint8_t v___x_606_; lean_object* v___y_608_; lean_object* v_a_609_; uint8_t v___y_624_; double v___y_656_; 
v_fst_587_ = lean_ctor_get(v_resStartStop_581_, 0);
lean_inc(v_fst_587_);
v_snd_588_ = lean_ctor_get(v_resStartStop_581_, 1);
lean_inc(v_snd_588_);
lean_dec_ref(v_resStartStop_581_);
v_fst_603_ = lean_ctor_get(v_snd_588_, 0);
lean_inc(v_fst_603_);
v_snd_604_ = lean_ctor_get(v_snd_588_, 1);
lean_inc(v_snd_604_);
lean_dec(v_snd_588_);
v___x_605_ = l_Lean_trace_profiler;
v___x_606_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_577_, v___x_605_);
if (v___x_606_ == 0)
{
v___y_624_ = v___x_606_;
goto v___jp_623_;
}
else
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = l_Lean_trace_profiler_useHeartbeats;
v___x_662_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_577_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; double v___x_665_; double v___x_666_; double v___x_667_; 
v___x_663_ = l_Lean_trace_profiler_threshold;
v___x_664_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_577_, v___x_663_);
v___x_665_ = lean_float_of_nat(v___x_664_);
v___x_666_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_667_ = lean_float_div(v___x_665_, v___x_666_);
v___y_656_ = v___x_667_;
goto v___jp_655_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; double v___x_670_; 
v___x_668_ = l_Lean_trace_profiler_threshold;
v___x_669_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_577_, v___x_668_);
v___x_670_ = lean_float_of_nat(v___x_669_);
v___y_656_ = v___x_670_;
goto v___jp_655_;
}
}
v___jp_589_:
{
lean_object* v___x_593_; 
lean_inc(v___y_590_);
v___x_593_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_579_, v_data_592_, v___y_590_, v___y_591_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v___x_594_; 
lean_dec_ref_known(v___x_593_, 1);
v___x_594_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_587_);
return v___x_594_;
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec(v_fst_587_);
v_a_595_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_593_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_593_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
v___jp_607_:
{
uint8_t v_result_610_; lean_object* v___x_611_; lean_object* v___x_612_; double v___x_613_; lean_object* v_data_614_; 
v_result_610_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__12(v_fst_587_);
v___x_611_ = lean_box(v_result_610_);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
v___x_613_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_576_);
lean_inc_ref(v___x_612_);
lean_inc(v_cls_574_);
v_data_614_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_614_, 0, v_cls_574_);
lean_ctor_set(v_data_614_, 1, v___x_612_);
lean_ctor_set(v_data_614_, 2, v_tag_576_);
lean_ctor_set_float(v_data_614_, sizeof(void*)*3, v___x_613_);
lean_ctor_set_float(v_data_614_, sizeof(void*)*3 + 8, v___x_613_);
lean_ctor_set_uint8(v_data_614_, sizeof(void*)*3 + 16, v_collapsed_575_);
if (v___x_606_ == 0)
{
lean_dec_ref_known(v___x_612_, 1);
lean_dec(v_snd_604_);
lean_dec(v_fst_603_);
lean_dec_ref(v_tag_576_);
lean_dec(v_cls_574_);
v___y_590_ = v___y_608_;
v___y_591_ = v_a_609_;
v_data_592_ = v_data_614_;
goto v___jp_589_;
}
else
{
lean_object* v_data_615_; double v___x_616_; double v___x_617_; 
lean_dec_ref_known(v_data_614_, 3);
v_data_615_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_615_, 0, v_cls_574_);
lean_ctor_set(v_data_615_, 1, v___x_612_);
lean_ctor_set(v_data_615_, 2, v_tag_576_);
v___x_616_ = lean_unbox_float(v_fst_603_);
lean_dec(v_fst_603_);
lean_ctor_set_float(v_data_615_, sizeof(void*)*3, v___x_616_);
v___x_617_ = lean_unbox_float(v_snd_604_);
lean_dec(v_snd_604_);
lean_ctor_set_float(v_data_615_, sizeof(void*)*3 + 8, v___x_617_);
lean_ctor_set_uint8(v_data_615_, sizeof(void*)*3 + 16, v_collapsed_575_);
v___y_590_ = v___y_608_;
v___y_591_ = v_a_609_;
v_data_592_ = v_data_615_;
goto v___jp_589_;
}
}
v___jp_618_:
{
lean_object* v_ref_619_; lean_object* v___x_620_; 
v_ref_619_ = lean_ctor_get(v___y_584_, 2);
lean_inc(v___y_585_);
lean_inc_ref(v___y_584_);
lean_inc(v___y_583_);
lean_inc_ref(v___y_582_);
lean_inc(v_fst_587_);
v___x_620_ = lean_apply_6(v_msg_580_, v_fst_587_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, lean_box(0));
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v___y_608_ = v_ref_619_;
v_a_609_ = v_a_621_;
goto v___jp_607_;
}
else
{
lean_object* v___x_622_; 
lean_dec_ref_known(v___x_620_, 1);
v___x_622_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_608_ = v_ref_619_;
v_a_609_ = v___x_622_;
goto v___jp_607_;
}
}
v___jp_623_:
{
if (v_clsEnabled_578_ == 0)
{
if (v___y_624_ == 0)
{
lean_object* v___x_625_; lean_object* v_traceState_626_; lean_object* v_env_627_; lean_object* v_nextMacroScope_628_; lean_object* v_ngen_629_; lean_object* v_auxDeclNGen_630_; lean_object* v_cache_631_; lean_object* v_recordedDeps_632_; lean_object* v_messages_633_; lean_object* v_infoState_634_; lean_object* v_snapshotTasks_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_snd_604_);
lean_dec(v_fst_603_);
lean_dec_ref(v_msg_580_);
lean_dec_ref(v_tag_576_);
lean_dec(v_cls_574_);
v___x_625_ = lean_st_ref_take(v___y_585_);
v_traceState_626_ = lean_ctor_get(v___x_625_, 4);
v_env_627_ = lean_ctor_get(v___x_625_, 0);
v_nextMacroScope_628_ = lean_ctor_get(v___x_625_, 1);
v_ngen_629_ = lean_ctor_get(v___x_625_, 2);
v_auxDeclNGen_630_ = lean_ctor_get(v___x_625_, 3);
v_cache_631_ = lean_ctor_get(v___x_625_, 5);
v_recordedDeps_632_ = lean_ctor_get(v___x_625_, 6);
v_messages_633_ = lean_ctor_get(v___x_625_, 7);
v_infoState_634_ = lean_ctor_get(v___x_625_, 8);
v_snapshotTasks_635_ = lean_ctor_get(v___x_625_, 9);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_654_ == 0)
{
v___x_637_ = v___x_625_;
v_isShared_638_ = v_isSharedCheck_654_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_snapshotTasks_635_);
lean_inc(v_infoState_634_);
lean_inc(v_messages_633_);
lean_inc(v_recordedDeps_632_);
lean_inc(v_cache_631_);
lean_inc(v_traceState_626_);
lean_inc(v_auxDeclNGen_630_);
lean_inc(v_ngen_629_);
lean_inc(v_nextMacroScope_628_);
lean_inc(v_env_627_);
lean_dec(v___x_625_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_654_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
uint64_t v_tid_639_; lean_object* v_traces_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_653_; 
v_tid_639_ = lean_ctor_get_uint64(v_traceState_626_, sizeof(void*)*1);
v_traces_640_ = lean_ctor_get(v_traceState_626_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_traceState_626_);
if (v_isSharedCheck_653_ == 0)
{
v___x_642_ = v_traceState_626_;
v_isShared_643_ = v_isSharedCheck_653_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_traces_640_);
lean_dec(v_traceState_626_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_653_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_579_, v_traces_640_);
lean_dec_ref(v_traces_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_644_);
lean_ctor_set_uint64(v_reuseFailAlloc_652_, sizeof(void*)*1, v_tid_639_);
v___x_646_ = v_reuseFailAlloc_652_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_648_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 4, v___x_646_);
v___x_648_ = v___x_637_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_env_627_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_nextMacroScope_628_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_ngen_629_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v_auxDeclNGen_630_);
lean_ctor_set(v_reuseFailAlloc_651_, 4, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_651_, 5, v_cache_631_);
lean_ctor_set(v_reuseFailAlloc_651_, 6, v_recordedDeps_632_);
lean_ctor_set(v_reuseFailAlloc_651_, 7, v_messages_633_);
lean_ctor_set(v_reuseFailAlloc_651_, 8, v_infoState_634_);
lean_ctor_set(v_reuseFailAlloc_651_, 9, v_snapshotTasks_635_);
v___x_648_ = v_reuseFailAlloc_651_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_st_ref_put(v___y_585_, v___x_648_);
v___x_650_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_587_);
return v___x_650_;
}
}
}
}
}
else
{
goto v___jp_618_;
}
}
else
{
goto v___jp_618_;
}
}
v___jp_655_:
{
double v___x_657_; double v___x_658_; double v___x_659_; uint8_t v___x_660_; 
v___x_657_ = lean_unbox_float(v_snd_604_);
v___x_658_ = lean_unbox_float(v_fst_603_);
v___x_659_ = lean_float_sub(v___x_657_, v___x_658_);
v___x_660_ = lean_float_decLt(v___y_656_, v___x_659_);
v___y_624_ = v___x_660_;
goto v___jp_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* v_cls_671_, lean_object* v_collapsed_672_, lean_object* v_tag_673_, lean_object* v_opts_674_, lean_object* v_clsEnabled_675_, lean_object* v_oldTraces_676_, lean_object* v_msg_677_, lean_object* v_resStartStop_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
uint8_t v_collapsed_boxed_684_; uint8_t v_clsEnabled_boxed_685_; lean_object* v_res_686_; 
v_collapsed_boxed_684_ = lean_unbox(v_collapsed_672_);
v_clsEnabled_boxed_685_ = lean_unbox(v_clsEnabled_675_);
v_res_686_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_cls_671_, v_collapsed_boxed_684_, v_tag_673_, v_opts_674_, v_clsEnabled_boxed_685_, v_oldTraces_676_, v_msg_677_, v_resStartStop_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec_ref(v_opts_674_);
return v_res_686_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(lean_object* v_keys_687_, lean_object* v_i_688_, lean_object* v_k_689_){
_start:
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_array_get_size(v_keys_687_);
v___x_691_ = lean_nat_dec_lt(v_i_688_, v___x_690_);
if (v___x_691_ == 0)
{
lean_dec(v_i_688_);
return v___x_691_;
}
else
{
lean_object* v_k_x27_692_; uint8_t v___x_693_; 
v_k_x27_692_ = lean_array_fget_borrowed(v_keys_687_, v_i_688_);
v___x_693_ = l_Lean_instBEqMVarId_beq(v_k_689_, v_k_x27_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_add(v_i_688_, v___x_694_);
lean_dec(v_i_688_);
v_i_688_ = v___x_695_;
goto _start;
}
else
{
lean_dec(v_i_688_);
return v___x_691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg___boxed(lean_object* v_keys_697_, lean_object* v_i_698_, lean_object* v_k_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_697_, v_i_698_, v_k_699_);
lean_dec(v_k_699_);
lean_dec_ref(v_keys_697_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(lean_object* v_x_702_, size_t v_x_703_, lean_object* v_x_704_){
_start:
{
if (lean_obj_tag(v_x_702_) == 0)
{
lean_object* v_es_705_; lean_object* v___x_706_; size_t v___x_707_; size_t v___x_708_; lean_object* v_j_709_; lean_object* v___x_710_; 
v_es_705_ = lean_ctor_get(v_x_702_, 0);
v___x_706_ = lean_box(2);
v___x_707_ = ((size_t)31ULL);
v___x_708_ = lean_usize_land(v_x_703_, v___x_707_);
v_j_709_ = lean_usize_to_nat(v___x_708_);
v___x_710_ = lean_array_get_borrowed(v___x_706_, v_es_705_, v_j_709_);
lean_dec(v_j_709_);
switch(lean_obj_tag(v___x_710_))
{
case 0:
{
lean_object* v_key_711_; uint8_t v___x_712_; 
v_key_711_ = lean_ctor_get(v___x_710_, 0);
v___x_712_ = l_Lean_instBEqMVarId_beq(v_x_704_, v_key_711_);
return v___x_712_;
}
case 1:
{
lean_object* v_node_713_; size_t v___x_714_; size_t v___x_715_; 
v_node_713_ = lean_ctor_get(v___x_710_, 0);
v___x_714_ = ((size_t)5ULL);
v___x_715_ = lean_usize_shift_right(v_x_703_, v___x_714_);
v_x_702_ = v_node_713_;
v_x_703_ = v___x_715_;
goto _start;
}
default: 
{
uint8_t v___x_717_; 
v___x_717_ = 0;
return v___x_717_;
}
}
}
else
{
lean_object* v_ks_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_ks_718_ = lean_ctor_get(v_x_702_, 0);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_ks_718_, v___x_719_, v_x_704_);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg___boxed(lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
size_t v_x_73976__boxed_724_; uint8_t v_res_725_; lean_object* v_r_726_; 
v_x_73976__boxed_724_ = lean_unbox_usize(v_x_722_);
lean_dec(v_x_722_);
v_res_725_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_721_, v_x_73976__boxed_724_, v_x_723_);
lean_dec(v_x_723_);
lean_dec_ref(v_x_721_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(lean_object* v_x_727_, lean_object* v_x_728_){
_start:
{
uint64_t v___x_729_; size_t v___x_730_; uint8_t v___x_731_; 
v___x_729_ = l_Lean_instHashableMVarId_hash(v_x_728_);
v___x_730_ = lean_uint64_to_usize(v___x_729_);
v___x_731_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_727_, v___x_730_, v_x_728_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg___boxed(lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_732_, v_x_733_);
lean_dec(v_x_733_);
lean_dec_ref(v_x_732_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(lean_object* v_mvarId_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; lean_object* v_mctx_740_; lean_object* v_eAssignment_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_739_ = lean_st_ref_get(v___y_737_);
v_mctx_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc_ref(v_mctx_740_);
lean_dec(v___x_739_);
v_eAssignment_741_ = lean_ctor_get(v_mctx_740_, 8);
lean_inc_ref(v_eAssignment_741_);
lean_dec_ref(v_mctx_740_);
v___x_742_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_eAssignment_741_, v_mvarId_736_);
lean_dec_ref(v_eAssignment_741_);
v___x_743_ = lean_box(v___x_742_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg___boxed(lean_object* v_mvarId_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec(v_mvarId_745_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* v_msg_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_ref_755_; lean_object* v___x_756_; lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
v_ref_755_ = lean_ctor_get(v___y_752_, 2);
v___x_756_ = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(v_msg_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_765_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
lean_inc(v_ref_755_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v_ref_755_);
lean_ctor_set(v___x_761_, 1, v_a_757_);
if (v_isShared_760_ == 0)
{
lean_ctor_set_tag(v___x_759_, 1);
lean_ctor_set(v___x_759_, 0, v___x_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* v_msg_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_772_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* v_a_776_, lean_object* v_x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_783_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
v___x_784_ = l_Lean_Exception_toMessageData(v_a_776_);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* v_a_787_, lean_object* v_x_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(v_a_787_, v_x_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec_ref(v_x_788_);
return v_res_794_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(lean_object* v_e_795_){
_start:
{
if (lean_obj_tag(v_e_795_) == 0)
{
uint8_t v___x_796_; 
v___x_796_ = 2;
return v___x_796_;
}
else
{
uint8_t v___x_797_; 
v___x_797_ = 0;
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5___boxed(lean_object* v_e_798_){
_start:
{
uint8_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_e_798_);
lean_dec_ref(v_e_798_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* v_cls_801_, uint8_t v_collapsed_802_, lean_object* v_tag_803_, lean_object* v_opts_804_, uint8_t v_clsEnabled_805_, lean_object* v_oldTraces_806_, lean_object* v_msg_807_, lean_object* v_resStartStop_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_fst_814_; lean_object* v_snd_815_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v_data_819_; lean_object* v_fst_830_; lean_object* v_snd_831_; lean_object* v___x_832_; uint8_t v___x_833_; lean_object* v___y_835_; lean_object* v_a_836_; uint8_t v___y_851_; double v___y_883_; 
v_fst_814_ = lean_ctor_get(v_resStartStop_808_, 0);
lean_inc(v_fst_814_);
v_snd_815_ = lean_ctor_get(v_resStartStop_808_, 1);
lean_inc(v_snd_815_);
lean_dec_ref(v_resStartStop_808_);
v_fst_830_ = lean_ctor_get(v_snd_815_, 0);
lean_inc(v_fst_830_);
v_snd_831_ = lean_ctor_get(v_snd_815_, 1);
lean_inc(v_snd_831_);
lean_dec(v_snd_815_);
v___x_832_ = l_Lean_trace_profiler;
v___x_833_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_804_, v___x_832_);
if (v___x_833_ == 0)
{
v___y_851_ = v___x_833_;
goto v___jp_850_;
}
else
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = l_Lean_trace_profiler_useHeartbeats;
v___x_889_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_opts_804_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; double v___x_892_; double v___x_893_; double v___x_894_; 
v___x_890_ = l_Lean_trace_profiler_threshold;
v___x_891_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_804_, v___x_890_);
v___x_892_ = lean_float_of_nat(v___x_891_);
v___x_893_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__3);
v___x_894_ = lean_float_div(v___x_892_, v___x_893_);
v___y_883_ = v___x_894_;
goto v___jp_882_;
}
else
{
lean_object* v___x_895_; lean_object* v___x_896_; double v___x_897_; 
v___x_895_ = l_Lean_trace_profiler_threshold;
v___x_896_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__6(v_opts_804_, v___x_895_);
v___x_897_ = lean_float_of_nat(v___x_896_);
v___y_883_ = v___x_897_;
goto v___jp_882_;
}
}
v___jp_816_:
{
lean_object* v___x_820_; 
lean_inc(v___y_817_);
v___x_820_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__3(v_oldTraces_806_, v_data_819_, v___y_817_, v___y_818_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_821_; 
lean_dec_ref_known(v___x_820_, 1);
v___x_821_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_814_);
return v___x_821_;
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_fst_814_);
v_a_822_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_820_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_820_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
v___jp_834_:
{
uint8_t v_result_837_; lean_object* v___x_838_; lean_object* v___x_839_; double v___x_840_; lean_object* v_data_841_; 
v_result_837_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__5(v_fst_814_);
v___x_838_ = lean_box(v_result_837_);
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
v___x_840_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__0);
lean_inc_ref(v_tag_803_);
lean_inc_ref(v___x_839_);
lean_inc(v_cls_801_);
v_data_841_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_841_, 0, v_cls_801_);
lean_ctor_set(v_data_841_, 1, v___x_839_);
lean_ctor_set(v_data_841_, 2, v_tag_803_);
lean_ctor_set_float(v_data_841_, sizeof(void*)*3, v___x_840_);
lean_ctor_set_float(v_data_841_, sizeof(void*)*3 + 8, v___x_840_);
lean_ctor_set_uint8(v_data_841_, sizeof(void*)*3 + 16, v_collapsed_802_);
if (v___x_833_ == 0)
{
lean_dec_ref_known(v___x_839_, 1);
lean_dec(v_snd_831_);
lean_dec(v_fst_830_);
lean_dec_ref(v_tag_803_);
lean_dec(v_cls_801_);
v___y_817_ = v___y_835_;
v___y_818_ = v_a_836_;
v_data_819_ = v_data_841_;
goto v___jp_816_;
}
else
{
lean_object* v_data_842_; double v___x_843_; double v___x_844_; 
lean_dec_ref_known(v_data_841_, 3);
v_data_842_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_842_, 0, v_cls_801_);
lean_ctor_set(v_data_842_, 1, v___x_839_);
lean_ctor_set(v_data_842_, 2, v_tag_803_);
v___x_843_ = lean_unbox_float(v_fst_830_);
lean_dec(v_fst_830_);
lean_ctor_set_float(v_data_842_, sizeof(void*)*3, v___x_843_);
v___x_844_ = lean_unbox_float(v_snd_831_);
lean_dec(v_snd_831_);
lean_ctor_set_float(v_data_842_, sizeof(void*)*3 + 8, v___x_844_);
lean_ctor_set_uint8(v_data_842_, sizeof(void*)*3 + 16, v_collapsed_802_);
v___y_817_ = v___y_835_;
v___y_818_ = v_a_836_;
v_data_819_ = v_data_842_;
goto v___jp_816_;
}
}
v___jp_845_:
{
lean_object* v_ref_846_; lean_object* v___x_847_; 
v_ref_846_ = lean_ctor_get(v___y_811_, 2);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v_fst_814_);
v___x_847_ = lean_apply_6(v_msg_807_, v_fst_814_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, lean_box(0));
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref_known(v___x_847_, 1);
v___y_835_ = v_ref_846_;
v_a_836_ = v_a_848_;
goto v___jp_834_;
}
else
{
lean_object* v___x_849_; 
lean_dec_ref_known(v___x_847_, 1);
v___x_849_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___closed__2);
v___y_835_ = v_ref_846_;
v_a_836_ = v___x_849_;
goto v___jp_834_;
}
}
v___jp_850_:
{
if (v_clsEnabled_805_ == 0)
{
if (v___y_851_ == 0)
{
lean_object* v___x_852_; lean_object* v_traceState_853_; lean_object* v_env_854_; lean_object* v_nextMacroScope_855_; lean_object* v_ngen_856_; lean_object* v_auxDeclNGen_857_; lean_object* v_cache_858_; lean_object* v_recordedDeps_859_; lean_object* v_messages_860_; lean_object* v_infoState_861_; lean_object* v_snapshotTasks_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_881_; 
lean_dec(v_snd_831_);
lean_dec(v_fst_830_);
lean_dec_ref(v_msg_807_);
lean_dec_ref(v_tag_803_);
lean_dec(v_cls_801_);
v___x_852_ = lean_st_ref_take(v___y_812_);
v_traceState_853_ = lean_ctor_get(v___x_852_, 4);
v_env_854_ = lean_ctor_get(v___x_852_, 0);
v_nextMacroScope_855_ = lean_ctor_get(v___x_852_, 1);
v_ngen_856_ = lean_ctor_get(v___x_852_, 2);
v_auxDeclNGen_857_ = lean_ctor_get(v___x_852_, 3);
v_cache_858_ = lean_ctor_get(v___x_852_, 5);
v_recordedDeps_859_ = lean_ctor_get(v___x_852_, 6);
v_messages_860_ = lean_ctor_get(v___x_852_, 7);
v_infoState_861_ = lean_ctor_get(v___x_852_, 8);
v_snapshotTasks_862_ = lean_ctor_get(v___x_852_, 9);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_881_ == 0)
{
v___x_864_ = v___x_852_;
v_isShared_865_ = v_isSharedCheck_881_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_snapshotTasks_862_);
lean_inc(v_infoState_861_);
lean_inc(v_messages_860_);
lean_inc(v_recordedDeps_859_);
lean_inc(v_cache_858_);
lean_inc(v_traceState_853_);
lean_inc(v_auxDeclNGen_857_);
lean_inc(v_ngen_856_);
lean_inc(v_nextMacroScope_855_);
lean_inc(v_env_854_);
lean_dec(v___x_852_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_881_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
uint64_t v_tid_866_; lean_object* v_traces_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_880_; 
v_tid_866_ = lean_ctor_get_uint64(v_traceState_853_, sizeof(void*)*1);
v_traces_867_ = lean_ctor_get(v_traceState_853_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v_traceState_853_);
if (v_isSharedCheck_880_ == 0)
{
v___x_869_ = v_traceState_853_;
v_isShared_870_ = v_isSharedCheck_880_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_traces_867_);
lean_dec(v_traceState_853_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_880_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_806_, v_traces_867_);
lean_dec_ref(v_traces_867_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_871_);
v___x_873_ = v___x_869_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_871_);
lean_ctor_set_uint64(v_reuseFailAlloc_879_, sizeof(void*)*1, v_tid_866_);
v___x_873_ = v_reuseFailAlloc_879_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 4, v___x_873_);
v___x_875_ = v___x_864_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_env_854_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_nextMacroScope_855_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_ngen_856_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v_auxDeclNGen_857_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_878_, 5, v_cache_858_);
lean_ctor_set(v_reuseFailAlloc_878_, 6, v_recordedDeps_859_);
lean_ctor_set(v_reuseFailAlloc_878_, 7, v_messages_860_);
lean_ctor_set(v_reuseFailAlloc_878_, 8, v_infoState_861_);
lean_ctor_set(v_reuseFailAlloc_878_, 9, v_snapshotTasks_862_);
v___x_875_ = v_reuseFailAlloc_878_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_st_ref_put(v___y_812_, v___x_875_);
v___x_877_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_fst_814_);
return v___x_877_;
}
}
}
}
}
else
{
goto v___jp_845_;
}
}
else
{
goto v___jp_845_;
}
}
v___jp_882_:
{
double v___x_884_; double v___x_885_; double v___x_886_; uint8_t v___x_887_; 
v___x_884_ = lean_unbox_float(v_snd_831_);
v___x_885_ = lean_unbox_float(v_fst_830_);
v___x_886_ = lean_float_sub(v___x_884_, v___x_885_);
v___x_887_ = lean_float_decLt(v___y_883_, v___x_886_);
v___y_851_ = v___x_887_;
goto v___jp_850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* v_cls_898_, lean_object* v_collapsed_899_, lean_object* v_tag_900_, lean_object* v_opts_901_, lean_object* v_clsEnabled_902_, lean_object* v_oldTraces_903_, lean_object* v_msg_904_, lean_object* v_resStartStop_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
uint8_t v_collapsed_boxed_911_; uint8_t v_clsEnabled_boxed_912_; lean_object* v_res_913_; 
v_collapsed_boxed_911_ = lean_unbox(v_collapsed_899_);
v_clsEnabled_boxed_912_ = lean_unbox(v_clsEnabled_902_);
v_res_913_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_cls_898_, v_collapsed_boxed_911_, v_tag_900_, v_opts_901_, v_clsEnabled_boxed_912_, v_oldTraces_903_, v_msg_904_, v_resStartStop_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec_ref(v_opts_901_);
return v_res_913_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__0));
v___x_916_ = l_Lean_stringToMessageData(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(lean_object* v_head_917_, lean_object* v_x_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___closed__1);
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v_head_917_);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___boxed(lean_object* v_head_928_, lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7(v_head_928_, v_x_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec_ref(v_x_929_);
return v_res_935_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void){
_start:
{
lean_object* v___x_936_; double v___x_937_; 
v___x_936_ = lean_unsigned_to_nat(1000000000u);
v___x_937_ = lean_float_of_nat(v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__8___boxed(lean_object* v_tail_949_, lean_object* v_cfg_950_, lean_object* v_trace_951_, lean_object* v_next_952_, lean_object* v_goals_953_, lean_object* v_n_954_, lean_object* v_acc_955_, lean_object* v_r_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__8(v_tail_949_, v_cfg_950_, v_trace_951_, v_next_952_, v_goals_953_, v_n_954_, v_acc_955_, v_r_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* v_cfg_963_, lean_object* v_trace_964_, lean_object* v_next_965_, lean_object* v_goals_966_, lean_object* v_n_967_, lean_object* v_curr_968_, lean_object* v_acc_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___y_976_; uint8_t v___y_977_; lean_object* v___y_978_; uint8_t v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v_a_983_; lean_object* v___y_993_; uint8_t v___y_994_; uint8_t v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v_a_1000_; uint8_t v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; uint8_t v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; uint8_t v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; uint8_t v___y_1067_; lean_object* v_a_1068_; lean_object* v___y_1078_; lean_object* v___y_1079_; uint8_t v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; uint8_t v___y_1084_; lean_object* v_a_1085_; lean_object* v___y_1088_; lean_object* v___y_1089_; uint8_t v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; uint8_t v___y_1094_; lean_object* v_a_1095_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; uint8_t v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; uint8_t v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; uint8_t v___y_1113_; lean_object* v___y_1114_; uint8_t v___y_1115_; lean_object* v_a_1116_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; uint8_t v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; uint8_t v___y_1135_; lean_object* v_a_1136_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; uint8_t v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; uint8_t v___y_1145_; lean_object* v_a_1146_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; uint8_t v___y_1153_; lean_object* v___y_1154_; uint8_t v___y_1155_; lean_object* v___y_1156_; lean_object* v_zero_1159_; uint8_t v_isZero_1160_; 
v_zero_1159_ = lean_unsigned_to_nat(0u);
v_isZero_1160_ = lean_nat_dec_eq(v_n_967_, v_zero_1159_);
if (v_isZero_1160_ == 1)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec(v_acc_969_);
lean_dec(v_curr_968_);
lean_dec(v_n_967_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
v___x_1161_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
v___x_1162_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_1161_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1162_;
}
else
{
lean_object* v_proc_1163_; lean_object* v_suspend_1164_; lean_object* v_discharge_1165_; lean_object* v___f_1166_; uint8_t v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; uint8_t v___y_1171_; lean_object* v___y_1172_; lean_object* v___f_1208_; lean_object* v___y_1210_; lean_object* v___y_1211_; uint8_t v___y_1212_; uint8_t v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v_a_1216_; lean_object* v___y_1229_; lean_object* v___y_1230_; uint8_t v___y_1231_; uint8_t v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v_a_1235_; lean_object* v___y_1245_; lean_object* v___y_1246_; uint8_t v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; uint8_t v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; uint8_t v___y_1254_; lean_object* v_a_1255_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; uint8_t v___y_1271_; uint8_t v___y_1272_; lean_object* v___y_1273_; uint8_t v___y_1274_; lean_object* v_a_1275_; lean_object* v___f_1287_; uint8_t v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; uint8_t v___y_1296_; lean_object* v___y_1297_; uint8_t v___y_1298_; lean_object* v_a_1299_; uint8_t v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; uint8_t v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; uint8_t v___y_1322_; lean_object* v___f_1343_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; uint8_t v___y_1349_; lean_object* v___y_1350_; uint8_t v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; uint8_t v___y_1354_; lean_object* v_a_1355_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1372_; lean_object* v___y_1373_; uint8_t v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; uint8_t v___y_1378_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; uint8_t v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; uint8_t v___y_1408_; lean_object* v___y_1409_; lean_object* v_a_1410_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; uint8_t v___y_1429_; uint8_t v___y_1430_; lean_object* v___y_1452_; lean_object* v___y_1453_; uint8_t v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; uint8_t v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; uint8_t v___y_1460_; lean_object* v___y_1461_; lean_object* v_a_1462_; lean_object* v___y_1472_; lean_object* v___y_1473_; uint8_t v___y_1474_; uint8_t v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; uint8_t v___y_1482_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; uint8_t v___y_1507_; uint8_t v___y_1508_; lean_object* v___y_1509_; lean_object* v_a_1510_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; uint8_t v___y_1524_; uint8_t v___y_1525_; lean_object* v_a_1526_; lean_object* v___y_1539_; lean_object* v___y_1540_; uint8_t v___y_1541_; lean_object* v___y_1542_; uint8_t v___y_1543_; lean_object* v___y_1544_; lean_object* v_a_1545_; lean_object* v___y_1558_; lean_object* v___y_1559_; uint8_t v___y_1560_; lean_object* v___y_1561_; uint8_t v___y_1562_; lean_object* v___y_1563_; lean_object* v_a_1564_; lean_object* v_one_1573_; lean_object* v_n_1574_; lean_object* v___y_1576_; lean_object* v___y_1577_; uint8_t v___y_1578_; uint8_t v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; uint8_t v___y_1584_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; uint8_t v___y_1609_; lean_object* v___y_1610_; uint8_t v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; uint8_t v___y_1614_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; uint8_t v___y_1644_; lean_object* v___y_1645_; uint8_t v___y_1646_; lean_object* v___y_1647_; lean_object* v_a_1727_; lean_object* v___y_1976_; lean_object* v___x_1986_; 
v_proc_1163_ = lean_ctor_get(v_cfg_963_, 1);
v_suspend_1164_ = lean_ctor_get(v_cfg_963_, 2);
v_discharge_1165_ = lean_ctor_get(v_cfg_963_, 3);
v___f_1166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
v___f_1208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
v___f_1287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
v___f_1343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
v_one_1573_ = lean_unsigned_to_nat(1u);
v_n_1574_ = lean_nat_sub(v_n_967_, v_one_1573_);
lean_dec(v_n_967_);
lean_inc_ref(v_proc_1163_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_curr_968_);
lean_inc(v_goals_966_);
v___x_1986_ = lean_apply_7(v_proc_1163_, v_goals_966_, v_curr_968_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v_a_1727_ = v_a_1987_;
goto v___jp_1726_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2053_; 
v_a_1988_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_1990_ = v___x_1986_;
v_isShared_1991_ = v_isSharedCheck_2053_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2053_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
uint8_t v___x_1992_; 
v___x_1992_ = l_Lean_Exception_isInterrupt(v_a_1988_);
if (v___x_1992_ == 0)
{
uint8_t v___x_1993_; 
lean_inc(v_a_1988_);
v___x_1993_ = l_Lean_Exception_isRuntime(v_a_1988_);
if (v___x_1993_ == 0)
{
lean_object* v_toCold_1994_; lean_object* v_options_1995_; uint8_t v_hasTrace_1996_; 
v_toCold_1994_ = lean_ctor_get(v_a_972_, 0);
v_options_1995_ = lean_ctor_get(v_toCold_1994_, 2);
v_hasTrace_1996_ = lean_ctor_get_uint8(v_options_1995_, sizeof(void*)*1);
if (v_hasTrace_1996_ == 0)
{
lean_object* v___x_1998_; 
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_curr_968_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
if (v_isShared_1991_ == 0)
{
v___x_1998_ = v___x_1990_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1988_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2000_; lean_object* v___f_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v_inheritedTraceOptions_2000_ = lean_ctor_get(v_toCold_1994_, 11);
lean_inc(v_a_1988_);
v___f_2001_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(v___f_2001_, 0, v_a_1988_);
v___x_2002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_964_);
v___x_2004_ = l_Lean_Name_append(v___x_2003_, v_trace_964_);
v___x_2005_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2000_, v_options_1995_, v___x_2004_);
lean_dec(v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2042_ = l_Lean_trace_profiler;
v___x_2043_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1995_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2045_; 
lean_dec_ref(v___f_2001_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_curr_968_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
if (v_isShared_1991_ == 0)
{
v___x_2045_ = v___x_1990_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_1988_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
else
{
lean_del_object(v___x_1990_);
goto v___jp_2006_;
}
}
else
{
lean_del_object(v___x_1990_);
goto v___jp_2006_;
}
v___jp_2006_:
{
lean_object* v___x_2007_; lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2041_; 
v___x_2007_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2041_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2041_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2013_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1995_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2014_ = lean_io_mono_nanos_now();
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v_a_1988_);
v___x_2016_ = v___x_2010_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_1988_);
v___x_2016_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; double v___x_2018_; double v___x_2019_; double v___x_2020_; double v___x_2021_; double v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2017_ = lean_io_mono_nanos_now();
v___x_2018_ = lean_float_of_nat(v___x_2014_);
v___x_2019_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2020_ = lean_float_div(v___x_2018_, v___x_2019_);
v___x_2021_ = lean_float_of_nat(v___x_2017_);
v___x_2022_ = lean_float_div(v___x_2021_, v___x_2019_);
v___x_2023_ = lean_box_float(v___x_2020_);
v___x_2024_ = lean_box_float(v___x_2022_);
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2016_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
lean_inc(v_trace_964_);
v___x_2027_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_964_, v_hasTrace_1996_, v___x_2002_, v_options_1995_, v___x_2005_, v_a_2008_, v___f_2001_, v___x_2026_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1976_ = v___x_2027_;
goto v___jp_1975_;
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = lean_io_get_num_heartbeats();
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v_a_1988_);
v___x_2031_ = v___x_2010_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_1988_);
v___x_2031_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; double v___x_2033_; double v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2032_ = lean_io_get_num_heartbeats();
v___x_2033_ = lean_float_of_nat(v___x_2029_);
v___x_2034_ = lean_float_of_nat(v___x_2032_);
v___x_2035_ = lean_box_float(v___x_2033_);
v___x_2036_ = lean_box_float(v___x_2034_);
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2035_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2031_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
lean_inc(v_trace_964_);
v___x_2039_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(v_trace_964_, v_hasTrace_1996_, v___x_2002_, v_options_1995_, v___x_2005_, v_a_2008_, v___f_2001_, v___x_2038_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1976_ = v___x_2039_;
goto v___jp_1975_;
}
}
}
}
}
}
else
{
lean_object* v___x_2048_; 
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_curr_968_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
if (v_isShared_1991_ == 0)
{
v___x_2048_ = v___x_1990_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_1988_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
lean_object* v___x_2051_; 
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_curr_968_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
if (v_isShared_1991_ == 0)
{
v___x_2051_ = v___x_1990_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_1988_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
v___jp_1167_:
{
lean_object* v___x_1173_; lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1207_; 
v___x_1173_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1207_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1207_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1179_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1169_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_io_mono_nanos_now();
if (v_isShared_1177_ == 0)
{
lean_ctor_set_tag(v___x_1176_, 1);
lean_ctor_set(v___x_1176_, 0, v___y_1172_);
v___x_1182_ = v___x_1176_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___y_1172_);
v___x_1182_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; double v___x_1184_; double v___x_1185_; double v___x_1186_; double v___x_1187_; double v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1183_ = lean_io_mono_nanos_now();
v___x_1184_ = lean_float_of_nat(v___x_1180_);
v___x_1185_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1186_ = lean_float_div(v___x_1184_, v___x_1185_);
v___x_1187_ = lean_float_of_nat(v___x_1183_);
v___x_1188_ = lean_float_div(v___x_1187_, v___x_1185_);
v___x_1189_ = lean_box_float(v___x_1186_);
v___x_1190_ = lean_box_float(v___x_1188_);
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1182_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
lean_inc_ref(v___y_1170_);
v___x_1193_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1171_, v___y_1170_, v___y_1169_, v___y_1168_, v_a_1174_, v___f_1166_, v___x_1192_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1193_;
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_io_get_num_heartbeats();
if (v_isShared_1177_ == 0)
{
lean_ctor_set_tag(v___x_1176_, 1);
lean_ctor_set(v___x_1176_, 0, v___y_1172_);
v___x_1197_ = v___x_1176_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___y_1172_);
v___x_1197_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; double v___x_1199_; double v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1198_ = lean_io_get_num_heartbeats();
v___x_1199_ = lean_float_of_nat(v___x_1195_);
v___x_1200_ = lean_float_of_nat(v___x_1198_);
v___x_1201_ = lean_box_float(v___x_1199_);
v___x_1202_ = lean_box_float(v___x_1200_);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1197_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
lean_inc_ref(v___y_1170_);
v___x_1205_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1171_, v___y_1170_, v___y_1169_, v___y_1168_, v_a_1174_, v___f_1166_, v___x_1204_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1205_;
}
}
}
}
v___jp_1209_:
{
lean_object* v___x_1217_; double v___x_1218_; double v___x_1219_; double v___x_1220_; double v___x_1221_; double v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1217_ = lean_io_mono_nanos_now();
v___x_1218_ = lean_float_of_nat(v___y_1215_);
v___x_1219_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1220_ = lean_float_div(v___x_1218_, v___x_1219_);
v___x_1221_ = lean_float_of_nat(v___x_1217_);
v___x_1222_ = lean_float_div(v___x_1221_, v___x_1219_);
v___x_1223_ = lean_box_float(v___x_1220_);
v___x_1224_ = lean_box_float(v___x_1222_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v_a_1216_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
lean_inc_ref(v___y_1210_);
v___x_1227_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1213_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1214_, v___f_1208_, v___x_1226_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1227_;
}
v___jp_1228_:
{
lean_object* v___x_1236_; double v___x_1237_; double v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1236_ = lean_io_get_num_heartbeats();
v___x_1237_ = lean_float_of_nat(v___y_1233_);
v___x_1238_ = lean_float_of_nat(v___x_1236_);
v___x_1239_ = lean_box_float(v___x_1237_);
v___x_1240_ = lean_box_float(v___x_1238_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v_a_1235_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
lean_inc_ref(v___y_1229_);
v___x_1243_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1232_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1234_, v___f_1208_, v___x_1242_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1243_;
}
v___jp_1244_:
{
lean_object* v___x_1256_; double v___x_1257_; double v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1256_ = lean_io_get_num_heartbeats();
v___x_1257_ = lean_float_of_nat(v___y_1246_);
v___x_1258_ = lean_float_of_nat(v___x_1256_);
v___x_1259_ = lean_box_float(v___x_1257_);
v___x_1260_ = lean_box_float(v___x_1258_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_a_1255_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
lean_inc_ref(v___y_1245_);
lean_inc(v_trace_964_);
v___x_1263_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1251_, v___y_1245_, v___y_1248_, v___y_1247_, v___y_1249_, v___f_1208_, v___x_1262_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1098_ = v___y_1245_;
v___y_1099_ = v___y_1248_;
v___y_1100_ = v___y_1250_;
v___y_1101_ = v___y_1251_;
v___y_1102_ = v___y_1252_;
v___y_1103_ = v___y_1253_;
v___y_1104_ = v___y_1254_;
v___y_1105_ = v___x_1263_;
goto v___jp_1097_;
}
v___jp_1264_:
{
lean_object* v___x_1276_; double v___x_1277_; double v___x_1278_; double v___x_1279_; double v___x_1280_; double v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1276_ = lean_io_mono_nanos_now();
v___x_1277_ = lean_float_of_nat(v___y_1265_);
v___x_1278_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1279_ = lean_float_div(v___x_1277_, v___x_1278_);
v___x_1280_ = lean_float_of_nat(v___x_1276_);
v___x_1281_ = lean_float_div(v___x_1280_, v___x_1278_);
v___x_1282_ = lean_box_float(v___x_1279_);
v___x_1283_ = lean_box_float(v___x_1281_);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v_a_1275_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
lean_inc_ref(v___y_1267_);
lean_inc(v_trace_964_);
v___x_1286_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1271_, v___y_1267_, v___y_1268_, v___y_1272_, v___y_1270_, v___f_1208_, v___x_1285_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1149_ = v___y_1266_;
v___y_1150_ = v___y_1267_;
v___y_1151_ = v___y_1268_;
v___y_1152_ = v___y_1269_;
v___y_1153_ = v___y_1271_;
v___y_1154_ = v___y_1273_;
v___y_1155_ = v___y_1274_;
v___y_1156_ = v___x_1286_;
goto v___jp_1148_;
}
v___jp_1288_:
{
lean_object* v___x_1300_; double v___x_1301_; double v___x_1302_; double v___x_1303_; double v___x_1304_; double v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1300_ = lean_io_mono_nanos_now();
v___x_1301_ = lean_float_of_nat(v___y_1294_);
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
lean_inc_ref(v___y_1292_);
lean_inc(v_trace_964_);
v___x_1310_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1296_, v___y_1292_, v___y_1293_, v___y_1289_, v___y_1291_, v___f_1287_, v___x_1309_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1149_ = v___y_1290_;
v___y_1150_ = v___y_1292_;
v___y_1151_ = v___y_1293_;
v___y_1152_ = v___y_1295_;
v___y_1153_ = v___y_1296_;
v___y_1154_ = v___y_1297_;
v___y_1155_ = v___y_1298_;
v___y_1156_ = v___x_1310_;
goto v___jp_1148_;
}
v___jp_1311_:
{
lean_object* v___x_1323_; lean_object* v_a_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1323_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = lean_io_mono_nanos_now();
lean_inc(v_trace_964_);
v___x_1326_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___y_1321_, v___y_1319_, v___y_1314_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set_tag(v___x_1329_, 1);
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
v___y_1289_ = v___y_1312_;
v___y_1290_ = v___y_1313_;
v___y_1291_ = v_a_1324_;
v___y_1292_ = v___y_1315_;
v___y_1293_ = v___y_1316_;
v___y_1294_ = v___x_1325_;
v___y_1295_ = v___y_1318_;
v___y_1296_ = v___y_1317_;
v___y_1297_ = v___y_1320_;
v___y_1298_ = v___y_1322_;
v_a_1299_ = v___x_1332_;
goto v___jp_1288_;
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
v_a_1335_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1326_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1326_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 0);
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
v___y_1289_ = v___y_1312_;
v___y_1290_ = v___y_1313_;
v___y_1291_ = v_a_1324_;
v___y_1292_ = v___y_1315_;
v___y_1293_ = v___y_1316_;
v___y_1294_ = v___x_1325_;
v___y_1295_ = v___y_1318_;
v___y_1296_ = v___y_1317_;
v___y_1297_ = v___y_1320_;
v___y_1298_ = v___y_1322_;
v_a_1299_ = v___x_1340_;
goto v___jp_1288_;
}
}
}
}
v___jp_1344_:
{
lean_object* v___x_1356_; double v___x_1357_; double v___x_1358_; double v___x_1359_; double v___x_1360_; double v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1356_ = lean_io_mono_nanos_now();
v___x_1357_ = lean_float_of_nat(v___y_1353_);
v___x_1358_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1359_ = lean_float_div(v___x_1357_, v___x_1358_);
v___x_1360_ = lean_float_of_nat(v___x_1356_);
v___x_1361_ = lean_float_div(v___x_1360_, v___x_1358_);
v___x_1362_ = lean_box_float(v___x_1359_);
v___x_1363_ = lean_box_float(v___x_1361_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v_a_1355_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
lean_inc_ref(v___y_1346_);
lean_inc(v_trace_964_);
v___x_1366_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1349_, v___y_1346_, v___y_1347_, v___y_1351_, v___y_1350_, v___f_1343_, v___x_1365_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1149_ = v___y_1345_;
v___y_1150_ = v___y_1346_;
v___y_1151_ = v___y_1347_;
v___y_1152_ = v___y_1348_;
v___y_1153_ = v___y_1349_;
v___y_1154_ = v___y_1352_;
v___y_1155_ = v___y_1354_;
v___y_1156_ = v___x_1366_;
goto v___jp_1148_;
}
v___jp_1367_:
{
lean_object* v___x_1379_; lean_object* v_a_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1379_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref(v___x_1379_);
v___x_1381_ = lean_io_mono_nanos_now();
lean_inc(v_trace_964_);
v___x_1382_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___y_1368_, v___y_1375_, v___y_1377_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set_tag(v___x_1385_, 1);
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
v___y_1345_ = v___y_1369_;
v___y_1346_ = v___y_1370_;
v___y_1347_ = v___y_1371_;
v___y_1348_ = v___y_1373_;
v___y_1349_ = v___y_1372_;
v___y_1350_ = v_a_1380_;
v___y_1351_ = v___y_1374_;
v___y_1352_ = v___y_1376_;
v___y_1353_ = v___x_1381_;
v___y_1354_ = v___y_1378_;
v_a_1355_ = v___x_1388_;
goto v___jp_1344_;
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
v_a_1391_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1382_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1382_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 0);
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
v___y_1345_ = v___y_1369_;
v___y_1346_ = v___y_1370_;
v___y_1347_ = v___y_1371_;
v___y_1348_ = v___y_1373_;
v___y_1349_ = v___y_1372_;
v___y_1350_ = v_a_1380_;
v___y_1351_ = v___y_1374_;
v___y_1352_ = v___y_1376_;
v___y_1353_ = v___x_1381_;
v___y_1354_ = v___y_1378_;
v_a_1355_ = v___x_1396_;
goto v___jp_1344_;
}
}
}
}
v___jp_1399_:
{
lean_object* v___x_1411_; double v___x_1412_; double v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1411_ = lean_io_get_num_heartbeats();
v___x_1412_ = lean_float_of_nat(v___y_1402_);
v___x_1413_ = lean_float_of_nat(v___x_1411_);
v___x_1414_ = lean_box_float(v___x_1412_);
v___x_1415_ = lean_box_float(v___x_1413_);
v___x_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1417_, 0, v_a_1410_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
lean_inc_ref(v___y_1400_);
lean_inc(v_trace_964_);
v___x_1418_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1404_, v___y_1400_, v___y_1401_, v___y_1407_, v___y_1409_, v___f_1287_, v___x_1417_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1098_ = v___y_1400_;
v___y_1099_ = v___y_1401_;
v___y_1100_ = v___y_1403_;
v___y_1101_ = v___y_1404_;
v___y_1102_ = v___y_1405_;
v___y_1103_ = v___y_1406_;
v___y_1104_ = v___y_1408_;
v___y_1105_ = v___x_1418_;
goto v___jp_1097_;
}
v___jp_1419_:
{
lean_object* v___x_1431_; lean_object* v_a_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1431_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_964_);
v___x_1434_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___y_1427_, v___y_1426_, v___y_1422_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
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
v___y_1400_ = v___y_1420_;
v___y_1401_ = v___y_1421_;
v___y_1402_ = v___x_1433_;
v___y_1403_ = v___y_1424_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1425_;
v___y_1406_ = v___y_1428_;
v___y_1407_ = v___y_1429_;
v___y_1408_ = v___y_1430_;
v___y_1409_ = v_a_1432_;
v_a_1410_ = v___x_1440_;
goto v___jp_1399_;
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
v___y_1400_ = v___y_1420_;
v___y_1401_ = v___y_1421_;
v___y_1402_ = v___x_1433_;
v___y_1403_ = v___y_1424_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___y_1425_;
v___y_1406_ = v___y_1428_;
v___y_1407_ = v___y_1429_;
v___y_1408_ = v___y_1430_;
v___y_1409_ = v_a_1432_;
v_a_1410_ = v___x_1448_;
goto v___jp_1399_;
}
}
}
}
v___jp_1451_:
{
lean_object* v___x_1463_; double v___x_1464_; double v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1463_ = lean_io_get_num_heartbeats();
v___x_1464_ = lean_float_of_nat(v___y_1455_);
v___x_1465_ = lean_float_of_nat(v___x_1463_);
v___x_1466_ = lean_box_float(v___x_1464_);
v___x_1467_ = lean_box_float(v___x_1465_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_a_1462_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
lean_inc_ref(v___y_1452_);
lean_inc(v_trace_964_);
v___x_1470_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1457_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1461_, v___f_1343_, v___x_1469_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1098_ = v___y_1452_;
v___y_1099_ = v___y_1453_;
v___y_1100_ = v___y_1456_;
v___y_1101_ = v___y_1457_;
v___y_1102_ = v___y_1458_;
v___y_1103_ = v___y_1459_;
v___y_1104_ = v___y_1460_;
v___y_1105_ = v___x_1470_;
goto v___jp_1097_;
}
v___jp_1471_:
{
lean_object* v___x_1483_; lean_object* v_a_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1483_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_964_);
v___x_1486_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___y_1481_, v___y_1478_, v___y_1480_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set_tag(v___x_1489_, 1);
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
v___y_1452_ = v___y_1472_;
v___y_1453_ = v___y_1473_;
v___y_1454_ = v___y_1474_;
v___y_1455_ = v___x_1485_;
v___y_1456_ = v___y_1476_;
v___y_1457_ = v___y_1475_;
v___y_1458_ = v___y_1477_;
v___y_1459_ = v___y_1479_;
v___y_1460_ = v___y_1482_;
v___y_1461_ = v_a_1484_;
v_a_1462_ = v___x_1492_;
goto v___jp_1451_;
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_a_1495_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1486_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1486_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set_tag(v___x_1497_, 0);
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
v___y_1452_ = v___y_1472_;
v___y_1453_ = v___y_1473_;
v___y_1454_ = v___y_1474_;
v___y_1455_ = v___x_1485_;
v___y_1456_ = v___y_1476_;
v___y_1457_ = v___y_1475_;
v___y_1458_ = v___y_1477_;
v___y_1459_ = v___y_1479_;
v___y_1460_ = v___y_1482_;
v___y_1461_ = v_a_1484_;
v_a_1462_ = v___x_1500_;
goto v___jp_1451_;
}
}
}
}
v___jp_1503_:
{
lean_object* v___x_1511_; double v___x_1512_; double v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1511_ = lean_io_get_num_heartbeats();
v___x_1512_ = lean_float_of_nat(v___y_1509_);
v___x_1513_ = lean_float_of_nat(v___x_1511_);
v___x_1514_ = lean_box_float(v___x_1512_);
v___x_1515_ = lean_box_float(v___x_1513_);
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_a_1510_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
lean_inc_ref(v___y_1505_);
v___x_1518_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1508_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1504_, v___f_1287_, v___x_1517_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1518_;
}
v___jp_1519_:
{
lean_object* v___x_1527_; double v___x_1528_; double v___x_1529_; double v___x_1530_; double v___x_1531_; double v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1527_ = lean_io_mono_nanos_now();
v___x_1528_ = lean_float_of_nat(v___y_1523_);
v___x_1529_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1530_ = lean_float_div(v___x_1528_, v___x_1529_);
v___x_1531_ = lean_float_of_nat(v___x_1527_);
v___x_1532_ = lean_float_div(v___x_1531_, v___x_1529_);
v___x_1533_ = lean_box_float(v___x_1530_);
v___x_1534_ = lean_box_float(v___x_1532_);
v___x_1535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v_a_1526_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
lean_inc_ref(v___y_1521_);
v___x_1537_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1525_, v___y_1521_, v___y_1522_, v___y_1524_, v___y_1520_, v___f_1287_, v___x_1536_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1537_;
}
v___jp_1538_:
{
lean_object* v___x_1546_; double v___x_1547_; double v___x_1548_; double v___x_1549_; double v___x_1550_; double v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1546_ = lean_io_mono_nanos_now();
v___x_1547_ = lean_float_of_nat(v___y_1542_);
v___x_1548_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1549_ = lean_float_div(v___x_1547_, v___x_1548_);
v___x_1550_ = lean_float_of_nat(v___x_1546_);
v___x_1551_ = lean_float_div(v___x_1550_, v___x_1548_);
v___x_1552_ = lean_box_float(v___x_1549_);
v___x_1553_ = lean_box_float(v___x_1551_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_a_1545_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
lean_inc_ref(v___y_1539_);
v___x_1556_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1541_, v___y_1539_, v___y_1540_, v___y_1543_, v___y_1544_, v___f_1343_, v___x_1555_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1556_;
}
v___jp_1557_:
{
lean_object* v___x_1565_; double v___x_1566_; double v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1565_ = lean_io_get_num_heartbeats();
v___x_1566_ = lean_float_of_nat(v___y_1561_);
v___x_1567_ = lean_float_of_nat(v___x_1565_);
v___x_1568_ = lean_box_float(v___x_1566_);
v___x_1569_ = lean_box_float(v___x_1567_);
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v_a_1564_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
lean_inc_ref(v___y_1558_);
v___x_1572_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1560_, v___y_1558_, v___y_1559_, v___y_1562_, v___y_1563_, v___f_1343_, v___x_1571_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1572_;
}
v___jp_1575_:
{
lean_object* v___x_1585_; lean_object* v_a_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1585_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1585_);
v___x_1587_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_964_);
v___x_1588_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v_n_1574_, v___y_1582_, v_acc_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
lean_ctor_set_tag(v___x_1591_, 1);
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
v___y_1245_ = v___y_1576_;
v___y_1246_ = v___x_1587_;
v___y_1247_ = v___y_1578_;
v___y_1248_ = v___y_1577_;
v___y_1249_ = v_a_1586_;
v___y_1250_ = v___y_1580_;
v___y_1251_ = v___y_1579_;
v___y_1252_ = v___y_1581_;
v___y_1253_ = v___y_1583_;
v___y_1254_ = v___y_1584_;
v_a_1255_ = v___x_1594_;
goto v___jp_1244_;
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
v_a_1597_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1588_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1588_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 0);
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
v___y_1245_ = v___y_1576_;
v___y_1246_ = v___x_1587_;
v___y_1247_ = v___y_1578_;
v___y_1248_ = v___y_1577_;
v___y_1249_ = v_a_1586_;
v___y_1250_ = v___y_1580_;
v___y_1251_ = v___y_1579_;
v___y_1252_ = v___y_1581_;
v___y_1253_ = v___y_1583_;
v___y_1254_ = v___y_1584_;
v_a_1255_ = v___x_1602_;
goto v___jp_1244_;
}
}
}
}
v___jp_1605_:
{
lean_object* v___x_1615_; lean_object* v_a_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1615_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref(v___x_1615_);
v___x_1617_ = lean_io_mono_nanos_now();
lean_inc(v_trace_964_);
v___x_1618_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v_n_1574_, v___y_1613_, v_acc_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
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
v___y_1265_ = v___x_1617_;
v___y_1266_ = v___y_1606_;
v___y_1267_ = v___y_1607_;
v___y_1268_ = v___y_1608_;
v___y_1269_ = v___y_1610_;
v___y_1270_ = v_a_1616_;
v___y_1271_ = v___y_1609_;
v___y_1272_ = v___y_1611_;
v___y_1273_ = v___y_1612_;
v___y_1274_ = v___y_1614_;
v_a_1275_ = v___x_1624_;
goto v___jp_1264_;
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
v___y_1265_ = v___x_1617_;
v___y_1266_ = v___y_1606_;
v___y_1267_ = v___y_1607_;
v___y_1268_ = v___y_1608_;
v___y_1269_ = v___y_1610_;
v___y_1270_ = v_a_1616_;
v___y_1271_ = v___y_1609_;
v___y_1272_ = v___y_1611_;
v___y_1273_ = v___y_1612_;
v___y_1274_ = v___y_1614_;
v_a_1275_ = v___x_1632_;
goto v___jp_1264_;
}
}
}
}
v___jp_1635_:
{
lean_object* v___x_1648_; lean_object* v_a_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1648_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1651_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1638_, v___x_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec_ref(v___y_1643_);
v___x_1652_ = lean_io_mono_nanos_now();
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v___y_1647_);
v___x_1653_ = lean_apply_6(v___y_1636_, v___y_1647_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; uint8_t v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v___x_1655_ = lean_unbox(v_a_1654_);
lean_dec(v_a_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_inc_ref(v_next_965_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v___y_1647_);
v___x_1656_ = lean_apply_7(v_next_965_, v___y_1647_, v___y_1637_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; 
lean_dec(v___y_1647_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1639_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec_ref(v_cfg_963_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___y_1139_ = v___x_1652_;
v___y_1140_ = v___y_1645_;
v___y_1141_ = v___y_1638_;
v___y_1142_ = v___y_1646_;
v___y_1143_ = v_a_1649_;
v___y_1144_ = v___y_1642_;
v___y_1145_ = v___y_1644_;
v_a_1146_ = v_a_1657_;
goto v___jp_1138_;
}
else
{
lean_object* v_a_1658_; uint8_t v___x_1659_; 
v_a_1658_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1659_ = l_Lean_Exception_isInterrupt(v_a_1658_);
if (v___x_1659_ == 0)
{
uint8_t v___x_1660_; 
lean_inc(v_a_1658_);
v___x_1660_ = l_Lean_Exception_isRuntime(v_a_1658_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; 
lean_dec(v_a_1658_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v___y_1647_);
v___x_1661_ = lean_apply_6(v___y_1639_, v___y_1647_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
if (lean_obj_tag(v_a_1662_) == 0)
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v___x_1663_ = lean_nat_add(v_n_1574_, v_one_1573_);
lean_dec(v_n_1574_);
v___x_1664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___y_1647_);
lean_ctor_set(v___x_1664_, 1, v_acc_969_);
v___x_1665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_964_);
v___x_1666_ = l_Lean_Name_append(v___x_1665_, v_trace_964_);
v___x_1667_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1640_, v___y_1638_, v___x_1666_);
lean_dec(v___x_1666_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = l_Lean_trace_profiler;
v___x_1669_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1638_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
lean_inc(v_trace_964_);
v___x_1670_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___x_1663_, v___y_1641_, v___x_1664_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1149_ = v___x_1652_;
v___y_1150_ = v___y_1645_;
v___y_1151_ = v___y_1638_;
v___y_1152_ = v_a_1649_;
v___y_1153_ = v___y_1646_;
v___y_1154_ = v___y_1642_;
v___y_1155_ = v___y_1644_;
v___y_1156_ = v___x_1670_;
goto v___jp_1148_;
}
else
{
v___y_1312_ = v___x_1667_;
v___y_1313_ = v___x_1652_;
v___y_1314_ = v___x_1664_;
v___y_1315_ = v___y_1645_;
v___y_1316_ = v___y_1638_;
v___y_1317_ = v___y_1646_;
v___y_1318_ = v_a_1649_;
v___y_1319_ = v___y_1641_;
v___y_1320_ = v___y_1642_;
v___y_1321_ = v___x_1663_;
v___y_1322_ = v___y_1644_;
goto v___jp_1311_;
}
}
else
{
v___y_1312_ = v___x_1667_;
v___y_1313_ = v___x_1652_;
v___y_1314_ = v___x_1664_;
v___y_1315_ = v___y_1645_;
v___y_1316_ = v___y_1638_;
v___y_1317_ = v___y_1646_;
v___y_1318_ = v_a_1649_;
v___y_1319_ = v___y_1641_;
v___y_1320_ = v___y_1642_;
v___y_1321_ = v___x_1663_;
v___y_1322_ = v___y_1644_;
goto v___jp_1311_;
}
}
else
{
lean_object* v_val_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
lean_dec(v___y_1647_);
v_val_1671_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_val_1671_);
lean_dec_ref_known(v_a_1662_, 1);
v___x_1672_ = l_List_appendTR___redArg(v_val_1671_, v___y_1641_);
v___x_1673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_964_);
v___x_1674_ = l_Lean_Name_append(v___x_1673_, v_trace_964_);
v___x_1675_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1640_, v___y_1638_, v___x_1674_);
lean_dec(v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1676_ = l_Lean_trace_profiler;
v___x_1677_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1638_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; 
lean_inc(v_trace_964_);
v___x_1678_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v_n_1574_, v___x_1672_, v_acc_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1149_ = v___x_1652_;
v___y_1150_ = v___y_1645_;
v___y_1151_ = v___y_1638_;
v___y_1152_ = v_a_1649_;
v___y_1153_ = v___y_1646_;
v___y_1154_ = v___y_1642_;
v___y_1155_ = v___y_1644_;
v___y_1156_ = v___x_1678_;
goto v___jp_1148_;
}
else
{
v___y_1606_ = v___x_1652_;
v___y_1607_ = v___y_1645_;
v___y_1608_ = v___y_1638_;
v___y_1609_ = v___y_1646_;
v___y_1610_ = v_a_1649_;
v___y_1611_ = v___x_1675_;
v___y_1612_ = v___y_1642_;
v___y_1613_ = v___x_1672_;
v___y_1614_ = v___y_1644_;
goto v___jp_1605_;
}
}
else
{
v___y_1606_ = v___x_1652_;
v___y_1607_ = v___y_1645_;
v___y_1608_ = v___y_1638_;
v___y_1609_ = v___y_1646_;
v___y_1610_ = v_a_1649_;
v___y_1611_ = v___x_1675_;
v___y_1612_ = v___y_1642_;
v___y_1613_ = v___x_1672_;
v___y_1614_ = v___y_1644_;
goto v___jp_1605_;
}
}
}
else
{
lean_object* v_a_1679_; 
lean_dec(v___y_1647_);
lean_dec(v___y_1641_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec_ref(v_cfg_963_);
v_a_1679_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1661_, 1);
v___y_1129_ = v___x_1652_;
v___y_1130_ = v___y_1645_;
v___y_1131_ = v___y_1638_;
v___y_1132_ = v___y_1646_;
v___y_1133_ = v_a_1649_;
v___y_1134_ = v___y_1642_;
v___y_1135_ = v___y_1644_;
v_a_1136_ = v_a_1679_;
goto v___jp_1128_;
}
}
else
{
lean_dec(v___y_1647_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1639_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec_ref(v_cfg_963_);
v___y_1129_ = v___x_1652_;
v___y_1130_ = v___y_1645_;
v___y_1131_ = v___y_1638_;
v___y_1132_ = v___y_1646_;
v___y_1133_ = v_a_1649_;
v___y_1134_ = v___y_1642_;
v___y_1135_ = v___y_1644_;
v_a_1136_ = v_a_1658_;
goto v___jp_1128_;
}
}
else
{
lean_dec(v___y_1647_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1639_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec_ref(v_cfg_963_);
v___y_1129_ = v___x_1652_;
v___y_1130_ = v___y_1645_;
v___y_1131_ = v___y_1638_;
v___y_1132_ = v___y_1646_;
v___y_1133_ = v_a_1649_;
v___y_1134_ = v___y_1642_;
v___y_1135_ = v___y_1644_;
v_a_1136_ = v_a_1658_;
goto v___jp_1128_;
}
}
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
lean_dec_ref(v___y_1639_);
lean_dec_ref(v___y_1637_);
v___x_1680_ = lean_nat_add(v_n_1574_, v_one_1573_);
lean_dec(v_n_1574_);
v___x_1681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___y_1647_);
lean_ctor_set(v___x_1681_, 1, v_acc_969_);
v___x_1682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_964_);
v___x_1683_ = l_Lean_Name_append(v___x_1682_, v_trace_964_);
v___x_1684_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1640_, v___y_1638_, v___x_1683_);
lean_dec(v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = l_Lean_trace_profiler;
v___x_1686_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1638_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; 
lean_inc(v_trace_964_);
v___x_1687_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___x_1680_, v___y_1641_, v___x_1681_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1149_ = v___x_1652_;
v___y_1150_ = v___y_1645_;
v___y_1151_ = v___y_1638_;
v___y_1152_ = v_a_1649_;
v___y_1153_ = v___y_1646_;
v___y_1154_ = v___y_1642_;
v___y_1155_ = v___y_1644_;
v___y_1156_ = v___x_1687_;
goto v___jp_1148_;
}
else
{
v___y_1368_ = v___x_1680_;
v___y_1369_ = v___x_1652_;
v___y_1370_ = v___y_1645_;
v___y_1371_ = v___y_1638_;
v___y_1372_ = v___y_1646_;
v___y_1373_ = v_a_1649_;
v___y_1374_ = v___x_1684_;
v___y_1375_ = v___y_1641_;
v___y_1376_ = v___y_1642_;
v___y_1377_ = v___x_1681_;
v___y_1378_ = v___y_1644_;
goto v___jp_1367_;
}
}
else
{
v___y_1368_ = v___x_1680_;
v___y_1369_ = v___x_1652_;
v___y_1370_ = v___y_1645_;
v___y_1371_ = v___y_1638_;
v___y_1372_ = v___y_1646_;
v___y_1373_ = v_a_1649_;
v___y_1374_ = v___x_1684_;
v___y_1375_ = v___y_1641_;
v___y_1376_ = v___y_1642_;
v___y_1377_ = v___x_1681_;
v___y_1378_ = v___y_1644_;
goto v___jp_1367_;
}
}
}
else
{
lean_object* v_a_1688_; 
lean_dec(v___y_1647_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v___y_1637_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec_ref(v_cfg_963_);
v_a_1688_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1653_, 1);
v___y_1129_ = v___x_1652_;
v___y_1130_ = v___y_1645_;
v___y_1131_ = v___y_1638_;
v___y_1132_ = v___y_1646_;
v___y_1133_ = v_a_1649_;
v___y_1134_ = v___y_1642_;
v___y_1135_ = v___y_1644_;
v_a_1136_ = v_a_1688_;
goto v___jp_1128_;
}
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec_ref(v___y_1637_);
v___x_1689_ = lean_io_get_num_heartbeats();
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v___y_1647_);
v___x_1690_ = lean_apply_6(v___y_1636_, v___y_1647_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; uint8_t v___x_1692_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = lean_unbox(v_a_1691_);
lean_dec(v_a_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; 
lean_inc_ref(v_next_965_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v___y_1647_);
v___x_1693_ = lean_apply_7(v_next_965_, v___y_1647_, v___y_1643_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; 
lean_dec(v___y_1647_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1639_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec_ref(v_cfg_963_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v___y_1088_ = v___y_1645_;
v___y_1089_ = v___y_1638_;
v___y_1090_ = v___y_1646_;
v___y_1091_ = v_a_1649_;
v___y_1092_ = v___x_1689_;
v___y_1093_ = v___y_1642_;
v___y_1094_ = v___y_1644_;
v_a_1095_ = v_a_1694_;
goto v___jp_1087_;
}
else
{
lean_object* v_a_1695_; uint8_t v___x_1696_; 
v_a_1695_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1696_ = l_Lean_Exception_isInterrupt(v_a_1695_);
if (v___x_1696_ == 0)
{
uint8_t v___x_1697_; 
lean_inc(v_a_1695_);
v___x_1697_ = l_Lean_Exception_isRuntime(v_a_1695_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
lean_dec(v_a_1695_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v___y_1647_);
v___x_1698_ = lean_apply_6(v___y_1639_, v___y_1647_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
if (lean_obj_tag(v_a_1699_) == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1700_ = lean_nat_add(v_n_1574_, v_one_1573_);
lean_dec(v_n_1574_);
v___x_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___y_1647_);
lean_ctor_set(v___x_1701_, 1, v_acc_969_);
v___x_1702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_964_);
v___x_1703_ = l_Lean_Name_append(v___x_1702_, v_trace_964_);
v___x_1704_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1640_, v___y_1638_, v___x_1703_);
lean_dec(v___x_1703_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = l_Lean_trace_profiler;
v___x_1706_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1638_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; 
lean_inc(v_trace_964_);
v___x_1707_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___x_1700_, v___y_1641_, v___x_1701_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1098_ = v___y_1645_;
v___y_1099_ = v___y_1638_;
v___y_1100_ = v_a_1649_;
v___y_1101_ = v___y_1646_;
v___y_1102_ = v___x_1689_;
v___y_1103_ = v___y_1642_;
v___y_1104_ = v___y_1644_;
v___y_1105_ = v___x_1707_;
goto v___jp_1097_;
}
else
{
v___y_1420_ = v___y_1645_;
v___y_1421_ = v___y_1638_;
v___y_1422_ = v___x_1701_;
v___y_1423_ = v___y_1646_;
v___y_1424_ = v_a_1649_;
v___y_1425_ = v___x_1689_;
v___y_1426_ = v___y_1641_;
v___y_1427_ = v___x_1700_;
v___y_1428_ = v___y_1642_;
v___y_1429_ = v___x_1704_;
v___y_1430_ = v___y_1644_;
goto v___jp_1419_;
}
}
else
{
v___y_1420_ = v___y_1645_;
v___y_1421_ = v___y_1638_;
v___y_1422_ = v___x_1701_;
v___y_1423_ = v___y_1646_;
v___y_1424_ = v_a_1649_;
v___y_1425_ = v___x_1689_;
v___y_1426_ = v___y_1641_;
v___y_1427_ = v___x_1700_;
v___y_1428_ = v___y_1642_;
v___y_1429_ = v___x_1704_;
v___y_1430_ = v___y_1644_;
goto v___jp_1419_;
}
}
else
{
lean_object* v_val_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
lean_dec(v___y_1647_);
v_val_1708_ = lean_ctor_get(v_a_1699_, 0);
lean_inc(v_val_1708_);
lean_dec_ref_known(v_a_1699_, 1);
v___x_1709_ = l_List_appendTR___redArg(v_val_1708_, v___y_1641_);
v___x_1710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_964_);
v___x_1711_ = l_Lean_Name_append(v___x_1710_, v_trace_964_);
v___x_1712_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1640_, v___y_1638_, v___x_1711_);
lean_dec(v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = l_Lean_trace_profiler;
v___x_1714_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1638_, v___x_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_inc(v_trace_964_);
v___x_1715_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v_n_1574_, v___x_1709_, v_acc_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1098_ = v___y_1645_;
v___y_1099_ = v___y_1638_;
v___y_1100_ = v_a_1649_;
v___y_1101_ = v___y_1646_;
v___y_1102_ = v___x_1689_;
v___y_1103_ = v___y_1642_;
v___y_1104_ = v___y_1644_;
v___y_1105_ = v___x_1715_;
goto v___jp_1097_;
}
else
{
v___y_1576_ = v___y_1645_;
v___y_1577_ = v___y_1638_;
v___y_1578_ = v___x_1712_;
v___y_1579_ = v___y_1646_;
v___y_1580_ = v_a_1649_;
v___y_1581_ = v___x_1689_;
v___y_1582_ = v___x_1709_;
v___y_1583_ = v___y_1642_;
v___y_1584_ = v___y_1644_;
goto v___jp_1575_;
}
}
else
{
v___y_1576_ = v___y_1645_;
v___y_1577_ = v___y_1638_;
v___y_1578_ = v___x_1712_;
v___y_1579_ = v___y_1646_;
v___y_1580_ = v_a_1649_;
v___y_1581_ = v___x_1689_;
v___y_1582_ = v___x_1709_;
v___y_1583_ = v___y_1642_;
v___y_1584_ = v___y_1644_;
goto v___jp_1575_;
}
}
}
else
{
lean_object* v_a_1716_; 
lean_dec(v___y_1647_);
lean_dec(v___y_1641_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec_ref(v_cfg_963_);
v_a_1716_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1698_, 1);
v___y_1078_ = v___y_1645_;
v___y_1079_ = v___y_1638_;
v___y_1080_ = v___y_1646_;
v___y_1081_ = v_a_1649_;
v___y_1082_ = v___x_1689_;
v___y_1083_ = v___y_1642_;
v___y_1084_ = v___y_1644_;
v_a_1085_ = v_a_1716_;
goto v___jp_1077_;
}
}
else
{
lean_dec(v___y_1647_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1639_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec_ref(v_cfg_963_);
v___y_1078_ = v___y_1645_;
v___y_1079_ = v___y_1638_;
v___y_1080_ = v___y_1646_;
v___y_1081_ = v_a_1649_;
v___y_1082_ = v___x_1689_;
v___y_1083_ = v___y_1642_;
v___y_1084_ = v___y_1644_;
v_a_1085_ = v_a_1695_;
goto v___jp_1077_;
}
}
else
{
lean_dec(v___y_1647_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1639_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec_ref(v_cfg_963_);
v___y_1078_ = v___y_1645_;
v___y_1079_ = v___y_1638_;
v___y_1080_ = v___y_1646_;
v___y_1081_ = v_a_1649_;
v___y_1082_ = v___x_1689_;
v___y_1083_ = v___y_1642_;
v___y_1084_ = v___y_1644_;
v_a_1085_ = v_a_1695_;
goto v___jp_1077_;
}
}
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
lean_dec_ref(v___y_1643_);
lean_dec_ref(v___y_1639_);
v___x_1717_ = lean_nat_add(v_n_1574_, v_one_1573_);
lean_dec(v_n_1574_);
v___x_1718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1718_, 0, v___y_1647_);
lean_ctor_set(v___x_1718_, 1, v_acc_969_);
v___x_1719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_964_);
v___x_1720_ = l_Lean_Name_append(v___x_1719_, v_trace_964_);
v___x_1721_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_1640_, v___y_1638_, v___x_1720_);
lean_dec(v___x_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = l_Lean_trace_profiler;
v___x_1723_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1638_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
lean_inc(v_trace_964_);
v___x_1724_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___x_1717_, v___y_1641_, v___x_1718_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
v___y_1098_ = v___y_1645_;
v___y_1099_ = v___y_1638_;
v___y_1100_ = v_a_1649_;
v___y_1101_ = v___y_1646_;
v___y_1102_ = v___x_1689_;
v___y_1103_ = v___y_1642_;
v___y_1104_ = v___y_1644_;
v___y_1105_ = v___x_1724_;
goto v___jp_1097_;
}
else
{
v___y_1472_ = v___y_1645_;
v___y_1473_ = v___y_1638_;
v___y_1474_ = v___x_1721_;
v___y_1475_ = v___y_1646_;
v___y_1476_ = v_a_1649_;
v___y_1477_ = v___x_1689_;
v___y_1478_ = v___y_1641_;
v___y_1479_ = v___y_1642_;
v___y_1480_ = v___x_1718_;
v___y_1481_ = v___x_1717_;
v___y_1482_ = v___y_1644_;
goto v___jp_1471_;
}
}
else
{
v___y_1472_ = v___y_1645_;
v___y_1473_ = v___y_1638_;
v___y_1474_ = v___x_1721_;
v___y_1475_ = v___y_1646_;
v___y_1476_ = v_a_1649_;
v___y_1477_ = v___x_1689_;
v___y_1478_ = v___y_1641_;
v___y_1479_ = v___y_1642_;
v___y_1480_ = v___x_1718_;
v___y_1481_ = v___x_1717_;
v___y_1482_ = v___y_1644_;
goto v___jp_1471_;
}
}
}
else
{
lean_object* v_a_1725_; 
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1639_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec_ref(v_cfg_963_);
v_a_1725_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1690_, 1);
v___y_1078_ = v___y_1645_;
v___y_1079_ = v___y_1638_;
v___y_1080_ = v___y_1646_;
v___y_1081_ = v_a_1649_;
v___y_1082_ = v___x_1689_;
v___y_1083_ = v___y_1642_;
v___y_1084_ = v___y_1644_;
v_a_1085_ = v_a_1725_;
goto v___jp_1077_;
}
}
}
v___jp_1726_:
{
if (lean_obj_tag(v_a_1727_) == 0)
{
if (lean_obj_tag(v_curr_968_) == 0)
{
lean_object* v_toCold_1728_; lean_object* v_options_1729_; lean_object* v_inheritedTraceOptions_1730_; uint8_t v_hasTrace_1731_; lean_object* v___x_1732_; 
lean_dec(v_n_1574_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec_ref(v_cfg_963_);
v_toCold_1728_ = lean_ctor_get(v_a_972_, 0);
v_options_1729_ = lean_ctor_get(v_toCold_1728_, 2);
v_inheritedTraceOptions_1730_ = lean_ctor_get(v_toCold_1728_, 11);
v_hasTrace_1731_ = lean_ctor_get_uint8(v_options_1729_, sizeof(void*)*1);
v___x_1732_ = l_List_reverse___redArg(v_acc_969_);
if (v_hasTrace_1731_ == 0)
{
lean_object* v___x_1733_; 
lean_dec(v_trace_964_);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_964_);
v___x_1736_ = l_Lean_Name_append(v___x_1735_, v_trace_964_);
v___x_1737_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1730_, v_options_1729_, v___x_1736_);
lean_dec(v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1738_ = l_Lean_trace_profiler;
v___x_1739_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1729_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; 
lean_dec(v_trace_964_);
v___x_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1732_);
return v___x_1740_;
}
else
{
v___y_1168_ = v___x_1737_;
v___y_1169_ = v_options_1729_;
v___y_1170_ = v___x_1734_;
v___y_1171_ = v_hasTrace_1731_;
v___y_1172_ = v___x_1732_;
goto v___jp_1167_;
}
}
else
{
v___y_1168_ = v___x_1737_;
v___y_1169_ = v_options_1729_;
v___y_1170_ = v___x_1734_;
v___y_1171_ = v_hasTrace_1731_;
v___y_1172_ = v___x_1732_;
goto v___jp_1167_;
}
}
}
else
{
lean_object* v_head_1741_; lean_object* v_tail_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1972_; 
v_head_1741_ = lean_ctor_get(v_curr_968_, 0);
v_tail_1742_ = lean_ctor_get(v_curr_968_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_curr_968_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1744_ = v_curr_968_;
v_isShared_1745_ = v_isSharedCheck_1972_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_tail_1742_);
lean_inc(v_head_1741_);
lean_dec(v_curr_968_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1972_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___f_1746_; lean_object* v___f_1747_; lean_object* v___f_1748_; lean_object* v___x_1749_; lean_object* v_a_1750_; uint8_t v___x_1751_; uint8_t v___x_1752_; 
lean_inc(v_acc_969_);
lean_inc(v_n_1574_);
lean_inc(v_goals_966_);
lean_inc_ref(v_next_965_);
lean_inc(v_trace_964_);
lean_inc_ref(v_cfg_963_);
lean_inc(v_tail_1742_);
v___f_1746_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__8___boxed), 13, 7);
lean_closure_set(v___f_1746_, 0, v_tail_1742_);
lean_closure_set(v___f_1746_, 1, v_cfg_963_);
lean_closure_set(v___f_1746_, 2, v_trace_964_);
lean_closure_set(v___f_1746_, 3, v_next_965_);
lean_closure_set(v___f_1746_, 4, v_goals_966_);
lean_closure_set(v___f_1746_, 5, v_n_1574_);
lean_closure_set(v___f_1746_, 6, v_acc_969_);
lean_inc_n(v_head_1741_, 2);
v___f_1747_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__7___boxed), 7, 1);
lean_closure_set(v___f_1747_, 0, v_head_1741_);
v___f_1748_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed), 7, 1);
lean_closure_set(v___f_1748_, 0, v_head_1741_);
v___x_1749_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_1741_, v_a_971_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = 1;
v___x_1752_ = lean_unbox(v_a_1750_);
lean_dec(v_a_1750_);
if (v___x_1752_ == 0)
{
lean_object* v_toCold_1753_; lean_object* v_options_1754_; uint8_t v_hasTrace_1755_; 
lean_dec_ref(v___f_1747_);
v_toCold_1753_ = lean_ctor_get(v_a_972_, 0);
v_options_1754_ = lean_ctor_get(v_toCold_1753_, 2);
v_hasTrace_1755_ = lean_ctor_get_uint8(v_options_1754_, sizeof(void*)*1);
if (v_hasTrace_1755_ == 0)
{
lean_object* v___x_1756_; 
lean_dec_ref(v___f_1748_);
lean_inc_ref(v_suspend_1164_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_head_1741_);
v___x_1756_ = lean_apply_6(v_suspend_1164_, v_head_1741_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; uint8_t v___x_1758_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___x_1756_, 1);
v___x_1758_ = lean_unbox(v_a_1757_);
lean_dec(v_a_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; 
lean_inc_ref(v_next_965_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_head_1741_);
v___x_1759_ = lean_apply_7(v_next_965_, v_head_1741_, v___f_1746_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_del_object(v___x_1744_);
lean_dec(v_tail_1742_);
lean_dec(v_head_1741_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
return v___x_1759_;
}
else
{
lean_object* v_a_1760_; uint8_t v___x_1761_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
v___x_1761_ = l_Lean_Exception_isInterrupt(v_a_1760_);
if (v___x_1761_ == 0)
{
uint8_t v___x_1762_; 
v___x_1762_ = l_Lean_Exception_isRuntime(v_a_1760_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; 
lean_dec_ref_known(v___x_1759_, 1);
lean_inc_ref(v_discharge_1165_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_head_1741_);
v___x_1763_ = lean_apply_6(v_discharge_1165_, v_head_1741_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
if (lean_obj_tag(v_a_1764_) == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = lean_nat_add(v_n_1574_, v_one_1573_);
lean_dec(v_n_1574_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v_acc_969_);
v___x_1767_ = v___x_1744_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_head_1741_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_acc_969_);
v___x_1767_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
v_n_967_ = v___x_1765_;
v_curr_968_ = v_tail_1742_;
v_acc_969_ = v___x_1767_;
goto _start;
}
}
else
{
lean_object* v_val_1770_; lean_object* v___x_1771_; 
lean_del_object(v___x_1744_);
lean_dec(v_head_1741_);
v_val_1770_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_val_1770_);
lean_dec_ref_known(v_a_1764_, 1);
v___x_1771_ = l_List_appendTR___redArg(v_val_1770_, v_tail_1742_);
v_n_967_ = v_n_1574_;
v_curr_968_ = v___x_1771_;
goto _start;
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_del_object(v___x_1744_);
lean_dec(v_tail_1742_);
lean_dec(v_head_1741_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
v_a_1773_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1763_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1763_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_del_object(v___x_1744_);
lean_dec(v_tail_1742_);
lean_dec(v_head_1741_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
return v___x_1759_;
}
}
else
{
lean_dec(v_a_1760_);
lean_del_object(v___x_1744_);
lean_dec(v_tail_1742_);
lean_dec(v_head_1741_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
return v___x_1759_;
}
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
lean_dec_ref(v___f_1746_);
v___x_1781_ = lean_nat_add(v_n_1574_, v_one_1573_);
lean_dec(v_n_1574_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v_acc_969_);
v___x_1783_ = v___x_1744_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_head_1741_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_acc_969_);
v___x_1783_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
v_n_967_ = v___x_1781_;
v_curr_968_ = v_tail_1742_;
v_acc_969_ = v___x_1783_;
goto _start;
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v___f_1746_);
lean_del_object(v___x_1744_);
lean_dec(v_tail_1742_);
lean_dec(v_head_1741_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
v_a_1786_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1756_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1756_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v_inheritedTraceOptions_1794_ = lean_ctor_get(v_toCold_1753_, 11);
v___x_1795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_1796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_964_);
v___x_1797_ = l_Lean_Name_append(v___x_1796_, v_trace_964_);
v___x_1798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1794_, v_options_1754_, v___x_1797_);
lean_dec(v___x_1797_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; uint8_t v___x_1800_; 
v___x_1799_ = l_Lean_trace_profiler;
v___x_1800_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1754_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; 
lean_dec_ref(v___f_1748_);
lean_inc_ref(v_suspend_1164_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_head_1741_);
v___x_1801_ = lean_apply_6(v_suspend_1164_, v_head_1741_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; uint8_t v___x_1803_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v___x_1803_ = lean_unbox(v_a_1802_);
lean_dec(v_a_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_inc_ref(v_next_965_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_head_1741_);
v___x_1804_ = lean_apply_7(v_next_965_, v_head_1741_, v___f_1746_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_del_object(v___x_1744_);
lean_dec(v_tail_1742_);
lean_dec(v_head_1741_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
return v___x_1804_;
}
else
{
lean_object* v_a_1805_; uint8_t v___x_1806_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
v___x_1806_ = l_Lean_Exception_isInterrupt(v_a_1805_);
if (v___x_1806_ == 0)
{
uint8_t v___x_1807_; 
v___x_1807_ = l_Lean_Exception_isRuntime(v_a_1805_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; 
lean_dec_ref_known(v___x_1804_, 1);
lean_inc_ref(v_discharge_1165_);
lean_inc(v_a_973_);
lean_inc_ref(v_a_972_);
lean_inc(v_a_971_);
lean_inc_ref(v_a_970_);
lean_inc(v_head_1741_);
v___x_1808_ = lean_apply_6(v_discharge_1165_, v_head_1741_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, lean_box(0));
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
if (lean_obj_tag(v_a_1809_) == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_nat_add(v_n_1574_, v_one_1573_);
lean_dec(v_n_1574_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v_acc_969_);
v___x_1812_ = v___x_1744_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_head_1741_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_acc_969_);
v___x_1812_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
if (v___x_1798_ == 0)
{
v_n_967_ = v___x_1810_;
v_curr_968_ = v_tail_1742_;
v_acc_969_ = v___x_1812_;
goto _start;
}
else
{
lean_object* v___x_1814_; lean_object* v_a_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1814_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref(v___x_1814_);
v___x_1816_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1817_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1754_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = lean_io_mono_nanos_now();
lean_inc(v_trace_964_);
v___x_1819_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___x_1810_, v_tail_1742_, v___x_1812_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set_tag(v___x_1822_, 1);
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
v___y_1520_ = v_a_1815_;
v___y_1521_ = v___x_1795_;
v___y_1522_ = v_options_1754_;
v___y_1523_ = v___x_1818_;
v___y_1524_ = v___x_1798_;
v___y_1525_ = v___x_1751_;
v_a_1526_ = v___x_1825_;
goto v___jp_1519_;
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
v_a_1828_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1819_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1819_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set_tag(v___x_1830_, 0);
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
v___y_1520_ = v_a_1815_;
v___y_1521_ = v___x_1795_;
v___y_1522_ = v_options_1754_;
v___y_1523_ = v___x_1818_;
v___y_1524_ = v___x_1798_;
v___y_1525_ = v___x_1751_;
v_a_1526_ = v___x_1833_;
goto v___jp_1519_;
}
}
}
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_964_);
v___x_1837_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___x_1810_, v_tail_1742_, v___x_1812_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set_tag(v___x_1840_, 1);
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
v___y_1504_ = v_a_1815_;
v___y_1505_ = v___x_1795_;
v___y_1506_ = v_options_1754_;
v___y_1507_ = v___x_1798_;
v___y_1508_ = v___x_1751_;
v___y_1509_ = v___x_1836_;
v_a_1510_ = v___x_1843_;
goto v___jp_1503_;
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_a_1846_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1837_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1837_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 0);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
v___y_1504_ = v_a_1815_;
v___y_1505_ = v___x_1795_;
v___y_1506_ = v_options_1754_;
v___y_1507_ = v___x_1798_;
v___y_1508_ = v___x_1751_;
v___y_1509_ = v___x_1836_;
v_a_1510_ = v___x_1851_;
goto v___jp_1503_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_1855_; lean_object* v___x_1856_; 
lean_del_object(v___x_1744_);
lean_dec(v_head_1741_);
v_val_1855_ = lean_ctor_get(v_a_1809_, 0);
lean_inc(v_val_1855_);
lean_dec_ref_known(v_a_1809_, 1);
v___x_1856_ = l_List_appendTR___redArg(v_val_1855_, v_tail_1742_);
if (v___x_1798_ == 0)
{
v_n_967_ = v_n_1574_;
v_curr_968_ = v___x_1856_;
goto _start;
}
else
{
lean_object* v___x_1858_; lean_object* v_a_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1858_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1861_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1754_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_io_mono_nanos_now();
lean_inc(v_trace_964_);
v___x_1863_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v_n_1574_, v___x_1856_, v_acc_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
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
v___y_1210_ = v___x_1795_;
v___y_1211_ = v_options_1754_;
v___y_1212_ = v___x_1798_;
v___y_1213_ = v___x_1751_;
v___y_1214_ = v_a_1859_;
v___y_1215_ = v___x_1862_;
v_a_1216_ = v___x_1869_;
goto v___jp_1209_;
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
v___y_1210_ = v___x_1795_;
v___y_1211_ = v_options_1754_;
v___y_1212_ = v___x_1798_;
v___y_1213_ = v___x_1751_;
v___y_1214_ = v_a_1859_;
v___y_1215_ = v___x_1862_;
v_a_1216_ = v___x_1877_;
goto v___jp_1209_;
}
}
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_964_);
v___x_1881_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v_n_1574_, v___x_1856_, v_acc_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
lean_ctor_set_tag(v___x_1884_, 1);
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
v___y_1229_ = v___x_1795_;
v___y_1230_ = v_options_1754_;
v___y_1231_ = v___x_1798_;
v___y_1232_ = v___x_1751_;
v___y_1233_ = v___x_1880_;
v___y_1234_ = v_a_1859_;
v_a_1235_ = v___x_1887_;
goto v___jp_1228_;
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_a_1890_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1881_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1881_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set_tag(v___x_1892_, 0);
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
v___y_1229_ = v___x_1795_;
v___y_1230_ = v_options_1754_;
v___y_1231_ = v___x_1798_;
v___y_1232_ = v___x_1751_;
v___y_1233_ = v___x_1880_;
v___y_1234_ = v_a_1859_;
v_a_1235_ = v___x_1895_;
goto v___jp_1228_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_del_object(v___x_1744_);
lean_dec(v_tail_1742_);
lean_dec(v_head_1741_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
v_a_1898_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1808_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1808_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_del_object(v___x_1744_);
lean_dec(v_tail_1742_);
lean_dec(v_head_1741_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
return v___x_1804_;
}
}
else
{
lean_dec(v_a_1805_);
lean_del_object(v___x_1744_);
lean_dec(v_tail_1742_);
lean_dec(v_head_1741_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
return v___x_1804_;
}
}
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
lean_dec_ref(v___f_1746_);
v___x_1906_ = lean_nat_add(v_n_1574_, v_one_1573_);
lean_dec(v_n_1574_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 1, v_acc_969_);
v___x_1908_ = v___x_1744_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_head_1741_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_acc_969_);
v___x_1908_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
if (v___x_1798_ == 0)
{
v_n_967_ = v___x_1906_;
v_curr_968_ = v_tail_1742_;
v_acc_969_ = v___x_1908_;
goto _start;
}
else
{
lean_object* v___x_1910_; lean_object* v_a_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1910_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref(v___x_1910_);
v___x_1912_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1913_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1754_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_io_mono_nanos_now();
lean_inc(v_trace_964_);
v___x_1915_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___x_1906_, v_tail_1742_, v___x_1908_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set_tag(v___x_1918_, 1);
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
v___y_1539_ = v___x_1795_;
v___y_1540_ = v_options_1754_;
v___y_1541_ = v___x_1751_;
v___y_1542_ = v___x_1914_;
v___y_1543_ = v___x_1798_;
v___y_1544_ = v_a_1911_;
v_a_1545_ = v___x_1921_;
goto v___jp_1538_;
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
v_a_1924_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1915_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1915_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set_tag(v___x_1926_, 0);
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
v___y_1539_ = v___x_1795_;
v___y_1540_ = v_options_1754_;
v___y_1541_ = v___x_1751_;
v___y_1542_ = v___x_1914_;
v___y_1543_ = v___x_1798_;
v___y_1544_ = v_a_1911_;
v_a_1545_ = v___x_1929_;
goto v___jp_1538_;
}
}
}
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_964_);
v___x_1933_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___x_1906_, v_tail_1742_, v___x_1908_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 1);
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
v___y_1558_ = v___x_1795_;
v___y_1559_ = v_options_1754_;
v___y_1560_ = v___x_1751_;
v___y_1561_ = v___x_1932_;
v___y_1562_ = v___x_1798_;
v___y_1563_ = v_a_1911_;
v_a_1564_ = v___x_1939_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_a_1942_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1933_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1933_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set_tag(v___x_1944_, 0);
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
v___y_1558_ = v___x_1795_;
v___y_1559_ = v_options_1754_;
v___y_1560_ = v___x_1751_;
v___y_1561_ = v___x_1932_;
v___y_1562_ = v___x_1798_;
v___y_1563_ = v_a_1911_;
v_a_1564_ = v___x_1947_;
goto v___jp_1557_;
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
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v___f_1746_);
lean_del_object(v___x_1744_);
lean_dec(v_tail_1742_);
lean_dec(v_head_1741_);
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
v_a_1951_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1801_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1801_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
else
{
lean_del_object(v___x_1744_);
lean_inc_ref(v_discharge_1165_);
lean_inc_ref(v___f_1746_);
lean_inc_ref(v_suspend_1164_);
v___y_1636_ = v_suspend_1164_;
v___y_1637_ = v___f_1746_;
v___y_1638_ = v_options_1754_;
v___y_1639_ = v_discharge_1165_;
v___y_1640_ = v_inheritedTraceOptions_1794_;
v___y_1641_ = v_tail_1742_;
v___y_1642_ = v___f_1748_;
v___y_1643_ = v___f_1746_;
v___y_1644_ = v___x_1798_;
v___y_1645_ = v___x_1795_;
v___y_1646_ = v___x_1751_;
v___y_1647_ = v_head_1741_;
goto v___jp_1635_;
}
}
else
{
lean_del_object(v___x_1744_);
lean_inc_ref(v_discharge_1165_);
lean_inc_ref(v___f_1746_);
lean_inc_ref(v_suspend_1164_);
v___y_1636_ = v_suspend_1164_;
v___y_1637_ = v___f_1746_;
v___y_1638_ = v_options_1754_;
v___y_1639_ = v_discharge_1165_;
v___y_1640_ = v_inheritedTraceOptions_1794_;
v___y_1641_ = v_tail_1742_;
v___y_1642_ = v___f_1748_;
v___y_1643_ = v___f_1746_;
v___y_1644_ = v___x_1798_;
v___y_1645_ = v___x_1795_;
v___y_1646_ = v___x_1751_;
v___y_1647_ = v_head_1741_;
goto v___jp_1635_;
}
}
}
else
{
lean_object* v_toCold_1959_; lean_object* v_options_1960_; lean_object* v_inheritedTraceOptions_1961_; uint8_t v_hasTrace_1962_; lean_object* v___x_1963_; 
lean_dec_ref(v___f_1748_);
lean_dec_ref(v___f_1746_);
lean_del_object(v___x_1744_);
lean_dec(v_head_1741_);
v_toCold_1959_ = lean_ctor_get(v_a_972_, 0);
v_options_1960_ = lean_ctor_get(v_toCold_1959_, 2);
v_inheritedTraceOptions_1961_ = lean_ctor_get(v_toCold_1959_, 11);
v_hasTrace_1962_ = lean_ctor_get_uint8(v_options_1960_, sizeof(void*)*1);
v___x_1963_ = lean_nat_add(v_n_1574_, v_one_1573_);
lean_dec(v_n_1574_);
if (v_hasTrace_1962_ == 0)
{
lean_dec_ref(v___f_1747_);
v_n_967_ = v___x_1963_;
v_curr_968_ = v_tail_1742_;
goto _start;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_1966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_964_);
v___x_1967_ = l_Lean_Name_append(v___x_1966_, v_trace_964_);
v___x_1968_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1961_, v_options_1960_, v___x_1967_);
lean_dec(v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1969_ = l_Lean_trace_profiler;
v___x_1970_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_1960_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_dec_ref(v___f_1747_);
v_n_967_ = v___x_1963_;
v_curr_968_ = v_tail_1742_;
goto _start;
}
else
{
v___y_1013_ = v___x_1968_;
v___y_1014_ = v___f_1747_;
v___y_1015_ = v___x_1963_;
v___y_1016_ = v___x_1751_;
v___y_1017_ = v_tail_1742_;
v___y_1018_ = v_options_1960_;
v___y_1019_ = v___x_1965_;
goto v___jp_1012_;
}
}
else
{
v___y_1013_ = v___x_1968_;
v___y_1014_ = v___f_1747_;
v___y_1015_ = v___x_1963_;
v___y_1016_ = v___x_1751_;
v___y_1017_ = v_tail_1742_;
v___y_1018_ = v_options_1960_;
v___y_1019_ = v___x_1965_;
goto v___jp_1012_;
}
}
}
}
}
}
else
{
lean_object* v_val_1973_; 
lean_dec(v_curr_968_);
v_val_1973_ = lean_ctor_get(v_a_1727_, 0);
lean_inc(v_val_1973_);
lean_dec_ref_known(v_a_1727_, 1);
v_n_967_ = v_n_1574_;
v_curr_968_ = v_val_1973_;
goto _start;
}
}
v___jp_1975_:
{
if (lean_obj_tag(v___y_1976_) == 0)
{
lean_object* v_a_1977_; 
v_a_1977_ = lean_ctor_get(v___y_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___y_1976_, 1);
v_a_1727_ = v_a_1977_;
goto v___jp_1726_;
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec(v_n_1574_);
lean_dec(v_acc_969_);
lean_dec(v_curr_968_);
lean_dec(v_goals_966_);
lean_dec_ref(v_next_965_);
lean_dec(v_trace_964_);
lean_dec_ref(v_cfg_963_);
v_a_1978_ = lean_ctor_get(v___y_1976_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___y_1976_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___y_1976_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___y_1976_);
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
}
v___jp_975_:
{
lean_object* v___x_984_; double v___x_985_; double v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_984_ = lean_io_get_num_heartbeats();
v___x_985_ = lean_float_of_nat(v___y_978_);
v___x_986_ = lean_float_of_nat(v___x_984_);
v___x_987_ = lean_box_float(v___x_985_);
v___x_988_ = lean_box_float(v___x_986_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v_a_983_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
lean_inc_ref(v___y_982_);
v___x_991_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_979_, v___y_982_, v___y_980_, v___y_977_, v___y_981_, v___y_976_, v___x_990_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_991_;
}
v___jp_992_:
{
lean_object* v___x_1001_; double v___x_1002_; double v___x_1003_; double v___x_1004_; double v___x_1005_; double v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1001_ = lean_io_mono_nanos_now();
v___x_1002_ = lean_float_of_nat(v___y_997_);
v___x_1003_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1004_ = lean_float_div(v___x_1002_, v___x_1003_);
v___x_1005_ = lean_float_of_nat(v___x_1001_);
v___x_1006_ = lean_float_div(v___x_1005_, v___x_1003_);
v___x_1007_ = lean_box_float(v___x_1004_);
v___x_1008_ = lean_box_float(v___x_1006_);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_a_1000_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
lean_inc_ref(v___y_999_);
v___x_1011_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_995_, v___y_999_, v___y_996_, v___y_994_, v___y_998_, v___y_993_, v___x_1010_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1011_;
}
v___jp_1012_:
{
lean_object* v___x_1020_; lean_object* v_a_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1020_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_973_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref(v___x_1020_);
v___x_1022_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1023_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v___y_1018_, v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_io_mono_nanos_now();
lean_inc(v_trace_964_);
v___x_1025_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___y_1015_, v___y_1017_, v_acc_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 1);
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
v___y_993_ = v___y_1014_;
v___y_994_ = v___y_1013_;
v___y_995_ = v___y_1016_;
v___y_996_ = v___y_1018_;
v___y_997_ = v___x_1024_;
v___y_998_ = v_a_1021_;
v___y_999_ = v___y_1019_;
v_a_1000_ = v___x_1031_;
goto v___jp_992_;
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
v_a_1034_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1025_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1025_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 0);
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
v___y_993_ = v___y_1014_;
v___y_994_ = v___y_1013_;
v___y_995_ = v___y_1016_;
v___y_996_ = v___y_1018_;
v___y_997_ = v___x_1024_;
v___y_998_ = v_a_1021_;
v___y_999_ = v___y_1019_;
v_a_1000_ = v___x_1039_;
goto v___jp_992_;
}
}
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_io_get_num_heartbeats();
lean_inc(v_trace_964_);
v___x_1043_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_963_, v_trace_964_, v_next_965_, v_goals_966_, v___y_1015_, v___y_1017_, v_acc_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 1);
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
v___y_976_ = v___y_1014_;
v___y_977_ = v___y_1013_;
v___y_978_ = v___x_1042_;
v___y_979_ = v___y_1016_;
v___y_980_ = v___y_1018_;
v___y_981_ = v_a_1021_;
v___y_982_ = v___y_1019_;
v_a_983_ = v___x_1049_;
goto v___jp_975_;
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1043_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1043_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 0);
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
v___y_976_ = v___y_1014_;
v___y_977_ = v___y_1013_;
v___y_978_ = v___x_1042_;
v___y_979_ = v___y_1016_;
v___y_980_ = v___y_1018_;
v___y_981_ = v_a_1021_;
v___y_982_ = v___y_1019_;
v_a_983_ = v___x_1057_;
goto v___jp_975_;
}
}
}
}
}
v___jp_1060_:
{
lean_object* v___x_1069_; double v___x_1070_; double v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1069_ = lean_io_get_num_heartbeats();
v___x_1070_ = lean_float_of_nat(v___y_1065_);
v___x_1071_ = lean_float_of_nat(v___x_1069_);
v___x_1072_ = lean_box_float(v___x_1070_);
v___x_1073_ = lean_box_float(v___x_1071_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_a_1068_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
lean_inc_ref(v___y_1061_);
v___x_1076_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1064_, v___y_1061_, v___y_1062_, v___y_1067_, v___y_1063_, v___y_1066_, v___x_1075_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1076_;
}
v___jp_1077_:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_a_1085_);
v___y_1061_ = v___y_1078_;
v___y_1062_ = v___y_1079_;
v___y_1063_ = v___y_1081_;
v___y_1064_ = v___y_1080_;
v___y_1065_ = v___y_1082_;
v___y_1066_ = v___y_1083_;
v___y_1067_ = v___y_1084_;
v_a_1068_ = v___x_1086_;
goto v___jp_1060_;
}
v___jp_1087_:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v_a_1095_);
v___y_1061_ = v___y_1088_;
v___y_1062_ = v___y_1089_;
v___y_1063_ = v___y_1091_;
v___y_1064_ = v___y_1090_;
v___y_1065_ = v___y_1092_;
v___y_1066_ = v___y_1093_;
v___y_1067_ = v___y_1094_;
v_a_1068_ = v___x_1096_;
goto v___jp_1060_;
}
v___jp_1097_:
{
if (lean_obj_tag(v___y_1105_) == 0)
{
lean_object* v_a_1106_; 
v_a_1106_ = lean_ctor_get(v___y_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___y_1105_, 1);
v___y_1088_ = v___y_1098_;
v___y_1089_ = v___y_1099_;
v___y_1090_ = v___y_1101_;
v___y_1091_ = v___y_1100_;
v___y_1092_ = v___y_1102_;
v___y_1093_ = v___y_1103_;
v___y_1094_ = v___y_1104_;
v_a_1095_ = v_a_1106_;
goto v___jp_1087_;
}
else
{
lean_object* v_a_1107_; 
v_a_1107_ = lean_ctor_get(v___y_1105_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___y_1105_, 1);
v___y_1078_ = v___y_1098_;
v___y_1079_ = v___y_1099_;
v___y_1080_ = v___y_1101_;
v___y_1081_ = v___y_1100_;
v___y_1082_ = v___y_1102_;
v___y_1083_ = v___y_1103_;
v___y_1084_ = v___y_1104_;
v_a_1085_ = v_a_1107_;
goto v___jp_1077_;
}
}
v___jp_1108_:
{
lean_object* v___x_1117_; double v___x_1118_; double v___x_1119_; double v___x_1120_; double v___x_1121_; double v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1117_ = lean_io_mono_nanos_now();
v___x_1118_ = lean_float_of_nat(v___y_1109_);
v___x_1119_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_1120_ = lean_float_div(v___x_1118_, v___x_1119_);
v___x_1121_ = lean_float_of_nat(v___x_1117_);
v___x_1122_ = lean_float_div(v___x_1121_, v___x_1119_);
v___x_1123_ = lean_box_float(v___x_1120_);
v___x_1124_ = lean_box_float(v___x_1122_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_a_1116_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
lean_inc_ref(v___y_1110_);
v___x_1127_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_964_, v___y_1113_, v___y_1110_, v___y_1111_, v___y_1115_, v___y_1112_, v___y_1114_, v___x_1126_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v___x_1127_;
}
v___jp_1128_:
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_a_1136_);
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___y_1130_;
v___y_1111_ = v___y_1131_;
v___y_1112_ = v___y_1133_;
v___y_1113_ = v___y_1132_;
v___y_1114_ = v___y_1134_;
v___y_1115_ = v___y_1135_;
v_a_1116_ = v___x_1137_;
goto v___jp_1108_;
}
v___jp_1138_:
{
lean_object* v___x_1147_; 
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_a_1146_);
v___y_1109_ = v___y_1139_;
v___y_1110_ = v___y_1140_;
v___y_1111_ = v___y_1141_;
v___y_1112_ = v___y_1143_;
v___y_1113_ = v___y_1142_;
v___y_1114_ = v___y_1144_;
v___y_1115_ = v___y_1145_;
v_a_1116_ = v___x_1147_;
goto v___jp_1108_;
}
v___jp_1148_:
{
if (lean_obj_tag(v___y_1156_) == 0)
{
lean_object* v_a_1157_; 
v_a_1157_ = lean_ctor_get(v___y_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___y_1156_, 1);
v___y_1139_ = v___y_1149_;
v___y_1140_ = v___y_1150_;
v___y_1141_ = v___y_1151_;
v___y_1142_ = v___y_1153_;
v___y_1143_ = v___y_1152_;
v___y_1144_ = v___y_1154_;
v___y_1145_ = v___y_1155_;
v_a_1146_ = v_a_1157_;
goto v___jp_1138_;
}
else
{
lean_object* v_a_1158_; 
v_a_1158_ = lean_ctor_get(v___y_1156_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___y_1156_, 1);
v___y_1129_ = v___y_1149_;
v___y_1130_ = v___y_1150_;
v___y_1131_ = v___y_1151_;
v___y_1132_ = v___y_1153_;
v___y_1133_ = v___y_1152_;
v___y_1134_ = v___y_1154_;
v___y_1135_ = v___y_1155_;
v_a_1136_ = v_a_1158_;
goto v___jp_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* v_cfg_2054_, lean_object* v_trace_2055_, lean_object* v_next_2056_, lean_object* v_goals_2057_, lean_object* v_n_2058_, lean_object* v_curr_2059_, lean_object* v_acc_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2054_, v_trace_2055_, v_next_2056_, v_goals_2057_, v_n_2058_, v_curr_2059_, v_acc_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__8(lean_object* v_tail_2067_, lean_object* v_cfg_2068_, lean_object* v_trace_2069_, lean_object* v_next_2070_, lean_object* v_goals_2071_, lean_object* v_n_2072_, lean_object* v_acc_2073_, lean_object* v_r_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = l_List_appendTR___redArg(v_r_2074_, v_tail_2067_);
v___x_2081_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(v___x_2081_, 0, v_cfg_2068_);
lean_closure_set(v___x_2081_, 1, v_trace_2069_);
lean_closure_set(v___x_2081_, 2, v_next_2070_);
lean_closure_set(v___x_2081_, 3, v_goals_2071_);
lean_closure_set(v___x_2081_, 4, v_n_2072_);
lean_closure_set(v___x_2081_, 5, v___x_2080_);
lean_closure_set(v___x_2081_, 6, v_acc_2073_);
v___x_2082_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(v___x_2081_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* v_00_u03b1_2083_, lean_object* v_msg_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v_msg_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* v_00_u03b1_2091_, lean_object* v_msg_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(v_00_u03b1_2091_, v_msg_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(lean_object* v_00_u03b1_2099_, lean_object* v_x_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___redArg(v_x_2100_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2107_, lean_object* v_x_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3_spec__4(v_00_u03b1_2107_, v_x_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* v_mvarId_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_mvarId_2115_, v___y_2117_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* v_mvarId_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(v_mvarId_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v_mvarId_2122_);
return v_res_2128_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(lean_object* v_00_u03b2_2129_, lean_object* v_x_2130_, lean_object* v_x_2131_){
_start:
{
uint8_t v___x_2132_; 
v___x_2132_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___redArg(v_x_2130_, v_x_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10___boxed(lean_object* v_00_u03b2_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
uint8_t v_res_2136_; lean_object* v_r_2137_; 
v_res_2136_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10(v_00_u03b2_2133_, v_x_2134_, v_x_2135_);
lean_dec(v_x_2135_);
lean_dec_ref(v_x_2134_);
v_r_2137_ = lean_box(v_res_2136_);
return v_r_2137_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_2138_, lean_object* v_x_2139_, size_t v_x_2140_, lean_object* v_x_2141_){
_start:
{
uint8_t v___x_2142_; 
v___x_2142_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___redArg(v_x_2139_, v_x_2140_, v_x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12___boxed(lean_object* v_00_u03b2_2143_, lean_object* v_x_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_){
_start:
{
size_t v_x_76631__boxed_2147_; uint8_t v_res_2148_; lean_object* v_r_2149_; 
v_x_76631__boxed_2147_ = lean_unbox_usize(v_x_2145_);
lean_dec(v_x_2145_);
v_res_2148_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12(v_00_u03b2_2143_, v_x_2144_, v_x_76631__boxed_2147_, v_x_2146_);
lean_dec(v_x_2146_);
lean_dec_ref(v_x_2144_);
v_r_2149_ = lean_box(v_res_2148_);
return v_r_2149_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(lean_object* v_00_u03b2_2150_, lean_object* v_keys_2151_, lean_object* v_vals_2152_, lean_object* v_heq_2153_, lean_object* v_i_2154_, lean_object* v_k_2155_){
_start:
{
uint8_t v___x_2156_; 
v___x_2156_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___redArg(v_keys_2151_, v_i_2154_, v_k_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15___boxed(lean_object* v_00_u03b2_2157_, lean_object* v_keys_2158_, lean_object* v_vals_2159_, lean_object* v_heq_2160_, lean_object* v_i_2161_, lean_object* v_k_2162_){
_start:
{
uint8_t v_res_2163_; lean_object* v_r_2164_; 
v_res_2163_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6_spec__10_spec__12_spec__15(v_00_u03b2_2157_, v_keys_2158_, v_vals_2159_, v_heq_2160_, v_i_2161_, v_k_2162_);
lean_dec(v_k_2162_);
lean_dec_ref(v_vals_2159_);
lean_dec_ref(v_keys_2158_);
v_r_2164_ = lean_box(v_res_2163_);
return v_r_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* v_n_2165_, lean_object* v_h__1_2166_, lean_object* v_h__2_2167_){
_start:
{
lean_object* v_zero_2168_; uint8_t v_isZero_2169_; 
v_zero_2168_ = lean_unsigned_to_nat(0u);
v_isZero_2169_ = lean_nat_dec_eq(v_n_2165_, v_zero_2168_);
if (v_isZero_2169_ == 1)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec(v_h__2_2167_);
v___x_2170_ = lean_box(0);
v___x_2171_ = lean_apply_1(v_h__1_2166_, v___x_2170_);
return v___x_2171_;
}
else
{
lean_object* v_one_2172_; lean_object* v_n_2173_; lean_object* v___x_2174_; 
lean_dec(v_h__1_2166_);
v_one_2172_ = lean_unsigned_to_nat(1u);
v_n_2173_ = lean_nat_sub(v_n_2165_, v_one_2172_);
v___x_2174_ = lean_apply_1(v_h__2_2167_, v_n_2173_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* v_n_2175_, lean_object* v_h__1_2176_, lean_object* v_h__2_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(v_n_2175_, v_h__1_2176_, v_h__2_2177_);
lean_dec(v_n_2175_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* v_motive_2179_, lean_object* v_n_2180_, lean_object* v_h__1_2181_, lean_object* v_h__2_2182_){
_start:
{
lean_object* v_zero_2183_; uint8_t v_isZero_2184_; 
v_zero_2183_ = lean_unsigned_to_nat(0u);
v_isZero_2184_ = lean_nat_dec_eq(v_n_2180_, v_zero_2183_);
if (v_isZero_2184_ == 1)
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec(v_h__2_2182_);
v___x_2185_ = lean_box(0);
v___x_2186_ = lean_apply_1(v_h__1_2181_, v___x_2185_);
return v___x_2186_;
}
else
{
lean_object* v_one_2187_; lean_object* v_n_2188_; lean_object* v___x_2189_; 
lean_dec(v_h__1_2181_);
v_one_2187_ = lean_unsigned_to_nat(1u);
v_n_2188_ = lean_nat_sub(v_n_2180_, v_one_2187_);
v___x_2189_ = lean_apply_1(v_h__2_2182_, v_n_2188_);
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* v_motive_2190_, lean_object* v_n_2191_, lean_object* v_h__1_2192_, lean_object* v_h__2_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(v_motive_2190_, v_n_2191_, v_h__1_2192_, v_h__2_2193_);
lean_dec(v_n_2191_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* v_procResult_x3f_2195_, lean_object* v_h__1_2196_, lean_object* v_h__2_2197_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2195_) == 0)
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec(v_h__1_2196_);
v___x_2198_ = lean_box(0);
v___x_2199_ = lean_apply_1(v_h__2_2197_, v___x_2198_);
return v___x_2199_;
}
else
{
lean_object* v_val_2200_; lean_object* v___x_2201_; 
lean_dec(v_h__2_2197_);
v_val_2200_ = lean_ctor_get(v_procResult_x3f_2195_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v_procResult_x3f_2195_, 1);
v___x_2201_ = lean_apply_1(v_h__1_2196_, v_val_2200_);
return v___x_2201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* v_motive_2202_, lean_object* v_procResult_x3f_2203_, lean_object* v_h__1_2204_, lean_object* v_h__2_2205_){
_start:
{
if (lean_obj_tag(v_procResult_x3f_2203_) == 0)
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec(v_h__1_2204_);
v___x_2206_ = lean_box(0);
v___x_2207_ = lean_apply_1(v_h__2_2205_, v___x_2206_);
return v___x_2207_;
}
else
{
lean_object* v_val_2208_; lean_object* v___x_2209_; 
lean_dec(v_h__2_2205_);
v_val_2208_ = lean_ctor_get(v_procResult_x3f_2203_, 0);
lean_inc(v_val_2208_);
lean_dec_ref_known(v_procResult_x3f_2203_, 1);
v___x_2209_ = lean_apply_1(v_h__1_2204_, v_val_2208_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* v_curr_2210_, lean_object* v_h__1_2211_, lean_object* v_h__2_2212_){
_start:
{
if (lean_obj_tag(v_curr_2210_) == 0)
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec(v_h__2_2212_);
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_apply_1(v_h__1_2211_, v___x_2213_);
return v___x_2214_;
}
else
{
lean_object* v_head_2215_; lean_object* v_tail_2216_; lean_object* v___x_2217_; 
lean_dec(v_h__1_2211_);
v_head_2215_ = lean_ctor_get(v_curr_2210_, 0);
lean_inc(v_head_2215_);
v_tail_2216_ = lean_ctor_get(v_curr_2210_, 1);
lean_inc(v_tail_2216_);
lean_dec_ref_known(v_curr_2210_, 2);
v___x_2217_ = lean_apply_2(v_h__2_2212_, v_head_2215_, v_tail_2216_);
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* v_motive_2218_, lean_object* v_curr_2219_, lean_object* v_h__1_2220_, lean_object* v_h__2_2221_){
_start:
{
if (lean_obj_tag(v_curr_2219_) == 0)
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec(v_h__2_2221_);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_apply_1(v_h__1_2220_, v___x_2222_);
return v___x_2223_;
}
else
{
lean_object* v_head_2224_; lean_object* v_tail_2225_; lean_object* v___x_2226_; 
lean_dec(v_h__1_2220_);
v_head_2224_ = lean_ctor_get(v_curr_2219_, 0);
lean_inc(v_head_2224_);
v_tail_2225_ = lean_ctor_get(v_curr_2219_, 1);
lean_inc(v_tail_2225_);
lean_dec_ref_known(v_curr_2219_, 2);
v___x_2226_ = lean_apply_2(v_h__2_2221_, v_head_2224_, v_tail_2225_);
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* v_____do__lift_2227_, lean_object* v_h__1_2228_, lean_object* v_h__2_2229_){
_start:
{
if (lean_obj_tag(v_____do__lift_2227_) == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v_h__2_2229_);
v___x_2230_ = lean_box(0);
v___x_2231_ = lean_apply_1(v_h__1_2228_, v___x_2230_);
return v___x_2231_;
}
else
{
lean_object* v_val_2232_; lean_object* v___x_2233_; 
lean_dec(v_h__1_2228_);
v_val_2232_ = lean_ctor_get(v_____do__lift_2227_, 0);
lean_inc(v_val_2232_);
lean_dec_ref_known(v_____do__lift_2227_, 1);
v___x_2233_ = lean_apply_1(v_h__2_2229_, v_val_2232_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* v_motive_2234_, lean_object* v_____do__lift_2235_, lean_object* v_h__1_2236_, lean_object* v_h__2_2237_){
_start:
{
if (lean_obj_tag(v_____do__lift_2235_) == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec(v_h__2_2237_);
v___x_2238_ = lean_box(0);
v___x_2239_ = lean_apply_1(v_h__1_2236_, v___x_2238_);
return v___x_2239_;
}
else
{
lean_object* v_val_2240_; lean_object* v___x_2241_; 
lean_dec(v_h__1_2236_);
v_val_2240_ = lean_ctor_get(v_____do__lift_2235_, 0);
lean_inc(v_val_2240_);
lean_dec_ref_known(v_____do__lift_2235_, 1);
v___x_2241_ = lean_apply_1(v_h__2_2237_, v_val_2240_);
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* v_cfg_2242_, lean_object* v_trace_2243_, lean_object* v_next_2244_, lean_object* v_orig_2245_, lean_object* v_g_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_maxDepth_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_maxDepth_2252_ = lean_ctor_get(v_cfg_2242_, 0);
lean_inc(v_maxDepth_2252_);
v___x_2253_ = lean_box(0);
v___x_2254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2254_, 0, v_g_2246_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2242_, v_trace_2243_, v_next_2244_, v_orig_2245_, v_maxDepth_2252_, v___x_2254_, v___x_2253_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* v_cfg_2256_, lean_object* v_trace_2257_, lean_object* v_next_2258_, lean_object* v_orig_2259_, lean_object* v_g_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(v_cfg_2256_, v_trace_2257_, v_next_2258_, v_orig_2259_, v_g_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
if (lean_obj_tag(v_a_2267_) == 0)
{
lean_object* v___x_2269_; 
v___x_2269_ = l_List_reverse___redArg(v_a_2268_);
return v___x_2269_;
}
else
{
lean_object* v_head_2270_; lean_object* v_tail_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2280_; 
v_head_2270_ = lean_ctor_get(v_a_2267_, 0);
v_tail_2271_ = lean_ctor_get(v_a_2267_, 1);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_a_2267_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2273_ = v_a_2267_;
v_isShared_2274_ = v_isSharedCheck_2280_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_tail_2271_);
lean_inc(v_head_2270_);
lean_dec(v_a_2267_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2280_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2275_ = l_Lean_MessageData_ofFormat(v_head_2270_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 1, v_a_2268_);
lean_ctor_set(v___x_2273_, 0, v___x_2275_);
v___x_2277_ = v___x_2273_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2275_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_a_2268_);
v___x_2277_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
v_a_2267_ = v_tail_2271_;
v_a_2268_ = v___x_2277_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
v___x_2283_ = l_Lean_stringToMessageData(v___x_2282_);
return v___x_2283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
v___x_2286_ = l_Lean_stringToMessageData(v___x_2285_);
return v___x_2286_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
v___x_2289_ = l_Lean_stringToMessageData(v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* v_fst_2290_, lean_object* v_snd_2291_, lean_object* v_x_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2290_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2300_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref_known(v___x_2298_, 1);
v___x_2300_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_snd_2291_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2320_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2320_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2320_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2305_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
v___x_2306_ = lean_box(0);
v___x_2307_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2299_, v___x_2306_);
v___x_2308_ = l_Lean_MessageData_ofList(v___x_2307_);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2305_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
v___x_2313_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2301_, v___x_2306_);
v___x_2314_ = l_Lean_MessageData_ofList(v___x_2313_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2312_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2311_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2316_);
v___x_2318_ = v___x_2303_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_a_2299_);
v_a_2321_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2300_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2300_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec(v_snd_2291_);
v_a_2329_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2298_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2298_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
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
return v___x_2334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* v_fst_2337_, lean_object* v_snd_2338_, lean_object* v_x_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(v_fst_2337_, v_snd_2338_, v_x_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec_ref(v_x_2339_);
return v_res_2345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
v___x_2348_ = l_Lean_stringToMessageData(v___x_2347_);
return v___x_2348_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
v___x_2351_ = l_Lean_stringToMessageData(v___x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* v_fst_2352_, lean_object* v___x_2353_, lean_object* v_x_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v_fst_2352_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2362_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2362_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(v___x_2353_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2380_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2380_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2380_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2367_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
v___x_2368_ = lean_box(0);
v___x_2369_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2361_, v___x_2368_);
v___x_2370_ = l_Lean_MessageData_ofList(v___x_2369_);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2367_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(v_a_2363_, v___x_2368_);
v___x_2375_ = l_Lean_MessageData_ofList(v___x_2374_);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2373_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2376_);
v___x_2378_ = v___x_2365_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v_a_2361_);
v_a_2381_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2362_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2362_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v___x_2353_);
v_a_2389_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2360_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2360_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* v_fst_2397_, lean_object* v___x_2398_, lean_object* v_x_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(v_fst_2397_, v___x_2398_, v_x_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec_ref(v_x_2399_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t v___x_2406_, lean_object* v_x_2407_, lean_object* v_x_2408_, lean_object* v___y_2409_){
_start:
{
if (lean_obj_tag(v_x_2407_) == 0)
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2411_, 0, v_x_2408_);
return v___x_2411_;
}
else
{
lean_object* v_head_2412_; lean_object* v_tail_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2426_; 
v_head_2412_ = lean_ctor_get(v_x_2407_, 0);
v_tail_2413_ = lean_ctor_get(v_x_2407_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_x_2407_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2415_ = v_x_2407_;
v_isShared_2416_ = v_isSharedCheck_2426_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_tail_2413_);
lean_inc(v_head_2412_);
lean_dec(v_x_2407_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2426_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2422_; lean_object* v_a_2423_; uint8_t v___x_2424_; 
v___x_2422_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2412_, v___y_2409_);
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref(v___x_2422_);
v___x_2424_ = lean_unbox(v_a_2423_);
lean_dec(v_a_2423_);
if (v___x_2424_ == 0)
{
goto v___jp_2417_;
}
else
{
if (v___x_2406_ == 0)
{
lean_del_object(v___x_2415_);
lean_dec(v_head_2412_);
v_x_2407_ = v_tail_2413_;
goto _start;
}
else
{
goto v___jp_2417_;
}
}
v___jp_2417_:
{
lean_object* v___x_2419_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 1, v_x_2408_);
v___x_2419_ = v___x_2415_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_head_2412_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_x_2408_);
v___x_2419_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
v_x_2407_ = v_tail_2413_;
v_x_2408_ = v___x_2419_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* v___x_2427_, lean_object* v_x_2428_, lean_object* v_x_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
uint8_t v___x_46397__boxed_2432_; lean_object* v_res_2433_; 
v___x_46397__boxed_2432_ = lean_unbox(v___x_2427_);
v_res_2433_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_46397__boxed_2432_, v_x_2428_, v_x_2429_, v___y_2430_);
lean_dec(v___y_2430_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
if (lean_obj_tag(v_a_2434_) == 0)
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_array_to_list(v_a_2435_);
return v___x_2436_;
}
else
{
lean_object* v_head_2437_; lean_object* v_tail_2438_; lean_object* v___x_2439_; 
v_head_2437_ = lean_ctor_get(v_a_2434_, 0);
lean_inc(v_head_2437_);
v_tail_2438_ = lean_ctor_get(v_a_2434_, 1);
lean_inc(v_tail_2438_);
lean_dec_ref_known(v_a_2434_, 2);
v___x_2439_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2435_, v_head_2437_);
v_a_2434_ = v_tail_2438_;
v_a_2435_ = v___x_2439_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* v_goals_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
if (lean_obj_tag(v_a_2442_) == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
lean_dec(v_goals_2441_);
v___x_2450_ = lean_array_to_list(v_a_2443_);
v___x_2451_ = lean_array_to_list(v_a_2444_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
return v___x_2453_;
}
else
{
lean_object* v_head_2454_; lean_object* v_tail_2455_; lean_object* v___x_2456_; 
v_head_2454_ = lean_ctor_get(v_a_2442_, 0);
lean_inc_n(v_head_2454_, 2);
v_tail_2455_ = lean_ctor_get(v_a_2442_, 1);
lean_inc(v_tail_2455_);
lean_dec_ref_known(v_a_2442_, 2);
lean_inc(v_goals_2441_);
v___x_2456_ = l_Lean_MVarId_isIndependentOf(v_goals_2441_, v_head_2454_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; uint8_t v___x_2458_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___x_2458_ = lean_unbox(v_a_2457_);
lean_dec(v_a_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_array_push(v_a_2444_, v_head_2454_);
v_a_2442_ = v_tail_2455_;
v_a_2444_ = v___x_2459_;
goto _start;
}
else
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_array_push(v_a_2443_, v_head_2454_);
v_a_2442_ = v_tail_2455_;
v_a_2443_ = v___x_2461_;
goto _start;
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_tail_2455_);
lean_dec(v_head_2454_);
lean_dec_ref(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_goals_2441_);
v_a_2463_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2456_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2456_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* v_goals_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
if (lean_obj_tag(v_a_2481_) == 0)
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_array_to_list(v_a_2482_);
return v___x_2483_;
}
else
{
lean_object* v_head_2484_; 
v_head_2484_ = lean_ctor_get(v_a_2481_, 0);
if (lean_obj_tag(v_head_2484_) == 0)
{
lean_object* v_tail_2485_; lean_object* v_val_2486_; lean_object* v___x_2487_; 
lean_inc_ref(v_head_2484_);
v_tail_2485_ = lean_ctor_get(v_a_2481_, 1);
lean_inc(v_tail_2485_);
lean_dec_ref_known(v_a_2481_, 2);
v_val_2486_ = lean_ctor_get(v_head_2484_, 0);
lean_inc(v_val_2486_);
lean_dec_ref_known(v_head_2484_, 1);
v___x_2487_ = lean_array_push(v_a_2482_, v_val_2486_);
v_a_2481_ = v_tail_2485_;
v_a_2482_ = v___x_2487_;
goto _start;
}
else
{
lean_object* v_tail_2489_; 
v_tail_2489_ = lean_ctor_get(v_a_2481_, 1);
lean_inc(v_tail_2489_);
lean_dec_ref_known(v_a_2481_, 2);
v_a_2481_ = v_tail_2489_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* v_f_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
if (lean_obj_tag(v_x_2492_) == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec_ref(v_f_2491_);
v___x_2499_ = l_List_reverse___redArg(v_x_2493_);
v___x_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
return v___x_2500_;
}
else
{
lean_object* v_head_2501_; lean_object* v_tail_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2548_; 
v_head_2501_ = lean_ctor_get(v_x_2492_, 0);
v_tail_2502_ = lean_ctor_get(v_x_2492_, 1);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_x_2492_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2504_ = v_x_2492_;
v_isShared_2505_ = v_isSharedCheck_2548_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_tail_2502_);
lean_inc(v_head_2501_);
lean_dec(v_x_2492_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2548_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v_a_2507_; lean_object* v___x_2512_; 
v___x_2512_ = l_Lean_Meta_saveState___redArg(v___y_2495_, v___y_2497_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2514_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
lean_inc_ref(v_f_2491_);
lean_inc(v___y_2497_);
lean_inc_ref(v___y_2496_);
lean_inc(v___y_2495_);
lean_inc_ref(v___y_2494_);
lean_inc(v_head_2501_);
v___x_2514_ = lean_apply_6(v_f_2491_, v_head_2501_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, lean_box(0));
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2516_; 
lean_dec(v_a_2513_);
lean_dec(v_head_2501_);
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_a_2515_);
v_a_2507_ = v___x_2516_;
goto v___jp_2506_;
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2539_; 
v_a_2517_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2519_ = v___x_2514_;
v_isShared_2520_ = v_isSharedCheck_2539_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2514_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2539_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
uint8_t v___x_2521_; 
v___x_2521_ = l_Lean_Exception_isInterrupt(v_a_2517_);
if (v___x_2521_ == 0)
{
uint8_t v___x_2522_; 
lean_inc(v_a_2517_);
v___x_2522_ = l_Lean_Exception_isRuntime(v_a_2517_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; 
lean_del_object(v___x_2519_);
lean_dec(v_a_2517_);
v___x_2523_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2513_, v___y_2495_, v___y_2497_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v___x_2524_; 
lean_dec_ref_known(v___x_2523_, 1);
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_head_2501_);
v_a_2507_ = v___x_2524_;
goto v___jp_2506_;
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_del_object(v___x_2504_);
lean_dec(v_tail_2502_);
lean_dec(v_head_2501_);
lean_dec(v_x_2493_);
lean_dec_ref(v_f_2491_);
v_a_2525_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2523_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2523_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
else
{
lean_object* v___x_2534_; 
lean_dec(v_a_2513_);
lean_del_object(v___x_2504_);
lean_dec(v_tail_2502_);
lean_dec(v_head_2501_);
lean_dec(v_x_2493_);
lean_dec_ref(v_f_2491_);
if (v_isShared_2520_ == 0)
{
v___x_2534_ = v___x_2519_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2517_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
else
{
lean_object* v___x_2537_; 
lean_dec(v_a_2513_);
lean_del_object(v___x_2504_);
lean_dec(v_tail_2502_);
lean_dec(v_head_2501_);
lean_dec(v_x_2493_);
lean_dec_ref(v_f_2491_);
if (v_isShared_2520_ == 0)
{
v___x_2537_ = v___x_2519_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2517_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_del_object(v___x_2504_);
lean_dec(v_tail_2502_);
lean_dec(v_head_2501_);
lean_dec(v_x_2493_);
lean_dec_ref(v_f_2491_);
v_a_2540_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2512_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2512_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
v___jp_2506_:
{
lean_object* v___x_2509_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 1, v_x_2493_);
lean_ctor_set(v___x_2504_, 0, v_a_2507_);
v___x_2509_ = v___x_2504_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2507_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_x_2493_);
v___x_2509_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
v_x_2492_ = v_tail_2502_;
v_x_2493_ = v___x_2509_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* v_f_2549_, lean_object* v_x_2550_, lean_object* v_x_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2549_, v_x_2550_, v_x_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
if (lean_obj_tag(v_a_2558_) == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_array_to_list(v_a_2559_);
return v___x_2560_;
}
else
{
lean_object* v_head_2561_; 
v_head_2561_ = lean_ctor_get(v_a_2558_, 0);
if (lean_obj_tag(v_head_2561_) == 1)
{
lean_object* v_tail_2562_; lean_object* v_val_2563_; lean_object* v___x_2564_; 
lean_inc_ref(v_head_2561_);
v_tail_2562_ = lean_ctor_get(v_a_2558_, 1);
lean_inc(v_tail_2562_);
lean_dec_ref_known(v_a_2558_, 2);
v_val_2563_ = lean_ctor_get(v_head_2561_, 0);
lean_inc(v_val_2563_);
lean_dec_ref_known(v_head_2561_, 1);
v___x_2564_ = lean_array_push(v_a_2559_, v_val_2563_);
v_a_2558_ = v_tail_2562_;
v_a_2559_ = v___x_2564_;
goto _start;
}
else
{
lean_object* v_tail_2566_; 
v_tail_2566_ = lean_ctor_get(v_a_2558_, 1);
lean_inc(v_tail_2566_);
lean_dec_ref_known(v_a_2558_, 2);
v_a_2558_ = v_tail_2566_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* v_L_2568_, lean_object* v_f_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = lean_box(0);
v___x_2576_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_2569_, v_L_2568_, v___x_2575_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2588_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2579_ = v___x_2576_;
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2581_ = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(v_a_2577_);
v___x_2582_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_2577_, v___x_2581_);
v___x_2583_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_2577_, v___x_2581_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2584_);
v___x_2586_ = v___x_2579_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
v_a_2589_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2576_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2576_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* v_L_2597_, lean_object* v_f_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_2597_, v_f_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t v___x_2605_, uint8_t v___x_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_, lean_object* v___y_2609_){
_start:
{
if (lean_obj_tag(v_x_2607_) == 0)
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_x_2608_);
return v___x_2611_;
}
else
{
lean_object* v_head_2612_; lean_object* v_tail_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2627_; 
v_head_2612_ = lean_ctor_get(v_x_2607_, 0);
v_tail_2613_ = lean_ctor_get(v_x_2607_, 1);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_x_2607_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2615_ = v_x_2607_;
v_isShared_2616_ = v_isSharedCheck_2627_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_tail_2613_);
lean_inc(v_head_2612_);
lean_dec(v_x_2607_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2627_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
uint8_t v_a_2618_; lean_object* v___x_2624_; lean_object* v_a_2625_; uint8_t v___x_2626_; 
v___x_2624_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___redArg(v_head_2612_, v___y_2609_);
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref(v___x_2624_);
v___x_2626_ = lean_unbox(v_a_2625_);
lean_dec(v_a_2625_);
if (v___x_2626_ == 0)
{
v_a_2618_ = v___x_2605_;
goto v___jp_2617_;
}
else
{
v_a_2618_ = v___x_2606_;
goto v___jp_2617_;
}
v___jp_2617_:
{
if (v_a_2618_ == 0)
{
lean_del_object(v___x_2615_);
lean_dec(v_head_2612_);
v_x_2607_ = v_tail_2613_;
goto _start;
}
else
{
lean_object* v___x_2621_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 1, v_x_2608_);
v___x_2621_ = v___x_2615_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_head_2612_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_x_2608_);
v___x_2621_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
v_x_2607_ = v_tail_2613_;
v_x_2608_ = v___x_2621_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* v___x_2628_, lean_object* v___x_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
uint8_t v___x_46749__boxed_2634_; uint8_t v___x_46750__boxed_2635_; lean_object* v_res_2636_; 
v___x_46749__boxed_2634_ = lean_unbox(v___x_2628_);
v___x_46750__boxed_2635_ = lean_unbox(v___x_2629_);
v_res_2636_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_46749__boxed_2634_, v___x_46750__boxed_2635_, v_x_2630_, v_x_2631_, v___y_2632_);
lean_dec(v___y_2632_);
return v_res_2636_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1));
v___x_2641_ = l_Lean_stringToMessageData(v___x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* v_cfg_2642_, lean_object* v_trace_2643_, lean_object* v_next_2644_, lean_object* v_orig_2645_, lean_object* v_goals_2646_, lean_object* v_remaining_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v___f_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_inc(v_orig_2645_);
lean_inc_ref(v_next_2644_);
lean_inc(v_trace_2643_);
lean_inc_ref(v_cfg_2642_);
v___f_2653_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2653_, 0, v_cfg_2642_);
lean_closure_set(v___f_2653_, 1, v_trace_2643_);
lean_closure_set(v___f_2653_, 2, v_next_2644_);
lean_closure_set(v___f_2653_, 3, v_orig_2645_);
v___x_2654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
lean_inc(v_remaining_2647_);
lean_inc(v_goals_2646_);
v___x_2655_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(v_goals_2646_, v_remaining_2647_, v___x_2654_, v___x_2654_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v_fst_2657_; lean_object* v_snd_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_3299_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v_fst_2657_ = lean_ctor_get(v_a_2656_, 0);
v_snd_2658_ = lean_ctor_get(v_a_2656_, 1);
v_isSharedCheck_3299_ = !lean_is_exclusive(v_a_2656_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_2660_ = v_a_2656_;
v_isShared_2661_ = v_isSharedCheck_3299_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2658_);
lean_inc(v_fst_2657_);
lean_dec(v_a_2656_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_3299_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
uint8_t v___x_2662_; 
v___x_2662_ = l_List_isEmpty___redArg(v_fst_2657_);
if (v___x_2662_ == 0)
{
lean_object* v_toCold_2663_; lean_object* v_options_2664_; uint8_t v_hasTrace_2665_; 
lean_dec(v_remaining_2647_);
v_toCold_2663_ = lean_ctor_get(v_a_2650_, 0);
v_options_2664_ = lean_ctor_get(v_toCold_2663_, 2);
v_hasTrace_2665_ = lean_ctor_get_uint8(v_options_2664_, sizeof(void*)*1);
if (v_hasTrace_2665_ == 0)
{
lean_object* v___x_2666_; 
lean_del_object(v___x_2660_);
v___x_2666_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2657_, v___f_2653_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2726_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2726_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2726_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v_fst_2671_; lean_object* v_snd_2672_; lean_object* v___x_2673_; lean_object* v_a_2675_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v_fst_2671_ = lean_ctor_get(v_a_2667_, 0);
lean_inc(v_fst_2671_);
v_snd_2672_ = lean_ctor_get(v_a_2667_, 1);
lean_inc(v_snd_2672_);
lean_dec(v_a_2667_);
v___x_2673_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_2672_, v___x_2654_);
v___x_2681_ = lean_box(0);
v___x_2682_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_2662_, v_goals_2646_, v___x_2681_, v_a_2649_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; uint8_t v_commitIndependentGoals_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v_commitIndependentGoals_2684_ = lean_ctor_get_uint8(v_cfg_2642_, sizeof(void*)*4);
v___x_2685_ = l_List_reverse___redArg(v_a_2683_);
lean_inc(v___x_2673_);
v___x_2686_ = l_List_appendTR___redArg(v___x_2685_, v___x_2673_);
if (v_commitIndependentGoals_2684_ == 0)
{
lean_del_object(v___x_2669_);
goto v___jp_2687_;
}
else
{
uint8_t v___x_2701_; 
v___x_2701_ = l_List_isEmpty___redArg(v___x_2673_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_Meta_saveState___redArg(v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
lean_inc(v_snd_2658_);
v___x_2704_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_2686_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; 
lean_dec(v_a_2703_);
lean_dec(v_snd_2658_);
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v_a_2675_ = v_a_2705_;
goto v___jp_2674_;
}
else
{
lean_object* v_a_2706_; uint8_t v___x_2707_; 
v_a_2706_ = lean_ctor_get(v___x_2704_, 0);
v___x_2707_ = l_Lean_Exception_isInterrupt(v_a_2706_);
if (v___x_2707_ == 0)
{
uint8_t v___x_2708_; 
lean_inc(v_a_2706_);
v___x_2708_ = l_Lean_Exception_isRuntime(v_a_2706_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; 
lean_dec_ref_known(v___x_2704_, 1);
v___x_2709_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2703_, v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_dec_ref_known(v___x_2709_, 1);
v_a_2675_ = v_snd_2658_;
goto v___jp_2674_;
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec(v___x_2673_);
lean_dec(v_fst_2671_);
lean_del_object(v___x_2669_);
lean_dec(v_snd_2658_);
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
else
{
lean_dec(v_a_2703_);
lean_dec(v___x_2673_);
lean_dec(v_fst_2671_);
lean_del_object(v___x_2669_);
lean_dec(v_snd_2658_);
return v___x_2704_;
}
}
else
{
lean_dec(v_a_2703_);
lean_dec(v___x_2673_);
lean_dec(v_fst_2671_);
lean_del_object(v___x_2669_);
lean_dec(v_snd_2658_);
return v___x_2704_;
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v___x_2686_);
lean_dec(v___x_2673_);
lean_dec(v_fst_2671_);
lean_del_object(v___x_2669_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec(v_trace_2643_);
lean_dec_ref(v_cfg_2642_);
v_a_2718_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2702_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2702_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_del_object(v___x_2669_);
goto v___jp_2687_;
}
}
v___jp_2687_:
{
uint8_t v___x_2688_; 
v___x_2688_ = l_List_isEmpty___redArg(v_fst_2671_);
lean_dec(v_fst_2671_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_dec(v___x_2686_);
lean_dec(v___x_2673_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec(v_trace_2643_);
lean_dec_ref(v_cfg_2642_);
v___x_2689_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_2690_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_2689_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v___x_2690_;
}
else
{
lean_object* v___x_2691_; 
v___x_2691_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_2686_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2700_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2694_ = v___x_2691_;
v_isShared_2695_ = v_isSharedCheck_2700_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2691_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2700_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = l_List_appendTR___redArg(v___x_2673_, v_a_2692_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2696_);
v___x_2698_ = v___x_2694_;
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
lean_dec(v___x_2673_);
return v___x_2691_;
}
}
}
}
else
{
lean_dec(v___x_2673_);
lean_dec(v_fst_2671_);
lean_del_object(v___x_2669_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec(v_trace_2643_);
lean_dec_ref(v_cfg_2642_);
return v___x_2682_;
}
v___jp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2676_ = l_List_appendTR___redArg(v___x_2673_, v_fst_2671_);
v___x_2677_ = l_List_appendTR___redArg(v___x_2676_, v_a_2675_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2677_);
v___x_2679_ = v___x_2669_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec(v_snd_2658_);
lean_dec(v_goals_2646_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec(v_trace_2643_);
lean_dec_ref(v_cfg_2642_);
v_a_2727_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2666_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2666_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2735_; lean_object* v___f_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; lean_object* v___y_2742_; lean_object* v___y_2743_; lean_object* v_a_2744_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v_a_2758_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v_a_2765_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v_a_2771_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2784_; lean_object* v___y_2785_; lean_object* v_a_2786_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; uint8_t v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v_a_2802_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; uint8_t v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v_a_2811_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; uint8_t v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; uint8_t v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v_a_2841_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; uint8_t v___y_2850_; lean_object* v___y_2851_; uint8_t v___y_2852_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v_a_2890_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v_a_2905_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v_a_2910_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v_a_2917_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; uint8_t v___y_2945_; lean_object* v_a_2946_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; uint8_t v___y_2964_; lean_object* v_a_2965_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; uint8_t v___y_2973_; lean_object* v_a_2974_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; uint8_t v___y_2984_; lean_object* v_a_2985_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; uint8_t v___y_2997_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; uint8_t v___y_3014_; 
v_inheritedTraceOptions_2735_ = lean_ctor_get(v_toCold_2663_, 11);
lean_inc(v_snd_2658_);
lean_inc(v_fst_2657_);
v___f_2736_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(v___f_2736_, 0, v_fst_2657_);
lean_closure_set(v___f_2736_, 1, v_snd_2658_);
v___x_2737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__9));
v___x_2738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__8));
lean_inc(v_trace_2643_);
v___x_2739_ = l_Lean_Name_append(v___x_2738_, v_trace_2643_);
v___x_2740_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2735_, v_options_2664_, v___x_2739_);
lean_dec(v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3105_ = l_Lean_trace_profiler;
v___x_3106_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2664_, v___x_3105_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; 
lean_dec_ref(v___f_2736_);
lean_del_object(v___x_2660_);
v___x_3107_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2657_, v___f_2653_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3287_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3287_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3287_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v_fst_3112_; lean_object* v_snd_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3286_; 
v_fst_3112_ = lean_ctor_get(v_a_3108_, 0);
v_snd_3113_ = lean_ctor_get(v_a_3108_, 1);
v_isSharedCheck_3286_ = !lean_is_exclusive(v_a_3108_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3115_ = v_a_3108_;
v_isShared_3116_ = v_isSharedCheck_3286_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_snd_3113_);
lean_inc(v_fst_3112_);
lean_dec(v_a_3108_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3286_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v_a_3119_; lean_object* v___x_3125_; 
v___x_3117_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3113_, v___x_2654_);
v___x_3125_ = lean_box(0);
if (v___x_2740_ == 0)
{
lean_object* v___x_3126_; 
lean_del_object(v___x_3115_);
v___x_3126_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2665_, v___x_2662_, v_goals_2646_, v___x_3125_, v_a_2649_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; uint8_t v_commitIndependentGoals_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref_known(v___x_3126_, 1);
v_commitIndependentGoals_3128_ = lean_ctor_get_uint8(v_cfg_2642_, sizeof(void*)*4);
v___x_3129_ = l_List_reverse___redArg(v_a_3127_);
lean_inc(v___x_3117_);
v___x_3130_ = l_List_appendTR___redArg(v___x_3129_, v___x_3117_);
if (v_commitIndependentGoals_3128_ == 0)
{
lean_del_object(v___x_3110_);
goto v___jp_3131_;
}
else
{
uint8_t v___x_3145_; 
v___x_3145_ = l_List_isEmpty___redArg(v___x_3117_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_Meta_saveState___redArg(v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3148_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3146_, 1);
lean_inc(v_snd_2658_);
v___x_3148_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_3130_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; 
lean_dec(v_a_3147_);
lean_dec(v_snd_2658_);
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3148_, 1);
v_a_3119_ = v_a_3149_;
goto v___jp_3118_;
}
else
{
lean_object* v_a_3150_; uint8_t v___x_3151_; 
v_a_3150_ = lean_ctor_get(v___x_3148_, 0);
v___x_3151_ = l_Lean_Exception_isInterrupt(v_a_3150_);
if (v___x_3151_ == 0)
{
uint8_t v___x_3152_; 
lean_inc(v_a_3150_);
v___x_3152_ = l_Lean_Exception_isRuntime(v_a_3150_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; 
lean_dec_ref_known(v___x_3148_, 1);
v___x_3153_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3147_, v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_dec_ref_known(v___x_3153_, 1);
v_a_3119_ = v_snd_2658_;
goto v___jp_3118_;
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_del_object(v___x_3110_);
lean_dec(v_snd_2658_);
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_dec(v_a_3147_);
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_del_object(v___x_3110_);
lean_dec(v_snd_2658_);
return v___x_3148_;
}
}
else
{
lean_dec(v_a_3147_);
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_del_object(v___x_3110_);
lean_dec(v_snd_2658_);
return v___x_3148_;
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v___x_3130_);
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_del_object(v___x_3110_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec(v_trace_2643_);
lean_dec_ref(v_cfg_2642_);
v_a_3162_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3146_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3146_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
lean_del_object(v___x_3110_);
goto v___jp_3131_;
}
}
v___jp_3131_:
{
uint8_t v___x_3132_; 
v___x_3132_ = l_List_isEmpty___redArg(v_fst_3112_);
lean_dec(v_fst_3112_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_dec(v___x_3130_);
lean_dec(v___x_3117_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec(v_trace_2643_);
lean_dec_ref(v_cfg_2642_);
v___x_3133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3134_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3133_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; 
v___x_3135_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_3130_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3144_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3144_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = l_List_appendTR___redArg(v___x_3117_, v_a_3136_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3140_);
v___x_3142_ = v___x_3138_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
else
{
lean_dec(v___x_3117_);
return v___x_3135_;
}
}
}
}
else
{
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_del_object(v___x_3110_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec(v_trace_2643_);
lean_dec_ref(v_cfg_2642_);
return v___x_3126_;
}
}
else
{
lean_object* v___f_3170_; lean_object* v___x_3171_; 
lean_del_object(v___x_3110_);
lean_inc(v___x_3117_);
lean_inc(v_fst_3112_);
v___f_3170_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3170_, 0, v_fst_3112_);
lean_closure_set(v___f_3170_, 1, v___x_3117_);
v___x_3171_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2651_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref_known(v___x_3171_, 1);
v___x_3173_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3174_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2664_, v___x_3173_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; lean_object* v_a_3177_; lean_object* v_a_3192_; lean_object* v_a_3195_; lean_object* v_a_3199_; lean_object* v___x_3201_; 
v___x_3175_ = lean_io_mono_nanos_now();
v___x_3201_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2665_, v___x_2662_, v_goals_2646_, v___x_3125_, v_a_2649_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; uint8_t v_commitIndependentGoals_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref_known(v___x_3201_, 1);
v_commitIndependentGoals_3203_ = lean_ctor_get_uint8(v_cfg_2642_, sizeof(void*)*4);
v___x_3204_ = l_List_reverse___redArg(v_a_3202_);
lean_inc(v___x_3117_);
v___x_3205_ = l_List_appendTR___redArg(v___x_3204_, v___x_3117_);
if (v_commitIndependentGoals_3203_ == 0)
{
goto v___jp_3206_;
}
else
{
uint8_t v___x_3216_; 
v___x_3216_ = l_List_isEmpty___redArg(v___x_3117_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_Meta_saveState___redArg(v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
lean_inc(v_snd_2658_);
lean_inc(v_trace_2643_);
v___x_3219_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_3205_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; 
lean_dec(v_a_3218_);
lean_dec(v_snd_2658_);
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v_a_3195_ = v_a_3220_;
goto v___jp_3194_;
}
else
{
lean_object* v_a_3221_; uint8_t v___x_3222_; 
v_a_3221_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3219_, 1);
v___x_3222_ = l_Lean_Exception_isInterrupt(v_a_3221_);
if (v___x_3222_ == 0)
{
uint8_t v___x_3223_; 
lean_inc(v_a_3221_);
v___x_3223_ = l_Lean_Exception_isRuntime(v_a_3221_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
lean_dec(v_a_3221_);
v___x_3224_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3218_, v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_dec_ref_known(v___x_3224_, 1);
v_a_3195_ = v_snd_2658_;
goto v___jp_3194_;
}
else
{
lean_object* v_a_3225_; 
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_dec(v_snd_2658_);
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v_a_3199_ = v_a_3225_;
goto v___jp_3198_;
}
}
else
{
lean_dec(v_a_3218_);
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_dec(v_snd_2658_);
v_a_3199_ = v_a_3221_;
goto v___jp_3198_;
}
}
else
{
lean_dec(v_a_3218_);
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_dec(v_snd_2658_);
v_a_3199_ = v_a_3221_;
goto v___jp_3198_;
}
}
}
else
{
lean_object* v_a_3226_; 
lean_dec(v___x_3205_);
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3226_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3217_, 1);
v_a_3199_ = v_a_3226_;
goto v___jp_3198_;
}
}
else
{
goto v___jp_3206_;
}
}
v___jp_3206_:
{
uint8_t v___x_3207_; 
v___x_3207_ = l_List_isEmpty___redArg(v_fst_3112_);
lean_dec(v_fst_3112_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_dec(v___x_3205_);
lean_dec(v___x_3117_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v___x_3208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3209_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3208_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v_a_3192_ = v_a_3210_;
goto v___jp_3191_;
}
else
{
lean_object* v_a_3211_; 
v_a_3211_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3209_, 1);
v_a_3199_ = v_a_3211_;
goto v___jp_3198_;
}
}
else
{
lean_object* v___x_3212_; 
lean_inc(v_trace_2643_);
v___x_3212_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_3205_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3214_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref_known(v___x_3212_, 1);
v___x_3214_ = l_List_appendTR___redArg(v___x_3117_, v_a_3213_);
v_a_3192_ = v___x_3214_;
goto v___jp_3191_;
}
else
{
lean_object* v_a_3215_; 
lean_dec(v___x_3117_);
v_a_3215_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v___x_3212_, 1);
v_a_3199_ = v_a_3215_;
goto v___jp_3198_;
}
}
}
}
else
{
lean_object* v_a_3227_; 
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3227_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3201_, 1);
v_a_3199_ = v_a_3227_;
goto v___jp_3198_;
}
v___jp_3176_:
{
lean_object* v___x_3178_; double v___x_3179_; double v___x_3180_; double v___x_3181_; double v___x_3182_; double v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3178_ = lean_io_mono_nanos_now();
v___x_3179_ = lean_float_of_nat(v___x_3175_);
v___x_3180_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_3181_ = lean_float_div(v___x_3179_, v___x_3180_);
v___x_3182_ = lean_float_of_nat(v___x_3178_);
v___x_3183_ = lean_float_div(v___x_3182_, v___x_3180_);
v___x_3184_ = lean_box_float(v___x_3181_);
v___x_3185_ = lean_box_float(v___x_3183_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 1, v___x_3185_);
lean_ctor_set(v___x_3115_, 0, v___x_3184_);
v___x_3187_ = v___x_3115_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3188_, 0, v_a_3177_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2643_, v_hasTrace_2665_, v___x_2737_, v_options_2664_, v___x_2740_, v_a_3172_, v___f_3170_, v___x_3188_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v___x_3189_;
}
}
v___jp_3191_:
{
lean_object* v___x_3193_; 
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v_a_3192_);
v_a_3177_ = v___x_3193_;
goto v___jp_3176_;
}
v___jp_3194_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3196_ = l_List_appendTR___redArg(v___x_3117_, v_fst_3112_);
v___x_3197_ = l_List_appendTR___redArg(v___x_3196_, v_a_3195_);
v_a_3192_ = v___x_3197_;
goto v___jp_3191_;
}
v___jp_3198_:
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v_a_3199_);
v_a_3177_ = v___x_3200_;
goto v___jp_3176_;
}
}
else
{
lean_object* v___x_3228_; lean_object* v_a_3230_; lean_object* v_a_3242_; lean_object* v_a_3245_; lean_object* v_a_3249_; lean_object* v___x_3251_; 
v___x_3228_ = lean_io_get_num_heartbeats();
v___x_3251_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2665_, v___x_2662_, v_goals_2646_, v___x_3125_, v_a_2649_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; uint8_t v_commitIndependentGoals_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v___x_3251_, 1);
v_commitIndependentGoals_3253_ = lean_ctor_get_uint8(v_cfg_2642_, sizeof(void*)*4);
v___x_3254_ = l_List_reverse___redArg(v_a_3252_);
lean_inc(v___x_3117_);
v___x_3255_ = l_List_appendTR___redArg(v___x_3254_, v___x_3117_);
if (v_commitIndependentGoals_3253_ == 0)
{
goto v___jp_3256_;
}
else
{
uint8_t v___x_3266_; 
v___x_3266_ = l_List_isEmpty___redArg(v___x_3117_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; 
v___x_3267_ = l_Lean_Meta_saveState___redArg(v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v___x_3269_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
lean_dec_ref_known(v___x_3267_, 1);
lean_inc(v_snd_2658_);
lean_inc(v_trace_2643_);
v___x_3269_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_3255_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v_a_3270_; 
lean_dec(v_a_3268_);
lean_dec(v_snd_2658_);
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3269_, 1);
v_a_3245_ = v_a_3270_;
goto v___jp_3244_;
}
else
{
lean_object* v_a_3271_; uint8_t v___x_3272_; 
v_a_3271_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3269_, 1);
v___x_3272_ = l_Lean_Exception_isInterrupt(v_a_3271_);
if (v___x_3272_ == 0)
{
uint8_t v___x_3273_; 
lean_inc(v_a_3271_);
v___x_3273_ = l_Lean_Exception_isRuntime(v_a_3271_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; 
lean_dec(v_a_3271_);
v___x_3274_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3268_, v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_dec_ref_known(v___x_3274_, 1);
v_a_3245_ = v_snd_2658_;
goto v___jp_3244_;
}
else
{
lean_object* v_a_3275_; 
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_dec(v_snd_2658_);
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v_a_3249_ = v_a_3275_;
goto v___jp_3248_;
}
}
else
{
lean_dec(v_a_3268_);
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_dec(v_snd_2658_);
v_a_3249_ = v_a_3271_;
goto v___jp_3248_;
}
}
else
{
lean_dec(v_a_3268_);
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_dec(v_snd_2658_);
v_a_3249_ = v_a_3271_;
goto v___jp_3248_;
}
}
}
else
{
lean_object* v_a_3276_; 
lean_dec(v___x_3255_);
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3276_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3267_, 1);
v_a_3249_ = v_a_3276_;
goto v___jp_3248_;
}
}
else
{
goto v___jp_3256_;
}
}
v___jp_3256_:
{
uint8_t v___x_3257_; 
v___x_3257_ = l_List_isEmpty___redArg(v_fst_3112_);
lean_dec(v_fst_3112_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
lean_dec(v___x_3255_);
lean_dec(v___x_3117_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v___x_3258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3259_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_3258_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v_a_3242_ = v_a_3260_;
goto v___jp_3241_;
}
else
{
lean_object* v_a_3261_; 
v_a_3261_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3259_, 1);
v_a_3249_ = v_a_3261_;
goto v___jp_3248_;
}
}
else
{
lean_object* v___x_3262_; 
lean_inc(v_trace_2643_);
v___x_3262_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_3255_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3264_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3264_ = l_List_appendTR___redArg(v___x_3117_, v_a_3263_);
v_a_3242_ = v___x_3264_;
goto v___jp_3241_;
}
else
{
lean_object* v_a_3265_; 
lean_dec(v___x_3117_);
v_a_3265_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v___x_3262_, 1);
v_a_3249_ = v_a_3265_;
goto v___jp_3248_;
}
}
}
}
else
{
lean_object* v_a_3277_; 
lean_dec(v___x_3117_);
lean_dec(v_fst_3112_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3277_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3251_, 1);
v_a_3249_ = v_a_3277_;
goto v___jp_3248_;
}
v___jp_3229_:
{
lean_object* v___x_3231_; double v___x_3232_; double v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3237_; 
v___x_3231_ = lean_io_get_num_heartbeats();
v___x_3232_ = lean_float_of_nat(v___x_3228_);
v___x_3233_ = lean_float_of_nat(v___x_3231_);
v___x_3234_ = lean_box_float(v___x_3232_);
v___x_3235_ = lean_box_float(v___x_3233_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 1, v___x_3235_);
lean_ctor_set(v___x_3115_, 0, v___x_3234_);
v___x_3237_ = v___x_3115_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v___x_3235_);
v___x_3237_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v_a_3230_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2643_, v_hasTrace_2665_, v___x_2737_, v_options_2664_, v___x_2740_, v_a_3172_, v___f_3170_, v___x_3238_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v___x_3239_;
}
}
v___jp_3241_:
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3243_, 0, v_a_3242_);
v_a_3230_ = v___x_3243_;
goto v___jp_3229_;
}
v___jp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = l_List_appendTR___redArg(v___x_3117_, v_fst_3112_);
v___x_3247_ = l_List_appendTR___redArg(v___x_3246_, v_a_3245_);
v_a_3242_ = v___x_3247_;
goto v___jp_3241_;
}
v___jp_3248_:
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v_a_3249_);
v_a_3230_ = v___x_3250_;
goto v___jp_3229_;
}
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec_ref(v___f_3170_);
lean_dec(v___x_3117_);
lean_del_object(v___x_3115_);
lean_dec(v_fst_3112_);
lean_dec(v_snd_2658_);
lean_dec(v_goals_2646_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec(v_trace_2643_);
lean_dec_ref(v_cfg_2642_);
v_a_3278_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3171_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3171_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
v___jp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3120_ = l_List_appendTR___redArg(v___x_3117_, v_fst_3112_);
v___x_3121_ = l_List_appendTR___redArg(v___x_3120_, v_a_3119_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3121_);
v___x_3123_ = v___x_3110_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec(v_snd_2658_);
lean_dec(v_goals_2646_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec(v_trace_2643_);
lean_dec_ref(v_cfg_2642_);
v_a_3288_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3107_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3107_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
else
{
goto v___jp_3036_;
}
}
else
{
goto v___jp_3036_;
}
v___jp_2741_:
{
lean_object* v___x_2745_; double v___x_2746_; double v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2745_ = lean_io_get_num_heartbeats();
v___x_2746_ = lean_float_of_nat(v___y_2742_);
v___x_2747_ = lean_float_of_nat(v___x_2745_);
v___x_2748_ = lean_box_float(v___x_2746_);
v___x_2749_ = lean_box_float(v___x_2747_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v___x_2749_);
lean_ctor_set(v___x_2660_, 0, v___x_2748_);
v___x_2751_ = v___x_2660_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2748_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v_a_2744_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2643_, v_hasTrace_2665_, v___x_2737_, v_options_2664_, v___x_2740_, v___y_2743_, v___f_2736_, v___x_2752_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v___x_2753_;
}
}
v___jp_2755_:
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2759_, 0, v_a_2758_);
v___y_2742_ = v___y_2756_;
v___y_2743_ = v___y_2757_;
v_a_2744_ = v___x_2759_;
goto v___jp_2741_;
}
v___jp_2760_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = l_List_appendTR___redArg(v___y_2761_, v___y_2764_);
v___x_2767_ = l_List_appendTR___redArg(v___x_2766_, v_a_2765_);
v___y_2756_ = v___y_2762_;
v___y_2757_ = v___y_2763_;
v_a_2758_ = v___x_2767_;
goto v___jp_2755_;
}
v___jp_2768_:
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_a_2771_);
v___y_2742_ = v___y_2769_;
v___y_2743_ = v___y_2770_;
v_a_2744_ = v___x_2772_;
goto v___jp_2741_;
}
v___jp_2773_:
{
if (lean_obj_tag(v___y_2776_) == 0)
{
lean_object* v_a_2777_; 
v_a_2777_ = lean_ctor_get(v___y_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___y_2776_, 1);
v___y_2756_ = v___y_2774_;
v___y_2757_ = v___y_2775_;
v_a_2758_ = v_a_2777_;
goto v___jp_2755_;
}
else
{
lean_object* v_a_2778_; 
v_a_2778_ = lean_ctor_get(v___y_2776_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___y_2776_, 1);
v___y_2769_ = v___y_2774_;
v___y_2770_ = v___y_2775_;
v_a_2771_ = v_a_2778_;
goto v___jp_2768_;
}
}
v___jp_2779_:
{
lean_object* v___x_2787_; double v___x_2788_; double v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2787_ = lean_io_get_num_heartbeats();
v___x_2788_ = lean_float_of_nat(v___y_2785_);
v___x_2789_ = lean_float_of_nat(v___x_2787_);
v___x_2790_ = lean_box_float(v___x_2788_);
v___x_2791_ = lean_box_float(v___x_2789_);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2790_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v_a_2786_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
lean_inc(v_trace_2643_);
v___x_2794_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2643_, v_hasTrace_2665_, v___x_2737_, v_options_2664_, v___y_2784_, v___y_2783_, v___y_2782_, v___x_2793_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
v___y_2774_ = v___y_2780_;
v___y_2775_ = v___y_2781_;
v___y_2776_ = v___x_2794_;
goto v___jp_2773_;
}
v___jp_2795_:
{
lean_object* v___x_2803_; 
v___x_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2803_, 0, v_a_2802_);
v___y_2780_ = v___y_2796_;
v___y_2781_ = v___y_2797_;
v___y_2782_ = v___y_2798_;
v___y_2783_ = v___y_2800_;
v___y_2784_ = v___y_2799_;
v___y_2785_ = v___y_2801_;
v_a_2786_ = v___x_2803_;
goto v___jp_2779_;
}
v___jp_2804_:
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2812_, 0, v_a_2811_);
v___y_2780_ = v___y_2805_;
v___y_2781_ = v___y_2806_;
v___y_2782_ = v___y_2807_;
v___y_2783_ = v___y_2809_;
v___y_2784_ = v___y_2808_;
v___y_2785_ = v___y_2810_;
v_a_2786_ = v___x_2812_;
goto v___jp_2779_;
}
v___jp_2813_:
{
uint8_t v___x_2823_; 
v___x_2823_ = l_List_isEmpty___redArg(v___y_2821_);
lean_dec(v___y_2821_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v___x_2824_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_2825_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_2824_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___y_2805_ = v___y_2816_;
v___y_2806_ = v___y_2817_;
v___y_2807_ = v___y_2818_;
v___y_2808_ = v___y_2820_;
v___y_2809_ = v___y_2819_;
v___y_2810_ = v___y_2822_;
v_a_2811_ = v_a_2826_;
goto v___jp_2804_;
}
else
{
lean_object* v_a_2827_; 
v_a_2827_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2825_, 1);
v___y_2796_ = v___y_2816_;
v___y_2797_ = v___y_2817_;
v___y_2798_ = v___y_2818_;
v___y_2799_ = v___y_2820_;
v___y_2800_ = v___y_2819_;
v___y_2801_ = v___y_2822_;
v_a_2802_ = v_a_2827_;
goto v___jp_2795_;
}
}
else
{
lean_object* v___x_2828_; 
lean_inc(v_trace_2643_);
v___x_2828_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___y_2815_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2828_, 1);
v___x_2830_ = l_List_appendTR___redArg(v___y_2814_, v_a_2829_);
v___y_2805_ = v___y_2816_;
v___y_2806_ = v___y_2817_;
v___y_2807_ = v___y_2818_;
v___y_2808_ = v___y_2820_;
v___y_2809_ = v___y_2819_;
v___y_2810_ = v___y_2822_;
v_a_2811_ = v___x_2830_;
goto v___jp_2804_;
}
else
{
lean_object* v_a_2831_; 
lean_dec(v___y_2814_);
v_a_2831_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2828_, 1);
v___y_2796_ = v___y_2816_;
v___y_2797_ = v___y_2817_;
v___y_2798_ = v___y_2818_;
v___y_2799_ = v___y_2820_;
v___y_2800_ = v___y_2819_;
v___y_2801_ = v___y_2822_;
v_a_2802_ = v_a_2831_;
goto v___jp_2795_;
}
}
}
v___jp_2832_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = l_List_appendTR___redArg(v___y_2833_, v___y_2839_);
v___x_2843_ = l_List_appendTR___redArg(v___x_2842_, v_a_2841_);
v___y_2805_ = v___y_2834_;
v___y_2806_ = v___y_2835_;
v___y_2807_ = v___y_2836_;
v___y_2808_ = v___y_2838_;
v___y_2809_ = v___y_2837_;
v___y_2810_ = v___y_2840_;
v_a_2811_ = v___x_2843_;
goto v___jp_2804_;
}
v___jp_2844_:
{
lean_object* v___x_2853_; 
v___x_2853_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2651_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v___x_2855_ = lean_io_get_num_heartbeats();
v___x_2856_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___y_2852_, v___x_2662_, v_goals_2646_, v___y_2846_, v_a_2649_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; uint8_t v_commitIndependentGoals_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2856_, 1);
v_commitIndependentGoals_2858_ = lean_ctor_get_uint8(v_cfg_2642_, sizeof(void*)*4);
v___x_2859_ = l_List_reverse___redArg(v_a_2857_);
lean_inc(v___y_2845_);
v___x_2860_ = l_List_appendTR___redArg(v___x_2859_, v___y_2845_);
if (v_commitIndependentGoals_2858_ == 0)
{
v___y_2814_ = v___y_2845_;
v___y_2815_ = v___x_2860_;
v___y_2816_ = v___y_2847_;
v___y_2817_ = v___y_2848_;
v___y_2818_ = v___y_2849_;
v___y_2819_ = v_a_2854_;
v___y_2820_ = v___y_2850_;
v___y_2821_ = v___y_2851_;
v___y_2822_ = v___x_2855_;
goto v___jp_2813_;
}
else
{
uint8_t v___x_2861_; 
v___x_2861_ = l_List_isEmpty___redArg(v___y_2845_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
v___x_2862_ = l_Lean_Meta_saveState___redArg(v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2864_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
lean_inc(v_snd_2658_);
lean_inc(v_trace_2643_);
v___x_2864_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_2860_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; 
lean_dec(v_a_2863_);
lean_dec(v_snd_2658_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___y_2833_ = v___y_2845_;
v___y_2834_ = v___y_2847_;
v___y_2835_ = v___y_2848_;
v___y_2836_ = v___y_2849_;
v___y_2837_ = v_a_2854_;
v___y_2838_ = v___y_2850_;
v___y_2839_ = v___y_2851_;
v___y_2840_ = v___x_2855_;
v_a_2841_ = v_a_2865_;
goto v___jp_2832_;
}
else
{
lean_object* v_a_2866_; uint8_t v___x_2867_; 
v_a_2866_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2867_ = l_Lean_Exception_isInterrupt(v_a_2866_);
if (v___x_2867_ == 0)
{
uint8_t v___x_2868_; 
lean_inc(v_a_2866_);
v___x_2868_ = l_Lean_Exception_isRuntime(v_a_2866_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; 
lean_dec(v_a_2866_);
v___x_2869_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2863_, v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_dec_ref_known(v___x_2869_, 1);
v___y_2833_ = v___y_2845_;
v___y_2834_ = v___y_2847_;
v___y_2835_ = v___y_2848_;
v___y_2836_ = v___y_2849_;
v___y_2837_ = v_a_2854_;
v___y_2838_ = v___y_2850_;
v___y_2839_ = v___y_2851_;
v___y_2840_ = v___x_2855_;
v_a_2841_ = v_snd_2658_;
goto v___jp_2832_;
}
else
{
lean_object* v_a_2870_; 
lean_dec(v___y_2851_);
lean_dec(v___y_2845_);
lean_dec(v_snd_2658_);
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v___y_2796_ = v___y_2847_;
v___y_2797_ = v___y_2848_;
v___y_2798_ = v___y_2849_;
v___y_2799_ = v___y_2850_;
v___y_2800_ = v_a_2854_;
v___y_2801_ = v___x_2855_;
v_a_2802_ = v_a_2870_;
goto v___jp_2795_;
}
}
else
{
lean_dec(v_a_2863_);
lean_dec(v___y_2851_);
lean_dec(v___y_2845_);
lean_dec(v_snd_2658_);
v___y_2796_ = v___y_2847_;
v___y_2797_ = v___y_2848_;
v___y_2798_ = v___y_2849_;
v___y_2799_ = v___y_2850_;
v___y_2800_ = v_a_2854_;
v___y_2801_ = v___x_2855_;
v_a_2802_ = v_a_2866_;
goto v___jp_2795_;
}
}
else
{
lean_dec(v_a_2863_);
lean_dec(v___y_2851_);
lean_dec(v___y_2845_);
lean_dec(v_snd_2658_);
v___y_2796_ = v___y_2847_;
v___y_2797_ = v___y_2848_;
v___y_2798_ = v___y_2849_;
v___y_2799_ = v___y_2850_;
v___y_2800_ = v_a_2854_;
v___y_2801_ = v___x_2855_;
v_a_2802_ = v_a_2866_;
goto v___jp_2795_;
}
}
}
else
{
lean_object* v_a_2871_; 
lean_dec(v___x_2860_);
lean_dec(v___y_2851_);
lean_dec(v___y_2845_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_2871_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___x_2862_, 1);
v___y_2796_ = v___y_2847_;
v___y_2797_ = v___y_2848_;
v___y_2798_ = v___y_2849_;
v___y_2799_ = v___y_2850_;
v___y_2800_ = v_a_2854_;
v___y_2801_ = v___x_2855_;
v_a_2802_ = v_a_2871_;
goto v___jp_2795_;
}
}
else
{
v___y_2814_ = v___y_2845_;
v___y_2815_ = v___x_2860_;
v___y_2816_ = v___y_2847_;
v___y_2817_ = v___y_2848_;
v___y_2818_ = v___y_2849_;
v___y_2819_ = v_a_2854_;
v___y_2820_ = v___y_2850_;
v___y_2821_ = v___y_2851_;
v___y_2822_ = v___x_2855_;
goto v___jp_2813_;
}
}
}
else
{
lean_object* v_a_2872_; 
lean_dec(v___y_2851_);
lean_dec(v___y_2845_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_2872_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2856_, 1);
v___y_2796_ = v___y_2847_;
v___y_2797_ = v___y_2848_;
v___y_2798_ = v___y_2849_;
v___y_2799_ = v___y_2850_;
v___y_2800_ = v_a_2854_;
v___y_2801_ = v___x_2855_;
v_a_2802_ = v_a_2872_;
goto v___jp_2795_;
}
}
else
{
lean_object* v_a_2873_; 
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v_snd_2658_);
lean_dec(v_goals_2646_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_2873_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2853_, 1);
v___y_2769_ = v___y_2847_;
v___y_2770_ = v___y_2848_;
v_a_2771_ = v_a_2873_;
goto v___jp_2768_;
}
}
v___jp_2874_:
{
uint8_t v___x_2880_; 
v___x_2880_ = l_List_isEmpty___redArg(v___y_2879_);
lean_dec(v___y_2879_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_dec(v___y_2877_);
lean_dec(v___y_2875_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v___x_2881_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_2882_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_2881_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
v___y_2774_ = v___y_2876_;
v___y_2775_ = v___y_2878_;
v___y_2776_ = v___x_2882_;
goto v___jp_2773_;
}
else
{
lean_object* v___x_2883_; 
lean_inc(v_trace_2643_);
v___x_2883_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___y_2877_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = l_List_appendTR___redArg(v___y_2875_, v_a_2884_);
v___y_2756_ = v___y_2876_;
v___y_2757_ = v___y_2878_;
v_a_2758_ = v___x_2885_;
goto v___jp_2755_;
}
else
{
lean_object* v_a_2886_; 
lean_dec(v___y_2875_);
v_a_2886_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2883_, 1);
v___y_2769_ = v___y_2876_;
v___y_2770_ = v___y_2878_;
v_a_2771_ = v_a_2886_;
goto v___jp_2768_;
}
}
}
v___jp_2887_:
{
lean_object* v___x_2891_; double v___x_2892_; double v___x_2893_; double v___x_2894_; double v___x_2895_; double v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2891_ = lean_io_mono_nanos_now();
v___x_2892_ = lean_float_of_nat(v___y_2888_);
v___x_2893_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2894_ = lean_float_div(v___x_2892_, v___x_2893_);
v___x_2895_ = lean_float_of_nat(v___x_2891_);
v___x_2896_ = lean_float_div(v___x_2895_, v___x_2893_);
v___x_2897_ = lean_box_float(v___x_2894_);
v___x_2898_ = lean_box_float(v___x_2896_);
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2897_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v_a_2890_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2643_, v_hasTrace_2665_, v___x_2737_, v_options_2664_, v___x_2740_, v___y_2889_, v___f_2736_, v___x_2900_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v___x_2901_;
}
v___jp_2902_:
{
lean_object* v___x_2906_; 
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_a_2905_);
v___y_2888_ = v___y_2903_;
v___y_2889_ = v___y_2904_;
v_a_2890_ = v___x_2906_;
goto v___jp_2887_;
}
v___jp_2907_:
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2911_, 0, v_a_2910_);
v___y_2888_ = v___y_2908_;
v___y_2889_ = v___y_2909_;
v_a_2890_ = v___x_2911_;
goto v___jp_2887_;
}
v___jp_2912_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = l_List_appendTR___redArg(v___y_2913_, v___y_2915_);
v___x_2919_ = l_List_appendTR___redArg(v___x_2918_, v_a_2917_);
v___y_2908_ = v___y_2914_;
v___y_2909_ = v___y_2916_;
v_a_2910_ = v___x_2919_;
goto v___jp_2907_;
}
v___jp_2920_:
{
if (lean_obj_tag(v___y_2923_) == 0)
{
lean_object* v_a_2924_; 
v_a_2924_ = lean_ctor_get(v___y_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___y_2923_, 1);
v___y_2908_ = v___y_2921_;
v___y_2909_ = v___y_2922_;
v_a_2910_ = v_a_2924_;
goto v___jp_2907_;
}
else
{
lean_object* v_a_2925_; 
v_a_2925_ = lean_ctor_get(v___y_2923_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___y_2923_, 1);
v___y_2903_ = v___y_2921_;
v___y_2904_ = v___y_2922_;
v_a_2905_ = v_a_2925_;
goto v___jp_2902_;
}
}
v___jp_2926_:
{
uint8_t v___x_2932_; 
v___x_2932_ = l_List_isEmpty___redArg(v___y_2929_);
lean_dec(v___y_2929_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec(v___y_2930_);
lean_dec(v___y_2927_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v___x_2933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_2934_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_2933_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
v___y_2921_ = v___y_2928_;
v___y_2922_ = v___y_2931_;
v___y_2923_ = v___x_2934_;
goto v___jp_2920_;
}
else
{
lean_object* v___x_2935_; 
lean_inc(v_trace_2643_);
v___x_2935_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___y_2930_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2937_ = l_List_appendTR___redArg(v___y_2927_, v_a_2936_);
v___y_2908_ = v___y_2928_;
v___y_2909_ = v___y_2931_;
v_a_2910_ = v___x_2937_;
goto v___jp_2907_;
}
else
{
lean_object* v_a_2938_; 
lean_dec(v___y_2927_);
v_a_2938_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2935_, 1);
v___y_2903_ = v___y_2928_;
v___y_2904_ = v___y_2931_;
v_a_2905_ = v_a_2938_;
goto v___jp_2902_;
}
}
}
v___jp_2939_:
{
lean_object* v___x_2947_; double v___x_2948_; double v___x_2949_; double v___x_2950_; double v___x_2951_; double v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2947_ = lean_io_mono_nanos_now();
v___x_2948_ = lean_float_of_nat(v___y_2943_);
v___x_2949_ = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
v___x_2950_ = lean_float_div(v___x_2948_, v___x_2949_);
v___x_2951_ = lean_float_of_nat(v___x_2947_);
v___x_2952_ = lean_float_div(v___x_2951_, v___x_2949_);
v___x_2953_ = lean_box_float(v___x_2950_);
v___x_2954_ = lean_box_float(v___x_2952_);
v___x_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2956_, 0, v_a_2946_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
lean_inc(v_trace_2643_);
v___x_2957_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(v_trace_2643_, v_hasTrace_2665_, v___x_2737_, v_options_2664_, v___y_2945_, v___y_2944_, v___y_2942_, v___x_2956_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
v___y_2921_ = v___y_2940_;
v___y_2922_ = v___y_2941_;
v___y_2923_ = v___x_2957_;
goto v___jp_2920_;
}
v___jp_2958_:
{
lean_object* v___x_2966_; 
v___x_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2966_, 0, v_a_2965_);
v___y_2940_ = v___y_2959_;
v___y_2941_ = v___y_2962_;
v___y_2942_ = v___y_2961_;
v___y_2943_ = v___y_2960_;
v___y_2944_ = v___y_2963_;
v___y_2945_ = v___y_2964_;
v_a_2946_ = v___x_2966_;
goto v___jp_2939_;
}
v___jp_2967_:
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_a_2974_);
v___y_2940_ = v___y_2968_;
v___y_2941_ = v___y_2971_;
v___y_2942_ = v___y_2970_;
v___y_2943_ = v___y_2969_;
v___y_2944_ = v___y_2972_;
v___y_2945_ = v___y_2973_;
v_a_2946_ = v___x_2975_;
goto v___jp_2939_;
}
v___jp_2976_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = l_List_appendTR___redArg(v___y_2977_, v___y_2979_);
v___x_2987_ = l_List_appendTR___redArg(v___x_2986_, v_a_2985_);
v___y_2968_ = v___y_2978_;
v___y_2969_ = v___y_2982_;
v___y_2970_ = v___y_2981_;
v___y_2971_ = v___y_2980_;
v___y_2972_ = v___y_2983_;
v___y_2973_ = v___y_2984_;
v_a_2974_ = v___x_2987_;
goto v___jp_2967_;
}
v___jp_2988_:
{
uint8_t v___x_2998_; 
v___x_2998_ = l_List_isEmpty___redArg(v___y_2992_);
lean_dec(v___y_2992_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v___x_2999_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
v___x_3000_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(v___x_2999_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___y_2968_ = v___y_2991_;
v___y_2969_ = v___y_2995_;
v___y_2970_ = v___y_2994_;
v___y_2971_ = v___y_2993_;
v___y_2972_ = v___y_2996_;
v___y_2973_ = v___y_2997_;
v_a_2974_ = v_a_3001_;
goto v___jp_2967_;
}
else
{
lean_object* v_a_3002_; 
v_a_3002_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3000_, 1);
v___y_2959_ = v___y_2991_;
v___y_2960_ = v___y_2995_;
v___y_2961_ = v___y_2994_;
v___y_2962_ = v___y_2993_;
v___y_2963_ = v___y_2996_;
v___y_2964_ = v___y_2997_;
v_a_2965_ = v_a_3002_;
goto v___jp_2958_;
}
}
else
{
lean_object* v___x_3003_; 
lean_inc(v_trace_2643_);
v___x_3003_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___y_2990_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = l_List_appendTR___redArg(v___y_2989_, v_a_3004_);
v___y_2968_ = v___y_2991_;
v___y_2969_ = v___y_2995_;
v___y_2970_ = v___y_2994_;
v___y_2971_ = v___y_2993_;
v___y_2972_ = v___y_2996_;
v___y_2973_ = v___y_2997_;
v_a_2974_ = v___x_3005_;
goto v___jp_2967_;
}
else
{
lean_object* v_a_3006_; 
lean_dec(v___y_2989_);
v_a_3006_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3003_, 1);
v___y_2959_ = v___y_2991_;
v___y_2960_ = v___y_2995_;
v___y_2961_ = v___y_2994_;
v___y_2962_ = v___y_2993_;
v___y_2963_ = v___y_2996_;
v___y_2964_ = v___y_2997_;
v_a_2965_ = v_a_3006_;
goto v___jp_2958_;
}
}
}
v___jp_3007_:
{
lean_object* v___x_3015_; 
v___x_3015_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2651_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = lean_io_mono_nanos_now();
v___x_3018_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2665_, v___x_2662_, v_goals_2646_, v___y_3013_, v_a_2649_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; uint8_t v_commitIndependentGoals_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v_commitIndependentGoals_3020_ = lean_ctor_get_uint8(v_cfg_2642_, sizeof(void*)*4);
v___x_3021_ = l_List_reverse___redArg(v_a_3019_);
lean_inc(v___y_3008_);
v___x_3022_ = l_List_appendTR___redArg(v___x_3021_, v___y_3008_);
if (v_commitIndependentGoals_3020_ == 0)
{
v___y_2989_ = v___y_3008_;
v___y_2990_ = v___x_3022_;
v___y_2991_ = v___y_3009_;
v___y_2992_ = v___y_3010_;
v___y_2993_ = v___y_3012_;
v___y_2994_ = v___y_3011_;
v___y_2995_ = v___x_3017_;
v___y_2996_ = v_a_3016_;
v___y_2997_ = v___y_3014_;
goto v___jp_2988_;
}
else
{
uint8_t v___x_3023_; 
v___x_3023_ = l_List_isEmpty___redArg(v___y_3008_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Lean_Meta_saveState___redArg(v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
lean_inc(v_snd_2658_);
lean_inc(v_trace_2643_);
v___x_3026_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_3022_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; 
lean_dec(v_a_3025_);
lean_dec(v_snd_2658_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref_known(v___x_3026_, 1);
v___y_2977_ = v___y_3008_;
v___y_2978_ = v___y_3009_;
v___y_2979_ = v___y_3010_;
v___y_2980_ = v___y_3012_;
v___y_2981_ = v___y_3011_;
v___y_2982_ = v___x_3017_;
v___y_2983_ = v_a_3016_;
v___y_2984_ = v___y_3014_;
v_a_2985_ = v_a_3027_;
goto v___jp_2976_;
}
else
{
lean_object* v_a_3028_; uint8_t v___x_3029_; 
v_a_3028_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3026_, 1);
v___x_3029_ = l_Lean_Exception_isInterrupt(v_a_3028_);
if (v___x_3029_ == 0)
{
uint8_t v___x_3030_; 
lean_inc(v_a_3028_);
v___x_3030_ = l_Lean_Exception_isRuntime(v_a_3028_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; 
lean_dec(v_a_3028_);
v___x_3031_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3025_, v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_dec_ref_known(v___x_3031_, 1);
v___y_2977_ = v___y_3008_;
v___y_2978_ = v___y_3009_;
v___y_2979_ = v___y_3010_;
v___y_2980_ = v___y_3012_;
v___y_2981_ = v___y_3011_;
v___y_2982_ = v___x_3017_;
v___y_2983_ = v_a_3016_;
v___y_2984_ = v___y_3014_;
v_a_2985_ = v_snd_2658_;
goto v___jp_2976_;
}
else
{
lean_object* v_a_3032_; 
lean_dec(v___y_3010_);
lean_dec(v___y_3008_);
lean_dec(v_snd_2658_);
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3031_, 1);
v___y_2959_ = v___y_3009_;
v___y_2960_ = v___x_3017_;
v___y_2961_ = v___y_3011_;
v___y_2962_ = v___y_3012_;
v___y_2963_ = v_a_3016_;
v___y_2964_ = v___y_3014_;
v_a_2965_ = v_a_3032_;
goto v___jp_2958_;
}
}
else
{
lean_dec(v_a_3025_);
lean_dec(v___y_3010_);
lean_dec(v___y_3008_);
lean_dec(v_snd_2658_);
v___y_2959_ = v___y_3009_;
v___y_2960_ = v___x_3017_;
v___y_2961_ = v___y_3011_;
v___y_2962_ = v___y_3012_;
v___y_2963_ = v_a_3016_;
v___y_2964_ = v___y_3014_;
v_a_2965_ = v_a_3028_;
goto v___jp_2958_;
}
}
else
{
lean_dec(v_a_3025_);
lean_dec(v___y_3010_);
lean_dec(v___y_3008_);
lean_dec(v_snd_2658_);
v___y_2959_ = v___y_3009_;
v___y_2960_ = v___x_3017_;
v___y_2961_ = v___y_3011_;
v___y_2962_ = v___y_3012_;
v___y_2963_ = v_a_3016_;
v___y_2964_ = v___y_3014_;
v_a_2965_ = v_a_3028_;
goto v___jp_2958_;
}
}
}
else
{
lean_object* v_a_3033_; 
lean_dec(v___x_3022_);
lean_dec(v___y_3010_);
lean_dec(v___y_3008_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3033_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3024_, 1);
v___y_2959_ = v___y_3009_;
v___y_2960_ = v___x_3017_;
v___y_2961_ = v___y_3011_;
v___y_2962_ = v___y_3012_;
v___y_2963_ = v_a_3016_;
v___y_2964_ = v___y_3014_;
v_a_2965_ = v_a_3033_;
goto v___jp_2958_;
}
}
else
{
v___y_2989_ = v___y_3008_;
v___y_2990_ = v___x_3022_;
v___y_2991_ = v___y_3009_;
v___y_2992_ = v___y_3010_;
v___y_2993_ = v___y_3012_;
v___y_2994_ = v___y_3011_;
v___y_2995_ = v___x_3017_;
v___y_2996_ = v_a_3016_;
v___y_2997_ = v___y_3014_;
goto v___jp_2988_;
}
}
}
else
{
lean_object* v_a_3034_; 
lean_dec(v___y_3010_);
lean_dec(v___y_3008_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3034_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3018_, 1);
v___y_2959_ = v___y_3009_;
v___y_2960_ = v___x_3017_;
v___y_2961_ = v___y_3011_;
v___y_2962_ = v___y_3012_;
v___y_2963_ = v_a_3016_;
v___y_2964_ = v___y_3014_;
v_a_2965_ = v_a_3034_;
goto v___jp_2958_;
}
}
else
{
lean_object* v_a_3035_; 
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec(v___y_3008_);
lean_dec(v_snd_2658_);
lean_dec(v_goals_2646_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3035_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3015_, 1);
v___y_2903_ = v___y_3009_;
v___y_2904_ = v___y_3012_;
v_a_2905_ = v_a_3035_;
goto v___jp_2902_;
}
}
v___jp_3036_:
{
lean_object* v___x_3037_; 
v___x_3037_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(v_a_2651_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3037_, 1);
v___x_3039_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3040_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2664_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
lean_del_object(v___x_2660_);
v___x_3041_ = lean_io_mono_nanos_now();
v___x_3042_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2657_, v___f_2653_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v_fst_3044_; lean_object* v_snd_3045_; lean_object* v___x_3046_; lean_object* v___f_3047_; lean_object* v___x_3048_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3042_, 1);
v_fst_3044_ = lean_ctor_get(v_a_3043_, 0);
lean_inc_n(v_fst_3044_, 2);
v_snd_3045_ = lean_ctor_get(v_a_3043_, 1);
lean_inc(v_snd_3045_);
lean_dec(v_a_3043_);
v___x_3046_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3045_, v___x_2654_);
lean_inc(v___x_3046_);
v___f_3047_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3047_, 0, v_fst_3044_);
lean_closure_set(v___f_3047_, 1, v___x_3046_);
v___x_3048_ = lean_box(0);
if (v___x_2740_ == 0)
{
lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = l_Lean_trace_profiler;
v___x_3050_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2664_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; 
lean_dec_ref(v___f_3047_);
v___x_3051_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v_hasTrace_2665_, v___x_2662_, v_goals_2646_, v___x_3048_, v_a_2649_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; uint8_t v_commitIndependentGoals_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref_known(v___x_3051_, 1);
v_commitIndependentGoals_3053_ = lean_ctor_get_uint8(v_cfg_2642_, sizeof(void*)*4);
v___x_3054_ = l_List_reverse___redArg(v_a_3052_);
lean_inc(v___x_3046_);
v___x_3055_ = l_List_appendTR___redArg(v___x_3054_, v___x_3046_);
if (v_commitIndependentGoals_3053_ == 0)
{
v___y_2927_ = v___x_3046_;
v___y_2928_ = v___x_3041_;
v___y_2929_ = v_fst_3044_;
v___y_2930_ = v___x_3055_;
v___y_2931_ = v_a_3038_;
goto v___jp_2926_;
}
else
{
uint8_t v___x_3056_; 
v___x_3056_ = l_List_isEmpty___redArg(v___x_3046_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_Meta_saveState___redArg(v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3059_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3057_, 1);
lean_inc(v_snd_2658_);
lean_inc(v_trace_2643_);
v___x_3059_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_3055_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; 
lean_dec(v_a_3058_);
lean_dec(v_snd_2658_);
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v___y_2913_ = v___x_3046_;
v___y_2914_ = v___x_3041_;
v___y_2915_ = v_fst_3044_;
v___y_2916_ = v_a_3038_;
v_a_2917_ = v_a_3060_;
goto v___jp_2912_;
}
else
{
lean_object* v_a_3061_; uint8_t v___x_3062_; 
v_a_3061_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3062_ = l_Lean_Exception_isInterrupt(v_a_3061_);
if (v___x_3062_ == 0)
{
uint8_t v___x_3063_; 
lean_inc(v_a_3061_);
v___x_3063_ = l_Lean_Exception_isRuntime(v_a_3061_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; 
lean_dec(v_a_3061_);
v___x_3064_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3058_, v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_dec_ref_known(v___x_3064_, 1);
v___y_2913_ = v___x_3046_;
v___y_2914_ = v___x_3041_;
v___y_2915_ = v_fst_3044_;
v___y_2916_ = v_a_3038_;
v_a_2917_ = v_snd_2658_;
goto v___jp_2912_;
}
else
{
lean_object* v_a_3065_; 
lean_dec(v___x_3046_);
lean_dec(v_fst_3044_);
lean_dec(v_snd_2658_);
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v___y_2903_ = v___x_3041_;
v___y_2904_ = v_a_3038_;
v_a_2905_ = v_a_3065_;
goto v___jp_2902_;
}
}
else
{
lean_dec(v_a_3058_);
lean_dec(v___x_3046_);
lean_dec(v_fst_3044_);
lean_dec(v_snd_2658_);
v___y_2903_ = v___x_3041_;
v___y_2904_ = v_a_3038_;
v_a_2905_ = v_a_3061_;
goto v___jp_2902_;
}
}
else
{
lean_dec(v_a_3058_);
lean_dec(v___x_3046_);
lean_dec(v_fst_3044_);
lean_dec(v_snd_2658_);
v___y_2903_ = v___x_3041_;
v___y_2904_ = v_a_3038_;
v_a_2905_ = v_a_3061_;
goto v___jp_2902_;
}
}
}
else
{
lean_object* v_a_3066_; 
lean_dec(v___x_3055_);
lean_dec(v___x_3046_);
lean_dec(v_fst_3044_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3066_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3057_, 1);
v___y_2903_ = v___x_3041_;
v___y_2904_ = v_a_3038_;
v_a_2905_ = v_a_3066_;
goto v___jp_2902_;
}
}
else
{
v___y_2927_ = v___x_3046_;
v___y_2928_ = v___x_3041_;
v___y_2929_ = v_fst_3044_;
v___y_2930_ = v___x_3055_;
v___y_2931_ = v_a_3038_;
goto v___jp_2926_;
}
}
}
else
{
lean_object* v_a_3067_; 
lean_dec(v___x_3046_);
lean_dec(v_fst_3044_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3067_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___x_3051_, 1);
v___y_2903_ = v___x_3041_;
v___y_2904_ = v_a_3038_;
v_a_2905_ = v_a_3067_;
goto v___jp_2902_;
}
}
else
{
v___y_3008_ = v___x_3046_;
v___y_3009_ = v___x_3041_;
v___y_3010_ = v_fst_3044_;
v___y_3011_ = v___f_3047_;
v___y_3012_ = v_a_3038_;
v___y_3013_ = v___x_3048_;
v___y_3014_ = v___x_2740_;
goto v___jp_3007_;
}
}
else
{
v___y_3008_ = v___x_3046_;
v___y_3009_ = v___x_3041_;
v___y_3010_ = v_fst_3044_;
v___y_3011_ = v___f_3047_;
v___y_3012_ = v_a_3038_;
v___y_3013_ = v___x_3048_;
v___y_3014_ = v___x_2740_;
goto v___jp_3007_;
}
}
else
{
lean_object* v_a_3068_; 
lean_dec(v_snd_2658_);
lean_dec(v_goals_2646_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3068_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3042_, 1);
v___y_2903_ = v___x_3041_;
v___y_2904_ = v_a_3038_;
v_a_2905_ = v_a_3068_;
goto v___jp_2902_;
}
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_io_get_num_heartbeats();
v___x_3070_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_fst_2657_, v___f_2653_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v_fst_3072_; lean_object* v_snd_3073_; lean_object* v___x_3074_; lean_object* v___f_3075_; lean_object* v___x_3076_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
v_fst_3072_ = lean_ctor_get(v_a_3071_, 0);
lean_inc_n(v_fst_3072_, 2);
v_snd_3073_ = lean_ctor_get(v_a_3071_, 1);
lean_inc(v_snd_3073_);
lean_dec(v_a_3071_);
v___x_3074_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(v_snd_3073_, v___x_2654_);
lean_inc(v___x_3074_);
v___f_3075_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3075_, 0, v_fst_3072_);
lean_closure_set(v___f_3075_, 1, v___x_3074_);
v___x_3076_ = lean_box(0);
if (v___x_2740_ == 0)
{
lean_object* v___x_3077_; uint8_t v___x_3078_; 
v___x_3077_ = l_Lean_trace_profiler;
v___x_3078_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(v_options_2664_, v___x_3077_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; 
lean_dec_ref(v___f_3075_);
v___x_3079_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3040_, v___x_2662_, v_goals_2646_, v___x_3076_, v_a_2649_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; uint8_t v_commitIndependentGoals_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v_commitIndependentGoals_3081_ = lean_ctor_get_uint8(v_cfg_2642_, sizeof(void*)*4);
v___x_3082_ = l_List_reverse___redArg(v_a_3080_);
lean_inc(v___x_3074_);
v___x_3083_ = l_List_appendTR___redArg(v___x_3082_, v___x_3074_);
if (v_commitIndependentGoals_3081_ == 0)
{
v___y_2875_ = v___x_3074_;
v___y_2876_ = v___x_3069_;
v___y_2877_ = v___x_3083_;
v___y_2878_ = v_a_3038_;
v___y_2879_ = v_fst_3072_;
goto v___jp_2874_;
}
else
{
uint8_t v___x_3084_; 
v___x_3084_ = l_List_isEmpty___redArg(v___x_3074_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Lean_Meta_saveState___redArg(v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3087_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3085_, 1);
lean_inc(v_snd_2658_);
lean_inc(v_trace_2643_);
v___x_3087_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v___x_3083_, v_snd_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; 
lean_dec(v_a_3086_);
lean_dec(v_snd_2658_);
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___x_3087_, 1);
v___y_2761_ = v___x_3074_;
v___y_2762_ = v___x_3069_;
v___y_2763_ = v_a_3038_;
v___y_2764_ = v_fst_3072_;
v_a_2765_ = v_a_3088_;
goto v___jp_2760_;
}
else
{
lean_object* v_a_3089_; uint8_t v___x_3090_; 
v_a_3089_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3087_, 1);
v___x_3090_ = l_Lean_Exception_isInterrupt(v_a_3089_);
if (v___x_3090_ == 0)
{
uint8_t v___x_3091_; 
lean_inc(v_a_3089_);
v___x_3091_ = l_Lean_Exception_isRuntime(v_a_3089_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; 
lean_dec(v_a_3089_);
v___x_3092_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3086_, v_a_2649_, v_a_2651_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_dec_ref_known(v___x_3092_, 1);
v___y_2761_ = v___x_3074_;
v___y_2762_ = v___x_3069_;
v___y_2763_ = v_a_3038_;
v___y_2764_ = v_fst_3072_;
v_a_2765_ = v_snd_2658_;
goto v___jp_2760_;
}
else
{
lean_object* v_a_3093_; 
lean_dec(v___x_3074_);
lean_dec(v_fst_3072_);
lean_dec(v_snd_2658_);
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v___x_3092_, 1);
v___y_2769_ = v___x_3069_;
v___y_2770_ = v_a_3038_;
v_a_2771_ = v_a_3093_;
goto v___jp_2768_;
}
}
else
{
lean_dec(v_a_3086_);
lean_dec(v___x_3074_);
lean_dec(v_fst_3072_);
lean_dec(v_snd_2658_);
v___y_2769_ = v___x_3069_;
v___y_2770_ = v_a_3038_;
v_a_2771_ = v_a_3089_;
goto v___jp_2768_;
}
}
else
{
lean_dec(v_a_3086_);
lean_dec(v___x_3074_);
lean_dec(v_fst_3072_);
lean_dec(v_snd_2658_);
v___y_2769_ = v___x_3069_;
v___y_2770_ = v_a_3038_;
v_a_2771_ = v_a_3089_;
goto v___jp_2768_;
}
}
}
else
{
lean_object* v_a_3094_; 
lean_dec(v___x_3083_);
lean_dec(v___x_3074_);
lean_dec(v_fst_3072_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3094_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3085_, 1);
v___y_2769_ = v___x_3069_;
v___y_2770_ = v_a_3038_;
v_a_2771_ = v_a_3094_;
goto v___jp_2768_;
}
}
else
{
v___y_2875_ = v___x_3074_;
v___y_2876_ = v___x_3069_;
v___y_2877_ = v___x_3083_;
v___y_2878_ = v_a_3038_;
v___y_2879_ = v_fst_3072_;
goto v___jp_2874_;
}
}
}
else
{
lean_object* v_a_3095_; 
lean_dec(v___x_3074_);
lean_dec(v_fst_3072_);
lean_dec(v_snd_2658_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3095_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3095_);
lean_dec_ref_known(v___x_3079_, 1);
v___y_2769_ = v___x_3069_;
v___y_2770_ = v_a_3038_;
v_a_2771_ = v_a_3095_;
goto v___jp_2768_;
}
}
else
{
v___y_2845_ = v___x_3074_;
v___y_2846_ = v___x_3076_;
v___y_2847_ = v___x_3069_;
v___y_2848_ = v_a_3038_;
v___y_2849_ = v___f_3075_;
v___y_2850_ = v___x_2740_;
v___y_2851_ = v_fst_3072_;
v___y_2852_ = v___x_3040_;
goto v___jp_2844_;
}
}
else
{
v___y_2845_ = v___x_3074_;
v___y_2846_ = v___x_3076_;
v___y_2847_ = v___x_3069_;
v___y_2848_ = v_a_3038_;
v___y_2849_ = v___f_3075_;
v___y_2850_ = v___x_2740_;
v___y_2851_ = v_fst_3072_;
v___y_2852_ = v___x_3040_;
goto v___jp_2844_;
}
}
else
{
lean_object* v_a_3096_; 
lean_dec(v_snd_2658_);
lean_dec(v_goals_2646_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec_ref(v_cfg_2642_);
v_a_3096_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3070_, 1);
v___y_2769_ = v___x_3069_;
v___y_2770_ = v_a_3038_;
v_a_2771_ = v_a_3096_;
goto v___jp_2768_;
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec_ref(v___f_2736_);
lean_del_object(v___x_2660_);
lean_dec(v_snd_2658_);
lean_dec(v_fst_2657_);
lean_dec_ref(v___f_2653_);
lean_dec(v_goals_2646_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec(v_trace_2643_);
lean_dec_ref(v_cfg_2642_);
v_a_3097_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3037_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3037_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
}
else
{
lean_object* v_maxDepth_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_del_object(v___x_2660_);
lean_dec(v_snd_2658_);
lean_dec(v_fst_2657_);
lean_dec_ref(v___f_2653_);
lean_dec(v_goals_2646_);
v_maxDepth_3296_ = lean_ctor_get(v_cfg_2642_, 0);
lean_inc(v_maxDepth_3296_);
v___x_3297_ = lean_box(0);
v___x_3298_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(v_cfg_2642_, v_trace_2643_, v_next_2644_, v_orig_2645_, v_maxDepth_3296_, v_remaining_2647_, v___x_3297_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v___x_3298_;
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec_ref(v___f_2653_);
lean_dec(v_remaining_2647_);
lean_dec(v_goals_2646_);
lean_dec(v_orig_2645_);
lean_dec_ref(v_next_2644_);
lean_dec(v_trace_2643_);
lean_dec_ref(v_cfg_2642_);
v_a_3300_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_2655_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_2655_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* v_cfg_3308_, lean_object* v_trace_3309_, lean_object* v_next_3310_, lean_object* v_orig_3311_, lean_object* v_goals_3312_, lean_object* v_remaining_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3308_, v_trace_3309_, v_next_3310_, v_orig_3311_, v_goals_3312_, v_remaining_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
lean_dec(v_a_3317_);
lean_dec_ref(v_a_3316_);
lean_dec(v_a_3315_);
lean_dec_ref(v_a_3314_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* v_00_u03b1_3320_, lean_object* v_00_u03b2_3321_, lean_object* v_L_3322_, lean_object* v_f_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(v_L_3322_, v_f_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* v_00_u03b1_3330_, lean_object* v_00_u03b2_3331_, lean_object* v_L_3332_, lean_object* v_f_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(v_00_u03b1_3330_, v_00_u03b2_3331_, v_L_3332_, v_f_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t v___x_3340_, lean_object* v_x_3341_, lean_object* v_x_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(v___x_3340_, v_x_3341_, v_x_3342_, v___y_3344_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* v___x_3349_, lean_object* v_x_3350_, lean_object* v_x_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
uint8_t v___x_48164__boxed_3357_; lean_object* v_res_3358_; 
v___x_48164__boxed_3357_ = lean_unbox(v___x_3349_);
v_res_3358_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(v___x_48164__boxed_3357_, v_x_3350_, v_x_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t v___x_3359_, uint8_t v___x_3360_, lean_object* v_x_3361_, lean_object* v_x_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(v___x_3359_, v___x_3360_, v_x_3361_, v_x_3362_, v___y_3364_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* v___x_3369_, lean_object* v___x_3370_, lean_object* v_x_3371_, lean_object* v_x_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
uint8_t v___x_48190__boxed_3378_; uint8_t v___x_48191__boxed_3379_; lean_object* v_res_3380_; 
v___x_48190__boxed_3378_ = lean_unbox(v___x_3369_);
v___x_48191__boxed_3379_ = lean_unbox(v___x_3370_);
v_res_3380_ = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(v___x_48190__boxed_3378_, v___x_48191__boxed_3379_, v_x_3371_, v_x_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* v_00_u03b1_3381_, lean_object* v_00_u03b2_3382_, lean_object* v_f_3383_, lean_object* v_x_3384_, lean_object* v_x_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(v_f_3383_, v_x_3384_, v_x_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3392_, lean_object* v_00_u03b2_3393_, lean_object* v_f_3394_, lean_object* v_x_3395_, lean_object* v_x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(v_00_u03b1_3392_, v_00_u03b2_3393_, v_f_3394_, v_x_3395_, v_x_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* v_00_u03b1_3403_, lean_object* v_00_u03b2_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(v_a_3405_, v_a_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* v_00_u03b1_3408_, lean_object* v_00_u03b2_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(v_a_3410_, v_a_3411_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* v_next_3413_, lean_object* v_g_3414_, lean_object* v_f_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v___x_3421_; 
lean_inc(v___y_3419_);
lean_inc_ref(v___y_3418_);
lean_inc(v___y_3417_);
lean_inc_ref(v___y_3416_);
v___x_3421_ = lean_apply_6(v_next_3413_, v_g_3414_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, lean_box(0));
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3423_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref_known(v___x_3421_, 1);
v___x_3423_ = l_Lean_Meta_Iterator_firstM___redArg(v_a_3422_, v_f_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
return v___x_3423_;
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_f_3415_);
v_a_3424_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3421_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3421_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* v_next_3432_, lean_object* v_g_3433_, lean_object* v_f_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(v_next_3432_, v_g_3433_, v_f_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* v_cfg_3441_, lean_object* v_trace_3442_, lean_object* v_next_3443_, lean_object* v_goals_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v_resolve_3450_; lean_object* v___x_3451_; 
v_resolve_3450_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(v_resolve_3450_, 0, v_next_3443_);
lean_inc_n(v_goals_3444_, 2);
v___x_3451_ = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(v_cfg_3441_, v_trace_3442_, v_resolve_3450_, v_goals_3444_, v_goals_3444_, v_goals_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* v_cfg_3452_, lean_object* v_trace_3453_, lean_object* v_next_3454_, lean_object* v_goals_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_Meta_Tactic_Backtrack_backtrack(v_cfg_3452_, v_trace_3453_, v_next_3454_, v_goals_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_);
lean_dec(v_a_3459_);
lean_dec_ref(v_a_3458_);
lean_dec(v_a_3457_);
lean_dec_ref(v_a_3456_);
return v_res_3461_;
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

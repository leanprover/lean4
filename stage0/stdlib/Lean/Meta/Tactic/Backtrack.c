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
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__2(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0_value;
lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__2_value;
lean_object* l_List_mapM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1;
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 45, .m_data = "⏸️ suspending search and returning as subgoal"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "success!"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 42, .m_data = "⏭️ deemed acceptable, returning as subgoal"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 35, .m_data = "⏬ discharger generated new subgoals"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "BacktrackConfig.proc failed: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13___boxed(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1;
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5;
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "discarding already assigned goal "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* l_Lean_MessageData_ofList(lean_object*);
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
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isIndependentOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
uint8_t l_List_isEmpty___redArg(lean_object*);
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
lean_object* l_Lean_Meta_Iterator_firstM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Meta_ppExpr(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
x_10 = lean_ctor_get(x_7, 0);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
x_11 = x_7;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___redArg(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_29; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
x_12 = x_1;
x_13 = x_29;
goto block_28;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(x_10, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 0, x_15);
x_16 = x_12;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_2);
x_16 = x_19;
goto block_18;
}
block_18:
{
x_1 = x_11;
x_2 = x_16;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_del_object(x_12);
lean_dec(x_11);
lean_dec(x_2);
x_20 = lean_ctor_get(x_14, 0);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
x_21 = x_14;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_List_mapM_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds_spec__0(x_1, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
x_3 = x_1;
x_4 = x_9;
goto block_8;
}
else
{
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = x_9;
goto block_8;
}
block_8:
{
lean_object* x_5; 
if (x_4 == 0)
{
x_5 = x_3;
goto block_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_5 = x_7;
goto block_6;
}
block_6:
{
return x_5;
}
}
}
else
{
lean_object* x_10; 
lean_dec_ref(x_1);
x_10 = lean_box(0);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
x_3 = x_1;
x_4 = x_9;
goto block_8;
}
else
{
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = x_9;
goto block_8;
}
block_8:
{
lean_object* x_5; 
if (x_4 == 0)
{
lean_ctor_set_tag(x_3, 1);
x_5 = x_3;
goto block_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_5 = x_7;
goto block_6;
}
block_6:
{
return x_5;
}
}
}
else
{
lean_object* x_10; 
lean_dec_ref(x_1);
x_10 = lean_box(0);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(x_4);
x_6 = l_List_filterMapTR_go___redArg(x_1, x_4, x_5);
x_7 = l_List_filterMapTR_go___redArg(x_2, x_4, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_apply_2(x_3, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__4), 3, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_apply_1(x_3, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_9);
x_11 = lean_apply_3(x_5, lean_box(0), x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__0));
x_11 = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__1));
x_12 = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___closed__2));
lean_inc(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3), 4, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__5), 6, 5);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_7);
x_15 = lean_box(0);
x_16 = l_List_mapM_loop___redArg(x_1, x_14, x_3, x_15);
x_17 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_16, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_34; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = lean_ctor_get(x_6, 4);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 2);
x_11 = lean_ctor_get(x_6, 3);
x_12 = lean_ctor_get(x_6, 5);
x_13 = lean_ctor_get(x_6, 6);
x_14 = lean_ctor_get(x_6, 7);
x_15 = lean_ctor_get(x_6, 8);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
x_16 = x_6;
x_17 = x_34;
goto block_33;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_34;
goto block_33;
}
block_33:
{
uint64_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_31; 
x_18 = lean_ctor_get_uint64(x_7, sizeof(void*)*1);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_7, 0);
lean_dec(x_32);
x_19 = x_7;
x_20 = x_31;
goto block_30;
}
else
{
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set_uint64(x_29, sizeof(void*)*1, x_18);
x_22 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_23; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_22);
x_23 = x_16;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_10);
lean_ctor_set(x_27, 3, x_11);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_12);
lean_ctor_set(x_27, 6, x_13);
lean_ctor_set(x_27, 7, x_14);
lean_ctor_set(x_27, 8, x_15);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_st_ref_set(x_1, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_9 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_ctor_get(x_9, 0);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
x_11 = x_9;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_13);
x_14 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_48; 
x_19 = lean_ctor_get(x_9, 0);
x_48 = !lean_is_exclusive(x_9);
if (x_48 == 0)
{
x_20 = x_9;
x_21 = x_48;
goto block_47;
}
else
{
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_box(0);
x_21 = x_48;
goto block_47;
}
block_47:
{
uint8_t x_22; uint8_t x_45; 
x_45 = l_Lean_Exception_isInterrupt(x_19);
if (x_45 == 0)
{
uint8_t x_46; 
lean_inc(x_19);
x_46 = l_Lean_Exception_isRuntime(x_19);
x_22 = x_46;
goto block_44;
}
else
{
x_22 = x_45;
goto block_44;
}
block_44:
{
if (x_22 == 0)
{
lean_object* x_23; 
lean_del_object(x_20);
lean_dec(x_19);
x_23 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; uint8_t x_31; 
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_23, 0);
lean_dec(x_32);
x_24 = x_23;
x_25 = x_31;
goto block_30;
}
else
{
lean_dec(x_23);
x_24 = lean_box(0);
x_25 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_26);
x_27 = x_24;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
x_33 = lean_ctor_get(x_23, 0);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
x_34 = x_23;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
if (x_21 == 0)
{
x_41 = x_20;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_19);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_ctor_get(x_7, 0);
x_56 = !lean_is_exclusive(x_7);
if (x_56 == 0)
{
x_50 = x_7;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_7);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___closed__1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
x_9 = l_Lean_Exception_toMessageData(x_1);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 2;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_80; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
x_15 = lean_ctor_get(x_7, 5);
x_16 = lean_ctor_get(x_7, 6);
x_17 = lean_ctor_get(x_7, 7);
x_18 = lean_ctor_get(x_7, 8);
x_19 = lean_ctor_get(x_7, 9);
x_20 = lean_ctor_get(x_7, 10);
x_21 = lean_ctor_get(x_7, 11);
x_22 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_23 = lean_ctor_get(x_7, 12);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_25 = lean_ctor_get(x_7, 13);
x_80 = !lean_is_exclusive(x_7);
if (x_80 == 0)
{
x_26 = x_7;
x_27 = x_80;
goto block_79;
}
else
{
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_st_ref_get(x_8);
x_29 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_replaceRef(x_3, x_15);
lean_dec(x_15);
if (x_27 == 0)
{
lean_ctor_set(x_26, 5, x_31);
x_32 = x_26;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_78, 0, x_10);
lean_ctor_set(x_78, 1, x_11);
lean_ctor_set(x_78, 2, x_12);
lean_ctor_set(x_78, 3, x_13);
lean_ctor_set(x_78, 4, x_14);
lean_ctor_set(x_78, 5, x_31);
lean_ctor_set(x_78, 6, x_16);
lean_ctor_set(x_78, 7, x_17);
lean_ctor_set(x_78, 8, x_18);
lean_ctor_set(x_78, 9, x_19);
lean_ctor_set(x_78, 10, x_20);
lean_ctor_set(x_78, 11, x_21);
lean_ctor_set(x_78, 12, x_23);
lean_ctor_set(x_78, 13, x_25);
lean_ctor_set_uint8(x_78, sizeof(void*)*14, x_22);
lean_ctor_set_uint8(x_78, sizeof(void*)*14 + 1, x_24);
x_32 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_76; 
x_33 = l_Lean_PersistentArray_toArray___redArg(x_30);
lean_dec_ref(x_30);
x_34 = lean_array_size(x_33);
x_35 = 0;
x_36 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5_spec__8(x_34, x_35, x_33);
x_37 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(x_37, x_5, x_6, x_32, x_8);
lean_dec_ref(x_32);
x_39 = lean_ctor_get(x_38, 0);
x_76 = !lean_is_exclusive(x_38);
if (x_76 == 0)
{
x_40 = x_38;
x_41 = x_76;
goto block_75;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_74; 
x_42 = lean_st_ref_take(x_8);
x_43 = lean_ctor_get(x_42, 4);
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_ctor_get(x_42, 2);
x_47 = lean_ctor_get(x_42, 3);
x_48 = lean_ctor_get(x_42, 5);
x_49 = lean_ctor_get(x_42, 6);
x_50 = lean_ctor_get(x_42, 7);
x_51 = lean_ctor_get(x_42, 8);
x_74 = !lean_is_exclusive(x_42);
if (x_74 == 0)
{
x_52 = x_42;
x_53 = x_74;
goto block_73;
}
else
{
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_43);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_52 = lean_box(0);
x_53 = x_74;
goto block_73;
}
block_73:
{
uint64_t x_54; lean_object* x_55; uint8_t x_56; uint8_t x_71; 
x_54 = lean_ctor_get_uint64(x_43, sizeof(void*)*1);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_43, 0);
lean_dec(x_72);
x_55 = x_43;
x_56 = x_71;
goto block_70;
}
else
{
lean_dec(x_43);
x_55 = lean_box(0);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_39);
x_58 = l_Lean_PersistentArray_push___redArg(x_1, x_57);
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_58);
x_59 = x_55;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set_uint64(x_69, sizeof(void*)*1, x_54);
x_59 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_60; 
if (x_53 == 0)
{
lean_ctor_set(x_52, 4, x_59);
x_60 = x_52;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_67, 0, x_44);
lean_ctor_set(x_67, 1, x_45);
lean_ctor_set(x_67, 2, x_46);
lean_ctor_set(x_67, 3, x_47);
lean_ctor_set(x_67, 4, x_59);
lean_ctor_set(x_67, 5, x_48);
lean_ctor_set(x_67, 6, x_49);
lean_ctor_set(x_67, 7, x_50);
lean_ctor_set(x_67, 8, x_51);
x_60 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_st_ref_set(x_8, x_60);
x_62 = lean_box(0);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_62);
x_63 = x_40;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
x_4 = x_1;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_1, 0);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_12 = x_1;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_113; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
x_113 = !lean_is_exclusive(x_8);
if (x_113 == 0)
{
x_16 = x_8;
x_17 = x_113;
goto block_112;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_111; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
x_111 = !lean_is_exclusive(x_15);
if (x_111 == 0)
{
x_34 = x_15;
x_35 = x_111;
goto block_110;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = x_111;
goto block_110;
}
block_31:
{
lean_object* x_21; 
x_21 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(x_6, x_20, x_18, x_19, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec_ref(x_21);
x_22 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_14);
x_23 = lean_ctor_get(x_21, 0);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
x_24 = x_21;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
block_110:
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_63; double x_94; 
x_36 = l_Lean_trace_profiler;
x_37 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_4, x_36);
if (x_37 == 0)
{
x_63 = x_37;
goto block_93;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = l_Lean_trace_profiler_useHeartbeats;
x_101 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_4, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; double x_104; double x_105; double x_106; 
x_102 = l_Lean_trace_profiler_threshold;
x_103 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(x_4, x_102);
x_104 = lean_float_of_nat(x_103);
x_105 = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5);
x_106 = lean_float_div(x_104, x_105);
x_94 = x_106;
goto block_99;
}
else
{
lean_object* x_107; lean_object* x_108; double x_109; 
x_107 = l_Lean_trace_profiler_threshold;
x_108 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(x_4, x_107);
x_109 = lean_float_of_nat(x_108);
x_94 = x_109;
goto block_99;
}
}
block_57:
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8_spec__13(x_14);
x_41 = l_Lean_TraceResult_toEmoji(x_40);
x_42 = l_Lean_stringToMessageData(x_41);
x_43 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1);
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 7);
lean_ctor_set(x_34, 1, x_43);
lean_ctor_set(x_34, 0, x_42);
x_44 = x_34;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_43);
x_44 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_45; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_39);
lean_ctor_set(x_16, 0, x_44);
x_45 = x_16;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_39);
x_45 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_46; lean_object* x_47; double x_48; lean_object* x_49; 
x_46 = lean_box(x_40);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2);
lean_inc_ref(x_3);
lean_inc_ref(x_47);
lean_inc(x_1);
x_49 = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_3);
lean_ctor_set_float(x_49, sizeof(void*)*3, x_48);
lean_ctor_set_float(x_49, sizeof(void*)*3 + 8, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 16, x_2);
if (x_37 == 0)
{
lean_dec_ref(x_47);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_3);
lean_dec(x_1);
x_18 = x_38;
x_19 = x_45;
x_20 = x_49;
goto block_31;
}
else
{
lean_object* x_50; double x_51; double x_52; 
lean_dec_ref(x_49);
x_50 = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_3);
x_51 = lean_unbox_float(x_32);
lean_dec(x_32);
lean_ctor_set_float(x_50, sizeof(void*)*3, x_51);
x_52 = lean_unbox_float(x_33);
lean_dec(x_33);
lean_ctor_set_float(x_50, sizeof(void*)*3 + 8, x_52);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 16, x_2);
x_18 = x_38;
x_19 = x_45;
x_20 = x_50;
goto block_31;
}
}
}
}
block_62:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_11, 5);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_14);
x_59 = lean_apply_6(x_7, x_14, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc(x_58);
x_38 = x_58;
x_39 = x_60;
goto block_57;
}
else
{
lean_object* x_61; 
lean_dec_ref(x_59);
x_61 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4);
lean_inc(x_58);
x_38 = x_58;
x_39 = x_61;
goto block_57;
}
}
block_93:
{
if (x_5 == 0)
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_92; 
lean_del_object(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_del_object(x_16);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_64 = lean_st_ref_take(x_12);
x_65 = lean_ctor_get(x_64, 4);
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
x_68 = lean_ctor_get(x_64, 2);
x_69 = lean_ctor_get(x_64, 3);
x_70 = lean_ctor_get(x_64, 5);
x_71 = lean_ctor_get(x_64, 6);
x_72 = lean_ctor_get(x_64, 7);
x_73 = lean_ctor_get(x_64, 8);
x_92 = !lean_is_exclusive(x_64);
if (x_92 == 0)
{
x_74 = x_64;
x_75 = x_92;
goto block_91;
}
else
{
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_65);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_74 = lean_box(0);
x_75 = x_92;
goto block_91;
}
block_91:
{
uint64_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_90; 
x_76 = lean_ctor_get_uint64(x_65, sizeof(void*)*1);
x_77 = lean_ctor_get(x_65, 0);
x_90 = !lean_is_exclusive(x_65);
if (x_90 == 0)
{
x_78 = x_65;
x_79 = x_90;
goto block_89;
}
else
{
lean_inc(x_77);
lean_dec(x_65);
x_78 = lean_box(0);
x_79 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_PersistentArray_append___redArg(x_6, x_77);
lean_dec_ref(x_77);
if (x_79 == 0)
{
lean_ctor_set(x_78, 0, x_80);
x_81 = x_78;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set_uint64(x_88, sizeof(void*)*1, x_76);
x_81 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_82; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 4, x_81);
x_82 = x_74;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_86, 0, x_66);
lean_ctor_set(x_86, 1, x_67);
lean_ctor_set(x_86, 2, x_68);
lean_ctor_set(x_86, 3, x_69);
lean_ctor_set(x_86, 4, x_81);
lean_ctor_set(x_86, 5, x_70);
lean_ctor_set(x_86, 6, x_71);
lean_ctor_set(x_86, 7, x_72);
lean_ctor_set(x_86, 8, x_73);
x_82 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_st_ref_set(x_12, x_82);
lean_dec(x_12);
x_84 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(x_14);
return x_84;
}
}
}
}
}
else
{
goto block_62;
}
}
else
{
goto block_62;
}
}
block_99:
{
double x_95; double x_96; double x_97; uint8_t x_98; 
x_95 = lean_unbox_float(x_33);
x_96 = lean_unbox_float(x_32);
x_97 = lean_float_sub(x_95, x_96);
x_98 = lean_float_decLt(x_94, x_97);
x_63 = x_98;
goto block_93;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_5);
x_16 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqMVarId_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqMVarId_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 7);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 2;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_113; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
x_113 = !lean_is_exclusive(x_8);
if (x_113 == 0)
{
x_16 = x_8;
x_17 = x_113;
goto block_112;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = x_113;
goto block_112;
}
block_112:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_111; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
x_111 = !lean_is_exclusive(x_15);
if (x_111 == 0)
{
x_34 = x_15;
x_35 = x_111;
goto block_110;
}
else
{
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = x_111;
goto block_110;
}
block_31:
{
lean_object* x_21; 
x_21 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(x_6, x_20, x_19, x_18, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec_ref(x_21);
x_22 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_14);
x_23 = lean_ctor_get(x_21, 0);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
x_24 = x_21;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
block_110:
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_63; double x_94; 
x_36 = l_Lean_trace_profiler;
x_37 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_4, x_36);
if (x_37 == 0)
{
x_63 = x_37;
goto block_93;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = l_Lean_trace_profiler_useHeartbeats;
x_101 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_4, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; double x_104; double x_105; double x_106; 
x_102 = l_Lean_trace_profiler_threshold;
x_103 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(x_4, x_102);
x_104 = lean_float_of_nat(x_103);
x_105 = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__5);
x_106 = lean_float_div(x_104, x_105);
x_94 = x_106;
goto block_99;
}
else
{
lean_object* x_107; lean_object* x_108; double x_109; 
x_107 = l_Lean_trace_profiler_threshold;
x_108 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__7(x_4, x_107);
x_109 = lean_float_of_nat(x_108);
x_94 = x_109;
goto block_99;
}
}
block_57:
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(x_14);
x_41 = l_Lean_TraceResult_toEmoji(x_40);
x_42 = l_Lean_stringToMessageData(x_41);
x_43 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__1);
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 7);
lean_ctor_set(x_34, 1, x_43);
lean_ctor_set(x_34, 0, x_42);
x_44 = x_34;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_43);
x_44 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_45; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_39);
lean_ctor_set(x_16, 0, x_44);
x_45 = x_16;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_39);
x_45 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_46; lean_object* x_47; double x_48; lean_object* x_49; 
x_46 = lean_box(x_40);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__2);
lean_inc_ref(x_3);
lean_inc_ref(x_47);
lean_inc(x_1);
x_49 = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_3);
lean_ctor_set_float(x_49, sizeof(void*)*3, x_48);
lean_ctor_set_float(x_49, sizeof(void*)*3 + 8, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 16, x_2);
if (x_37 == 0)
{
lean_dec_ref(x_47);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_3);
lean_dec(x_1);
x_18 = x_45;
x_19 = x_38;
x_20 = x_49;
goto block_31;
}
else
{
lean_object* x_50; double x_51; double x_52; 
lean_dec_ref(x_49);
x_50 = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_3);
x_51 = lean_unbox_float(x_32);
lean_dec(x_32);
lean_ctor_set_float(x_50, sizeof(void*)*3, x_51);
x_52 = lean_unbox_float(x_33);
lean_dec(x_33);
lean_ctor_set_float(x_50, sizeof(void*)*3 + 8, x_52);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 16, x_2);
x_18 = x_45;
x_19 = x_38;
x_20 = x_50;
goto block_31;
}
}
}
}
block_62:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_11, 5);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_14);
x_59 = lean_apply_6(x_7, x_14, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc(x_58);
x_38 = x_58;
x_39 = x_60;
goto block_57;
}
else
{
lean_object* x_61; 
lean_dec_ref(x_59);
x_61 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8___closed__4);
lean_inc(x_58);
x_38 = x_58;
x_39 = x_61;
goto block_57;
}
}
block_93:
{
if (x_5 == 0)
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_92; 
lean_del_object(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_del_object(x_16);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_64 = lean_st_ref_take(x_12);
x_65 = lean_ctor_get(x_64, 4);
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
x_68 = lean_ctor_get(x_64, 2);
x_69 = lean_ctor_get(x_64, 3);
x_70 = lean_ctor_get(x_64, 5);
x_71 = lean_ctor_get(x_64, 6);
x_72 = lean_ctor_get(x_64, 7);
x_73 = lean_ctor_get(x_64, 8);
x_92 = !lean_is_exclusive(x_64);
if (x_92 == 0)
{
x_74 = x_64;
x_75 = x_92;
goto block_91;
}
else
{
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_65);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_74 = lean_box(0);
x_75 = x_92;
goto block_91;
}
block_91:
{
uint64_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_90; 
x_76 = lean_ctor_get_uint64(x_65, sizeof(void*)*1);
x_77 = lean_ctor_get(x_65, 0);
x_90 = !lean_is_exclusive(x_65);
if (x_90 == 0)
{
x_78 = x_65;
x_79 = x_90;
goto block_89;
}
else
{
lean_inc(x_77);
lean_dec(x_65);
x_78 = lean_box(0);
x_79 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_PersistentArray_append___redArg(x_6, x_77);
lean_dec_ref(x_77);
if (x_79 == 0)
{
lean_ctor_set(x_78, 0, x_80);
x_81 = x_78;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set_uint64(x_88, sizeof(void*)*1, x_76);
x_81 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_82; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 4, x_81);
x_82 = x_74;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_86, 0, x_66);
lean_ctor_set(x_86, 1, x_67);
lean_ctor_set(x_86, 2, x_68);
lean_ctor_set(x_86, 3, x_69);
lean_ctor_set(x_86, 4, x_81);
lean_ctor_set(x_86, 5, x_70);
lean_ctor_set(x_86, 6, x_71);
lean_ctor_set(x_86, 7, x_72);
lean_ctor_set(x_86, 8, x_73);
x_82 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_st_ref_set(x_12, x_82);
lean_dec(x_12);
x_84 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(x_14);
return x_84;
}
}
}
}
}
else
{
goto block_62;
}
}
else
{
goto block_62;
}
}
block_99:
{
double x_95; double x_96; double x_97; uint8_t x_98; 
x_95 = lean_unbox_float(x_33);
x_96 = lean_unbox_float(x_32);
x_97 = lean_float_sub(x_95, x_96);
x_98 = lean_float_decLt(x_94, x_97);
x_63 = x_98;
goto block_93;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_5);
x_16 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_19; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(x_8, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
x_11 = x_9;
x_12 = x_19;
goto block_18;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_14);
x_15 = x_11;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_197; uint8_t x_198; 
x_197 = lean_unsigned_to_nat(0u);
x_198 = lean_nat_dec_eq(x_5, x_197);
if (x_198 == 1)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_199 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
x_200 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_199, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_224; uint8_t x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_240; uint8_t x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_330; uint8_t x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; uint8_t x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_470; uint8_t x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; lean_object* x_493; uint8_t x_494; uint8_t x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; uint8_t x_521; lean_object* x_522; lean_object* x_523; uint8_t x_524; lean_object* x_565; uint8_t x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; uint8_t x_573; lean_object* x_574; lean_object* x_575; lean_object* x_585; uint8_t x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; uint8_t x_592; uint8_t x_593; lean_object* x_594; lean_object* x_595; uint8_t x_608; uint8_t x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; uint8_t x_616; lean_object* x_617; lean_object* x_618; uint8_t x_628; uint8_t x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; uint8_t x_636; lean_object* x_637; lean_object* x_638; uint8_t x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; uint8_t x_658; uint8_t x_659; lean_object* x_660; lean_object* x_661; uint8_t x_662; uint8_t x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; uint8_t x_708; lean_object* x_709; uint8_t x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; uint8_t x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; lean_object* x_730; uint8_t x_731; lean_object* x_732; lean_object* x_733; uint8_t x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; lean_object* x_752; uint8_t x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; uint8_t x_757; lean_object* x_798; uint8_t x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; lean_object* x_803; lean_object* x_804; lean_object* x_817; uint8_t x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; uint8_t x_822; lean_object* x_823; lean_object* x_833; uint8_t x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; uint8_t x_838; lean_object* x_839; uint8_t x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; uint8_t x_857; lean_object* x_858; lean_object* x_868; uint8_t x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; uint8_t x_873; lean_object* x_874; lean_object* x_916; lean_object* x_917; uint8_t x_918; lean_object* x_919; lean_object* x_920; uint8_t x_921; lean_object* x_922; uint8_t x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; uint8_t x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; uint8_t x_972; uint8_t x_1000; uint8_t x_1001; uint8_t x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; uint8_t x_1009; uint8_t x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; uint8_t x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; uint8_t x_1061; uint8_t x_1062; lean_object* x_1087; uint8_t x_1088; uint8_t x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; uint8_t x_1093; lean_object* x_1094; lean_object* x_1095; uint8_t x_1096; uint8_t x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; uint8_t x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; uint8_t x_1148; uint8_t x_1149; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; uint8_t x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; uint8_t x_1183; lean_object* x_1184; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; uint8_t x_1234; lean_object* x_1252; lean_object* x_1357; lean_object* x_1368; 
x_201 = lean_ctor_get(x_1, 1);
x_202 = lean_ctor_get(x_1, 2);
x_203 = lean_ctor_get(x_1, 3);
x_204 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
x_288 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
x_330 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
x_426 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
x_916 = lean_unsigned_to_nat(1u);
x_917 = lean_nat_sub(x_5, x_916);
lean_dec(x_5);
lean_inc_ref(x_201);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_1368 = lean_apply_7(x_201, x_4, x_6, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1368) == 0)
{
lean_object* x_1369; 
x_1369 = lean_ctor_get(x_1368, 0);
lean_inc(x_1369);
lean_dec_ref(x_1368);
x_1252 = x_1369;
goto block_1356;
}
else
{
lean_object* x_1370; lean_object* x_1371; uint8_t x_1372; uint8_t x_1442; 
x_1370 = lean_ctor_get(x_1368, 0);
x_1442 = !lean_is_exclusive(x_1368);
if (x_1442 == 0)
{
x_1371 = x_1368;
x_1372 = x_1442;
goto block_1441;
}
else
{
lean_inc(x_1370);
lean_dec(x_1368);
x_1371 = lean_box(0);
x_1372 = x_1442;
goto block_1441;
}
block_1441:
{
lean_object* x_1373; lean_object* x_1374; uint8_t x_1375; lean_object* x_1376; uint8_t x_1377; uint8_t x_1414; uint8_t x_1439; 
lean_inc(x_1370);
x_1373 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(x_1373, 0, x_1370);
x_1439 = l_Lean_Exception_isInterrupt(x_1370);
if (x_1439 == 0)
{
uint8_t x_1440; 
lean_inc(x_1370);
x_1440 = l_Lean_Exception_isRuntime(x_1370);
x_1414 = x_1440;
goto block_1438;
}
else
{
x_1414 = x_1439;
goto block_1438;
}
block_1413:
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; uint8_t x_1381; uint8_t x_1412; 
x_1378 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
x_1379 = lean_ctor_get(x_1378, 0);
x_1412 = !lean_is_exclusive(x_1378);
if (x_1412 == 0)
{
x_1380 = x_1378;
x_1381 = x_1412;
goto block_1411;
}
else
{
lean_inc(x_1379);
lean_dec(x_1378);
x_1380 = lean_box(0);
x_1381 = x_1412;
goto block_1411;
}
block_1411:
{
lean_object* x_1382; uint8_t x_1383; 
x_1382 = l_Lean_trace_profiler_useHeartbeats;
x_1383 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1374, x_1382);
if (x_1383 == 0)
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1384 = lean_io_mono_nanos_now();
x_1385 = lean_io_mono_nanos_now();
if (x_1381 == 0)
{
lean_ctor_set(x_1380, 0, x_1370);
x_1386 = x_1380;
goto block_1397;
}
else
{
lean_object* x_1398; 
x_1398 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1398, 0, x_1370);
x_1386 = x_1398;
goto block_1397;
}
block_1397:
{
double x_1387; double x_1388; double x_1389; double x_1390; double x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; 
x_1387 = lean_float_of_nat(x_1384);
x_1388 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_1389 = lean_float_div(x_1387, x_1388);
x_1390 = lean_float_of_nat(x_1385);
x_1391 = lean_float_div(x_1390, x_1388);
x_1392 = lean_box_float(x_1389);
x_1393 = lean_box_float(x_1391);
x_1394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1394, 0, x_1392);
lean_ctor_set(x_1394, 1, x_1393);
x_1395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1395, 0, x_1386);
lean_ctor_set(x_1395, 1, x_1394);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1396 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(x_2, x_1375, x_1376, x_1374, x_1377, x_1379, x_1373, x_1395, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1374);
x_1357 = x_1396;
goto block_1367;
}
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
x_1399 = lean_io_get_num_heartbeats();
x_1400 = lean_io_get_num_heartbeats();
if (x_1381 == 0)
{
lean_ctor_set(x_1380, 0, x_1370);
x_1401 = x_1380;
goto block_1409;
}
else
{
lean_object* x_1410; 
x_1410 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1410, 0, x_1370);
x_1401 = x_1410;
goto block_1409;
}
block_1409:
{
double x_1402; double x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; 
x_1402 = lean_float_of_nat(x_1399);
x_1403 = lean_float_of_nat(x_1400);
x_1404 = lean_box_float(x_1402);
x_1405 = lean_box_float(x_1403);
x_1406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1406, 0, x_1404);
lean_ctor_set(x_1406, 1, x_1405);
x_1407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1407, 0, x_1401);
lean_ctor_set(x_1407, 1, x_1406);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1408 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__8(x_2, x_1375, x_1376, x_1374, x_1377, x_1379, x_1373, x_1407, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1374);
x_1357 = x_1408;
goto block_1367;
}
}
}
}
block_1438:
{
if (x_1414 == 0)
{
lean_object* x_1415; uint8_t x_1416; 
x_1415 = lean_ctor_get(x_10, 2);
x_1416 = lean_ctor_get_uint8(x_1415, sizeof(void*)*1);
if (x_1416 == 0)
{
lean_object* x_1417; 
lean_dec_ref(x_1373);
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
if (x_1372 == 0)
{
x_1417 = x_1371;
goto block_1418;
}
else
{
lean_object* x_1419; 
x_1419 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1419, 0, x_1370);
x_1417 = x_1419;
goto block_1418;
}
block_1418:
{
return x_1417;
}
}
else
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; uint8_t x_1423; uint8_t x_1434; 
lean_del_object(x_1371);
lean_inc(x_2);
x_1420 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1421 = lean_ctor_get(x_1420, 0);
x_1434 = !lean_is_exclusive(x_1420);
if (x_1434 == 0)
{
x_1422 = x_1420;
x_1423 = x_1434;
goto block_1433;
}
else
{
lean_inc(x_1421);
lean_dec(x_1420);
x_1422 = lean_box(0);
x_1423 = x_1434;
goto block_1433;
}
block_1433:
{
lean_object* x_1424; uint8_t x_1425; 
x_1424 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1425 = lean_unbox(x_1421);
if (x_1425 == 0)
{
lean_object* x_1426; uint8_t x_1427; 
x_1426 = l_Lean_trace_profiler;
x_1427 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1415, x_1426);
if (x_1427 == 0)
{
lean_object* x_1428; 
lean_dec(x_1421);
lean_dec_ref(x_1373);
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
if (x_1423 == 0)
{
lean_ctor_set_tag(x_1422, 1);
lean_ctor_set(x_1422, 0, x_1370);
x_1428 = x_1422;
goto block_1429;
}
else
{
lean_object* x_1430; 
x_1430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1430, 0, x_1370);
x_1428 = x_1430;
goto block_1429;
}
block_1429:
{
return x_1428;
}
}
else
{
uint8_t x_1431; 
lean_del_object(x_1422);
x_1431 = lean_unbox(x_1421);
lean_dec(x_1421);
lean_inc_ref(x_1415);
x_1374 = x_1415;
x_1375 = x_1416;
x_1376 = x_1424;
x_1377 = x_1431;
goto block_1413;
}
}
else
{
uint8_t x_1432; 
lean_del_object(x_1422);
x_1432 = lean_unbox(x_1421);
lean_dec(x_1421);
lean_inc_ref(x_1415);
x_1374 = x_1415;
x_1375 = x_1416;
x_1376 = x_1424;
x_1377 = x_1432;
goto block_1413;
}
}
}
}
else
{
lean_object* x_1435; 
lean_dec_ref(x_1373);
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
if (x_1372 == 0)
{
x_1435 = x_1371;
goto block_1436;
}
else
{
lean_object* x_1437; 
x_1437 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1437, 0, x_1370);
x_1435 = x_1437;
goto block_1436;
}
block_1436:
{
return x_1435;
}
}
}
}
}
block_223:
{
lean_object* x_212; double x_213; double x_214; double x_215; double x_216; double x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_212 = lean_io_mono_nanos_now();
x_213 = lean_float_of_nat(x_210);
x_214 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_215 = lean_float_div(x_213, x_214);
x_216 = lean_float_of_nat(x_212);
x_217 = lean_float_div(x_216, x_214);
x_218 = lean_box_float(x_215);
x_219 = lean_box_float(x_217);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_211);
lean_ctor_set(x_221, 1, x_220);
x_222 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_206, x_209, x_208, x_207, x_205, x_204, x_221, x_8, x_9, x_10, x_11);
lean_dec_ref(x_208);
return x_222;
}
block_239:
{
lean_object* x_231; double x_232; double x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_231 = lean_io_get_num_heartbeats();
x_232 = lean_float_of_nat(x_229);
x_233 = lean_float_of_nat(x_231);
x_234 = lean_box_float(x_232);
x_235 = lean_box_float(x_233);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_230);
lean_ctor_set(x_237, 1, x_236);
x_238 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_225, x_228, x_227, x_226, x_224, x_204, x_237, x_8, x_9, x_10, x_11);
lean_dec_ref(x_227);
return x_238;
}
block_287:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_247 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_dec_ref(x_247);
x_249 = l_Lean_trace_profiler_useHeartbeats;
x_250 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_245, x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_io_mono_nanos_now();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_252 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_243, x_240, x_244, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; uint8_t x_260; 
x_253 = lean_ctor_get(x_252, 0);
x_260 = !lean_is_exclusive(x_252);
if (x_260 == 0)
{
x_254 = x_252;
x_255 = x_260;
goto block_259;
}
else
{
lean_inc(x_253);
lean_dec(x_252);
x_254 = lean_box(0);
x_255 = x_260;
goto block_259;
}
block_259:
{
lean_object* x_256; 
if (x_255 == 0)
{
lean_ctor_set_tag(x_254, 1);
x_256 = x_254;
goto block_257;
}
else
{
lean_object* x_258; 
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_253);
x_256 = x_258;
goto block_257;
}
block_257:
{
x_205 = x_248;
x_206 = x_241;
x_207 = x_242;
x_208 = x_245;
x_209 = x_246;
x_210 = x_251;
x_211 = x_256;
goto block_223;
}
}
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_268; 
x_261 = lean_ctor_get(x_252, 0);
x_268 = !lean_is_exclusive(x_252);
if (x_268 == 0)
{
x_262 = x_252;
x_263 = x_268;
goto block_267;
}
else
{
lean_inc(x_261);
lean_dec(x_252);
x_262 = lean_box(0);
x_263 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_264; 
if (x_263 == 0)
{
lean_ctor_set_tag(x_262, 0);
x_264 = x_262;
goto block_265;
}
else
{
lean_object* x_266; 
x_266 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_266, 0, x_261);
x_264 = x_266;
goto block_265;
}
block_265:
{
x_205 = x_248;
x_206 = x_241;
x_207 = x_242;
x_208 = x_245;
x_209 = x_246;
x_210 = x_251;
x_211 = x_264;
goto block_223;
}
}
}
}
else
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_io_get_num_heartbeats();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_270 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_243, x_240, x_244, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_278; 
x_271 = lean_ctor_get(x_270, 0);
x_278 = !lean_is_exclusive(x_270);
if (x_278 == 0)
{
x_272 = x_270;
x_273 = x_278;
goto block_277;
}
else
{
lean_inc(x_271);
lean_dec(x_270);
x_272 = lean_box(0);
x_273 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_274; 
if (x_273 == 0)
{
lean_ctor_set_tag(x_272, 1);
x_274 = x_272;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_271);
x_274 = x_276;
goto block_275;
}
block_275:
{
x_224 = x_248;
x_225 = x_241;
x_226 = x_242;
x_227 = x_245;
x_228 = x_246;
x_229 = x_269;
x_230 = x_274;
goto block_239;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; uint8_t x_281; uint8_t x_286; 
x_279 = lean_ctor_get(x_270, 0);
x_286 = !lean_is_exclusive(x_270);
if (x_286 == 0)
{
x_280 = x_270;
x_281 = x_286;
goto block_285;
}
else
{
lean_inc(x_279);
lean_dec(x_270);
x_280 = lean_box(0);
x_281 = x_286;
goto block_285;
}
block_285:
{
lean_object* x_282; 
if (x_281 == 0)
{
lean_ctor_set_tag(x_280, 0);
x_282 = x_280;
goto block_283;
}
else
{
lean_object* x_284; 
x_284 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_284, 0, x_279);
x_282 = x_284;
goto block_283;
}
block_283:
{
x_224 = x_248;
x_225 = x_241;
x_226 = x_242;
x_227 = x_245;
x_228 = x_246;
x_229 = x_269;
x_230 = x_282;
goto block_239;
}
}
}
}
}
block_329:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; uint8_t x_328; 
x_294 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
x_295 = lean_ctor_get(x_294, 0);
x_328 = !lean_is_exclusive(x_294);
if (x_328 == 0)
{
x_296 = x_294;
x_297 = x_328;
goto block_327;
}
else
{
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_box(0);
x_297 = x_328;
goto block_327;
}
block_327:
{
lean_object* x_298; uint8_t x_299; 
x_298 = l_Lean_trace_profiler_useHeartbeats;
x_299 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_292, x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_io_mono_nanos_now();
x_301 = lean_io_mono_nanos_now();
if (x_297 == 0)
{
lean_ctor_set_tag(x_296, 1);
lean_ctor_set(x_296, 0, x_290);
x_302 = x_296;
goto block_313;
}
else
{
lean_object* x_314; 
x_314 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_314, 0, x_290);
x_302 = x_314;
goto block_313;
}
block_313:
{
double x_303; double x_304; double x_305; double x_306; double x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_303 = lean_float_of_nat(x_300);
x_304 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_305 = lean_float_div(x_303, x_304);
x_306 = lean_float_of_nat(x_301);
x_307 = lean_float_div(x_306, x_304);
x_308 = lean_box_float(x_305);
x_309 = lean_box_float(x_307);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_302);
lean_ctor_set(x_311, 1, x_310);
x_312 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_293, x_291, x_292, x_289, x_295, x_288, x_311, x_8, x_9, x_10, x_11);
lean_dec_ref(x_292);
return x_312;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_io_get_num_heartbeats();
x_316 = lean_io_get_num_heartbeats();
if (x_297 == 0)
{
lean_ctor_set_tag(x_296, 1);
lean_ctor_set(x_296, 0, x_290);
x_317 = x_296;
goto block_325;
}
else
{
lean_object* x_326; 
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_290);
x_317 = x_326;
goto block_325;
}
block_325:
{
double x_318; double x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_318 = lean_float_of_nat(x_315);
x_319 = lean_float_of_nat(x_316);
x_320 = lean_box_float(x_318);
x_321 = lean_box_float(x_319);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_317);
lean_ctor_set(x_323, 1, x_322);
x_324 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_293, x_291, x_292, x_289, x_295, x_288, x_323, x_8, x_9, x_10, x_11);
lean_dec_ref(x_292);
return x_324;
}
}
}
}
block_350:
{
lean_object* x_342; double x_343; double x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_342 = lean_io_get_num_heartbeats();
x_343 = lean_float_of_nat(x_338);
x_344 = lean_float_of_nat(x_342);
x_345 = lean_box_float(x_343);
x_346 = lean_box_float(x_344);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_341);
lean_ctor_set(x_348, 1, x_347);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_336);
lean_inc(x_2);
x_349 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_332, x_336, x_334, x_331, x_335, x_330, x_348, x_8, x_9, x_10, x_11);
x_135 = x_332;
x_136 = x_333;
x_137 = x_334;
x_138 = x_336;
x_139 = x_337;
x_140 = x_340;
x_141 = x_339;
x_142 = x_349;
goto block_145;
}
block_373:
{
lean_object* x_362; double x_363; double x_364; double x_365; double x_366; double x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_362 = lean_io_mono_nanos_now();
x_363 = lean_float_of_nat(x_354);
x_364 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_365 = lean_float_div(x_363, x_364);
x_366 = lean_float_of_nat(x_362);
x_367 = lean_float_div(x_366, x_364);
x_368 = lean_box_float(x_365);
x_369 = lean_box_float(x_367);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_361);
lean_ctor_set(x_371, 1, x_370);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_357);
lean_inc(x_2);
x_372 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_352, x_357, x_355, x_351, x_356, x_330, x_371, x_8, x_9, x_10, x_11);
x_135 = x_352;
x_136 = x_353;
x_137 = x_355;
x_138 = x_357;
x_139 = x_358;
x_140 = x_360;
x_141 = x_359;
x_142 = x_372;
goto block_145;
}
block_425:
{
lean_object* x_386; 
x_386 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
if (x_382 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
lean_dec_ref(x_386);
x_388 = lean_io_mono_nanos_now();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_389 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_376, x_381, x_374, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; uint8_t x_397; 
x_390 = lean_ctor_get(x_389, 0);
x_397 = !lean_is_exclusive(x_389);
if (x_397 == 0)
{
x_391 = x_389;
x_392 = x_397;
goto block_396;
}
else
{
lean_inc(x_390);
lean_dec(x_389);
x_391 = lean_box(0);
x_392 = x_397;
goto block_396;
}
block_396:
{
lean_object* x_393; 
if (x_392 == 0)
{
lean_ctor_set_tag(x_391, 1);
x_393 = x_391;
goto block_394;
}
else
{
lean_object* x_395; 
x_395 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_395, 0, x_390);
x_393 = x_395;
goto block_394;
}
block_394:
{
x_351 = x_380;
x_352 = x_375;
x_353 = x_383;
x_354 = x_388;
x_355 = x_384;
x_356 = x_387;
x_357 = x_377;
x_358 = x_378;
x_359 = x_385;
x_360 = x_379;
x_361 = x_393;
goto block_373;
}
}
}
else
{
lean_object* x_398; lean_object* x_399; uint8_t x_400; uint8_t x_405; 
x_398 = lean_ctor_get(x_389, 0);
x_405 = !lean_is_exclusive(x_389);
if (x_405 == 0)
{
x_399 = x_389;
x_400 = x_405;
goto block_404;
}
else
{
lean_inc(x_398);
lean_dec(x_389);
x_399 = lean_box(0);
x_400 = x_405;
goto block_404;
}
block_404:
{
lean_object* x_401; 
if (x_400 == 0)
{
lean_ctor_set_tag(x_399, 0);
x_401 = x_399;
goto block_402;
}
else
{
lean_object* x_403; 
x_403 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_403, 0, x_398);
x_401 = x_403;
goto block_402;
}
block_402:
{
x_351 = x_380;
x_352 = x_375;
x_353 = x_383;
x_354 = x_388;
x_355 = x_384;
x_356 = x_387;
x_357 = x_377;
x_358 = x_378;
x_359 = x_385;
x_360 = x_379;
x_361 = x_401;
goto block_373;
}
}
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_386, 0);
lean_inc(x_406);
lean_dec_ref(x_386);
x_407 = lean_io_get_num_heartbeats();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_408 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_376, x_381, x_374, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; uint8_t x_411; uint8_t x_416; 
x_409 = lean_ctor_get(x_408, 0);
x_416 = !lean_is_exclusive(x_408);
if (x_416 == 0)
{
x_410 = x_408;
x_411 = x_416;
goto block_415;
}
else
{
lean_inc(x_409);
lean_dec(x_408);
x_410 = lean_box(0);
x_411 = x_416;
goto block_415;
}
block_415:
{
lean_object* x_412; 
if (x_411 == 0)
{
lean_ctor_set_tag(x_410, 1);
x_412 = x_410;
goto block_413;
}
else
{
lean_object* x_414; 
x_414 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_414, 0, x_409);
x_412 = x_414;
goto block_413;
}
block_413:
{
x_331 = x_380;
x_332 = x_375;
x_333 = x_383;
x_334 = x_384;
x_335 = x_406;
x_336 = x_377;
x_337 = x_378;
x_338 = x_407;
x_339 = x_385;
x_340 = x_379;
x_341 = x_412;
goto block_350;
}
}
}
else
{
lean_object* x_417; lean_object* x_418; uint8_t x_419; uint8_t x_424; 
x_417 = lean_ctor_get(x_408, 0);
x_424 = !lean_is_exclusive(x_408);
if (x_424 == 0)
{
x_418 = x_408;
x_419 = x_424;
goto block_423;
}
else
{
lean_inc(x_417);
lean_dec(x_408);
x_418 = lean_box(0);
x_419 = x_424;
goto block_423;
}
block_423:
{
lean_object* x_420; 
if (x_419 == 0)
{
lean_ctor_set_tag(x_418, 0);
x_420 = x_418;
goto block_421;
}
else
{
lean_object* x_422; 
x_422 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_422, 0, x_417);
x_420 = x_422;
goto block_421;
}
block_421:
{
x_331 = x_380;
x_332 = x_375;
x_333 = x_383;
x_334 = x_384;
x_335 = x_406;
x_336 = x_377;
x_337 = x_378;
x_338 = x_407;
x_339 = x_385;
x_340 = x_379;
x_341 = x_420;
goto block_350;
}
}
}
}
}
block_449:
{
lean_object* x_438; double x_439; double x_440; double x_441; double x_442; double x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_438 = lean_io_mono_nanos_now();
x_439 = lean_float_of_nat(x_428);
x_440 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_441 = lean_float_div(x_439, x_440);
x_442 = lean_float_of_nat(x_438);
x_443 = lean_float_div(x_442, x_440);
x_444 = lean_box_float(x_441);
x_445 = lean_box_float(x_443);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_437);
lean_ctor_set(x_447, 1, x_446);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_432);
lean_inc(x_2);
x_448 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_429, x_432, x_431, x_427, x_436, x_426, x_447, x_8, x_9, x_10, x_11);
x_135 = x_429;
x_136 = x_430;
x_137 = x_431;
x_138 = x_432;
x_139 = x_433;
x_140 = x_435;
x_141 = x_434;
x_142 = x_448;
goto block_145;
}
block_469:
{
lean_object* x_461; double x_462; double x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_461 = lean_io_get_num_heartbeats();
x_462 = lean_float_of_nat(x_459);
x_463 = lean_float_of_nat(x_461);
x_464 = lean_box_float(x_462);
x_465 = lean_box_float(x_463);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
x_467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_467, 0, x_460);
lean_ctor_set(x_467, 1, x_466);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_454);
lean_inc(x_2);
x_468 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_451, x_454, x_453, x_450, x_458, x_426, x_467, x_8, x_9, x_10, x_11);
x_135 = x_451;
x_136 = x_452;
x_137 = x_453;
x_138 = x_454;
x_139 = x_455;
x_140 = x_457;
x_141 = x_456;
x_142 = x_468;
goto block_145;
}
block_492:
{
lean_object* x_481; double x_482; double x_483; double x_484; double x_485; double x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_481 = lean_io_mono_nanos_now();
x_482 = lean_float_of_nat(x_473);
x_483 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_484 = lean_float_div(x_482, x_483);
x_485 = lean_float_of_nat(x_481);
x_486 = lean_float_div(x_485, x_483);
x_487 = lean_box_float(x_484);
x_488 = lean_box_float(x_486);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_480);
lean_ctor_set(x_490, 1, x_489);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_476);
lean_inc(x_2);
x_491 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_472, x_476, x_474, x_471, x_470, x_204, x_490, x_8, x_9, x_10, x_11);
x_186 = x_472;
x_187 = x_474;
x_188 = x_476;
x_189 = x_475;
x_190 = x_477;
x_191 = x_479;
x_192 = x_478;
x_193 = x_491;
goto block_196;
}
block_512:
{
lean_object* x_504; double x_505; double x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_504 = lean_io_get_num_heartbeats();
x_505 = lean_float_of_nat(x_502);
x_506 = lean_float_of_nat(x_504);
x_507 = lean_box_float(x_505);
x_508 = lean_box_float(x_506);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_503);
lean_ctor_set(x_510, 1, x_509);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_498);
lean_inc(x_2);
x_511 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_495, x_498, x_496, x_494, x_493, x_204, x_510, x_8, x_9, x_10, x_11);
x_186 = x_495;
x_187 = x_496;
x_188 = x_498;
x_189 = x_497;
x_190 = x_499;
x_191 = x_501;
x_192 = x_500;
x_193 = x_511;
goto block_196;
}
block_564:
{
lean_object* x_525; 
x_525 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
if (x_521 == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
lean_dec_ref(x_525);
x_527 = lean_io_mono_nanos_now();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_528 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_523, x_519, x_514, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; uint8_t x_536; 
x_529 = lean_ctor_get(x_528, 0);
x_536 = !lean_is_exclusive(x_528);
if (x_536 == 0)
{
x_530 = x_528;
x_531 = x_536;
goto block_535;
}
else
{
lean_inc(x_529);
lean_dec(x_528);
x_530 = lean_box(0);
x_531 = x_536;
goto block_535;
}
block_535:
{
lean_object* x_532; 
if (x_531 == 0)
{
lean_ctor_set_tag(x_530, 1);
x_532 = x_530;
goto block_533;
}
else
{
lean_object* x_534; 
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_529);
x_532 = x_534;
goto block_533;
}
block_533:
{
x_470 = x_526;
x_471 = x_520;
x_472 = x_513;
x_473 = x_527;
x_474 = x_522;
x_475 = x_515;
x_476 = x_516;
x_477 = x_517;
x_478 = x_524;
x_479 = x_518;
x_480 = x_532;
goto block_492;
}
}
}
else
{
lean_object* x_537; lean_object* x_538; uint8_t x_539; uint8_t x_544; 
x_537 = lean_ctor_get(x_528, 0);
x_544 = !lean_is_exclusive(x_528);
if (x_544 == 0)
{
x_538 = x_528;
x_539 = x_544;
goto block_543;
}
else
{
lean_inc(x_537);
lean_dec(x_528);
x_538 = lean_box(0);
x_539 = x_544;
goto block_543;
}
block_543:
{
lean_object* x_540; 
if (x_539 == 0)
{
lean_ctor_set_tag(x_538, 0);
x_540 = x_538;
goto block_541;
}
else
{
lean_object* x_542; 
x_542 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_542, 0, x_537);
x_540 = x_542;
goto block_541;
}
block_541:
{
x_470 = x_526;
x_471 = x_520;
x_472 = x_513;
x_473 = x_527;
x_474 = x_522;
x_475 = x_515;
x_476 = x_516;
x_477 = x_517;
x_478 = x_524;
x_479 = x_518;
x_480 = x_540;
goto block_492;
}
}
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_545 = lean_ctor_get(x_525, 0);
lean_inc(x_545);
lean_dec_ref(x_525);
x_546 = lean_io_get_num_heartbeats();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_547 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_523, x_519, x_514, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; uint8_t x_550; uint8_t x_555; 
x_548 = lean_ctor_get(x_547, 0);
x_555 = !lean_is_exclusive(x_547);
if (x_555 == 0)
{
x_549 = x_547;
x_550 = x_555;
goto block_554;
}
else
{
lean_inc(x_548);
lean_dec(x_547);
x_549 = lean_box(0);
x_550 = x_555;
goto block_554;
}
block_554:
{
lean_object* x_551; 
if (x_550 == 0)
{
lean_ctor_set_tag(x_549, 1);
x_551 = x_549;
goto block_552;
}
else
{
lean_object* x_553; 
x_553 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_553, 0, x_548);
x_551 = x_553;
goto block_552;
}
block_552:
{
x_493 = x_545;
x_494 = x_520;
x_495 = x_513;
x_496 = x_522;
x_497 = x_515;
x_498 = x_516;
x_499 = x_517;
x_500 = x_524;
x_501 = x_518;
x_502 = x_546;
x_503 = x_551;
goto block_512;
}
}
}
else
{
lean_object* x_556; lean_object* x_557; uint8_t x_558; uint8_t x_563; 
x_556 = lean_ctor_get(x_547, 0);
x_563 = !lean_is_exclusive(x_547);
if (x_563 == 0)
{
x_557 = x_547;
x_558 = x_563;
goto block_562;
}
else
{
lean_inc(x_556);
lean_dec(x_547);
x_557 = lean_box(0);
x_558 = x_563;
goto block_562;
}
block_562:
{
lean_object* x_559; 
if (x_558 == 0)
{
lean_ctor_set_tag(x_557, 0);
x_559 = x_557;
goto block_560;
}
else
{
lean_object* x_561; 
x_561 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_561, 0, x_556);
x_559 = x_561;
goto block_560;
}
block_560:
{
x_493 = x_545;
x_494 = x_520;
x_495 = x_513;
x_496 = x_522;
x_497 = x_515;
x_498 = x_516;
x_499 = x_517;
x_500 = x_524;
x_501 = x_518;
x_502 = x_546;
x_503 = x_559;
goto block_512;
}
}
}
}
}
block_584:
{
lean_object* x_576; double x_577; double x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_576 = lean_io_get_num_heartbeats();
x_577 = lean_float_of_nat(x_567);
x_578 = lean_float_of_nat(x_576);
x_579 = lean_box_float(x_577);
x_580 = lean_box_float(x_578);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_575);
lean_ctor_set(x_582, 1, x_581);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_570);
lean_inc(x_2);
x_583 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_566, x_570, x_568, x_572, x_565, x_426, x_582, x_8, x_9, x_10, x_11);
x_186 = x_566;
x_187 = x_568;
x_188 = x_570;
x_189 = x_569;
x_190 = x_571;
x_191 = x_574;
x_192 = x_573;
x_193 = x_583;
goto block_196;
}
block_607:
{
lean_object* x_596; double x_597; double x_598; double x_599; double x_600; double x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_596 = lean_io_mono_nanos_now();
x_597 = lean_float_of_nat(x_590);
x_598 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_599 = lean_float_div(x_597, x_598);
x_600 = lean_float_of_nat(x_596);
x_601 = lean_float_div(x_600, x_598);
x_602 = lean_box_float(x_599);
x_603 = lean_box_float(x_601);
x_604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
x_605 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_605, 0, x_595);
lean_ctor_set(x_605, 1, x_604);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_589);
lean_inc(x_2);
x_606 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_586, x_589, x_587, x_592, x_585, x_426, x_605, x_8, x_9, x_10, x_11);
x_186 = x_586;
x_187 = x_587;
x_188 = x_589;
x_189 = x_588;
x_190 = x_591;
x_191 = x_594;
x_192 = x_593;
x_193 = x_606;
goto block_196;
}
block_627:
{
lean_object* x_619; double x_620; double x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_619 = lean_io_get_num_heartbeats();
x_620 = lean_float_of_nat(x_614);
x_621 = lean_float_of_nat(x_619);
x_622 = lean_box_float(x_620);
x_623 = lean_box_float(x_621);
x_624 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_624, 0, x_622);
lean_ctor_set(x_624, 1, x_623);
x_625 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_625, 0, x_618);
lean_ctor_set(x_625, 1, x_624);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_613);
lean_inc(x_2);
x_626 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_608, x_613, x_611, x_609, x_610, x_330, x_625, x_8, x_9, x_10, x_11);
x_186 = x_608;
x_187 = x_611;
x_188 = x_613;
x_189 = x_612;
x_190 = x_615;
x_191 = x_617;
x_192 = x_616;
x_193 = x_626;
goto block_196;
}
block_650:
{
lean_object* x_639; double x_640; double x_641; double x_642; double x_643; double x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_639 = lean_io_mono_nanos_now();
x_640 = lean_float_of_nat(x_635);
x_641 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_642 = lean_float_div(x_640, x_641);
x_643 = lean_float_of_nat(x_639);
x_644 = lean_float_div(x_643, x_641);
x_645 = lean_box_float(x_642);
x_646 = lean_box_float(x_644);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_645);
lean_ctor_set(x_647, 1, x_646);
x_648 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_648, 0, x_638);
lean_ctor_set(x_648, 1, x_647);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_633);
lean_inc(x_2);
x_649 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_628, x_633, x_631, x_629, x_630, x_330, x_648, x_8, x_9, x_10, x_11);
x_186 = x_628;
x_187 = x_631;
x_188 = x_633;
x_189 = x_632;
x_190 = x_634;
x_191 = x_637;
x_192 = x_636;
x_193 = x_649;
goto block_196;
}
block_702:
{
lean_object* x_663; 
x_663 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
if (x_658 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
lean_dec_ref(x_663);
x_665 = lean_io_mono_nanos_now();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_666 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_661, x_657, x_652, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; uint8_t x_669; uint8_t x_674; 
x_667 = lean_ctor_get(x_666, 0);
x_674 = !lean_is_exclusive(x_666);
if (x_674 == 0)
{
x_668 = x_666;
x_669 = x_674;
goto block_673;
}
else
{
lean_inc(x_667);
lean_dec(x_666);
x_668 = lean_box(0);
x_669 = x_674;
goto block_673;
}
block_673:
{
lean_object* x_670; 
if (x_669 == 0)
{
lean_ctor_set_tag(x_668, 1);
x_670 = x_668;
goto block_671;
}
else
{
lean_object* x_672; 
x_672 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_672, 0, x_667);
x_670 = x_672;
goto block_671;
}
block_671:
{
x_628 = x_651;
x_629 = x_659;
x_630 = x_664;
x_631 = x_660;
x_632 = x_653;
x_633 = x_654;
x_634 = x_655;
x_635 = x_665;
x_636 = x_662;
x_637 = x_656;
x_638 = x_670;
goto block_650;
}
}
}
else
{
lean_object* x_675; lean_object* x_676; uint8_t x_677; uint8_t x_682; 
x_675 = lean_ctor_get(x_666, 0);
x_682 = !lean_is_exclusive(x_666);
if (x_682 == 0)
{
x_676 = x_666;
x_677 = x_682;
goto block_681;
}
else
{
lean_inc(x_675);
lean_dec(x_666);
x_676 = lean_box(0);
x_677 = x_682;
goto block_681;
}
block_681:
{
lean_object* x_678; 
if (x_677 == 0)
{
lean_ctor_set_tag(x_676, 0);
x_678 = x_676;
goto block_679;
}
else
{
lean_object* x_680; 
x_680 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_680, 0, x_675);
x_678 = x_680;
goto block_679;
}
block_679:
{
x_628 = x_651;
x_629 = x_659;
x_630 = x_664;
x_631 = x_660;
x_632 = x_653;
x_633 = x_654;
x_634 = x_655;
x_635 = x_665;
x_636 = x_662;
x_637 = x_656;
x_638 = x_678;
goto block_650;
}
}
}
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_683 = lean_ctor_get(x_663, 0);
lean_inc(x_683);
lean_dec_ref(x_663);
x_684 = lean_io_get_num_heartbeats();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_685 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_661, x_657, x_652, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; uint8_t x_688; uint8_t x_693; 
x_686 = lean_ctor_get(x_685, 0);
x_693 = !lean_is_exclusive(x_685);
if (x_693 == 0)
{
x_687 = x_685;
x_688 = x_693;
goto block_692;
}
else
{
lean_inc(x_686);
lean_dec(x_685);
x_687 = lean_box(0);
x_688 = x_693;
goto block_692;
}
block_692:
{
lean_object* x_689; 
if (x_688 == 0)
{
lean_ctor_set_tag(x_687, 1);
x_689 = x_687;
goto block_690;
}
else
{
lean_object* x_691; 
x_691 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_691, 0, x_686);
x_689 = x_691;
goto block_690;
}
block_690:
{
x_608 = x_651;
x_609 = x_659;
x_610 = x_683;
x_611 = x_660;
x_612 = x_653;
x_613 = x_654;
x_614 = x_684;
x_615 = x_655;
x_616 = x_662;
x_617 = x_656;
x_618 = x_689;
goto block_627;
}
}
}
else
{
lean_object* x_694; lean_object* x_695; uint8_t x_696; uint8_t x_701; 
x_694 = lean_ctor_get(x_685, 0);
x_701 = !lean_is_exclusive(x_685);
if (x_701 == 0)
{
x_695 = x_685;
x_696 = x_701;
goto block_700;
}
else
{
lean_inc(x_694);
lean_dec(x_685);
x_695 = lean_box(0);
x_696 = x_701;
goto block_700;
}
block_700:
{
lean_object* x_697; 
if (x_696 == 0)
{
lean_ctor_set_tag(x_695, 0);
x_697 = x_695;
goto block_698;
}
else
{
lean_object* x_699; 
x_699 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_699, 0, x_694);
x_697 = x_699;
goto block_698;
}
block_698:
{
x_608 = x_651;
x_609 = x_659;
x_610 = x_683;
x_611 = x_660;
x_612 = x_653;
x_613 = x_654;
x_614 = x_684;
x_615 = x_655;
x_616 = x_662;
x_617 = x_656;
x_618 = x_697;
goto block_627;
}
}
}
}
}
block_722:
{
lean_object* x_714; double x_715; double x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_714 = lean_io_get_num_heartbeats();
x_715 = lean_float_of_nat(x_711);
x_716 = lean_float_of_nat(x_714);
x_717 = lean_box_float(x_715);
x_718 = lean_box_float(x_716);
x_719 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_713);
lean_ctor_set(x_720, 1, x_719);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_706);
lean_inc(x_2);
x_721 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_703, x_706, x_705, x_710, x_712, x_204, x_720, x_8, x_9, x_10, x_11);
x_135 = x_703;
x_136 = x_704;
x_137 = x_705;
x_138 = x_706;
x_139 = x_707;
x_140 = x_709;
x_141 = x_708;
x_142 = x_721;
goto block_145;
}
block_745:
{
lean_object* x_734; double x_735; double x_736; double x_737; double x_738; double x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_734 = lean_io_mono_nanos_now();
x_735 = lean_float_of_nat(x_726);
x_736 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_737 = lean_float_div(x_735, x_736);
x_738 = lean_float_of_nat(x_734);
x_739 = lean_float_div(x_738, x_736);
x_740 = lean_box_float(x_737);
x_741 = lean_box_float(x_739);
x_742 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_742, 0, x_740);
lean_ctor_set(x_742, 1, x_741);
x_743 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_743, 0, x_733);
lean_ctor_set(x_743, 1, x_742);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_727);
lean_inc(x_2);
x_744 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_723, x_727, x_725, x_731, x_732, x_204, x_743, x_8, x_9, x_10, x_11);
x_135 = x_723;
x_136 = x_724;
x_137 = x_725;
x_138 = x_727;
x_139 = x_728;
x_140 = x_730;
x_141 = x_729;
x_142 = x_744;
goto block_145;
}
block_797:
{
lean_object* x_758; 
x_758 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
if (x_753 == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
lean_dec_ref(x_758);
x_760 = lean_io_mono_nanos_now();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_761 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_755, x_752, x_749, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; lean_object* x_763; uint8_t x_764; uint8_t x_769; 
x_762 = lean_ctor_get(x_761, 0);
x_769 = !lean_is_exclusive(x_761);
if (x_769 == 0)
{
x_763 = x_761;
x_764 = x_769;
goto block_768;
}
else
{
lean_inc(x_762);
lean_dec(x_761);
x_763 = lean_box(0);
x_764 = x_769;
goto block_768;
}
block_768:
{
lean_object* x_765; 
if (x_764 == 0)
{
lean_ctor_set_tag(x_763, 1);
x_765 = x_763;
goto block_766;
}
else
{
lean_object* x_767; 
x_767 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_767, 0, x_762);
x_765 = x_767;
goto block_766;
}
block_766:
{
x_723 = x_746;
x_724 = x_754;
x_725 = x_756;
x_726 = x_760;
x_727 = x_747;
x_728 = x_748;
x_729 = x_757;
x_730 = x_750;
x_731 = x_751;
x_732 = x_759;
x_733 = x_765;
goto block_745;
}
}
}
else
{
lean_object* x_770; lean_object* x_771; uint8_t x_772; uint8_t x_777; 
x_770 = lean_ctor_get(x_761, 0);
x_777 = !lean_is_exclusive(x_761);
if (x_777 == 0)
{
x_771 = x_761;
x_772 = x_777;
goto block_776;
}
else
{
lean_inc(x_770);
lean_dec(x_761);
x_771 = lean_box(0);
x_772 = x_777;
goto block_776;
}
block_776:
{
lean_object* x_773; 
if (x_772 == 0)
{
lean_ctor_set_tag(x_771, 0);
x_773 = x_771;
goto block_774;
}
else
{
lean_object* x_775; 
x_775 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_775, 0, x_770);
x_773 = x_775;
goto block_774;
}
block_774:
{
x_723 = x_746;
x_724 = x_754;
x_725 = x_756;
x_726 = x_760;
x_727 = x_747;
x_728 = x_748;
x_729 = x_757;
x_730 = x_750;
x_731 = x_751;
x_732 = x_759;
x_733 = x_773;
goto block_745;
}
}
}
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_758, 0);
lean_inc(x_778);
lean_dec_ref(x_758);
x_779 = lean_io_get_num_heartbeats();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_780 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_755, x_752, x_749, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; uint8_t x_783; uint8_t x_788; 
x_781 = lean_ctor_get(x_780, 0);
x_788 = !lean_is_exclusive(x_780);
if (x_788 == 0)
{
x_782 = x_780;
x_783 = x_788;
goto block_787;
}
else
{
lean_inc(x_781);
lean_dec(x_780);
x_782 = lean_box(0);
x_783 = x_788;
goto block_787;
}
block_787:
{
lean_object* x_784; 
if (x_783 == 0)
{
lean_ctor_set_tag(x_782, 1);
x_784 = x_782;
goto block_785;
}
else
{
lean_object* x_786; 
x_786 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_786, 0, x_781);
x_784 = x_786;
goto block_785;
}
block_785:
{
x_703 = x_746;
x_704 = x_754;
x_705 = x_756;
x_706 = x_747;
x_707 = x_748;
x_708 = x_757;
x_709 = x_750;
x_710 = x_751;
x_711 = x_779;
x_712 = x_778;
x_713 = x_784;
goto block_722;
}
}
}
else
{
lean_object* x_789; lean_object* x_790; uint8_t x_791; uint8_t x_796; 
x_789 = lean_ctor_get(x_780, 0);
x_796 = !lean_is_exclusive(x_780);
if (x_796 == 0)
{
x_790 = x_780;
x_791 = x_796;
goto block_795;
}
else
{
lean_inc(x_789);
lean_dec(x_780);
x_790 = lean_box(0);
x_791 = x_796;
goto block_795;
}
block_795:
{
lean_object* x_792; 
if (x_791 == 0)
{
lean_ctor_set_tag(x_790, 0);
x_792 = x_790;
goto block_793;
}
else
{
lean_object* x_794; 
x_794 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_794, 0, x_789);
x_792 = x_794;
goto block_793;
}
block_793:
{
x_703 = x_746;
x_704 = x_754;
x_705 = x_756;
x_706 = x_747;
x_707 = x_748;
x_708 = x_757;
x_709 = x_750;
x_710 = x_751;
x_711 = x_779;
x_712 = x_778;
x_713 = x_792;
goto block_722;
}
}
}
}
}
block_816:
{
lean_object* x_805; double x_806; double x_807; double x_808; double x_809; double x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_805 = lean_io_mono_nanos_now();
x_806 = lean_float_of_nat(x_803);
x_807 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_808 = lean_float_div(x_806, x_807);
x_809 = lean_float_of_nat(x_805);
x_810 = lean_float_div(x_809, x_807);
x_811 = lean_box_float(x_808);
x_812 = lean_box_float(x_810);
x_813 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_813, 0, x_811);
lean_ctor_set(x_813, 1, x_812);
x_814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_814, 0, x_804);
lean_ctor_set(x_814, 1, x_813);
x_815 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_799, x_801, x_800, x_802, x_798, x_426, x_814, x_8, x_9, x_10, x_11);
lean_dec_ref(x_800);
return x_815;
}
block_832:
{
lean_object* x_824; double x_825; double x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_824 = lean_io_get_num_heartbeats();
x_825 = lean_float_of_nat(x_819);
x_826 = lean_float_of_nat(x_824);
x_827 = lean_box_float(x_825);
x_828 = lean_box_float(x_826);
x_829 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_829, 0, x_827);
lean_ctor_set(x_829, 1, x_828);
x_830 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_830, 0, x_823);
lean_ctor_set(x_830, 1, x_829);
x_831 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_818, x_821, x_820, x_822, x_817, x_426, x_830, x_8, x_9, x_10, x_11);
lean_dec_ref(x_820);
return x_831;
}
block_851:
{
lean_object* x_840; double x_841; double x_842; double x_843; double x_844; double x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
x_840 = lean_io_mono_nanos_now();
x_841 = lean_float_of_nat(x_833);
x_842 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_843 = lean_float_div(x_841, x_842);
x_844 = lean_float_of_nat(x_840);
x_845 = lean_float_div(x_844, x_842);
x_846 = lean_box_float(x_843);
x_847 = lean_box_float(x_845);
x_848 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_848, 0, x_846);
lean_ctor_set(x_848, 1, x_847);
x_849 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_849, 0, x_839);
lean_ctor_set(x_849, 1, x_848);
x_850 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_834, x_837, x_836, x_838, x_835, x_330, x_849, x_8, x_9, x_10, x_11);
lean_dec_ref(x_836);
return x_850;
}
block_867:
{
lean_object* x_859; double x_860; double x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
x_859 = lean_io_get_num_heartbeats();
x_860 = lean_float_of_nat(x_854);
x_861 = lean_float_of_nat(x_859);
x_862 = lean_box_float(x_860);
x_863 = lean_box_float(x_861);
x_864 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_864, 0, x_862);
lean_ctor_set(x_864, 1, x_863);
x_865 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_865, 0, x_858);
lean_ctor_set(x_865, 1, x_864);
x_866 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_852, x_856, x_855, x_857, x_853, x_330, x_865, x_8, x_9, x_10, x_11);
lean_dec_ref(x_855);
return x_866;
}
block_915:
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; uint8_t x_878; 
x_875 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
lean_dec_ref(x_875);
x_877 = l_Lean_trace_profiler_useHeartbeats;
x_878 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_871, x_877);
if (x_878 == 0)
{
lean_object* x_879; lean_object* x_880; 
x_879 = lean_io_mono_nanos_now();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_880 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_870, x_868, x_874, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; lean_object* x_882; uint8_t x_883; uint8_t x_888; 
x_881 = lean_ctor_get(x_880, 0);
x_888 = !lean_is_exclusive(x_880);
if (x_888 == 0)
{
x_882 = x_880;
x_883 = x_888;
goto block_887;
}
else
{
lean_inc(x_881);
lean_dec(x_880);
x_882 = lean_box(0);
x_883 = x_888;
goto block_887;
}
block_887:
{
lean_object* x_884; 
if (x_883 == 0)
{
lean_ctor_set_tag(x_882, 1);
x_884 = x_882;
goto block_885;
}
else
{
lean_object* x_886; 
x_886 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_886, 0, x_881);
x_884 = x_886;
goto block_885;
}
block_885:
{
x_833 = x_879;
x_834 = x_869;
x_835 = x_876;
x_836 = x_871;
x_837 = x_872;
x_838 = x_873;
x_839 = x_884;
goto block_851;
}
}
}
else
{
lean_object* x_889; lean_object* x_890; uint8_t x_891; uint8_t x_896; 
x_889 = lean_ctor_get(x_880, 0);
x_896 = !lean_is_exclusive(x_880);
if (x_896 == 0)
{
x_890 = x_880;
x_891 = x_896;
goto block_895;
}
else
{
lean_inc(x_889);
lean_dec(x_880);
x_890 = lean_box(0);
x_891 = x_896;
goto block_895;
}
block_895:
{
lean_object* x_892; 
if (x_891 == 0)
{
lean_ctor_set_tag(x_890, 0);
x_892 = x_890;
goto block_893;
}
else
{
lean_object* x_894; 
x_894 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_894, 0, x_889);
x_892 = x_894;
goto block_893;
}
block_893:
{
x_833 = x_879;
x_834 = x_869;
x_835 = x_876;
x_836 = x_871;
x_837 = x_872;
x_838 = x_873;
x_839 = x_892;
goto block_851;
}
}
}
}
else
{
lean_object* x_897; lean_object* x_898; 
x_897 = lean_io_get_num_heartbeats();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_898 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_870, x_868, x_874, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; uint8_t x_901; uint8_t x_906; 
x_899 = lean_ctor_get(x_898, 0);
x_906 = !lean_is_exclusive(x_898);
if (x_906 == 0)
{
x_900 = x_898;
x_901 = x_906;
goto block_905;
}
else
{
lean_inc(x_899);
lean_dec(x_898);
x_900 = lean_box(0);
x_901 = x_906;
goto block_905;
}
block_905:
{
lean_object* x_902; 
if (x_901 == 0)
{
lean_ctor_set_tag(x_900, 1);
x_902 = x_900;
goto block_903;
}
else
{
lean_object* x_904; 
x_904 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_904, 0, x_899);
x_902 = x_904;
goto block_903;
}
block_903:
{
x_852 = x_869;
x_853 = x_876;
x_854 = x_897;
x_855 = x_871;
x_856 = x_872;
x_857 = x_873;
x_858 = x_902;
goto block_867;
}
}
}
else
{
lean_object* x_907; lean_object* x_908; uint8_t x_909; uint8_t x_914; 
x_907 = lean_ctor_get(x_898, 0);
x_914 = !lean_is_exclusive(x_898);
if (x_914 == 0)
{
x_908 = x_898;
x_909 = x_914;
goto block_913;
}
else
{
lean_inc(x_907);
lean_dec(x_898);
x_908 = lean_box(0);
x_909 = x_914;
goto block_913;
}
block_913:
{
lean_object* x_910; 
if (x_909 == 0)
{
lean_ctor_set_tag(x_908, 0);
x_910 = x_908;
goto block_911;
}
else
{
lean_object* x_912; 
x_912 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_912, 0, x_907);
x_910 = x_912;
goto block_911;
}
block_911:
{
x_852 = x_869;
x_853 = x_876;
x_854 = x_897;
x_855 = x_871;
x_856 = x_872;
x_857 = x_873;
x_858 = x_910;
goto block_867;
}
}
}
}
}
block_963:
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; uint8_t x_926; 
x_923 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
x_924 = lean_ctor_get(x_923, 0);
lean_inc(x_924);
lean_dec_ref(x_923);
x_925 = l_Lean_trace_profiler_useHeartbeats;
x_926 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_919, x_925);
if (x_926 == 0)
{
lean_object* x_927; lean_object* x_928; 
x_927 = lean_io_mono_nanos_now();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_928 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_917, x_922, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; uint8_t x_931; uint8_t x_936; 
x_929 = lean_ctor_get(x_928, 0);
x_936 = !lean_is_exclusive(x_928);
if (x_936 == 0)
{
x_930 = x_928;
x_931 = x_936;
goto block_935;
}
else
{
lean_inc(x_929);
lean_dec(x_928);
x_930 = lean_box(0);
x_931 = x_936;
goto block_935;
}
block_935:
{
lean_object* x_932; 
if (x_931 == 0)
{
lean_ctor_set_tag(x_930, 1);
x_932 = x_930;
goto block_933;
}
else
{
lean_object* x_934; 
x_934 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_934, 0, x_929);
x_932 = x_934;
goto block_933;
}
block_933:
{
x_798 = x_924;
x_799 = x_918;
x_800 = x_919;
x_801 = x_920;
x_802 = x_921;
x_803 = x_927;
x_804 = x_932;
goto block_816;
}
}
}
else
{
lean_object* x_937; lean_object* x_938; uint8_t x_939; uint8_t x_944; 
x_937 = lean_ctor_get(x_928, 0);
x_944 = !lean_is_exclusive(x_928);
if (x_944 == 0)
{
x_938 = x_928;
x_939 = x_944;
goto block_943;
}
else
{
lean_inc(x_937);
lean_dec(x_928);
x_938 = lean_box(0);
x_939 = x_944;
goto block_943;
}
block_943:
{
lean_object* x_940; 
if (x_939 == 0)
{
lean_ctor_set_tag(x_938, 0);
x_940 = x_938;
goto block_941;
}
else
{
lean_object* x_942; 
x_942 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_942, 0, x_937);
x_940 = x_942;
goto block_941;
}
block_941:
{
x_798 = x_924;
x_799 = x_918;
x_800 = x_919;
x_801 = x_920;
x_802 = x_921;
x_803 = x_927;
x_804 = x_940;
goto block_816;
}
}
}
}
else
{
lean_object* x_945; lean_object* x_946; 
x_945 = lean_io_get_num_heartbeats();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_946 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_917, x_922, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_946) == 0)
{
lean_object* x_947; lean_object* x_948; uint8_t x_949; uint8_t x_954; 
x_947 = lean_ctor_get(x_946, 0);
x_954 = !lean_is_exclusive(x_946);
if (x_954 == 0)
{
x_948 = x_946;
x_949 = x_954;
goto block_953;
}
else
{
lean_inc(x_947);
lean_dec(x_946);
x_948 = lean_box(0);
x_949 = x_954;
goto block_953;
}
block_953:
{
lean_object* x_950; 
if (x_949 == 0)
{
lean_ctor_set_tag(x_948, 1);
x_950 = x_948;
goto block_951;
}
else
{
lean_object* x_952; 
x_952 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_952, 0, x_947);
x_950 = x_952;
goto block_951;
}
block_951:
{
x_817 = x_924;
x_818 = x_918;
x_819 = x_945;
x_820 = x_919;
x_821 = x_920;
x_822 = x_921;
x_823 = x_950;
goto block_832;
}
}
}
else
{
lean_object* x_955; lean_object* x_956; uint8_t x_957; uint8_t x_962; 
x_955 = lean_ctor_get(x_946, 0);
x_962 = !lean_is_exclusive(x_946);
if (x_962 == 0)
{
x_956 = x_946;
x_957 = x_962;
goto block_961;
}
else
{
lean_inc(x_955);
lean_dec(x_946);
x_956 = lean_box(0);
x_957 = x_962;
goto block_961;
}
block_961:
{
lean_object* x_958; 
if (x_957 == 0)
{
lean_ctor_set_tag(x_956, 0);
x_958 = x_956;
goto block_959;
}
else
{
lean_object* x_960; 
x_960 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_960, 0, x_955);
x_958 = x_960;
goto block_959;
}
block_959:
{
x_817 = x_924;
x_818 = x_918;
x_819 = x_945;
x_820 = x_919;
x_821 = x_920;
x_822 = x_921;
x_823 = x_958;
goto block_832;
}
}
}
}
}
block_999:
{
if (x_972 == 0)
{
lean_object* x_973; 
lean_dec_ref(x_967);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_966);
x_973 = lean_apply_6(x_969, x_966, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; 
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
lean_dec_ref(x_973);
if (lean_obj_tag(x_974) == 0)
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; uint8_t x_979; 
lean_inc(x_2);
x_975 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_976 = lean_ctor_get(x_975, 0);
lean_inc(x_976);
lean_dec_ref(x_975);
x_977 = lean_nat_add(x_917, x_916);
lean_dec(x_917);
x_978 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_978, 0, x_966);
lean_ctor_set(x_978, 1, x_7);
x_979 = lean_unbox(x_976);
if (x_979 == 0)
{
if (x_964 == 0)
{
lean_dec(x_976);
lean_dec_ref(x_971);
lean_dec_ref(x_970);
x_5 = x_977;
x_6 = x_965;
x_7 = x_978;
goto _start;
}
else
{
uint8_t x_981; 
x_981 = lean_unbox(x_976);
lean_dec(x_976);
x_868 = x_965;
x_869 = x_968;
x_870 = x_977;
x_871 = x_970;
x_872 = x_971;
x_873 = x_981;
x_874 = x_978;
goto block_915;
}
}
else
{
uint8_t x_982; 
x_982 = lean_unbox(x_976);
lean_dec(x_976);
x_868 = x_965;
x_869 = x_968;
x_870 = x_977;
x_871 = x_970;
x_872 = x_971;
x_873 = x_982;
x_874 = x_978;
goto block_915;
}
}
else
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; uint8_t x_987; 
lean_dec(x_966);
x_983 = lean_ctor_get(x_974, 0);
lean_inc(x_983);
lean_dec_ref(x_974);
lean_inc(x_2);
x_984 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_985 = lean_ctor_get(x_984, 0);
lean_inc(x_985);
lean_dec_ref(x_984);
x_986 = l_List_appendTR___redArg(x_983, x_965);
x_987 = lean_unbox(x_985);
if (x_987 == 0)
{
if (x_964 == 0)
{
lean_dec(x_985);
lean_dec_ref(x_971);
lean_dec_ref(x_970);
x_5 = x_917;
x_6 = x_986;
goto _start;
}
else
{
uint8_t x_989; 
x_989 = lean_unbox(x_985);
lean_dec(x_985);
x_918 = x_968;
x_919 = x_970;
x_920 = x_971;
x_921 = x_989;
x_922 = x_986;
goto block_963;
}
}
else
{
uint8_t x_990; 
x_990 = lean_unbox(x_985);
lean_dec(x_985);
x_918 = x_968;
x_919 = x_970;
x_920 = x_971;
x_921 = x_990;
x_922 = x_986;
goto block_963;
}
}
}
else
{
lean_object* x_991; lean_object* x_992; uint8_t x_993; uint8_t x_998; 
lean_dec_ref(x_971);
lean_dec_ref(x_970);
lean_dec(x_966);
lean_dec(x_965);
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_991 = lean_ctor_get(x_973, 0);
x_998 = !lean_is_exclusive(x_973);
if (x_998 == 0)
{
x_992 = x_973;
x_993 = x_998;
goto block_997;
}
else
{
lean_inc(x_991);
lean_dec(x_973);
x_992 = lean_box(0);
x_993 = x_998;
goto block_997;
}
block_997:
{
lean_object* x_994; 
if (x_993 == 0)
{
x_994 = x_992;
goto block_995;
}
else
{
lean_object* x_996; 
x_996 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_996, 0, x_991);
x_994 = x_996;
goto block_995;
}
block_995:
{
return x_994;
}
}
}
}
else
{
lean_dec_ref(x_971);
lean_dec_ref(x_970);
lean_dec_ref(x_969);
lean_dec(x_966);
lean_dec(x_965);
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_967;
}
}
block_1049:
{
lean_object* x_1010; 
x_1010 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
if (x_1002 == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
lean_dec_ref(x_1010);
x_1012 = lean_io_mono_nanos_now();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1013 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_917, x_1006, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1013) == 0)
{
lean_object* x_1014; lean_object* x_1015; uint8_t x_1016; uint8_t x_1021; 
x_1014 = lean_ctor_get(x_1013, 0);
x_1021 = !lean_is_exclusive(x_1013);
if (x_1021 == 0)
{
x_1015 = x_1013;
x_1016 = x_1021;
goto block_1020;
}
else
{
lean_inc(x_1014);
lean_dec(x_1013);
x_1015 = lean_box(0);
x_1016 = x_1021;
goto block_1020;
}
block_1020:
{
lean_object* x_1017; 
if (x_1016 == 0)
{
lean_ctor_set_tag(x_1015, 1);
x_1017 = x_1015;
goto block_1018;
}
else
{
lean_object* x_1019; 
x_1019 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1019, 0, x_1014);
x_1017 = x_1019;
goto block_1018;
}
block_1018:
{
x_427 = x_1000;
x_428 = x_1012;
x_429 = x_1001;
x_430 = x_1003;
x_431 = x_1004;
x_432 = x_1005;
x_433 = x_1007;
x_434 = x_1009;
x_435 = x_1008;
x_436 = x_1011;
x_437 = x_1017;
goto block_449;
}
}
}
else
{
lean_object* x_1022; lean_object* x_1023; uint8_t x_1024; uint8_t x_1029; 
x_1022 = lean_ctor_get(x_1013, 0);
x_1029 = !lean_is_exclusive(x_1013);
if (x_1029 == 0)
{
x_1023 = x_1013;
x_1024 = x_1029;
goto block_1028;
}
else
{
lean_inc(x_1022);
lean_dec(x_1013);
x_1023 = lean_box(0);
x_1024 = x_1029;
goto block_1028;
}
block_1028:
{
lean_object* x_1025; 
if (x_1024 == 0)
{
lean_ctor_set_tag(x_1023, 0);
x_1025 = x_1023;
goto block_1026;
}
else
{
lean_object* x_1027; 
x_1027 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1027, 0, x_1022);
x_1025 = x_1027;
goto block_1026;
}
block_1026:
{
x_427 = x_1000;
x_428 = x_1012;
x_429 = x_1001;
x_430 = x_1003;
x_431 = x_1004;
x_432 = x_1005;
x_433 = x_1007;
x_434 = x_1009;
x_435 = x_1008;
x_436 = x_1011;
x_437 = x_1025;
goto block_449;
}
}
}
}
else
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1030 = lean_ctor_get(x_1010, 0);
lean_inc(x_1030);
lean_dec_ref(x_1010);
x_1031 = lean_io_get_num_heartbeats();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1032 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_917, x_1006, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; uint8_t x_1035; uint8_t x_1040; 
x_1033 = lean_ctor_get(x_1032, 0);
x_1040 = !lean_is_exclusive(x_1032);
if (x_1040 == 0)
{
x_1034 = x_1032;
x_1035 = x_1040;
goto block_1039;
}
else
{
lean_inc(x_1033);
lean_dec(x_1032);
x_1034 = lean_box(0);
x_1035 = x_1040;
goto block_1039;
}
block_1039:
{
lean_object* x_1036; 
if (x_1035 == 0)
{
lean_ctor_set_tag(x_1034, 1);
x_1036 = x_1034;
goto block_1037;
}
else
{
lean_object* x_1038; 
x_1038 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1038, 0, x_1033);
x_1036 = x_1038;
goto block_1037;
}
block_1037:
{
x_450 = x_1000;
x_451 = x_1001;
x_452 = x_1003;
x_453 = x_1004;
x_454 = x_1005;
x_455 = x_1007;
x_456 = x_1009;
x_457 = x_1008;
x_458 = x_1030;
x_459 = x_1031;
x_460 = x_1036;
goto block_469;
}
}
}
else
{
lean_object* x_1041; lean_object* x_1042; uint8_t x_1043; uint8_t x_1048; 
x_1041 = lean_ctor_get(x_1032, 0);
x_1048 = !lean_is_exclusive(x_1032);
if (x_1048 == 0)
{
x_1042 = x_1032;
x_1043 = x_1048;
goto block_1047;
}
else
{
lean_inc(x_1041);
lean_dec(x_1032);
x_1042 = lean_box(0);
x_1043 = x_1048;
goto block_1047;
}
block_1047:
{
lean_object* x_1044; 
if (x_1043 == 0)
{
lean_ctor_set_tag(x_1042, 0);
x_1044 = x_1042;
goto block_1045;
}
else
{
lean_object* x_1046; 
x_1046 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1046, 0, x_1041);
x_1044 = x_1046;
goto block_1045;
}
block_1045:
{
x_450 = x_1000;
x_451 = x_1001;
x_452 = x_1003;
x_453 = x_1004;
x_454 = x_1005;
x_455 = x_1007;
x_456 = x_1009;
x_457 = x_1008;
x_458 = x_1030;
x_459 = x_1031;
x_460 = x_1044;
goto block_469;
}
}
}
}
}
block_1086:
{
if (x_1062 == 0)
{
lean_object* x_1063; 
lean_dec_ref(x_1054);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1056);
x_1063 = lean_apply_6(x_1059, x_1056, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1063) == 0)
{
lean_object* x_1064; 
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
lean_dec_ref(x_1063);
if (lean_obj_tag(x_1064) == 0)
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; uint8_t x_1069; 
lean_inc(x_2);
x_1065 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
lean_dec_ref(x_1065);
x_1067 = lean_nat_add(x_917, x_916);
lean_dec(x_917);
x_1068 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1068, 0, x_1056);
lean_ctor_set(x_1068, 1, x_7);
x_1069 = lean_unbox(x_1066);
if (x_1069 == 0)
{
lean_object* x_1070; uint8_t x_1071; 
x_1070 = l_Lean_trace_profiler;
x_1071 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1060, x_1070);
if (x_1071 == 0)
{
lean_object* x_1072; 
lean_dec(x_1066);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1072 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1067, x_1055, x_1068, x_8, x_9, x_10, x_11);
x_135 = x_1050;
x_136 = x_1058;
x_137 = x_1060;
x_138 = x_1051;
x_139 = x_1052;
x_140 = x_1053;
x_141 = x_1061;
x_142 = x_1072;
goto block_145;
}
else
{
uint8_t x_1073; 
x_1073 = lean_unbox(x_1066);
lean_dec(x_1066);
x_374 = x_1068;
x_375 = x_1050;
x_376 = x_1067;
x_377 = x_1051;
x_378 = x_1052;
x_379 = x_1053;
x_380 = x_1073;
x_381 = x_1055;
x_382 = x_1057;
x_383 = x_1058;
x_384 = x_1060;
x_385 = x_1061;
goto block_425;
}
}
else
{
uint8_t x_1074; 
x_1074 = lean_unbox(x_1066);
lean_dec(x_1066);
x_374 = x_1068;
x_375 = x_1050;
x_376 = x_1067;
x_377 = x_1051;
x_378 = x_1052;
x_379 = x_1053;
x_380 = x_1074;
x_381 = x_1055;
x_382 = x_1057;
x_383 = x_1058;
x_384 = x_1060;
x_385 = x_1061;
goto block_425;
}
}
else
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; uint8_t x_1079; 
lean_dec(x_1056);
x_1075 = lean_ctor_get(x_1064, 0);
lean_inc(x_1075);
lean_dec_ref(x_1064);
lean_inc(x_2);
x_1076 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1077 = lean_ctor_get(x_1076, 0);
lean_inc(x_1077);
lean_dec_ref(x_1076);
x_1078 = l_List_appendTR___redArg(x_1075, x_1055);
x_1079 = lean_unbox(x_1077);
if (x_1079 == 0)
{
lean_object* x_1080; uint8_t x_1081; 
x_1080 = l_Lean_trace_profiler;
x_1081 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1060, x_1080);
if (x_1081 == 0)
{
lean_object* x_1082; 
lean_dec(x_1077);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1082 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_917, x_1078, x_7, x_8, x_9, x_10, x_11);
x_135 = x_1050;
x_136 = x_1058;
x_137 = x_1060;
x_138 = x_1051;
x_139 = x_1052;
x_140 = x_1053;
x_141 = x_1061;
x_142 = x_1082;
goto block_145;
}
else
{
uint8_t x_1083; 
x_1083 = lean_unbox(x_1077);
lean_dec(x_1077);
x_1000 = x_1083;
x_1001 = x_1050;
x_1002 = x_1057;
x_1003 = x_1058;
x_1004 = x_1060;
x_1005 = x_1051;
x_1006 = x_1078;
x_1007 = x_1052;
x_1008 = x_1053;
x_1009 = x_1061;
goto block_1049;
}
}
else
{
uint8_t x_1084; 
x_1084 = lean_unbox(x_1077);
lean_dec(x_1077);
x_1000 = x_1084;
x_1001 = x_1050;
x_1002 = x_1057;
x_1003 = x_1058;
x_1004 = x_1060;
x_1005 = x_1051;
x_1006 = x_1078;
x_1007 = x_1052;
x_1008 = x_1053;
x_1009 = x_1061;
goto block_1049;
}
}
}
else
{
lean_object* x_1085; 
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_917);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1085 = lean_ctor_get(x_1063, 0);
lean_inc(x_1085);
lean_dec_ref(x_1063);
x_125 = x_1050;
x_126 = x_1058;
x_127 = x_1060;
x_128 = x_1051;
x_129 = x_1052;
x_130 = x_1061;
x_131 = x_1053;
x_132 = x_1085;
goto block_134;
}
}
else
{
lean_dec_ref(x_1059);
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_917);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_125 = x_1050;
x_126 = x_1058;
x_127 = x_1060;
x_128 = x_1051;
x_129 = x_1052;
x_130 = x_1061;
x_131 = x_1053;
x_132 = x_1054;
goto block_134;
}
}
block_1136:
{
lean_object* x_1097; 
x_1097 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
if (x_1089 == 0)
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1098 = lean_ctor_get(x_1097, 0);
lean_inc(x_1098);
lean_dec_ref(x_1097);
x_1099 = lean_io_mono_nanos_now();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1100 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_917, x_1087, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; lean_object* x_1102; uint8_t x_1103; uint8_t x_1108; 
x_1101 = lean_ctor_get(x_1100, 0);
x_1108 = !lean_is_exclusive(x_1100);
if (x_1108 == 0)
{
x_1102 = x_1100;
x_1103 = x_1108;
goto block_1107;
}
else
{
lean_inc(x_1101);
lean_dec(x_1100);
x_1102 = lean_box(0);
x_1103 = x_1108;
goto block_1107;
}
block_1107:
{
lean_object* x_1104; 
if (x_1103 == 0)
{
lean_ctor_set_tag(x_1102, 1);
x_1104 = x_1102;
goto block_1105;
}
else
{
lean_object* x_1106; 
x_1106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1106, 0, x_1101);
x_1104 = x_1106;
goto block_1105;
}
block_1105:
{
x_585 = x_1098;
x_586 = x_1088;
x_587 = x_1090;
x_588 = x_1092;
x_589 = x_1091;
x_590 = x_1099;
x_591 = x_1094;
x_592 = x_1093;
x_593 = x_1096;
x_594 = x_1095;
x_595 = x_1104;
goto block_607;
}
}
}
else
{
lean_object* x_1109; lean_object* x_1110; uint8_t x_1111; uint8_t x_1116; 
x_1109 = lean_ctor_get(x_1100, 0);
x_1116 = !lean_is_exclusive(x_1100);
if (x_1116 == 0)
{
x_1110 = x_1100;
x_1111 = x_1116;
goto block_1115;
}
else
{
lean_inc(x_1109);
lean_dec(x_1100);
x_1110 = lean_box(0);
x_1111 = x_1116;
goto block_1115;
}
block_1115:
{
lean_object* x_1112; 
if (x_1111 == 0)
{
lean_ctor_set_tag(x_1110, 0);
x_1112 = x_1110;
goto block_1113;
}
else
{
lean_object* x_1114; 
x_1114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1114, 0, x_1109);
x_1112 = x_1114;
goto block_1113;
}
block_1113:
{
x_585 = x_1098;
x_586 = x_1088;
x_587 = x_1090;
x_588 = x_1092;
x_589 = x_1091;
x_590 = x_1099;
x_591 = x_1094;
x_592 = x_1093;
x_593 = x_1096;
x_594 = x_1095;
x_595 = x_1112;
goto block_607;
}
}
}
}
else
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
x_1117 = lean_ctor_get(x_1097, 0);
lean_inc(x_1117);
lean_dec_ref(x_1097);
x_1118 = lean_io_get_num_heartbeats();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1119 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_917, x_1087, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_1119) == 0)
{
lean_object* x_1120; lean_object* x_1121; uint8_t x_1122; uint8_t x_1127; 
x_1120 = lean_ctor_get(x_1119, 0);
x_1127 = !lean_is_exclusive(x_1119);
if (x_1127 == 0)
{
x_1121 = x_1119;
x_1122 = x_1127;
goto block_1126;
}
else
{
lean_inc(x_1120);
lean_dec(x_1119);
x_1121 = lean_box(0);
x_1122 = x_1127;
goto block_1126;
}
block_1126:
{
lean_object* x_1123; 
if (x_1122 == 0)
{
lean_ctor_set_tag(x_1121, 1);
x_1123 = x_1121;
goto block_1124;
}
else
{
lean_object* x_1125; 
x_1125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1125, 0, x_1120);
x_1123 = x_1125;
goto block_1124;
}
block_1124:
{
x_565 = x_1117;
x_566 = x_1088;
x_567 = x_1118;
x_568 = x_1090;
x_569 = x_1092;
x_570 = x_1091;
x_571 = x_1094;
x_572 = x_1093;
x_573 = x_1096;
x_574 = x_1095;
x_575 = x_1123;
goto block_584;
}
}
}
else
{
lean_object* x_1128; lean_object* x_1129; uint8_t x_1130; uint8_t x_1135; 
x_1128 = lean_ctor_get(x_1119, 0);
x_1135 = !lean_is_exclusive(x_1119);
if (x_1135 == 0)
{
x_1129 = x_1119;
x_1130 = x_1135;
goto block_1134;
}
else
{
lean_inc(x_1128);
lean_dec(x_1119);
x_1129 = lean_box(0);
x_1130 = x_1135;
goto block_1134;
}
block_1134:
{
lean_object* x_1131; 
if (x_1130 == 0)
{
lean_ctor_set_tag(x_1129, 0);
x_1131 = x_1129;
goto block_1132;
}
else
{
lean_object* x_1133; 
x_1133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1133, 0, x_1128);
x_1131 = x_1133;
goto block_1132;
}
block_1132:
{
x_565 = x_1117;
x_566 = x_1088;
x_567 = x_1118;
x_568 = x_1090;
x_569 = x_1092;
x_570 = x_1091;
x_571 = x_1094;
x_572 = x_1093;
x_573 = x_1096;
x_574 = x_1095;
x_575 = x_1131;
goto block_584;
}
}
}
}
}
block_1173:
{
if (x_1149 == 0)
{
lean_object* x_1150; 
lean_dec_ref(x_1147);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1143);
x_1150 = lean_apply_6(x_1145, x_1143, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1150) == 0)
{
lean_object* x_1151; 
x_1151 = lean_ctor_get(x_1150, 0);
lean_inc(x_1151);
lean_dec_ref(x_1150);
if (lean_obj_tag(x_1151) == 0)
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; uint8_t x_1156; 
lean_inc(x_2);
x_1152 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1153 = lean_ctor_get(x_1152, 0);
lean_inc(x_1153);
lean_dec_ref(x_1152);
x_1154 = lean_nat_add(x_917, x_916);
lean_dec(x_917);
x_1155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1155, 0, x_1143);
lean_ctor_set(x_1155, 1, x_7);
x_1156 = lean_unbox(x_1153);
if (x_1156 == 0)
{
lean_object* x_1157; uint8_t x_1158; 
x_1157 = l_Lean_trace_profiler;
x_1158 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1146, x_1157);
if (x_1158 == 0)
{
lean_object* x_1159; 
lean_dec(x_1153);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1159 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1154, x_1142, x_1155, x_8, x_9, x_10, x_11);
x_186 = x_1137;
x_187 = x_1146;
x_188 = x_1139;
x_189 = x_1138;
x_190 = x_1140;
x_191 = x_1141;
x_192 = x_1148;
x_193 = x_1159;
goto block_196;
}
else
{
uint8_t x_1160; 
x_1160 = lean_unbox(x_1153);
lean_dec(x_1153);
x_651 = x_1137;
x_652 = x_1155;
x_653 = x_1138;
x_654 = x_1139;
x_655 = x_1140;
x_656 = x_1141;
x_657 = x_1142;
x_658 = x_1144;
x_659 = x_1160;
x_660 = x_1146;
x_661 = x_1154;
x_662 = x_1148;
goto block_702;
}
}
else
{
uint8_t x_1161; 
x_1161 = lean_unbox(x_1153);
lean_dec(x_1153);
x_651 = x_1137;
x_652 = x_1155;
x_653 = x_1138;
x_654 = x_1139;
x_655 = x_1140;
x_656 = x_1141;
x_657 = x_1142;
x_658 = x_1144;
x_659 = x_1161;
x_660 = x_1146;
x_661 = x_1154;
x_662 = x_1148;
goto block_702;
}
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; uint8_t x_1166; 
lean_dec(x_1143);
x_1162 = lean_ctor_get(x_1151, 0);
lean_inc(x_1162);
lean_dec_ref(x_1151);
lean_inc(x_2);
x_1163 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1164 = lean_ctor_get(x_1163, 0);
lean_inc(x_1164);
lean_dec_ref(x_1163);
x_1165 = l_List_appendTR___redArg(x_1162, x_1142);
x_1166 = lean_unbox(x_1164);
if (x_1166 == 0)
{
lean_object* x_1167; uint8_t x_1168; 
x_1167 = l_Lean_trace_profiler;
x_1168 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1146, x_1167);
if (x_1168 == 0)
{
lean_object* x_1169; 
lean_dec(x_1164);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1169 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_917, x_1165, x_7, x_8, x_9, x_10, x_11);
x_186 = x_1137;
x_187 = x_1146;
x_188 = x_1139;
x_189 = x_1138;
x_190 = x_1140;
x_191 = x_1141;
x_192 = x_1148;
x_193 = x_1169;
goto block_196;
}
else
{
uint8_t x_1170; 
x_1170 = lean_unbox(x_1164);
lean_dec(x_1164);
x_1087 = x_1165;
x_1088 = x_1137;
x_1089 = x_1144;
x_1090 = x_1146;
x_1091 = x_1139;
x_1092 = x_1138;
x_1093 = x_1170;
x_1094 = x_1140;
x_1095 = x_1141;
x_1096 = x_1148;
goto block_1136;
}
}
else
{
uint8_t x_1171; 
x_1171 = lean_unbox(x_1164);
lean_dec(x_1164);
x_1087 = x_1165;
x_1088 = x_1137;
x_1089 = x_1144;
x_1090 = x_1146;
x_1091 = x_1139;
x_1092 = x_1138;
x_1093 = x_1171;
x_1094 = x_1140;
x_1095 = x_1141;
x_1096 = x_1148;
goto block_1136;
}
}
}
else
{
lean_object* x_1172; 
lean_dec(x_1143);
lean_dec(x_1142);
lean_dec(x_917);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1172 = lean_ctor_get(x_1150, 0);
lean_inc(x_1172);
lean_dec_ref(x_1150);
x_176 = x_1137;
x_177 = x_1146;
x_178 = x_1138;
x_179 = x_1139;
x_180 = x_1140;
x_181 = x_1148;
x_182 = x_1141;
x_183 = x_1172;
goto block_185;
}
}
else
{
lean_dec_ref(x_1145);
lean_dec(x_1143);
lean_dec(x_1142);
lean_dec(x_917);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_176 = x_1137;
x_177 = x_1146;
x_178 = x_1138;
x_179 = x_1139;
x_180 = x_1140;
x_181 = x_1148;
x_182 = x_1141;
x_183 = x_1147;
goto block_185;
}
}
block_1229:
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; uint8_t x_1188; 
x_1185 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
x_1186 = lean_ctor_get(x_1185, 0);
lean_inc(x_1186);
lean_dec_ref(x_1185);
x_1187 = l_Lean_trace_profiler_useHeartbeats;
x_1188 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1180, x_1187);
if (x_1188 == 0)
{
lean_object* x_1189; lean_object* x_1190; 
lean_dec_ref(x_1182);
x_1189 = lean_io_mono_nanos_now();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1175);
x_1190 = lean_apply_6(x_1176, x_1175, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1190) == 0)
{
lean_object* x_1191; uint8_t x_1192; 
x_1191 = lean_ctor_get(x_1190, 0);
lean_inc(x_1191);
lean_dec_ref(x_1190);
x_1192 = lean_unbox(x_1191);
lean_dec(x_1191);
if (x_1192 == 0)
{
lean_object* x_1193; 
lean_inc_ref(x_3);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1175);
x_1193 = lean_apply_7(x_3, x_1175, x_1178, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1193) == 0)
{
lean_object* x_1194; 
lean_dec_ref(x_1179);
lean_dec(x_1175);
lean_dec(x_1174);
lean_dec(x_917);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1194 = lean_ctor_get(x_1193, 0);
lean_inc(x_1194);
lean_dec_ref(x_1193);
x_166 = x_1177;
x_167 = x_1180;
x_168 = x_1189;
x_169 = x_1181;
x_170 = x_1186;
x_171 = x_1183;
x_172 = x_1184;
x_173 = x_1194;
goto block_175;
}
else
{
lean_object* x_1195; uint8_t x_1196; 
x_1195 = lean_ctor_get(x_1193, 0);
lean_inc(x_1195);
lean_dec_ref(x_1193);
x_1196 = l_Lean_Exception_isInterrupt(x_1195);
if (x_1196 == 0)
{
uint8_t x_1197; 
lean_inc(x_1195);
x_1197 = l_Lean_Exception_isRuntime(x_1195);
x_1137 = x_1177;
x_1138 = x_1189;
x_1139 = x_1181;
x_1140 = x_1186;
x_1141 = x_1184;
x_1142 = x_1174;
x_1143 = x_1175;
x_1144 = x_1188;
x_1145 = x_1179;
x_1146 = x_1180;
x_1147 = x_1195;
x_1148 = x_1183;
x_1149 = x_1197;
goto block_1173;
}
else
{
x_1137 = x_1177;
x_1138 = x_1189;
x_1139 = x_1181;
x_1140 = x_1186;
x_1141 = x_1184;
x_1142 = x_1174;
x_1143 = x_1175;
x_1144 = x_1188;
x_1145 = x_1179;
x_1146 = x_1180;
x_1147 = x_1195;
x_1148 = x_1183;
x_1149 = x_1196;
goto block_1173;
}
}
}
else
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; uint8_t x_1202; 
lean_dec_ref(x_1179);
lean_dec_ref(x_1178);
lean_inc(x_2);
x_1198 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
lean_dec_ref(x_1198);
x_1200 = lean_nat_add(x_917, x_916);
lean_dec(x_917);
x_1201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1201, 0, x_1175);
lean_ctor_set(x_1201, 1, x_7);
x_1202 = lean_unbox(x_1199);
if (x_1202 == 0)
{
lean_object* x_1203; uint8_t x_1204; 
x_1203 = l_Lean_trace_profiler;
x_1204 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1180, x_1203);
if (x_1204 == 0)
{
lean_object* x_1205; 
lean_dec(x_1199);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1205 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1200, x_1174, x_1201, x_8, x_9, x_10, x_11);
x_186 = x_1177;
x_187 = x_1180;
x_188 = x_1181;
x_189 = x_1189;
x_190 = x_1186;
x_191 = x_1184;
x_192 = x_1183;
x_193 = x_1205;
goto block_196;
}
else
{
uint8_t x_1206; 
x_1206 = lean_unbox(x_1199);
lean_dec(x_1199);
x_513 = x_1177;
x_514 = x_1201;
x_515 = x_1189;
x_516 = x_1181;
x_517 = x_1186;
x_518 = x_1184;
x_519 = x_1174;
x_520 = x_1206;
x_521 = x_1188;
x_522 = x_1180;
x_523 = x_1200;
x_524 = x_1183;
goto block_564;
}
}
else
{
uint8_t x_1207; 
x_1207 = lean_unbox(x_1199);
lean_dec(x_1199);
x_513 = x_1177;
x_514 = x_1201;
x_515 = x_1189;
x_516 = x_1181;
x_517 = x_1186;
x_518 = x_1184;
x_519 = x_1174;
x_520 = x_1207;
x_521 = x_1188;
x_522 = x_1180;
x_523 = x_1200;
x_524 = x_1183;
goto block_564;
}
}
}
else
{
lean_object* x_1208; 
lean_dec_ref(x_1179);
lean_dec_ref(x_1178);
lean_dec(x_1175);
lean_dec(x_1174);
lean_dec(x_917);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1208 = lean_ctor_get(x_1190, 0);
lean_inc(x_1208);
lean_dec_ref(x_1190);
x_176 = x_1177;
x_177 = x_1180;
x_178 = x_1189;
x_179 = x_1181;
x_180 = x_1186;
x_181 = x_1183;
x_182 = x_1184;
x_183 = x_1208;
goto block_185;
}
}
else
{
lean_object* x_1209; lean_object* x_1210; 
lean_dec_ref(x_1178);
x_1209 = lean_io_get_num_heartbeats();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1175);
x_1210 = lean_apply_6(x_1176, x_1175, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1210) == 0)
{
lean_object* x_1211; uint8_t x_1212; 
x_1211 = lean_ctor_get(x_1210, 0);
lean_inc(x_1211);
lean_dec_ref(x_1210);
x_1212 = lean_unbox(x_1211);
lean_dec(x_1211);
if (x_1212 == 0)
{
lean_object* x_1213; 
lean_inc_ref(x_3);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1175);
x_1213 = lean_apply_7(x_3, x_1175, x_1182, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1213) == 0)
{
lean_object* x_1214; 
lean_dec_ref(x_1179);
lean_dec(x_1175);
lean_dec(x_1174);
lean_dec(x_917);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1214 = lean_ctor_get(x_1213, 0);
lean_inc(x_1214);
lean_dec_ref(x_1213);
x_115 = x_1177;
x_116 = x_1209;
x_117 = x_1180;
x_118 = x_1181;
x_119 = x_1186;
x_120 = x_1183;
x_121 = x_1184;
x_122 = x_1214;
goto block_124;
}
else
{
lean_object* x_1215; uint8_t x_1216; 
x_1215 = lean_ctor_get(x_1213, 0);
lean_inc(x_1215);
lean_dec_ref(x_1213);
x_1216 = l_Lean_Exception_isInterrupt(x_1215);
if (x_1216 == 0)
{
uint8_t x_1217; 
lean_inc(x_1215);
x_1217 = l_Lean_Exception_isRuntime(x_1215);
x_1050 = x_1177;
x_1051 = x_1181;
x_1052 = x_1186;
x_1053 = x_1184;
x_1054 = x_1215;
x_1055 = x_1174;
x_1056 = x_1175;
x_1057 = x_1188;
x_1058 = x_1209;
x_1059 = x_1179;
x_1060 = x_1180;
x_1061 = x_1183;
x_1062 = x_1217;
goto block_1086;
}
else
{
x_1050 = x_1177;
x_1051 = x_1181;
x_1052 = x_1186;
x_1053 = x_1184;
x_1054 = x_1215;
x_1055 = x_1174;
x_1056 = x_1175;
x_1057 = x_1188;
x_1058 = x_1209;
x_1059 = x_1179;
x_1060 = x_1180;
x_1061 = x_1183;
x_1062 = x_1216;
goto block_1086;
}
}
}
else
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; uint8_t x_1222; 
lean_dec_ref(x_1182);
lean_dec_ref(x_1179);
lean_inc(x_2);
x_1218 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1219 = lean_ctor_get(x_1218, 0);
lean_inc(x_1219);
lean_dec_ref(x_1218);
x_1220 = lean_nat_add(x_917, x_916);
lean_dec(x_917);
x_1221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1221, 0, x_1175);
lean_ctor_set(x_1221, 1, x_7);
x_1222 = lean_unbox(x_1219);
if (x_1222 == 0)
{
lean_object* x_1223; uint8_t x_1224; 
x_1223 = l_Lean_trace_profiler;
x_1224 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1180, x_1223);
if (x_1224 == 0)
{
lean_object* x_1225; 
lean_dec(x_1219);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1225 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1220, x_1174, x_1221, x_8, x_9, x_10, x_11);
x_135 = x_1177;
x_136 = x_1209;
x_137 = x_1180;
x_138 = x_1181;
x_139 = x_1186;
x_140 = x_1184;
x_141 = x_1183;
x_142 = x_1225;
goto block_145;
}
else
{
uint8_t x_1226; 
x_1226 = lean_unbox(x_1219);
lean_dec(x_1219);
x_746 = x_1177;
x_747 = x_1181;
x_748 = x_1186;
x_749 = x_1221;
x_750 = x_1184;
x_751 = x_1226;
x_752 = x_1174;
x_753 = x_1188;
x_754 = x_1209;
x_755 = x_1220;
x_756 = x_1180;
x_757 = x_1183;
goto block_797;
}
}
else
{
uint8_t x_1227; 
x_1227 = lean_unbox(x_1219);
lean_dec(x_1219);
x_746 = x_1177;
x_747 = x_1181;
x_748 = x_1186;
x_749 = x_1221;
x_750 = x_1184;
x_751 = x_1227;
x_752 = x_1174;
x_753 = x_1188;
x_754 = x_1209;
x_755 = x_1220;
x_756 = x_1180;
x_757 = x_1183;
goto block_797;
}
}
}
else
{
lean_object* x_1228; 
lean_dec_ref(x_1182);
lean_dec_ref(x_1179);
lean_dec(x_1175);
lean_dec(x_1174);
lean_dec(x_917);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1228 = lean_ctor_get(x_1210, 0);
lean_inc(x_1228);
lean_dec_ref(x_1210);
x_125 = x_1177;
x_126 = x_1209;
x_127 = x_1180;
x_128 = x_1181;
x_129 = x_1186;
x_130 = x_1183;
x_131 = x_1184;
x_132 = x_1228;
goto block_134;
}
}
}
block_1251:
{
if (x_1234 == 0)
{
lean_object* x_1235; 
lean_dec_ref(x_1232);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1231);
x_1235 = lean_apply_6(x_1233, x_1231, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1235) == 0)
{
lean_object* x_1236; 
x_1236 = lean_ctor_get(x_1235, 0);
lean_inc(x_1236);
lean_dec_ref(x_1235);
if (lean_obj_tag(x_1236) == 0)
{
lean_object* x_1237; lean_object* x_1238; 
x_1237 = lean_nat_add(x_917, x_916);
lean_dec(x_917);
x_1238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1238, 0, x_1231);
lean_ctor_set(x_1238, 1, x_7);
x_5 = x_1237;
x_6 = x_1230;
x_7 = x_1238;
goto _start;
}
else
{
lean_object* x_1240; lean_object* x_1241; 
lean_dec(x_1231);
x_1240 = lean_ctor_get(x_1236, 0);
lean_inc(x_1240);
lean_dec_ref(x_1236);
x_1241 = l_List_appendTR___redArg(x_1240, x_1230);
x_5 = x_917;
x_6 = x_1241;
goto _start;
}
}
else
{
lean_object* x_1243; lean_object* x_1244; uint8_t x_1245; uint8_t x_1250; 
lean_dec(x_1231);
lean_dec(x_1230);
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1243 = lean_ctor_get(x_1235, 0);
x_1250 = !lean_is_exclusive(x_1235);
if (x_1250 == 0)
{
x_1244 = x_1235;
x_1245 = x_1250;
goto block_1249;
}
else
{
lean_inc(x_1243);
lean_dec(x_1235);
x_1244 = lean_box(0);
x_1245 = x_1250;
goto block_1249;
}
block_1249:
{
lean_object* x_1246; 
if (x_1245 == 0)
{
x_1246 = x_1244;
goto block_1247;
}
else
{
lean_object* x_1248; 
x_1248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1248, 0, x_1243);
x_1246 = x_1248;
goto block_1247;
}
block_1247:
{
return x_1246;
}
}
}
}
else
{
lean_dec_ref(x_1233);
lean_dec(x_1231);
lean_dec(x_1230);
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1232;
}
}
block_1356:
{
if (lean_obj_tag(x_1252) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_1253; uint8_t x_1254; lean_object* x_1255; 
lean_dec(x_917);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1253 = lean_ctor_get(x_10, 2);
x_1254 = lean_ctor_get_uint8(x_1253, sizeof(void*)*1);
x_1255 = l_List_reverse___redArg(x_7);
if (x_1254 == 0)
{
lean_object* x_1256; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
x_1256 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1256, 0, x_1255);
return x_1256;
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; uint8_t x_1260; uint8_t x_1271; 
lean_inc(x_2);
x_1257 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1258 = lean_ctor_get(x_1257, 0);
x_1271 = !lean_is_exclusive(x_1257);
if (x_1271 == 0)
{
x_1259 = x_1257;
x_1260 = x_1271;
goto block_1270;
}
else
{
lean_inc(x_1258);
lean_dec(x_1257);
x_1259 = lean_box(0);
x_1260 = x_1271;
goto block_1270;
}
block_1270:
{
lean_object* x_1261; uint8_t x_1262; 
x_1261 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1262 = lean_unbox(x_1258);
if (x_1262 == 0)
{
lean_object* x_1263; uint8_t x_1264; 
x_1263 = l_Lean_trace_profiler;
x_1264 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1253, x_1263);
if (x_1264 == 0)
{
lean_object* x_1265; 
lean_dec(x_1258);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
if (x_1260 == 0)
{
lean_ctor_set(x_1259, 0, x_1255);
x_1265 = x_1259;
goto block_1266;
}
else
{
lean_object* x_1267; 
x_1267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1267, 0, x_1255);
x_1265 = x_1267;
goto block_1266;
}
block_1266:
{
return x_1265;
}
}
else
{
uint8_t x_1268; 
lean_del_object(x_1259);
x_1268 = lean_unbox(x_1258);
lean_dec(x_1258);
lean_inc_ref(x_1253);
x_289 = x_1268;
x_290 = x_1255;
x_291 = x_1261;
x_292 = x_1253;
x_293 = x_1254;
goto block_329;
}
}
else
{
uint8_t x_1269; 
lean_del_object(x_1259);
x_1269 = lean_unbox(x_1258);
lean_dec(x_1258);
lean_inc_ref(x_1253);
x_289 = x_1269;
x_290 = x_1255;
x_291 = x_1261;
x_292 = x_1253;
x_293 = x_1254;
goto block_329;
}
}
}
}
else
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; uint8_t x_1275; uint8_t x_1353; 
x_1272 = lean_ctor_get(x_6, 0);
x_1273 = lean_ctor_get(x_6, 1);
x_1353 = !lean_is_exclusive(x_6);
if (x_1353 == 0)
{
x_1274 = x_6;
x_1275 = x_1353;
goto block_1352;
}
else
{
lean_inc(x_1273);
lean_inc(x_1272);
lean_dec(x_6);
x_1274 = lean_box(0);
x_1275 = x_1353;
goto block_1352;
}
block_1352:
{
lean_object* x_1276; lean_object* x_1277; uint8_t x_1278; uint8_t x_1279; 
x_1276 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_1272, x_9);
x_1277 = lean_ctor_get(x_1276, 0);
lean_inc(x_1277);
lean_dec_ref(x_1276);
x_1278 = 1;
x_1279 = lean_unbox(x_1277);
lean_dec(x_1277);
if (x_1279 == 0)
{
lean_object* x_1280; uint8_t x_1281; 
x_1280 = lean_ctor_get(x_10, 2);
x_1281 = lean_ctor_get_uint8(x_1280, sizeof(void*)*1);
if (x_1281 == 0)
{
lean_object* x_1282; 
lean_inc_ref(x_202);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1272);
x_1282 = lean_apply_6(x_202, x_1272, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1282) == 0)
{
lean_object* x_1283; uint8_t x_1284; 
x_1283 = lean_ctor_get(x_1282, 0);
lean_inc(x_1283);
lean_dec_ref(x_1282);
x_1284 = lean_unbox(x_1283);
lean_dec(x_1283);
if (x_1284 == 0)
{
lean_object* x_1285; lean_object* x_1286; 
lean_del_object(x_1274);
lean_inc(x_7);
lean_inc(x_917);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc(x_1273);
x_1285 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(x_1285, 0, x_1273);
lean_closure_set(x_1285, 1, x_1);
lean_closure_set(x_1285, 2, x_2);
lean_closure_set(x_1285, 3, x_3);
lean_closure_set(x_1285, 4, x_4);
lean_closure_set(x_1285, 5, x_917);
lean_closure_set(x_1285, 6, x_7);
lean_inc_ref(x_3);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1272);
x_1286 = lean_apply_7(x_3, x_1272, x_1285, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1286) == 0)
{
lean_dec(x_1273);
lean_dec(x_1272);
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1286;
}
else
{
lean_object* x_1287; uint8_t x_1288; 
x_1287 = lean_ctor_get(x_1286, 0);
lean_inc(x_1287);
x_1288 = l_Lean_Exception_isInterrupt(x_1287);
if (x_1288 == 0)
{
uint8_t x_1289; 
x_1289 = l_Lean_Exception_isRuntime(x_1287);
lean_inc_ref(x_203);
x_1230 = x_1273;
x_1231 = x_1272;
x_1232 = x_1286;
x_1233 = x_203;
x_1234 = x_1289;
goto block_1251;
}
else
{
lean_dec(x_1287);
lean_inc_ref(x_203);
x_1230 = x_1273;
x_1231 = x_1272;
x_1232 = x_1286;
x_1233 = x_203;
x_1234 = x_1288;
goto block_1251;
}
}
}
else
{
lean_object* x_1290; lean_object* x_1291; 
x_1290 = lean_nat_add(x_917, x_916);
lean_dec(x_917);
if (x_1275 == 0)
{
lean_ctor_set(x_1274, 1, x_7);
x_1291 = x_1274;
goto block_1293;
}
else
{
lean_object* x_1294; 
x_1294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1294, 0, x_1272);
lean_ctor_set(x_1294, 1, x_7);
x_1291 = x_1294;
goto block_1293;
}
block_1293:
{
x_5 = x_1290;
x_6 = x_1273;
x_7 = x_1291;
goto _start;
}
}
}
else
{
lean_object* x_1295; lean_object* x_1296; uint8_t x_1297; uint8_t x_1302; 
lean_del_object(x_1274);
lean_dec(x_1273);
lean_dec(x_1272);
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1295 = lean_ctor_get(x_1282, 0);
x_1302 = !lean_is_exclusive(x_1282);
if (x_1302 == 0)
{
x_1296 = x_1282;
x_1297 = x_1302;
goto block_1301;
}
else
{
lean_inc(x_1295);
lean_dec(x_1282);
x_1296 = lean_box(0);
x_1297 = x_1302;
goto block_1301;
}
block_1301:
{
lean_object* x_1298; 
if (x_1297 == 0)
{
x_1298 = x_1296;
goto block_1299;
}
else
{
lean_object* x_1300; 
x_1300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1300, 0, x_1295);
x_1298 = x_1300;
goto block_1299;
}
block_1299:
{
return x_1298;
}
}
}
}
else
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; uint8_t x_1308; 
lean_inc(x_2);
x_1303 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
lean_dec_ref(x_1303);
lean_inc(x_7);
lean_inc(x_917);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc(x_1273);
x_1305 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10___boxed), 13, 7);
lean_closure_set(x_1305, 0, x_1273);
lean_closure_set(x_1305, 1, x_1);
lean_closure_set(x_1305, 2, x_2);
lean_closure_set(x_1305, 3, x_3);
lean_closure_set(x_1305, 4, x_4);
lean_closure_set(x_1305, 5, x_917);
lean_closure_set(x_1305, 6, x_7);
lean_inc(x_1272);
x_1306 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(x_1306, 0, x_1272);
x_1307 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1308 = lean_unbox(x_1304);
if (x_1308 == 0)
{
lean_object* x_1309; uint8_t x_1310; 
x_1309 = l_Lean_trace_profiler;
x_1310 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1280, x_1309);
if (x_1310 == 0)
{
lean_object* x_1311; 
lean_dec_ref(x_1306);
lean_dec(x_1304);
lean_inc_ref(x_202);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1272);
x_1311 = lean_apply_6(x_202, x_1272, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1311) == 0)
{
lean_object* x_1312; uint8_t x_1313; 
x_1312 = lean_ctor_get(x_1311, 0);
lean_inc(x_1312);
lean_dec_ref(x_1311);
x_1313 = lean_unbox(x_1312);
lean_dec(x_1312);
if (x_1313 == 0)
{
lean_object* x_1314; 
lean_del_object(x_1274);
lean_inc_ref(x_3);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1272);
x_1314 = lean_apply_7(x_3, x_1272, x_1305, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1314) == 0)
{
lean_dec(x_1273);
lean_dec(x_1272);
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1314;
}
else
{
lean_object* x_1315; uint8_t x_1316; 
x_1315 = lean_ctor_get(x_1314, 0);
lean_inc(x_1315);
x_1316 = l_Lean_Exception_isInterrupt(x_1315);
if (x_1316 == 0)
{
uint8_t x_1317; 
x_1317 = l_Lean_Exception_isRuntime(x_1315);
lean_inc_ref(x_1280);
lean_inc_ref(x_203);
x_964 = x_1310;
x_965 = x_1273;
x_966 = x_1272;
x_967 = x_1314;
x_968 = x_1278;
x_969 = x_203;
x_970 = x_1280;
x_971 = x_1307;
x_972 = x_1317;
goto block_999;
}
else
{
lean_dec(x_1315);
lean_inc_ref(x_1280);
lean_inc_ref(x_203);
x_964 = x_1310;
x_965 = x_1273;
x_966 = x_1272;
x_967 = x_1314;
x_968 = x_1278;
x_969 = x_203;
x_970 = x_1280;
x_971 = x_1307;
x_972 = x_1316;
goto block_999;
}
}
}
else
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; 
lean_dec_ref(x_1305);
lean_inc(x_2);
x_1318 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1319 = lean_ctor_get(x_1318, 0);
lean_inc(x_1319);
lean_dec_ref(x_1318);
x_1320 = lean_nat_add(x_917, x_916);
lean_dec(x_917);
if (x_1275 == 0)
{
lean_ctor_set(x_1274, 1, x_7);
x_1321 = x_1274;
goto block_1326;
}
else
{
lean_object* x_1327; 
x_1327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1327, 0, x_1272);
lean_ctor_set(x_1327, 1, x_7);
x_1321 = x_1327;
goto block_1326;
}
block_1326:
{
uint8_t x_1322; 
x_1322 = lean_unbox(x_1319);
if (x_1322 == 0)
{
if (x_1310 == 0)
{
lean_dec(x_1319);
x_5 = x_1320;
x_6 = x_1273;
x_7 = x_1321;
goto _start;
}
else
{
uint8_t x_1324; 
x_1324 = lean_unbox(x_1319);
lean_dec(x_1319);
lean_inc_ref(x_1280);
x_240 = x_1273;
x_241 = x_1278;
x_242 = x_1324;
x_243 = x_1320;
x_244 = x_1321;
x_245 = x_1280;
x_246 = x_1307;
goto block_287;
}
}
else
{
uint8_t x_1325; 
x_1325 = lean_unbox(x_1319);
lean_dec(x_1319);
lean_inc_ref(x_1280);
x_240 = x_1273;
x_241 = x_1278;
x_242 = x_1325;
x_243 = x_1320;
x_244 = x_1321;
x_245 = x_1280;
x_246 = x_1307;
goto block_287;
}
}
}
}
else
{
lean_object* x_1328; lean_object* x_1329; uint8_t x_1330; uint8_t x_1335; 
lean_dec_ref(x_1305);
lean_del_object(x_1274);
lean_dec(x_1273);
lean_dec(x_1272);
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1328 = lean_ctor_get(x_1311, 0);
x_1335 = !lean_is_exclusive(x_1311);
if (x_1335 == 0)
{
x_1329 = x_1311;
x_1330 = x_1335;
goto block_1334;
}
else
{
lean_inc(x_1328);
lean_dec(x_1311);
x_1329 = lean_box(0);
x_1330 = x_1335;
goto block_1334;
}
block_1334:
{
lean_object* x_1331; 
if (x_1330 == 0)
{
x_1331 = x_1329;
goto block_1332;
}
else
{
lean_object* x_1333; 
x_1333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1333, 0, x_1328);
x_1331 = x_1333;
goto block_1332;
}
block_1332:
{
return x_1331;
}
}
}
}
else
{
uint8_t x_1336; 
lean_del_object(x_1274);
x_1336 = lean_unbox(x_1304);
lean_dec(x_1304);
lean_inc_ref(x_1280);
lean_inc_ref(x_203);
lean_inc_ref(x_1305);
lean_inc_ref(x_202);
x_1174 = x_1273;
x_1175 = x_1272;
x_1176 = x_202;
x_1177 = x_1278;
x_1178 = x_1305;
x_1179 = x_203;
x_1180 = x_1280;
x_1181 = x_1307;
x_1182 = x_1305;
x_1183 = x_1336;
x_1184 = x_1306;
goto block_1229;
}
}
else
{
uint8_t x_1337; 
lean_del_object(x_1274);
x_1337 = lean_unbox(x_1304);
lean_dec(x_1304);
lean_inc_ref(x_1280);
lean_inc_ref(x_203);
lean_inc_ref(x_1305);
lean_inc_ref(x_202);
x_1174 = x_1273;
x_1175 = x_1272;
x_1176 = x_202;
x_1177 = x_1278;
x_1178 = x_1305;
x_1179 = x_203;
x_1180 = x_1280;
x_1181 = x_1307;
x_1182 = x_1305;
x_1183 = x_1337;
x_1184 = x_1306;
goto block_1229;
}
}
}
else
{
lean_object* x_1338; uint8_t x_1339; lean_object* x_1340; 
lean_del_object(x_1274);
x_1338 = lean_ctor_get(x_10, 2);
x_1339 = lean_ctor_get_uint8(x_1338, sizeof(void*)*1);
x_1340 = lean_nat_add(x_917, x_916);
lean_dec(x_917);
if (x_1339 == 0)
{
lean_dec(x_1272);
x_5 = x_1340;
x_6 = x_1273;
goto _start;
}
else
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; uint8_t x_1346; 
lean_inc(x_2);
x_1342 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1343 = lean_ctor_get(x_1342, 0);
lean_inc(x_1343);
lean_dec_ref(x_1342);
x_1344 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(x_1344, 0, x_1272);
x_1345 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1346 = lean_unbox(x_1343);
if (x_1346 == 0)
{
lean_object* x_1347; uint8_t x_1348; 
x_1347 = l_Lean_trace_profiler;
x_1348 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1338, x_1347);
if (x_1348 == 0)
{
lean_dec_ref(x_1344);
lean_dec(x_1343);
x_5 = x_1340;
x_6 = x_1273;
goto _start;
}
else
{
uint8_t x_1350; 
x_1350 = lean_unbox(x_1343);
lean_dec(x_1343);
lean_inc_ref(x_1338);
x_50 = x_1273;
x_51 = x_1340;
x_52 = x_1278;
x_53 = x_1350;
x_54 = x_1338;
x_55 = x_1345;
x_56 = x_1344;
goto block_97;
}
}
else
{
uint8_t x_1351; 
x_1351 = lean_unbox(x_1343);
lean_dec(x_1343);
lean_inc_ref(x_1338);
x_50 = x_1273;
x_51 = x_1340;
x_52 = x_1278;
x_53 = x_1351;
x_54 = x_1338;
x_55 = x_1345;
x_56 = x_1344;
goto block_97;
}
}
}
}
}
}
else
{
lean_object* x_1354; 
lean_dec(x_6);
x_1354 = lean_ctor_get(x_1252, 0);
lean_inc(x_1354);
lean_dec_ref(x_1252);
x_5 = x_917;
x_6 = x_1354;
goto _start;
}
}
block_1367:
{
if (lean_obj_tag(x_1357) == 0)
{
lean_object* x_1358; 
x_1358 = lean_ctor_get(x_1357, 0);
lean_inc(x_1358);
lean_dec_ref(x_1357);
x_1252 = x_1358;
goto block_1356;
}
else
{
lean_object* x_1359; lean_object* x_1360; uint8_t x_1361; uint8_t x_1366; 
lean_dec(x_917);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1359 = lean_ctor_get(x_1357, 0);
x_1366 = !lean_is_exclusive(x_1357);
if (x_1366 == 0)
{
x_1360 = x_1357;
x_1361 = x_1366;
goto block_1365;
}
else
{
lean_inc(x_1359);
lean_dec(x_1357);
x_1360 = lean_box(0);
x_1361 = x_1366;
goto block_1365;
}
block_1365:
{
lean_object* x_1362; 
if (x_1361 == 0)
{
x_1362 = x_1360;
goto block_1363;
}
else
{
lean_object* x_1364; 
x_1364 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1364, 0, x_1359);
x_1362 = x_1364;
goto block_1363;
}
block_1363:
{
return x_1362;
}
}
}
}
}
block_29:
{
lean_object* x_21; double x_22; double x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_io_get_num_heartbeats();
x_22 = lean_float_of_nat(x_13);
x_23 = lean_float_of_nat(x_21);
x_24 = lean_box_float(x_22);
x_25 = lean_box_float(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_14, x_19, x_17, x_16, x_15, x_18, x_27, x_8, x_9, x_10, x_11);
lean_dec_ref(x_17);
return x_28;
}
block_49:
{
lean_object* x_38; double x_39; double x_40; double x_41; double x_42; double x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_io_mono_nanos_now();
x_39 = lean_float_of_nat(x_32);
x_40 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_41 = lean_float_div(x_39, x_40);
x_42 = lean_float_of_nat(x_38);
x_43 = lean_float_div(x_42, x_40);
x_44 = lean_box_float(x_41);
x_45 = lean_box_float(x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
x_48 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_30, x_36, x_34, x_33, x_31, x_35, x_47, x_8, x_9, x_10, x_11);
lean_dec_ref(x_34);
return x_48;
}
block_97:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Lean_trace_profiler_useHeartbeats;
x_60 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_54, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_io_mono_nanos_now();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_62 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_51, x_50, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
x_63 = lean_ctor_get(x_62, 0);
x_70 = !lean_is_exclusive(x_62);
if (x_70 == 0)
{
x_64 = x_62;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
lean_ctor_set_tag(x_64, 1);
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
x_30 = x_52;
x_31 = x_58;
x_32 = x_61;
x_33 = x_53;
x_34 = x_54;
x_35 = x_56;
x_36 = x_55;
x_37 = x_66;
goto block_49;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
x_71 = lean_ctor_get(x_62, 0);
x_78 = !lean_is_exclusive(x_62);
if (x_78 == 0)
{
x_72 = x_62;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_62);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
lean_ctor_set_tag(x_72, 0);
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
x_30 = x_52;
x_31 = x_58;
x_32 = x_61;
x_33 = x_53;
x_34 = x_54;
x_35 = x_56;
x_36 = x_55;
x_37 = x_74;
goto block_49;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_io_get_num_heartbeats();
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_80 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_51, x_50, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
x_81 = lean_ctor_get(x_80, 0);
x_88 = !lean_is_exclusive(x_80);
if (x_88 == 0)
{
x_82 = x_80;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
lean_ctor_set_tag(x_82, 1);
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
x_13 = x_79;
x_14 = x_52;
x_15 = x_58;
x_16 = x_53;
x_17 = x_54;
x_18 = x_56;
x_19 = x_55;
x_20 = x_84;
goto block_29;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
x_89 = lean_ctor_get(x_80, 0);
x_96 = !lean_is_exclusive(x_80);
if (x_96 == 0)
{
x_90 = x_80;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_80);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
lean_ctor_set_tag(x_90, 0);
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
x_13 = x_79;
x_14 = x_52;
x_15 = x_58;
x_16 = x_53;
x_17 = x_54;
x_18 = x_56;
x_19 = x_55;
x_20 = x_92;
goto block_29;
}
}
}
}
}
block_114:
{
lean_object* x_106; double x_107; double x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_io_get_num_heartbeats();
x_107 = lean_float_of_nat(x_99);
x_108 = lean_float_of_nat(x_106);
x_109 = lean_box_float(x_107);
x_110 = lean_box_float(x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_105);
lean_ctor_set(x_112, 1, x_111);
x_113 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_98, x_101, x_100, x_104, x_102, x_103, x_112, x_8, x_9, x_10, x_11);
lean_dec_ref(x_100);
return x_113;
}
block_124:
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_98 = x_115;
x_99 = x_116;
x_100 = x_117;
x_101 = x_118;
x_102 = x_119;
x_103 = x_121;
x_104 = x_120;
x_105 = x_123;
goto block_114;
}
block_134:
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_98 = x_125;
x_99 = x_126;
x_100 = x_127;
x_101 = x_128;
x_102 = x_129;
x_103 = x_131;
x_104 = x_130;
x_105 = x_133;
goto block_114;
}
block_145:
{
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_115 = x_135;
x_116 = x_136;
x_117 = x_137;
x_118 = x_138;
x_119 = x_139;
x_120 = x_141;
x_121 = x_140;
x_122 = x_143;
goto block_124;
}
else
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
lean_dec_ref(x_142);
x_125 = x_135;
x_126 = x_136;
x_127 = x_137;
x_128 = x_138;
x_129 = x_139;
x_130 = x_141;
x_131 = x_140;
x_132 = x_144;
goto block_134;
}
}
block_165:
{
lean_object* x_154; double x_155; double x_156; double x_157; double x_158; double x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_154 = lean_io_mono_nanos_now();
x_155 = lean_float_of_nat(x_149);
x_156 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_157 = lean_float_div(x_155, x_156);
x_158 = lean_float_of_nat(x_154);
x_159 = lean_float_div(x_158, x_156);
x_160 = lean_box_float(x_157);
x_161 = lean_box_float(x_159);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_153);
lean_ctor_set(x_163, 1, x_162);
x_164 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_146, x_148, x_147, x_152, x_150, x_151, x_163, x_8, x_9, x_10, x_11);
lean_dec_ref(x_147);
return x_164;
}
block_175:
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_146 = x_166;
x_147 = x_167;
x_148 = x_169;
x_149 = x_168;
x_150 = x_170;
x_151 = x_172;
x_152 = x_171;
x_153 = x_174;
goto block_165;
}
block_185:
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_183);
x_146 = x_176;
x_147 = x_177;
x_148 = x_179;
x_149 = x_178;
x_150 = x_180;
x_151 = x_182;
x_152 = x_181;
x_153 = x_184;
goto block_165;
}
block_196:
{
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
x_166 = x_186;
x_167 = x_187;
x_168 = x_189;
x_169 = x_188;
x_170 = x_190;
x_171 = x_192;
x_172 = x_191;
x_173 = x_194;
goto block_175;
}
else
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
lean_dec_ref(x_193);
x_176 = x_186;
x_177 = x_187;
x_178 = x_189;
x_179 = x_188;
x_180 = x_190;
x_181 = x_192;
x_182 = x_191;
x_183 = x_195;
goto block_185;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_List_appendTR___redArg(x_8, x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed), 12, 7);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_5);
lean_closure_set(x_15, 4, x_6);
lean_closure_set(x_15, 5, x_14);
lean_closure_set(x_15, 6, x_7);
x_16 = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__5___redArg(x_15, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___redArg(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__11_spec__13_spec__16(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__7_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__5_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__3_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_11, x_13, x_12, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_MessageData_ofFormat(x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_31; 
x_12 = lean_ctor_get(x_11, 0);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
x_13 = x_11;
x_14 = x_31;
goto block_30;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
x_16 = lean_box(0);
x_17 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_10, x_16);
x_18 = l_Lean_MessageData_ofList(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__5);
x_23 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_12, x_16);
x_24 = l_Lean_MessageData_ofList(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_26);
x_27 = x_13;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec(x_10);
x_32 = lean_ctor_get(x_11, 0);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
x_33 = x_11;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_2);
x_40 = lean_ctor_get(x_9, 0);
x_47 = !lean_is_exclusive(x_9);
if (x_47 == 0)
{
x_41 = x_9;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_9);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarIds(x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_29; 
x_12 = lean_ctor_get(x_11, 0);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
x_13 = x_11;
x_14 = x_29;
goto block_28;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
x_16 = lean_box(0);
x_17 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_10, x_16);
x_18 = l_Lean_MessageData_ofList(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_12, x_16);
x_23 = l_Lean_MessageData_ofList(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_24);
x_25 = x_13;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_10);
x_30 = lean_ctor_get(x_11, 0);
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
x_31 = x_11;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_2);
x_38 = lean_ctor_get(x_9, 0);
x_45 = !lean_is_exclusive(x_9);
if (x_45 == 0)
{
x_39 = x_9;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_9);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_23; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
x_9 = x_2;
x_10 = x_23;
goto block_22;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_23;
goto block_22;
}
block_22:
{
uint8_t x_16; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_7, x_4);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
goto block_15;
}
else
{
x_16 = x_1;
goto block_18;
}
block_15:
{
lean_object* x_11; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_3);
x_11 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_3);
x_11 = x_14;
goto block_13;
}
block_13:
{
x_2 = x_8;
x_3 = x_11;
goto _start;
}
}
block_18:
{
if (x_16 == 0)
{
lean_del_object(x_9);
lean_dec(x_7);
x_2 = x_8;
goto _start;
}
else
{
goto block_15;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_6, x_2, x_3, x_4);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___00Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_10 = lean_array_to_list(x_3);
x_11 = lean_array_to_list(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec_ref(x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_14);
lean_inc(x_1);
x_16 = l_Lean_MVarId_isIndependentOf(x_1, x_14, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_array_push(x_4, x_14);
x_2 = x_15;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
x_21 = lean_array_push(x_3, x_14);
x_2 = x_15;
x_3 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_23 = lean_ctor_get(x_16, 0);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
x_24 = x_16;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_array_push(x_2, x_6);
x_1 = x_5;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_1 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_9 = l_List_reverse___redArg(x_3);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_57; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_57 = !lean_is_exclusive(x_2);
if (x_57 == 0)
{
x_13 = x_2;
x_14 = x_57;
goto block_56;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_15; lean_object* x_21; 
x_21 = l_Lean_Meta_saveState___redArg(x_5, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc_ref(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_11);
x_23 = lean_apply_6(x_1, x_11, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_15 = x_25;
goto block_20;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_47; 
x_26 = lean_ctor_get(x_23, 0);
x_47 = !lean_is_exclusive(x_23);
if (x_47 == 0)
{
x_27 = x_23;
x_28 = x_47;
goto block_46;
}
else
{
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = x_47;
goto block_46;
}
block_46:
{
uint8_t x_29; uint8_t x_44; 
x_44 = l_Lean_Exception_isInterrupt(x_26);
if (x_44 == 0)
{
uint8_t x_45; 
lean_inc(x_26);
x_45 = l_Lean_Exception_isRuntime(x_26);
x_29 = x_45;
goto block_43;
}
else
{
x_29 = x_44;
goto block_43;
}
block_43:
{
if (x_29 == 0)
{
lean_object* x_30; 
lean_del_object(x_27);
lean_dec(x_26);
x_30 = l_Lean_Meta_SavedState_restore___redArg(x_22, x_5, x_7);
lean_dec(x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec_ref(x_30);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_11);
x_15 = x_31;
goto block_20;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_30, 0);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
x_33 = x_30;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_22);
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
if (x_28 == 0)
{
x_40 = x_27;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_26);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_21, 0);
x_55 = !lean_is_exclusive(x_21);
if (x_55 == 0)
{
x_49 = x_21;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_21);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
block_20:
{
lean_object* x_16; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_3);
x_16 = x_19;
goto block_18;
}
block_18:
{
x_2 = x_12;
x_3 = x_16;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_array_push(x_2, x_6);
x_1 = x_5;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec_ref(x_1);
x_1 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(x_2, x_1, x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_21; 
x_10 = lean_ctor_get(x_9, 0);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
x_11 = x_9;
x_12 = x_21;
goto block_20;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = ((lean_object*)(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0));
lean_inc(x_10);
x_14 = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(x_10, x_13);
x_15 = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(x_10, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_16);
x_17 = x_11;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
x_22 = lean_ctor_get(x_9, 0);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
x_23 = x_9;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_23; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
x_10 = x_3;
x_11 = x_23;
goto block_22;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_23;
goto block_22;
}
block_22:
{
uint8_t x_12; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_8, x_5);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
x_12 = x_1;
goto block_18;
}
else
{
x_12 = x_2;
goto block_18;
}
block_18:
{
if (x_12 == 0)
{
lean_del_object(x_10);
lean_dec(x_8);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_14; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_4);
x_14 = x_10;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_4);
x_14 = x_17;
goto block_16;
}
block_16:
{
x_3 = x_9;
x_4 = x_14;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox(x_2);
x_9 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_7, x_8, x_3, x_4, x_5);
lean_dec(x_5);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2));
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(x_5, x_6, x_15, x_15, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_1261; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get(x_17, 1);
x_1261 = !lean_is_exclusive(x_17);
if (x_1261 == 0)
{
x_20 = x_17;
x_21 = x_1261;
goto block_1260;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = x_1261;
goto block_1260;
}
block_1260:
{
uint8_t x_22; 
x_22 = l_List_isEmpty___redArg(x_18);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_6);
x_23 = lean_ctor_get(x_9, 2);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*1);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_4);
if (x_24 == 0)
{
lean_object* x_26; 
lean_del_object(x_20);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_26 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_18, x_25, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_96; 
x_27 = lean_ctor_get(x_26, 0);
x_96 = !lean_is_exclusive(x_26);
if (x_96 == 0)
{
x_28 = x_26;
x_29 = x_96;
goto block_95;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_40; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_56; lean_object* x_71; lean_object* x_90; lean_object* x_91; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_31, x_15);
x_90 = lean_box(0);
x_91 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_24, x_5, x_90, x_8);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = l_List_reverse___redArg(x_92);
x_71 = x_93;
goto block_89;
}
else
{
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_dec_ref(x_91);
x_71 = x_94;
goto block_89;
}
else
{
lean_dec(x_32);
lean_dec(x_30);
lean_del_object(x_28);
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_91;
}
}
block_39:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_List_appendTR___redArg(x_32, x_30);
x_35 = l_List_appendTR___redArg(x_34, x_33);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_35);
x_36 = x_28;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
block_42:
{
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_33 = x_41;
goto block_39;
}
else
{
lean_dec(x_32);
lean_dec(x_30);
lean_del_object(x_28);
return x_40;
}
}
block_55:
{
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec_ref(x_44);
x_46 = l_Lean_Meta_SavedState_restore___redArg(x_43, x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_dec_ref(x_46);
x_33 = x_19;
goto block_39;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_32);
lean_dec(x_30);
lean_del_object(x_28);
lean_dec(x_19);
x_47 = lean_ctor_get(x_46, 0);
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
x_48 = x_46;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_dec_ref(x_43);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_8);
x_40 = x_44;
goto block_42;
}
}
block_70:
{
uint8_t x_57; 
x_57 = l_List_isEmpty___redArg(x_30);
lean_dec(x_30);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_58 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
x_59 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_58, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_59;
}
else
{
lean_object* x_60; 
x_60 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_56, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_69; 
x_61 = lean_ctor_get(x_60, 0);
x_69 = !lean_is_exclusive(x_60);
if (x_69 == 0)
{
x_62 = x_60;
x_63 = x_69;
goto block_68;
}
else
{
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_box(0);
x_63 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_List_appendTR___redArg(x_32, x_61);
if (x_63 == 0)
{
lean_ctor_set(x_62, 0, x_64);
x_65 = x_62;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
else
{
lean_dec(x_32);
return x_60;
}
}
}
block_89:
{
uint8_t x_72; lean_object* x_73; 
x_72 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_32);
x_73 = l_List_appendTR___redArg(x_71, x_32);
if (x_72 == 0)
{
lean_del_object(x_28);
x_56 = x_73;
goto block_70;
}
else
{
uint8_t x_74; 
x_74 = l_List_isEmpty___redArg(x_32);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_19);
x_77 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_73, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_77) == 0)
{
lean_dec(x_76);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_8);
x_40 = x_77;
goto block_42;
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = l_Lean_Exception_isInterrupt(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Exception_isRuntime(x_78);
x_43 = x_76;
x_44 = x_77;
x_45 = x_80;
goto block_55;
}
else
{
lean_dec(x_78);
x_43 = x_76;
x_44 = x_77;
x_45 = x_79;
goto block_55;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec(x_73);
lean_dec(x_32);
lean_dec(x_30);
lean_del_object(x_28);
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_81 = lean_ctor_get(x_75, 0);
x_88 = !lean_is_exclusive(x_75);
if (x_88 == 0)
{
x_82 = x_75;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
else
{
lean_del_object(x_28);
x_56 = x_73;
goto block_70;
}
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_104; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_26, 0);
x_104 = !lean_is_exclusive(x_26);
if (x_104 == 0)
{
x_98 = x_26;
x_99 = x_104;
goto block_103;
}
else
{
lean_inc(x_97);
lean_dec(x_26);
x_98 = lean_box(0);
x_99 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_100; 
if (x_99 == 0)
{
x_100 = x_98;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_97);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
}
}
}
}
else
{
lean_object* x_105; 
lean_inc(x_2);
x_105 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_435; lean_object* x_436; uint8_t x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; lean_object* x_474; lean_object* x_475; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; lean_object* x_495; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; lean_object* x_543; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; lean_object* x_562; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; lean_object* x_573; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; uint8_t x_582; lean_object* x_583; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; lean_object* x_592; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; uint8_t x_601; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; uint8_t x_613; lean_object* x_614; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; lean_object* x_628; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; lean_object* x_641; uint8_t x_642; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; uint8_t x_653; lean_object* x_654; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_670; uint8_t x_671; lean_object* x_672; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; uint8_t x_682; lean_object* x_683; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; lean_object* x_699; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; uint8_t x_709; lean_object* x_710; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; uint8_t x_719; lean_object* x_720; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; uint8_t x_728; lean_object* x_729; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; uint8_t x_740; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; uint8_t x_753; uint8_t x_754; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; lean_object* x_767; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; uint8_t x_779; lean_object* x_780; uint8_t x_781; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; uint8_t x_793; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; uint8_t x_809; uint8_t x_810; lean_object* x_811; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; uint8_t x_822; uint8_t x_823; lean_object* x_841; lean_object* x_842; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; uint8_t x_851; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; uint8_t x_871; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; uint8_t x_892; lean_object* x_893; uint8_t x_955; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
lean_inc(x_19);
lean_inc(x_18);
x_107 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(x_107, 0, x_18);
lean_closure_set(x_107, 1, x_19);
x_108 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_955 = lean_unbox(x_106);
if (x_955 == 0)
{
lean_object* x_956; uint8_t x_957; 
x_956 = l_Lean_trace_profiler;
x_957 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_23, x_956);
if (x_957 == 0)
{
lean_object* x_958; 
lean_dec_ref(x_107);
lean_dec(x_106);
lean_del_object(x_20);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_958 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_18, x_25, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; uint8_t x_963; uint8_t x_1240; 
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
lean_dec_ref(x_958);
x_960 = lean_ctor_get(x_959, 0);
x_961 = lean_ctor_get(x_959, 1);
x_1240 = !lean_is_exclusive(x_959);
if (x_1240 == 0)
{
x_962 = x_959;
x_963 = x_1240;
goto block_1239;
}
else
{
lean_inc(x_961);
lean_inc(x_960);
lean_dec(x_959);
x_962 = lean_box(0);
x_963 = x_1240;
goto block_1239;
}
block_1239:
{
lean_object* x_964; 
lean_inc(x_2);
x_964 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; uint8_t x_967; uint8_t x_1230; 
x_965 = lean_ctor_get(x_964, 0);
x_1230 = !lean_is_exclusive(x_964);
if (x_1230 == 0)
{
x_966 = x_964;
x_967 = x_1230;
goto block_1229;
}
else
{
lean_inc(x_965);
lean_dec(x_964);
x_966 = lean_box(0);
x_967 = x_1230;
goto block_1229;
}
block_1229:
{
lean_object* x_968; lean_object* x_969; lean_object* x_982; lean_object* x_989; lean_object* x_992; lean_object* x_993; uint8_t x_994; lean_object* x_1005; lean_object* x_1021; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; uint8_t x_1067; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; uint8_t x_1077; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; uint8_t x_1090; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1105; lean_object* x_1106; uint8_t x_1107; lean_object* x_1108; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1151; lean_object* x_1152; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; uint8_t x_1159; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; uint8_t x_1175; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1190; lean_object* x_1191; uint8_t x_1192; lean_object* x_1193; lean_object* x_1198; uint8_t x_1224; 
x_968 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_961, x_15);
lean_inc(x_968);
lean_inc(x_960);
x_1026 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(x_1026, 0, x_960);
lean_closure_set(x_1026, 1, x_968);
x_1198 = lean_box(0);
x_1224 = lean_unbox(x_965);
if (x_1224 == 0)
{
if (x_957 == 0)
{
lean_object* x_1225; 
lean_dec_ref(x_1026);
lean_dec(x_965);
lean_del_object(x_962);
x_1225 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_24, x_957, x_5, x_1198, x_8);
if (lean_obj_tag(x_1225) == 0)
{
lean_object* x_1226; lean_object* x_1227; 
x_1226 = lean_ctor_get(x_1225, 0);
lean_inc(x_1226);
lean_dec_ref(x_1225);
x_1227 = l_List_reverse___redArg(x_1226);
x_1021 = x_1227;
goto block_1025;
}
else
{
if (lean_obj_tag(x_1225) == 0)
{
lean_object* x_1228; 
x_1228 = lean_ctor_get(x_1225, 0);
lean_inc(x_1228);
lean_dec_ref(x_1225);
x_1021 = x_1228;
goto block_1025;
}
else
{
lean_dec(x_968);
lean_del_object(x_966);
lean_dec(x_960);
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1225;
}
}
}
else
{
lean_inc_ref(x_23);
lean_del_object(x_966);
goto block_1223;
}
}
else
{
lean_inc_ref(x_23);
lean_del_object(x_966);
goto block_1223;
}
block_981:
{
uint8_t x_970; 
x_970 = l_List_isEmpty___redArg(x_960);
lean_dec(x_960);
if (x_970 == 0)
{
lean_dec(x_969);
lean_dec(x_968);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_14;
}
else
{
if (x_957 == 0)
{
lean_object* x_971; 
x_971 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_969, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_971) == 0)
{
lean_object* x_972; lean_object* x_973; uint8_t x_974; uint8_t x_980; 
x_972 = lean_ctor_get(x_971, 0);
x_980 = !lean_is_exclusive(x_971);
if (x_980 == 0)
{
x_973 = x_971;
x_974 = x_980;
goto block_979;
}
else
{
lean_inc(x_972);
lean_dec(x_971);
x_973 = lean_box(0);
x_974 = x_980;
goto block_979;
}
block_979:
{
lean_object* x_975; lean_object* x_976; 
x_975 = l_List_appendTR___redArg(x_968, x_972);
if (x_974 == 0)
{
lean_ctor_set(x_973, 0, x_975);
x_976 = x_973;
goto block_977;
}
else
{
lean_object* x_978; 
x_978 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_978, 0, x_975);
x_976 = x_978;
goto block_977;
}
block_977:
{
return x_976;
}
}
}
else
{
lean_dec(x_968);
return x_971;
}
}
else
{
lean_dec(x_969);
lean_dec(x_968);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_14;
}
}
}
block_988:
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; 
x_983 = l_List_appendTR___redArg(x_968, x_960);
x_984 = l_List_appendTR___redArg(x_983, x_982);
if (x_967 == 0)
{
lean_ctor_set(x_966, 0, x_984);
x_985 = x_966;
goto block_986;
}
else
{
lean_object* x_987; 
x_987 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_987, 0, x_984);
x_985 = x_987;
goto block_986;
}
block_986:
{
return x_985;
}
}
block_991:
{
if (lean_obj_tag(x_989) == 0)
{
lean_object* x_990; 
x_990 = lean_ctor_get(x_989, 0);
lean_inc(x_990);
lean_dec_ref(x_989);
x_982 = x_990;
goto block_988;
}
else
{
lean_dec(x_968);
lean_del_object(x_966);
lean_dec(x_960);
return x_989;
}
}
block_1004:
{
if (x_994 == 0)
{
lean_object* x_995; 
lean_dec_ref(x_992);
x_995 = l_Lean_Meta_SavedState_restore___redArg(x_993, x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_993);
if (lean_obj_tag(x_995) == 0)
{
lean_dec_ref(x_995);
x_982 = x_19;
goto block_988;
}
else
{
lean_object* x_996; lean_object* x_997; uint8_t x_998; uint8_t x_1003; 
lean_dec(x_968);
lean_del_object(x_966);
lean_dec(x_960);
lean_dec(x_19);
x_996 = lean_ctor_get(x_995, 0);
x_1003 = !lean_is_exclusive(x_995);
if (x_1003 == 0)
{
x_997 = x_995;
x_998 = x_1003;
goto block_1002;
}
else
{
lean_inc(x_996);
lean_dec(x_995);
x_997 = lean_box(0);
x_998 = x_1003;
goto block_1002;
}
block_1002:
{
lean_object* x_999; 
if (x_998 == 0)
{
x_999 = x_997;
goto block_1000;
}
else
{
lean_object* x_1001; 
x_1001 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1001, 0, x_996);
x_999 = x_1001;
goto block_1000;
}
block_1000:
{
return x_999;
}
}
}
}
else
{
lean_dec_ref(x_993);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_8);
x_989 = x_992;
goto block_991;
}
}
block_1020:
{
lean_object* x_1006; 
x_1006 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1006) == 0)
{
lean_object* x_1007; lean_object* x_1008; 
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
lean_dec_ref(x_1006);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_19);
x_1008 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1005, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1008) == 0)
{
lean_dec(x_1007);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_8);
x_989 = x_1008;
goto block_991;
}
else
{
lean_object* x_1009; uint8_t x_1010; 
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
x_1010 = l_Lean_Exception_isInterrupt(x_1009);
if (x_1010 == 0)
{
uint8_t x_1011; 
x_1011 = l_Lean_Exception_isRuntime(x_1009);
x_992 = x_1008;
x_993 = x_1007;
x_994 = x_1011;
goto block_1004;
}
else
{
lean_dec(x_1009);
x_992 = x_1008;
x_993 = x_1007;
x_994 = x_1010;
goto block_1004;
}
}
}
else
{
lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; uint8_t x_1019; 
lean_dec(x_1005);
lean_dec(x_968);
lean_del_object(x_966);
lean_dec(x_960);
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1012 = lean_ctor_get(x_1006, 0);
x_1019 = !lean_is_exclusive(x_1006);
if (x_1019 == 0)
{
x_1013 = x_1006;
x_1014 = x_1019;
goto block_1018;
}
else
{
lean_inc(x_1012);
lean_dec(x_1006);
x_1013 = lean_box(0);
x_1014 = x_1019;
goto block_1018;
}
block_1018:
{
lean_object* x_1015; 
if (x_1014 == 0)
{
x_1015 = x_1013;
goto block_1016;
}
else
{
lean_object* x_1017; 
x_1017 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1017, 0, x_1012);
x_1015 = x_1017;
goto block_1016;
}
block_1016:
{
return x_1015;
}
}
}
}
block_1025:
{
uint8_t x_1022; lean_object* x_1023; 
x_1022 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_968);
x_1023 = l_List_appendTR___redArg(x_1021, x_968);
if (x_1022 == 0)
{
lean_del_object(x_966);
x_969 = x_1023;
goto block_981;
}
else
{
uint8_t x_1024; 
x_1024 = l_List_isEmpty___redArg(x_968);
if (x_1024 == 0)
{
x_1005 = x_1023;
goto block_1020;
}
else
{
if (x_957 == 0)
{
lean_del_object(x_966);
x_969 = x_1023;
goto block_981;
}
else
{
x_1005 = x_1023;
goto block_1020;
}
}
}
}
block_1041:
{
lean_object* x_1030; double x_1031; double x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1030 = lean_io_get_num_heartbeats();
x_1031 = lean_float_of_nat(x_1027);
x_1032 = lean_float_of_nat(x_1030);
x_1033 = lean_box_float(x_1031);
x_1034 = lean_box_float(x_1032);
if (x_963 == 0)
{
lean_ctor_set(x_962, 1, x_1034);
lean_ctor_set(x_962, 0, x_1033);
x_1035 = x_962;
goto block_1039;
}
else
{
lean_object* x_1040; 
x_1040 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1040, 0, x_1033);
lean_ctor_set(x_1040, 1, x_1034);
x_1035 = x_1040;
goto block_1039;
}
block_1039:
{
lean_object* x_1036; uint8_t x_1037; lean_object* x_1038; 
x_1036 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1036, 0, x_1029);
lean_ctor_set(x_1036, 1, x_1035);
x_1037 = lean_unbox(x_965);
lean_dec(x_965);
x_1038 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_24, x_108, x_23, x_1037, x_1028, x_1026, x_1036, x_7, x_8, x_9, x_10);
lean_dec_ref(x_23);
return x_1038;
}
}
block_1046:
{
lean_object* x_1045; 
x_1045 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1045, 0, x_1044);
x_1027 = x_1042;
x_1028 = x_1043;
x_1029 = x_1045;
goto block_1041;
}
block_1052:
{
lean_object* x_1050; lean_object* x_1051; 
x_1050 = l_List_appendTR___redArg(x_968, x_960);
x_1051 = l_List_appendTR___redArg(x_1050, x_1049);
x_1042 = x_1047;
x_1043 = x_1048;
x_1044 = x_1051;
goto block_1046;
}
block_1057:
{
lean_object* x_1056; 
x_1056 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1056, 0, x_1055);
x_1027 = x_1053;
x_1028 = x_1054;
x_1029 = x_1056;
goto block_1041;
}
block_1063:
{
if (lean_obj_tag(x_1060) == 0)
{
lean_object* x_1061; 
x_1061 = lean_ctor_get(x_1060, 0);
lean_inc(x_1061);
lean_dec_ref(x_1060);
x_1042 = x_1058;
x_1043 = x_1059;
x_1044 = x_1061;
goto block_1046;
}
else
{
lean_object* x_1062; 
x_1062 = lean_ctor_get(x_1060, 0);
lean_inc(x_1062);
lean_dec_ref(x_1060);
x_1053 = x_1058;
x_1054 = x_1059;
x_1055 = x_1062;
goto block_1057;
}
}
block_1073:
{
if (x_1067 == 0)
{
lean_object* x_1068; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1068 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1064, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1068) == 0)
{
lean_object* x_1069; lean_object* x_1070; 
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
lean_dec_ref(x_1068);
x_1070 = l_List_appendTR___redArg(x_968, x_1069);
x_1042 = x_1065;
x_1043 = x_1066;
x_1044 = x_1070;
goto block_1046;
}
else
{
lean_dec(x_968);
x_1058 = x_1065;
x_1059 = x_1066;
x_1060 = x_1068;
goto block_1063;
}
}
else
{
lean_object* x_1071; lean_object* x_1072; 
lean_dec(x_1064);
lean_dec(x_968);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1071 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
x_1072 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1071, x_7, x_8, x_9, x_10);
x_1058 = x_1065;
x_1059 = x_1066;
x_1060 = x_1072;
goto block_1063;
}
}
block_1079:
{
uint8_t x_1078; 
x_1078 = l_List_isEmpty___redArg(x_960);
lean_dec(x_960);
if (x_1078 == 0)
{
x_1064 = x_1074;
x_1065 = x_1075;
x_1066 = x_1076;
x_1067 = x_1077;
goto block_1073;
}
else
{
x_1064 = x_1074;
x_1065 = x_1075;
x_1066 = x_1076;
x_1067 = x_957;
goto block_1073;
}
}
block_1085:
{
if (lean_obj_tag(x_1082) == 0)
{
lean_object* x_1083; 
x_1083 = lean_ctor_get(x_1082, 0);
lean_inc(x_1083);
lean_dec_ref(x_1082);
x_1047 = x_1080;
x_1048 = x_1081;
x_1049 = x_1083;
goto block_1052;
}
else
{
lean_object* x_1084; 
lean_dec(x_968);
lean_dec(x_960);
x_1084 = lean_ctor_get(x_1082, 0);
lean_inc(x_1084);
lean_dec_ref(x_1082);
x_1053 = x_1080;
x_1054 = x_1081;
x_1055 = x_1084;
goto block_1057;
}
}
block_1093:
{
if (x_1090 == 0)
{
lean_object* x_1091; 
lean_dec_ref(x_1087);
x_1091 = l_Lean_Meta_SavedState_restore___redArg(x_1086, x_8, x_10);
lean_dec_ref(x_1086);
if (lean_obj_tag(x_1091) == 0)
{
lean_dec_ref(x_1091);
x_1047 = x_1088;
x_1048 = x_1089;
x_1049 = x_19;
goto block_1052;
}
else
{
lean_object* x_1092; 
lean_dec(x_968);
lean_dec(x_960);
lean_dec(x_19);
x_1092 = lean_ctor_get(x_1091, 0);
lean_inc(x_1092);
lean_dec_ref(x_1091);
x_1053 = x_1088;
x_1054 = x_1089;
x_1055 = x_1092;
goto block_1057;
}
}
else
{
lean_dec_ref(x_1086);
lean_dec(x_19);
x_1080 = x_1088;
x_1081 = x_1089;
x_1082 = x_1087;
goto block_1085;
}
}
block_1104:
{
lean_object* x_1097; 
x_1097 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1097) == 0)
{
lean_object* x_1098; lean_object* x_1099; 
x_1098 = lean_ctor_get(x_1097, 0);
lean_inc(x_1098);
lean_dec_ref(x_1097);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_19);
lean_inc(x_2);
x_1099 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1094, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1099) == 0)
{
lean_dec(x_1098);
lean_dec(x_19);
x_1080 = x_1095;
x_1081 = x_1096;
x_1082 = x_1099;
goto block_1085;
}
else
{
lean_object* x_1100; uint8_t x_1101; 
x_1100 = lean_ctor_get(x_1099, 0);
lean_inc(x_1100);
x_1101 = l_Lean_Exception_isInterrupt(x_1100);
if (x_1101 == 0)
{
uint8_t x_1102; 
x_1102 = l_Lean_Exception_isRuntime(x_1100);
x_1086 = x_1098;
x_1087 = x_1099;
x_1088 = x_1095;
x_1089 = x_1096;
x_1090 = x_1102;
goto block_1093;
}
else
{
lean_dec(x_1100);
x_1086 = x_1098;
x_1087 = x_1099;
x_1088 = x_1095;
x_1089 = x_1096;
x_1090 = x_1101;
goto block_1093;
}
}
}
else
{
lean_object* x_1103; 
lean_dec(x_1094);
lean_dec(x_968);
lean_dec(x_960);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1103 = lean_ctor_get(x_1097, 0);
lean_inc(x_1103);
lean_dec_ref(x_1097);
x_1053 = x_1095;
x_1054 = x_1096;
x_1055 = x_1103;
goto block_1057;
}
}
block_1112:
{
uint8_t x_1109; lean_object* x_1110; 
x_1109 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_968);
x_1110 = l_List_appendTR___redArg(x_1108, x_968);
if (x_1109 == 0)
{
x_1074 = x_1110;
x_1075 = x_1105;
x_1076 = x_1106;
x_1077 = x_1107;
goto block_1079;
}
else
{
uint8_t x_1111; 
x_1111 = l_List_isEmpty___redArg(x_968);
if (x_1111 == 0)
{
x_1094 = x_1110;
x_1095 = x_1105;
x_1096 = x_1106;
goto block_1104;
}
else
{
if (x_957 == 0)
{
x_1074 = x_1110;
x_1075 = x_1105;
x_1076 = x_1106;
x_1077 = x_1107;
goto block_1079;
}
else
{
x_1094 = x_1110;
x_1095 = x_1105;
x_1096 = x_1106;
goto block_1104;
}
}
}
}
block_1128:
{
lean_object* x_1116; double x_1117; double x_1118; double x_1119; double x_1120; double x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; uint8_t x_1126; lean_object* x_1127; 
x_1116 = lean_io_mono_nanos_now();
x_1117 = lean_float_of_nat(x_1114);
x_1118 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_1119 = lean_float_div(x_1117, x_1118);
x_1120 = lean_float_of_nat(x_1116);
x_1121 = lean_float_div(x_1120, x_1118);
x_1122 = lean_box_float(x_1119);
x_1123 = lean_box_float(x_1121);
x_1124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1124, 0, x_1122);
lean_ctor_set(x_1124, 1, x_1123);
x_1125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1125, 0, x_1115);
lean_ctor_set(x_1125, 1, x_1124);
x_1126 = lean_unbox(x_965);
lean_dec(x_965);
x_1127 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_24, x_108, x_23, x_1126, x_1113, x_1026, x_1125, x_7, x_8, x_9, x_10);
lean_dec_ref(x_23);
return x_1127;
}
block_1133:
{
lean_object* x_1132; 
x_1132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1132, 0, x_1131);
x_1113 = x_1130;
x_1114 = x_1129;
x_1115 = x_1132;
goto block_1128;
}
block_1139:
{
lean_object* x_1137; lean_object* x_1138; 
x_1137 = l_List_appendTR___redArg(x_968, x_960);
x_1138 = l_List_appendTR___redArg(x_1137, x_1136);
x_1129 = x_1135;
x_1130 = x_1134;
x_1131 = x_1138;
goto block_1133;
}
block_1144:
{
lean_object* x_1143; 
x_1143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1143, 0, x_1142);
x_1113 = x_1141;
x_1114 = x_1140;
x_1115 = x_1143;
goto block_1128;
}
block_1150:
{
if (lean_obj_tag(x_1147) == 0)
{
lean_object* x_1148; 
x_1148 = lean_ctor_get(x_1147, 0);
lean_inc(x_1148);
lean_dec_ref(x_1147);
x_1129 = x_1146;
x_1130 = x_1145;
x_1131 = x_1148;
goto block_1133;
}
else
{
lean_object* x_1149; 
x_1149 = lean_ctor_get(x_1147, 0);
lean_inc(x_1149);
lean_dec_ref(x_1147);
x_1140 = x_1146;
x_1141 = x_1145;
x_1142 = x_1149;
goto block_1144;
}
}
block_1155:
{
lean_object* x_1153; lean_object* x_1154; 
x_1153 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
x_1154 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1153, x_7, x_8, x_9, x_10);
x_1145 = x_1152;
x_1146 = x_1151;
x_1147 = x_1154;
goto block_1150;
}
block_1164:
{
uint8_t x_1160; 
x_1160 = l_List_isEmpty___redArg(x_960);
lean_dec(x_960);
if (x_1160 == 0)
{
lean_dec(x_1156);
lean_dec(x_968);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1151 = x_1158;
x_1152 = x_1157;
goto block_1155;
}
else
{
if (x_1159 == 0)
{
lean_object* x_1161; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1161 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1156, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1161) == 0)
{
lean_object* x_1162; lean_object* x_1163; 
x_1162 = lean_ctor_get(x_1161, 0);
lean_inc(x_1162);
lean_dec_ref(x_1161);
x_1163 = l_List_appendTR___redArg(x_968, x_1162);
x_1129 = x_1158;
x_1130 = x_1157;
x_1131 = x_1163;
goto block_1133;
}
else
{
lean_dec(x_968);
x_1145 = x_1157;
x_1146 = x_1158;
x_1147 = x_1161;
goto block_1150;
}
}
else
{
lean_dec(x_1156);
lean_dec(x_968);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1151 = x_1158;
x_1152 = x_1157;
goto block_1155;
}
}
}
block_1170:
{
if (lean_obj_tag(x_1167) == 0)
{
lean_object* x_1168; 
x_1168 = lean_ctor_get(x_1167, 0);
lean_inc(x_1168);
lean_dec_ref(x_1167);
x_1134 = x_1166;
x_1135 = x_1165;
x_1136 = x_1168;
goto block_1139;
}
else
{
lean_object* x_1169; 
lean_dec(x_968);
lean_dec(x_960);
x_1169 = lean_ctor_get(x_1167, 0);
lean_inc(x_1169);
lean_dec_ref(x_1167);
x_1140 = x_1165;
x_1141 = x_1166;
x_1142 = x_1169;
goto block_1144;
}
}
block_1178:
{
if (x_1175 == 0)
{
lean_object* x_1176; 
lean_dec_ref(x_1172);
x_1176 = l_Lean_Meta_SavedState_restore___redArg(x_1171, x_8, x_10);
lean_dec_ref(x_1171);
if (lean_obj_tag(x_1176) == 0)
{
lean_dec_ref(x_1176);
x_1134 = x_1174;
x_1135 = x_1173;
x_1136 = x_19;
goto block_1139;
}
else
{
lean_object* x_1177; 
lean_dec(x_968);
lean_dec(x_960);
lean_dec(x_19);
x_1177 = lean_ctor_get(x_1176, 0);
lean_inc(x_1177);
lean_dec_ref(x_1176);
x_1140 = x_1173;
x_1141 = x_1174;
x_1142 = x_1177;
goto block_1144;
}
}
else
{
lean_dec_ref(x_1171);
lean_dec(x_19);
x_1165 = x_1173;
x_1166 = x_1174;
x_1167 = x_1172;
goto block_1170;
}
}
block_1189:
{
lean_object* x_1182; 
x_1182 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1182) == 0)
{
lean_object* x_1183; lean_object* x_1184; 
x_1183 = lean_ctor_get(x_1182, 0);
lean_inc(x_1183);
lean_dec_ref(x_1182);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_19);
lean_inc(x_2);
x_1184 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1179, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1184) == 0)
{
lean_dec(x_1183);
lean_dec(x_19);
x_1165 = x_1181;
x_1166 = x_1180;
x_1167 = x_1184;
goto block_1170;
}
else
{
lean_object* x_1185; uint8_t x_1186; 
x_1185 = lean_ctor_get(x_1184, 0);
lean_inc(x_1185);
x_1186 = l_Lean_Exception_isInterrupt(x_1185);
if (x_1186 == 0)
{
uint8_t x_1187; 
x_1187 = l_Lean_Exception_isRuntime(x_1185);
x_1171 = x_1183;
x_1172 = x_1184;
x_1173 = x_1181;
x_1174 = x_1180;
x_1175 = x_1187;
goto block_1178;
}
else
{
lean_dec(x_1185);
x_1171 = x_1183;
x_1172 = x_1184;
x_1173 = x_1181;
x_1174 = x_1180;
x_1175 = x_1186;
goto block_1178;
}
}
}
else
{
lean_object* x_1188; 
lean_dec(x_1179);
lean_dec(x_968);
lean_dec(x_960);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1188 = lean_ctor_get(x_1182, 0);
lean_inc(x_1188);
lean_dec_ref(x_1182);
x_1140 = x_1181;
x_1141 = x_1180;
x_1142 = x_1188;
goto block_1144;
}
}
block_1197:
{
uint8_t x_1194; lean_object* x_1195; 
x_1194 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_968);
x_1195 = l_List_appendTR___redArg(x_1193, x_968);
if (x_1194 == 0)
{
x_1156 = x_1195;
x_1157 = x_1190;
x_1158 = x_1191;
x_1159 = x_1192;
goto block_1164;
}
else
{
uint8_t x_1196; 
x_1196 = l_List_isEmpty___redArg(x_968);
if (x_1196 == 0)
{
x_1179 = x_1195;
x_1180 = x_1190;
x_1181 = x_1191;
goto block_1189;
}
else
{
if (x_1192 == 0)
{
x_1156 = x_1195;
x_1157 = x_1190;
x_1158 = x_1191;
x_1159 = x_1192;
goto block_1164;
}
else
{
x_1179 = x_1195;
x_1180 = x_1190;
x_1181 = x_1191;
goto block_1189;
}
}
}
}
block_1223:
{
lean_object* x_1199; 
x_1199 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_1199) == 0)
{
lean_object* x_1200; lean_object* x_1201; uint8_t x_1202; 
x_1200 = lean_ctor_get(x_1199, 0);
lean_inc(x_1200);
lean_dec_ref(x_1199);
x_1201 = l_Lean_trace_profiler_useHeartbeats;
x_1202 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_23, x_1201);
if (x_1202 == 0)
{
lean_object* x_1203; lean_object* x_1204; 
lean_del_object(x_962);
x_1203 = lean_io_mono_nanos_now();
x_1204 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_24, x_957, x_5, x_1198, x_8);
if (lean_obj_tag(x_1204) == 0)
{
lean_object* x_1205; lean_object* x_1206; 
x_1205 = lean_ctor_get(x_1204, 0);
lean_inc(x_1205);
lean_dec_ref(x_1204);
x_1206 = l_List_reverse___redArg(x_1205);
x_1190 = x_1200;
x_1191 = x_1203;
x_1192 = x_1202;
x_1193 = x_1206;
goto block_1197;
}
else
{
if (lean_obj_tag(x_1204) == 0)
{
lean_object* x_1207; 
x_1207 = lean_ctor_get(x_1204, 0);
lean_inc(x_1207);
lean_dec_ref(x_1204);
x_1190 = x_1200;
x_1191 = x_1203;
x_1192 = x_1202;
x_1193 = x_1207;
goto block_1197;
}
else
{
lean_object* x_1208; 
lean_dec(x_968);
lean_dec(x_960);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1208 = lean_ctor_get(x_1204, 0);
lean_inc(x_1208);
lean_dec_ref(x_1204);
x_1140 = x_1203;
x_1141 = x_1200;
x_1142 = x_1208;
goto block_1144;
}
}
}
else
{
lean_object* x_1209; lean_object* x_1210; 
x_1209 = lean_io_get_num_heartbeats();
x_1210 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_24, x_957, x_5, x_1198, x_8);
if (lean_obj_tag(x_1210) == 0)
{
lean_object* x_1211; lean_object* x_1212; 
x_1211 = lean_ctor_get(x_1210, 0);
lean_inc(x_1211);
lean_dec_ref(x_1210);
x_1212 = l_List_reverse___redArg(x_1211);
x_1105 = x_1209;
x_1106 = x_1200;
x_1107 = x_1202;
x_1108 = x_1212;
goto block_1112;
}
else
{
if (lean_obj_tag(x_1210) == 0)
{
lean_object* x_1213; 
x_1213 = lean_ctor_get(x_1210, 0);
lean_inc(x_1213);
lean_dec_ref(x_1210);
x_1105 = x_1209;
x_1106 = x_1200;
x_1107 = x_1202;
x_1108 = x_1213;
goto block_1112;
}
else
{
lean_object* x_1214; 
lean_dec(x_968);
lean_dec(x_960);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1214 = lean_ctor_get(x_1210, 0);
lean_inc(x_1214);
lean_dec_ref(x_1210);
x_1053 = x_1209;
x_1054 = x_1200;
x_1055 = x_1214;
goto block_1057;
}
}
}
}
else
{
lean_object* x_1215; lean_object* x_1216; uint8_t x_1217; uint8_t x_1222; 
lean_dec_ref(x_1026);
lean_dec(x_968);
lean_dec(x_965);
lean_del_object(x_962);
lean_dec(x_960);
lean_dec_ref(x_23);
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1215 = lean_ctor_get(x_1199, 0);
x_1222 = !lean_is_exclusive(x_1199);
if (x_1222 == 0)
{
x_1216 = x_1199;
x_1217 = x_1222;
goto block_1221;
}
else
{
lean_inc(x_1215);
lean_dec(x_1199);
x_1216 = lean_box(0);
x_1217 = x_1222;
goto block_1221;
}
block_1221:
{
lean_object* x_1218; 
if (x_1217 == 0)
{
x_1218 = x_1216;
goto block_1219;
}
else
{
lean_object* x_1220; 
x_1220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1220, 0, x_1215);
x_1218 = x_1220;
goto block_1219;
}
block_1219:
{
return x_1218;
}
}
}
}
}
}
else
{
lean_object* x_1231; lean_object* x_1232; uint8_t x_1233; uint8_t x_1238; 
lean_del_object(x_962);
lean_dec(x_961);
lean_dec(x_960);
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1231 = lean_ctor_get(x_964, 0);
x_1238 = !lean_is_exclusive(x_964);
if (x_1238 == 0)
{
x_1232 = x_964;
x_1233 = x_1238;
goto block_1237;
}
else
{
lean_inc(x_1231);
lean_dec(x_964);
x_1232 = lean_box(0);
x_1233 = x_1238;
goto block_1237;
}
block_1237:
{
lean_object* x_1234; 
if (x_1233 == 0)
{
x_1234 = x_1232;
goto block_1235;
}
else
{
lean_object* x_1236; 
x_1236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1236, 0, x_1231);
x_1234 = x_1236;
goto block_1235;
}
block_1235:
{
return x_1234;
}
}
}
}
}
else
{
lean_object* x_1241; lean_object* x_1242; uint8_t x_1243; uint8_t x_1248; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1241 = lean_ctor_get(x_958, 0);
x_1248 = !lean_is_exclusive(x_958);
if (x_1248 == 0)
{
x_1242 = x_958;
x_1243 = x_1248;
goto block_1247;
}
else
{
lean_inc(x_1241);
lean_dec(x_958);
x_1242 = lean_box(0);
x_1243 = x_1248;
goto block_1247;
}
block_1247:
{
lean_object* x_1244; 
if (x_1243 == 0)
{
x_1244 = x_1242;
goto block_1245;
}
else
{
lean_object* x_1246; 
x_1246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1246, 0, x_1241);
x_1244 = x_1246;
goto block_1245;
}
block_1245:
{
return x_1244;
}
}
}
}
else
{
lean_inc_ref(x_23);
goto block_954;
}
}
else
{
lean_inc_ref(x_23);
goto block_954;
}
block_126:
{
lean_object* x_112; double x_113; double x_114; double x_115; double x_116; double x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_112 = lean_io_mono_nanos_now();
x_113 = lean_float_of_nat(x_109);
x_114 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_115 = lean_float_div(x_113, x_114);
x_116 = lean_float_of_nat(x_112);
x_117 = lean_float_div(x_116, x_114);
x_118 = lean_box_float(x_115);
x_119 = lean_box_float(x_117);
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_119);
lean_ctor_set(x_20, 0, x_118);
x_120 = x_20;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_119);
x_120 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_121; uint8_t x_122; lean_object* x_123; 
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_111);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_unbox(x_106);
lean_dec(x_106);
x_123 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_24, x_108, x_23, x_122, x_110, x_107, x_121, x_7, x_8, x_9, x_10);
lean_dec_ref(x_23);
return x_123;
}
}
block_131:
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_109 = x_127;
x_110 = x_128;
x_111 = x_130;
goto block_126;
}
block_136:
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_109 = x_132;
x_110 = x_133;
x_111 = x_135;
goto block_126;
}
block_144:
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_List_appendTR___redArg(x_140, x_139);
x_143 = l_List_appendTR___redArg(x_142, x_141);
x_132 = x_137;
x_133 = x_138;
x_134 = x_143;
goto block_136;
}
block_152:
{
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
x_137 = x_145;
x_138 = x_146;
x_139 = x_147;
x_140 = x_148;
x_141 = x_150;
goto block_144;
}
else
{
lean_object* x_151; 
lean_dec(x_148);
lean_dec(x_147);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
lean_dec_ref(x_149);
x_127 = x_145;
x_128 = x_146;
x_129 = x_151;
goto block_131;
}
}
block_162:
{
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec_ref(x_153);
x_160 = l_Lean_Meta_SavedState_restore___redArg(x_154, x_8, x_10);
lean_dec_ref(x_154);
if (lean_obj_tag(x_160) == 0)
{
lean_dec_ref(x_160);
x_137 = x_155;
x_138 = x_156;
x_139 = x_157;
x_140 = x_158;
x_141 = x_19;
goto block_144;
}
else
{
lean_object* x_161; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_19);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
x_127 = x_155;
x_128 = x_156;
x_129 = x_161;
goto block_131;
}
}
else
{
lean_dec_ref(x_154);
lean_dec(x_19);
x_145 = x_155;
x_146 = x_156;
x_147 = x_157;
x_148 = x_158;
x_149 = x_153;
goto block_152;
}
}
block_175:
{
lean_object* x_168; 
x_168 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_19);
lean_inc(x_2);
x_170 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_167, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_170) == 0)
{
lean_dec(x_169);
lean_dec(x_19);
x_145 = x_163;
x_146 = x_164;
x_147 = x_165;
x_148 = x_166;
x_149 = x_170;
goto block_152;
}
else
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = l_Lean_Exception_isInterrupt(x_171);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Exception_isRuntime(x_171);
x_153 = x_170;
x_154 = x_169;
x_155 = x_163;
x_156 = x_164;
x_157 = x_165;
x_158 = x_166;
x_159 = x_173;
goto block_162;
}
else
{
lean_dec(x_171);
x_153 = x_170;
x_154 = x_169;
x_155 = x_163;
x_156 = x_164;
x_157 = x_165;
x_158 = x_166;
x_159 = x_172;
goto block_162;
}
}
}
else
{
lean_object* x_174; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_174 = lean_ctor_get(x_168, 0);
lean_inc(x_174);
lean_dec_ref(x_168);
x_127 = x_163;
x_128 = x_164;
x_129 = x_174;
goto block_131;
}
}
block_181:
{
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec_ref(x_178);
x_132 = x_176;
x_133 = x_177;
x_134 = x_179;
goto block_136;
}
else
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
lean_dec_ref(x_178);
x_127 = x_176;
x_128 = x_177;
x_129 = x_180;
goto block_131;
}
}
block_197:
{
lean_object* x_189; double x_190; double x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_189 = lean_io_get_num_heartbeats();
x_190 = lean_float_of_nat(x_183);
x_191 = lean_float_of_nat(x_189);
x_192 = lean_box_float(x_190);
x_193 = lean_box_float(x_191);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_188);
lean_ctor_set(x_195, 1, x_194);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_196 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_24, x_108, x_23, x_184, x_186, x_187, x_195, x_7, x_8, x_9, x_10);
x_176 = x_182;
x_177 = x_185;
x_178 = x_196;
goto block_181;
}
block_206:
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_182 = x_199;
x_183 = x_198;
x_184 = x_200;
x_185 = x_202;
x_186 = x_201;
x_187 = x_203;
x_188 = x_205;
goto block_197;
}
block_215:
{
lean_object* x_214; 
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_182 = x_208;
x_183 = x_207;
x_184 = x_209;
x_185 = x_211;
x_186 = x_210;
x_187 = x_212;
x_188 = x_214;
goto block_197;
}
block_227:
{
lean_object* x_225; lean_object* x_226; 
x_225 = l_List_appendTR___redArg(x_223, x_222);
x_226 = l_List_appendTR___redArg(x_225, x_224);
x_207 = x_217;
x_208 = x_216;
x_209 = x_218;
x_210 = x_220;
x_211 = x_219;
x_212 = x_221;
x_213 = x_226;
goto block_215;
}
block_239:
{
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec_ref(x_236);
x_216 = x_229;
x_217 = x_228;
x_218 = x_230;
x_219 = x_232;
x_220 = x_231;
x_221 = x_234;
x_222 = x_233;
x_223 = x_235;
x_224 = x_237;
goto block_227;
}
else
{
lean_object* x_238; 
lean_dec(x_235);
lean_dec(x_233);
x_238 = lean_ctor_get(x_236, 0);
lean_inc(x_238);
lean_dec_ref(x_236);
x_198 = x_228;
x_199 = x_229;
x_200 = x_230;
x_201 = x_231;
x_202 = x_232;
x_203 = x_234;
x_204 = x_238;
goto block_206;
}
}
block_253:
{
if (x_250 == 0)
{
lean_object* x_251; 
lean_dec_ref(x_240);
x_251 = l_Lean_Meta_SavedState_restore___redArg(x_243, x_8, x_10);
lean_dec_ref(x_243);
if (lean_obj_tag(x_251) == 0)
{
lean_dec_ref(x_251);
x_216 = x_242;
x_217 = x_241;
x_218 = x_244;
x_219 = x_246;
x_220 = x_245;
x_221 = x_248;
x_222 = x_247;
x_223 = x_249;
x_224 = x_19;
goto block_227;
}
else
{
lean_object* x_252; 
lean_dec(x_249);
lean_dec(x_247);
lean_dec(x_19);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
x_198 = x_241;
x_199 = x_242;
x_200 = x_244;
x_201 = x_245;
x_202 = x_246;
x_203 = x_248;
x_204 = x_252;
goto block_206;
}
}
else
{
lean_dec_ref(x_243);
lean_dec(x_19);
x_228 = x_241;
x_229 = x_242;
x_230 = x_244;
x_231 = x_245;
x_232 = x_246;
x_233 = x_247;
x_234 = x_248;
x_235 = x_249;
x_236 = x_240;
goto block_239;
}
}
block_270:
{
lean_object* x_263; 
x_263 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_19);
lean_inc(x_2);
x_265 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_254, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_265) == 0)
{
lean_dec(x_264);
lean_dec(x_19);
x_228 = x_256;
x_229 = x_255;
x_230 = x_257;
x_231 = x_259;
x_232 = x_258;
x_233 = x_261;
x_234 = x_260;
x_235 = x_262;
x_236 = x_265;
goto block_239;
}
else
{
lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = l_Lean_Exception_isInterrupt(x_266);
if (x_267 == 0)
{
uint8_t x_268; 
x_268 = l_Lean_Exception_isRuntime(x_266);
x_240 = x_265;
x_241 = x_256;
x_242 = x_255;
x_243 = x_264;
x_244 = x_257;
x_245 = x_259;
x_246 = x_258;
x_247 = x_261;
x_248 = x_260;
x_249 = x_262;
x_250 = x_268;
goto block_253;
}
else
{
lean_dec(x_266);
x_240 = x_265;
x_241 = x_256;
x_242 = x_255;
x_243 = x_264;
x_244 = x_257;
x_245 = x_259;
x_246 = x_258;
x_247 = x_261;
x_248 = x_260;
x_249 = x_262;
x_250 = x_267;
goto block_253;
}
}
}
else
{
lean_object* x_269; 
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_254);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_269 = lean_ctor_get(x_263, 0);
lean_inc(x_269);
lean_dec_ref(x_263);
x_198 = x_256;
x_199 = x_255;
x_200 = x_257;
x_201 = x_259;
x_202 = x_258;
x_203 = x_260;
x_204 = x_269;
goto block_206;
}
}
block_280:
{
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
lean_dec_ref(x_277);
x_207 = x_272;
x_208 = x_271;
x_209 = x_273;
x_210 = x_275;
x_211 = x_274;
x_212 = x_276;
x_213 = x_278;
goto block_215;
}
else
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
lean_dec_ref(x_277);
x_198 = x_272;
x_199 = x_271;
x_200 = x_273;
x_201 = x_275;
x_202 = x_274;
x_203 = x_276;
x_204 = x_279;
goto block_206;
}
}
block_292:
{
lean_object* x_289; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_289 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_281, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
x_291 = l_List_appendTR___redArg(x_288, x_290);
x_207 = x_283;
x_208 = x_282;
x_209 = x_284;
x_210 = x_286;
x_211 = x_285;
x_212 = x_287;
x_213 = x_291;
goto block_215;
}
else
{
lean_dec(x_288);
x_271 = x_282;
x_272 = x_283;
x_273 = x_284;
x_274 = x_285;
x_275 = x_286;
x_276 = x_287;
x_277 = x_289;
goto block_280;
}
}
block_308:
{
uint8_t x_303; lean_object* x_304; 
x_303 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_301);
x_304 = l_List_appendTR___redArg(x_302, x_301);
if (x_303 == 0)
{
lean_dec(x_298);
if (x_300 == 0)
{
x_281 = x_304;
x_282 = x_294;
x_283 = x_293;
x_284 = x_295;
x_285 = x_297;
x_286 = x_296;
x_287 = x_299;
x_288 = x_301;
goto block_292;
}
else
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_304);
lean_dec(x_301);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_305 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
x_306 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_305, x_7, x_8, x_9, x_10);
x_271 = x_294;
x_272 = x_293;
x_273 = x_295;
x_274 = x_297;
x_275 = x_296;
x_276 = x_299;
x_277 = x_306;
goto block_280;
}
}
else
{
uint8_t x_307; 
x_307 = l_List_isEmpty___redArg(x_301);
if (x_307 == 0)
{
x_254 = x_304;
x_255 = x_294;
x_256 = x_293;
x_257 = x_295;
x_258 = x_297;
x_259 = x_296;
x_260 = x_299;
x_261 = x_298;
x_262 = x_301;
goto block_270;
}
else
{
if (x_300 == 0)
{
lean_dec(x_298);
x_281 = x_304;
x_282 = x_294;
x_283 = x_293;
x_284 = x_295;
x_285 = x_297;
x_286 = x_296;
x_287 = x_299;
x_288 = x_301;
goto block_292;
}
else
{
x_254 = x_304;
x_255 = x_294;
x_256 = x_293;
x_257 = x_295;
x_258 = x_297;
x_259 = x_296;
x_260 = x_299;
x_261 = x_298;
x_262 = x_301;
goto block_270;
}
}
}
}
block_327:
{
lean_object* x_316; double x_317; double x_318; double x_319; double x_320; double x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_316 = lean_io_mono_nanos_now();
x_317 = lean_float_of_nat(x_309);
x_318 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_319 = lean_float_div(x_317, x_318);
x_320 = lean_float_of_nat(x_316);
x_321 = lean_float_div(x_320, x_318);
x_322 = lean_box_float(x_319);
x_323 = lean_box_float(x_321);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_315);
lean_ctor_set(x_325, 1, x_324);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_326 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_24, x_108, x_23, x_311, x_313, x_314, x_325, x_7, x_8, x_9, x_10);
x_176 = x_310;
x_177 = x_312;
x_178 = x_326;
goto block_181;
}
block_336:
{
lean_object* x_335; 
x_335 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_335, 0, x_334);
x_309 = x_328;
x_310 = x_329;
x_311 = x_330;
x_312 = x_332;
x_313 = x_331;
x_314 = x_333;
x_315 = x_335;
goto block_327;
}
block_348:
{
lean_object* x_346; lean_object* x_347; 
x_346 = l_List_appendTR___redArg(x_344, x_343);
x_347 = l_List_appendTR___redArg(x_346, x_345);
x_328 = x_337;
x_329 = x_338;
x_330 = x_339;
x_331 = x_341;
x_332 = x_340;
x_333 = x_342;
x_334 = x_347;
goto block_336;
}
block_357:
{
lean_object* x_356; 
x_356 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_356, 0, x_355);
x_309 = x_349;
x_310 = x_350;
x_311 = x_351;
x_312 = x_353;
x_313 = x_352;
x_314 = x_354;
x_315 = x_356;
goto block_327;
}
block_367:
{
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec_ref(x_364);
x_328 = x_358;
x_329 = x_359;
x_330 = x_360;
x_331 = x_362;
x_332 = x_361;
x_333 = x_363;
x_334 = x_365;
goto block_336;
}
else
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_364, 0);
lean_inc(x_366);
lean_dec_ref(x_364);
x_349 = x_358;
x_350 = x_359;
x_351 = x_360;
x_352 = x_362;
x_353 = x_361;
x_354 = x_363;
x_355 = x_366;
goto block_357;
}
}
block_376:
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
x_375 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_374, x_7, x_8, x_9, x_10);
x_358 = x_368;
x_359 = x_369;
x_360 = x_370;
x_361 = x_372;
x_362 = x_371;
x_363 = x_373;
x_364 = x_375;
goto block_367;
}
block_391:
{
uint8_t x_387; 
x_387 = l_List_isEmpty___redArg(x_384);
lean_dec(x_384);
if (x_387 == 0)
{
lean_dec(x_385);
lean_dec(x_382);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_368 = x_377;
x_369 = x_378;
x_370 = x_379;
x_371 = x_381;
x_372 = x_380;
x_373 = x_383;
goto block_376;
}
else
{
if (x_386 == 0)
{
lean_object* x_388; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_388 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_382, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
lean_dec_ref(x_388);
x_390 = l_List_appendTR___redArg(x_385, x_389);
x_328 = x_377;
x_329 = x_378;
x_330 = x_379;
x_331 = x_381;
x_332 = x_380;
x_333 = x_383;
x_334 = x_390;
goto block_336;
}
else
{
lean_dec(x_385);
x_358 = x_377;
x_359 = x_378;
x_360 = x_379;
x_361 = x_380;
x_362 = x_381;
x_363 = x_383;
x_364 = x_388;
goto block_367;
}
}
else
{
lean_dec(x_385);
lean_dec(x_382);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_368 = x_377;
x_369 = x_378;
x_370 = x_379;
x_371 = x_381;
x_372 = x_380;
x_373 = x_383;
goto block_376;
}
}
}
block_403:
{
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
x_337 = x_392;
x_338 = x_393;
x_339 = x_394;
x_340 = x_396;
x_341 = x_395;
x_342 = x_398;
x_343 = x_397;
x_344 = x_399;
x_345 = x_401;
goto block_348;
}
else
{
lean_object* x_402; 
lean_dec(x_399);
lean_dec(x_397);
x_402 = lean_ctor_get(x_400, 0);
lean_inc(x_402);
lean_dec_ref(x_400);
x_349 = x_392;
x_350 = x_393;
x_351 = x_394;
x_352 = x_395;
x_353 = x_396;
x_354 = x_398;
x_355 = x_402;
goto block_357;
}
}
block_417:
{
if (x_414 == 0)
{
lean_object* x_415; 
lean_dec_ref(x_409);
x_415 = l_Lean_Meta_SavedState_restore___redArg(x_412, x_8, x_10);
lean_dec_ref(x_412);
if (lean_obj_tag(x_415) == 0)
{
lean_dec_ref(x_415);
x_337 = x_404;
x_338 = x_405;
x_339 = x_406;
x_340 = x_408;
x_341 = x_407;
x_342 = x_411;
x_343 = x_410;
x_344 = x_413;
x_345 = x_19;
goto block_348;
}
else
{
lean_object* x_416; 
lean_dec(x_413);
lean_dec(x_410);
lean_dec(x_19);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
lean_dec_ref(x_415);
x_349 = x_404;
x_350 = x_405;
x_351 = x_406;
x_352 = x_407;
x_353 = x_408;
x_354 = x_411;
x_355 = x_416;
goto block_357;
}
}
else
{
lean_dec_ref(x_412);
lean_dec(x_19);
x_392 = x_404;
x_393 = x_405;
x_394 = x_406;
x_395 = x_407;
x_396 = x_408;
x_397 = x_410;
x_398 = x_411;
x_399 = x_413;
x_400 = x_409;
goto block_403;
}
}
block_434:
{
lean_object* x_427; 
x_427 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
lean_dec_ref(x_427);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_19);
lean_inc(x_2);
x_429 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_423, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_429) == 0)
{
lean_dec(x_428);
lean_dec(x_19);
x_392 = x_418;
x_393 = x_419;
x_394 = x_420;
x_395 = x_422;
x_396 = x_421;
x_397 = x_425;
x_398 = x_424;
x_399 = x_426;
x_400 = x_429;
goto block_403;
}
else
{
lean_object* x_430; uint8_t x_431; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = l_Lean_Exception_isInterrupt(x_430);
if (x_431 == 0)
{
uint8_t x_432; 
x_432 = l_Lean_Exception_isRuntime(x_430);
x_404 = x_418;
x_405 = x_419;
x_406 = x_420;
x_407 = x_422;
x_408 = x_421;
x_409 = x_429;
x_410 = x_425;
x_411 = x_424;
x_412 = x_428;
x_413 = x_426;
x_414 = x_432;
goto block_417;
}
else
{
lean_dec(x_430);
x_404 = x_418;
x_405 = x_419;
x_406 = x_420;
x_407 = x_422;
x_408 = x_421;
x_409 = x_429;
x_410 = x_425;
x_411 = x_424;
x_412 = x_428;
x_413 = x_426;
x_414 = x_431;
goto block_417;
}
}
}
else
{
lean_object* x_433; 
lean_dec(x_426);
lean_dec(x_425);
lean_dec(x_423);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_433 = lean_ctor_get(x_427, 0);
lean_inc(x_433);
lean_dec_ref(x_427);
x_349 = x_418;
x_350 = x_419;
x_351 = x_420;
x_352 = x_422;
x_353 = x_421;
x_354 = x_424;
x_355 = x_433;
goto block_357;
}
}
block_448:
{
uint8_t x_445; lean_object* x_446; 
x_445 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_443);
x_446 = l_List_appendTR___redArg(x_444, x_443);
if (x_445 == 0)
{
x_377 = x_435;
x_378 = x_436;
x_379 = x_437;
x_380 = x_438;
x_381 = x_439;
x_382 = x_446;
x_383 = x_441;
x_384 = x_440;
x_385 = x_443;
x_386 = x_442;
goto block_391;
}
else
{
uint8_t x_447; 
x_447 = l_List_isEmpty___redArg(x_443);
if (x_447 == 0)
{
x_418 = x_435;
x_419 = x_436;
x_420 = x_437;
x_421 = x_438;
x_422 = x_439;
x_423 = x_446;
x_424 = x_441;
x_425 = x_440;
x_426 = x_443;
goto block_434;
}
else
{
if (x_442 == 0)
{
x_377 = x_435;
x_378 = x_436;
x_379 = x_437;
x_380 = x_438;
x_381 = x_439;
x_382 = x_446;
x_383 = x_441;
x_384 = x_440;
x_385 = x_443;
x_386 = x_442;
goto block_391;
}
else
{
x_418 = x_435;
x_419 = x_436;
x_420 = x_437;
x_421 = x_438;
x_422 = x_439;
x_423 = x_446;
x_424 = x_441;
x_425 = x_440;
x_426 = x_443;
goto block_434;
}
}
}
}
block_473:
{
lean_object* x_457; 
x_457 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_457) == 0)
{
if (x_455 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
lean_dec_ref(x_457);
x_459 = lean_io_mono_nanos_now();
x_460 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_24, x_455, x_5, x_456, x_8);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
lean_dec_ref(x_460);
x_462 = l_List_reverse___redArg(x_461);
x_435 = x_459;
x_436 = x_449;
x_437 = x_450;
x_438 = x_451;
x_439 = x_458;
x_440 = x_452;
x_441 = x_453;
x_442 = x_455;
x_443 = x_454;
x_444 = x_462;
goto block_448;
}
else
{
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_460, 0);
lean_inc(x_463);
lean_dec_ref(x_460);
x_435 = x_459;
x_436 = x_449;
x_437 = x_450;
x_438 = x_451;
x_439 = x_458;
x_440 = x_452;
x_441 = x_453;
x_442 = x_455;
x_443 = x_454;
x_444 = x_463;
goto block_448;
}
else
{
lean_object* x_464; 
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_464 = lean_ctor_get(x_460, 0);
lean_inc(x_464);
lean_dec_ref(x_460);
x_349 = x_459;
x_350 = x_449;
x_351 = x_450;
x_352 = x_458;
x_353 = x_451;
x_354 = x_453;
x_355 = x_464;
goto block_357;
}
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_457, 0);
lean_inc(x_465);
lean_dec_ref(x_457);
x_466 = lean_io_get_num_heartbeats();
x_467 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_24, x_455, x_5, x_456, x_8);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
lean_dec_ref(x_467);
x_469 = l_List_reverse___redArg(x_468);
x_293 = x_466;
x_294 = x_449;
x_295 = x_450;
x_296 = x_465;
x_297 = x_451;
x_298 = x_452;
x_299 = x_453;
x_300 = x_455;
x_301 = x_454;
x_302 = x_469;
goto block_308;
}
else
{
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_470; 
x_470 = lean_ctor_get(x_467, 0);
lean_inc(x_470);
lean_dec_ref(x_467);
x_293 = x_466;
x_294 = x_449;
x_295 = x_450;
x_296 = x_465;
x_297 = x_451;
x_298 = x_452;
x_299 = x_453;
x_300 = x_455;
x_301 = x_454;
x_302 = x_470;
goto block_308;
}
else
{
lean_object* x_471; 
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_471 = lean_ctor_get(x_467, 0);
lean_inc(x_471);
lean_dec_ref(x_467);
x_198 = x_466;
x_199 = x_449;
x_200 = x_450;
x_201 = x_465;
x_202 = x_451;
x_203 = x_453;
x_204 = x_471;
goto block_206;
}
}
}
}
else
{
lean_object* x_472; 
lean_dec(x_456);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_472 = lean_ctor_get(x_457, 0);
lean_inc(x_472);
lean_dec_ref(x_457);
x_127 = x_449;
x_128 = x_451;
x_129 = x_472;
goto block_131;
}
}
block_478:
{
lean_object* x_476; lean_object* x_477; 
x_476 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
x_477 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_476, x_7, x_8, x_9, x_10);
x_176 = x_474;
x_177 = x_475;
x_178 = x_477;
goto block_181;
}
block_489:
{
uint8_t x_485; 
x_485 = l_List_isEmpty___redArg(x_481);
lean_dec(x_481);
if (x_485 == 0)
{
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_474 = x_479;
x_475 = x_480;
goto block_478;
}
else
{
if (x_484 == 0)
{
lean_object* x_486; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_486 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_483, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
lean_dec_ref(x_486);
x_488 = l_List_appendTR___redArg(x_482, x_487);
x_132 = x_479;
x_133 = x_480;
x_134 = x_488;
goto block_136;
}
else
{
lean_dec(x_482);
x_176 = x_479;
x_177 = x_480;
x_178 = x_486;
goto block_181;
}
}
else
{
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_474 = x_479;
x_475 = x_480;
goto block_478;
}
}
}
block_499:
{
uint8_t x_496; lean_object* x_497; 
x_496 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_493);
x_497 = l_List_appendTR___redArg(x_495, x_493);
if (x_496 == 0)
{
x_479 = x_490;
x_480 = x_491;
x_481 = x_492;
x_482 = x_493;
x_483 = x_497;
x_484 = x_494;
goto block_489;
}
else
{
uint8_t x_498; 
x_498 = l_List_isEmpty___redArg(x_493);
if (x_498 == 0)
{
x_163 = x_490;
x_164 = x_491;
x_165 = x_492;
x_166 = x_493;
x_167 = x_497;
goto block_175;
}
else
{
if (x_494 == 0)
{
x_479 = x_490;
x_480 = x_491;
x_481 = x_492;
x_482 = x_493;
x_483 = x_497;
x_484 = x_494;
goto block_489;
}
else
{
x_163 = x_490;
x_164 = x_491;
x_165 = x_492;
x_166 = x_493;
x_167 = x_497;
goto block_175;
}
}
}
}
block_512:
{
lean_object* x_503; double x_504; double x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; lean_object* x_511; 
x_503 = lean_io_get_num_heartbeats();
x_504 = lean_float_of_nat(x_501);
x_505 = lean_float_of_nat(x_503);
x_506 = lean_box_float(x_504);
x_507 = lean_box_float(x_505);
x_508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_502);
lean_ctor_set(x_509, 1, x_508);
x_510 = lean_unbox(x_106);
lean_dec(x_106);
x_511 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_24, x_108, x_23, x_510, x_500, x_107, x_509, x_7, x_8, x_9, x_10);
lean_dec_ref(x_23);
return x_511;
}
block_517:
{
lean_object* x_516; 
x_516 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_516, 0, x_515);
x_500 = x_513;
x_501 = x_514;
x_502 = x_516;
goto block_512;
}
block_525:
{
lean_object* x_523; lean_object* x_524; 
x_523 = l_List_appendTR___redArg(x_521, x_518);
x_524 = l_List_appendTR___redArg(x_523, x_522);
x_513 = x_519;
x_514 = x_520;
x_515 = x_524;
goto block_517;
}
block_530:
{
lean_object* x_529; 
x_529 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_529, 0, x_528);
x_500 = x_526;
x_501 = x_527;
x_502 = x_529;
goto block_512;
}
block_536:
{
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
lean_dec_ref(x_533);
x_513 = x_531;
x_514 = x_532;
x_515 = x_534;
goto block_517;
}
else
{
lean_object* x_535; 
x_535 = lean_ctor_get(x_533, 0);
lean_inc(x_535);
lean_dec_ref(x_533);
x_526 = x_531;
x_527 = x_532;
x_528 = x_535;
goto block_530;
}
}
block_555:
{
lean_object* x_544; double x_545; double x_546; double x_547; double x_548; double x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_544 = lean_io_mono_nanos_now();
x_545 = lean_float_of_nat(x_538);
x_546 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_547 = lean_float_div(x_545, x_546);
x_548 = lean_float_of_nat(x_544);
x_549 = lean_float_div(x_548, x_546);
x_550 = lean_box_float(x_547);
x_551 = lean_box_float(x_549);
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_543);
lean_ctor_set(x_553, 1, x_552);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_554 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_24, x_108, x_23, x_542, x_537, x_539, x_553, x_7, x_8, x_9, x_10);
x_531 = x_540;
x_532 = x_541;
x_533 = x_554;
goto block_536;
}
block_564:
{
lean_object* x_563; 
x_563 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_563, 0, x_562);
x_537 = x_557;
x_538 = x_556;
x_539 = x_558;
x_540 = x_559;
x_541 = x_560;
x_542 = x_561;
x_543 = x_563;
goto block_555;
}
block_576:
{
lean_object* x_574; lean_object* x_575; 
x_574 = l_List_appendTR___redArg(x_571, x_565);
x_575 = l_List_appendTR___redArg(x_574, x_573);
x_556 = x_567;
x_557 = x_566;
x_558 = x_568;
x_559 = x_569;
x_560 = x_570;
x_561 = x_572;
x_562 = x_575;
goto block_564;
}
block_585:
{
lean_object* x_584; 
x_584 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_584, 0, x_583);
x_537 = x_578;
x_538 = x_577;
x_539 = x_579;
x_540 = x_580;
x_541 = x_581;
x_542 = x_582;
x_543 = x_584;
goto block_555;
}
block_595:
{
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
lean_dec_ref(x_592);
x_556 = x_587;
x_557 = x_586;
x_558 = x_588;
x_559 = x_589;
x_560 = x_590;
x_561 = x_591;
x_562 = x_593;
goto block_564;
}
else
{
lean_object* x_594; 
x_594 = lean_ctor_get(x_592, 0);
lean_inc(x_594);
lean_dec_ref(x_592);
x_577 = x_587;
x_578 = x_586;
x_579 = x_588;
x_580 = x_589;
x_581 = x_590;
x_582 = x_591;
x_583 = x_594;
goto block_585;
}
}
block_604:
{
lean_object* x_602; lean_object* x_603; 
x_602 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
x_603 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_602, x_7, x_8, x_9, x_10);
x_586 = x_597;
x_587 = x_596;
x_588 = x_598;
x_589 = x_599;
x_590 = x_600;
x_591 = x_601;
x_592 = x_603;
goto block_595;
}
block_619:
{
uint8_t x_615; 
x_615 = l_List_isEmpty___redArg(x_605);
lean_dec(x_605);
if (x_615 == 0)
{
lean_dec(x_614);
lean_dec(x_611);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_596 = x_607;
x_597 = x_606;
x_598 = x_608;
x_599 = x_609;
x_600 = x_610;
x_601 = x_612;
goto block_604;
}
else
{
if (x_613 == 0)
{
lean_object* x_616; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_616 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_614, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; lean_object* x_618; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
lean_dec_ref(x_616);
x_618 = l_List_appendTR___redArg(x_611, x_617);
x_556 = x_607;
x_557 = x_606;
x_558 = x_608;
x_559 = x_609;
x_560 = x_610;
x_561 = x_612;
x_562 = x_618;
goto block_564;
}
else
{
lean_dec(x_611);
x_586 = x_606;
x_587 = x_607;
x_588 = x_608;
x_589 = x_609;
x_590 = x_610;
x_591 = x_612;
x_592 = x_616;
goto block_595;
}
}
else
{
lean_dec(x_614);
lean_dec(x_611);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_596 = x_607;
x_597 = x_606;
x_598 = x_608;
x_599 = x_609;
x_600 = x_610;
x_601 = x_612;
goto block_604;
}
}
}
block_631:
{
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; 
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
lean_dec_ref(x_628);
x_565 = x_620;
x_566 = x_622;
x_567 = x_621;
x_568 = x_623;
x_569 = x_624;
x_570 = x_625;
x_571 = x_626;
x_572 = x_627;
x_573 = x_629;
goto block_576;
}
else
{
lean_object* x_630; 
lean_dec(x_626);
lean_dec(x_620);
x_630 = lean_ctor_get(x_628, 0);
lean_inc(x_630);
lean_dec_ref(x_628);
x_577 = x_621;
x_578 = x_622;
x_579 = x_623;
x_580 = x_624;
x_581 = x_625;
x_582 = x_627;
x_583 = x_630;
goto block_585;
}
}
block_645:
{
if (x_642 == 0)
{
lean_object* x_643; 
lean_dec_ref(x_638);
x_643 = l_Lean_Meta_SavedState_restore___redArg(x_641, x_8, x_10);
lean_dec_ref(x_641);
if (lean_obj_tag(x_643) == 0)
{
lean_dec_ref(x_643);
x_565 = x_632;
x_566 = x_634;
x_567 = x_633;
x_568 = x_635;
x_569 = x_636;
x_570 = x_637;
x_571 = x_639;
x_572 = x_640;
x_573 = x_19;
goto block_576;
}
else
{
lean_object* x_644; 
lean_dec(x_639);
lean_dec(x_632);
lean_dec(x_19);
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
lean_dec_ref(x_643);
x_577 = x_633;
x_578 = x_634;
x_579 = x_635;
x_580 = x_636;
x_581 = x_637;
x_582 = x_640;
x_583 = x_644;
goto block_585;
}
}
else
{
lean_dec_ref(x_641);
lean_dec(x_19);
x_620 = x_632;
x_621 = x_633;
x_622 = x_634;
x_623 = x_635;
x_624 = x_636;
x_625 = x_637;
x_626 = x_639;
x_627 = x_640;
x_628 = x_638;
goto block_631;
}
}
block_662:
{
lean_object* x_655; 
x_655 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
lean_dec_ref(x_655);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_19);
lean_inc(x_2);
x_657 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_654, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_657) == 0)
{
lean_dec(x_656);
lean_dec(x_19);
x_620 = x_646;
x_621 = x_648;
x_622 = x_647;
x_623 = x_649;
x_624 = x_650;
x_625 = x_651;
x_626 = x_652;
x_627 = x_653;
x_628 = x_657;
goto block_631;
}
else
{
lean_object* x_658; uint8_t x_659; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = l_Lean_Exception_isInterrupt(x_658);
if (x_659 == 0)
{
uint8_t x_660; 
x_660 = l_Lean_Exception_isRuntime(x_658);
x_632 = x_646;
x_633 = x_648;
x_634 = x_647;
x_635 = x_649;
x_636 = x_650;
x_637 = x_651;
x_638 = x_657;
x_639 = x_652;
x_640 = x_653;
x_641 = x_656;
x_642 = x_660;
goto block_645;
}
else
{
lean_dec(x_658);
x_632 = x_646;
x_633 = x_648;
x_634 = x_647;
x_635 = x_649;
x_636 = x_650;
x_637 = x_651;
x_638 = x_657;
x_639 = x_652;
x_640 = x_653;
x_641 = x_656;
x_642 = x_659;
goto block_645;
}
}
}
else
{
lean_object* x_661; 
lean_dec(x_654);
lean_dec(x_652);
lean_dec(x_646);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_661 = lean_ctor_get(x_655, 0);
lean_inc(x_661);
lean_dec_ref(x_655);
x_577 = x_648;
x_578 = x_647;
x_579 = x_649;
x_580 = x_650;
x_581 = x_651;
x_582 = x_653;
x_583 = x_661;
goto block_585;
}
}
block_676:
{
uint8_t x_673; lean_object* x_674; 
x_673 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_669);
x_674 = l_List_appendTR___redArg(x_672, x_669);
if (x_673 == 0)
{
x_605 = x_663;
x_606 = x_664;
x_607 = x_665;
x_608 = x_666;
x_609 = x_667;
x_610 = x_668;
x_611 = x_669;
x_612 = x_670;
x_613 = x_671;
x_614 = x_674;
goto block_619;
}
else
{
uint8_t x_675; 
x_675 = l_List_isEmpty___redArg(x_669);
if (x_675 == 0)
{
x_646 = x_663;
x_647 = x_664;
x_648 = x_665;
x_649 = x_666;
x_650 = x_667;
x_651 = x_668;
x_652 = x_669;
x_653 = x_670;
x_654 = x_674;
goto block_662;
}
else
{
if (x_671 == 0)
{
x_605 = x_663;
x_606 = x_664;
x_607 = x_665;
x_608 = x_666;
x_609 = x_667;
x_610 = x_668;
x_611 = x_669;
x_612 = x_670;
x_613 = x_671;
x_614 = x_674;
goto block_619;
}
else
{
x_646 = x_663;
x_647 = x_664;
x_648 = x_665;
x_649 = x_666;
x_650 = x_667;
x_651 = x_668;
x_652 = x_669;
x_653 = x_670;
x_654 = x_674;
goto block_662;
}
}
}
}
block_692:
{
lean_object* x_684; double x_685; double x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_684 = lean_io_get_num_heartbeats();
x_685 = lean_float_of_nat(x_681);
x_686 = lean_float_of_nat(x_684);
x_687 = lean_box_float(x_685);
x_688 = lean_box_float(x_686);
x_689 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_689, 0, x_687);
lean_ctor_set(x_689, 1, x_688);
x_690 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_690, 0, x_683);
lean_ctor_set(x_690, 1, x_689);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_691 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_2, x_24, x_108, x_23, x_682, x_677, x_678, x_690, x_7, x_8, x_9, x_10);
x_531 = x_679;
x_532 = x_680;
x_533 = x_691;
goto block_536;
}
block_701:
{
lean_object* x_700; 
x_700 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_700, 0, x_699);
x_677 = x_693;
x_678 = x_694;
x_679 = x_695;
x_680 = x_696;
x_681 = x_697;
x_682 = x_698;
x_683 = x_700;
goto block_692;
}
block_713:
{
lean_object* x_711; lean_object* x_712; 
x_711 = l_List_appendTR___redArg(x_708, x_702);
x_712 = l_List_appendTR___redArg(x_711, x_710);
x_693 = x_703;
x_694 = x_704;
x_695 = x_705;
x_696 = x_706;
x_697 = x_707;
x_698 = x_709;
x_699 = x_712;
goto block_701;
}
block_722:
{
lean_object* x_721; 
x_721 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_721, 0, x_720);
x_677 = x_714;
x_678 = x_715;
x_679 = x_716;
x_680 = x_717;
x_681 = x_718;
x_682 = x_719;
x_683 = x_721;
goto block_692;
}
block_732:
{
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
lean_dec_ref(x_729);
x_693 = x_723;
x_694 = x_724;
x_695 = x_725;
x_696 = x_726;
x_697 = x_727;
x_698 = x_728;
x_699 = x_730;
goto block_701;
}
else
{
lean_object* x_731; 
x_731 = lean_ctor_get(x_729, 0);
lean_inc(x_731);
lean_dec_ref(x_729);
x_714 = x_723;
x_715 = x_724;
x_716 = x_725;
x_717 = x_726;
x_718 = x_727;
x_719 = x_728;
x_720 = x_731;
goto block_722;
}
}
block_744:
{
lean_object* x_741; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_741 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_739, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; lean_object* x_743; 
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
lean_dec_ref(x_741);
x_743 = l_List_appendTR___redArg(x_738, x_742);
x_693 = x_733;
x_694 = x_734;
x_695 = x_735;
x_696 = x_736;
x_697 = x_737;
x_698 = x_740;
x_699 = x_743;
goto block_701;
}
else
{
lean_dec(x_738);
x_723 = x_733;
x_724 = x_734;
x_725 = x_735;
x_726 = x_736;
x_727 = x_737;
x_728 = x_740;
x_729 = x_741;
goto block_732;
}
}
block_758:
{
uint8_t x_755; 
x_755 = l_List_isEmpty___redArg(x_745);
lean_dec(x_745);
if (x_755 == 0)
{
if (x_754 == 0)
{
x_733 = x_746;
x_734 = x_747;
x_735 = x_748;
x_736 = x_749;
x_737 = x_750;
x_738 = x_752;
x_739 = x_751;
x_740 = x_753;
goto block_744;
}
else
{
lean_object* x_756; lean_object* x_757; 
lean_dec(x_752);
lean_dec(x_751);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_756 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
x_757 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_756, x_7, x_8, x_9, x_10);
x_723 = x_746;
x_724 = x_747;
x_725 = x_748;
x_726 = x_749;
x_727 = x_750;
x_728 = x_753;
x_729 = x_757;
goto block_732;
}
}
else
{
x_733 = x_746;
x_734 = x_747;
x_735 = x_748;
x_736 = x_749;
x_737 = x_750;
x_738 = x_752;
x_739 = x_751;
x_740 = x_753;
goto block_744;
}
}
block_770:
{
if (lean_obj_tag(x_767) == 0)
{
lean_object* x_768; 
x_768 = lean_ctor_get(x_767, 0);
lean_inc(x_768);
lean_dec_ref(x_767);
x_702 = x_759;
x_703 = x_760;
x_704 = x_761;
x_705 = x_762;
x_706 = x_763;
x_707 = x_764;
x_708 = x_765;
x_709 = x_766;
x_710 = x_768;
goto block_713;
}
else
{
lean_object* x_769; 
lean_dec(x_765);
lean_dec(x_759);
x_769 = lean_ctor_get(x_767, 0);
lean_inc(x_769);
lean_dec_ref(x_767);
x_714 = x_760;
x_715 = x_761;
x_716 = x_762;
x_717 = x_763;
x_718 = x_764;
x_719 = x_766;
x_720 = x_769;
goto block_722;
}
}
block_784:
{
if (x_781 == 0)
{
lean_object* x_782; 
lean_dec_ref(x_780);
x_782 = l_Lean_Meta_SavedState_restore___redArg(x_775, x_8, x_10);
lean_dec_ref(x_775);
if (lean_obj_tag(x_782) == 0)
{
lean_dec_ref(x_782);
x_702 = x_771;
x_703 = x_772;
x_704 = x_773;
x_705 = x_774;
x_706 = x_776;
x_707 = x_777;
x_708 = x_778;
x_709 = x_779;
x_710 = x_19;
goto block_713;
}
else
{
lean_object* x_783; 
lean_dec(x_778);
lean_dec(x_771);
lean_dec(x_19);
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
lean_dec_ref(x_782);
x_714 = x_772;
x_715 = x_773;
x_716 = x_774;
x_717 = x_776;
x_718 = x_777;
x_719 = x_779;
x_720 = x_783;
goto block_722;
}
}
else
{
lean_dec_ref(x_775);
lean_dec(x_19);
x_759 = x_771;
x_760 = x_772;
x_761 = x_773;
x_762 = x_774;
x_763 = x_776;
x_764 = x_777;
x_765 = x_778;
x_766 = x_779;
x_767 = x_780;
goto block_770;
}
}
block_801:
{
lean_object* x_794; 
x_794 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; 
x_795 = lean_ctor_get(x_794, 0);
lean_inc(x_795);
lean_dec_ref(x_794);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_19);
lean_inc(x_2);
x_796 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_792, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_796) == 0)
{
lean_dec(x_795);
lean_dec(x_19);
x_759 = x_785;
x_760 = x_786;
x_761 = x_787;
x_762 = x_788;
x_763 = x_789;
x_764 = x_790;
x_765 = x_791;
x_766 = x_793;
x_767 = x_796;
goto block_770;
}
else
{
lean_object* x_797; uint8_t x_798; 
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
x_798 = l_Lean_Exception_isInterrupt(x_797);
if (x_798 == 0)
{
uint8_t x_799; 
x_799 = l_Lean_Exception_isRuntime(x_797);
x_771 = x_785;
x_772 = x_786;
x_773 = x_787;
x_774 = x_788;
x_775 = x_795;
x_776 = x_789;
x_777 = x_790;
x_778 = x_791;
x_779 = x_793;
x_780 = x_796;
x_781 = x_799;
goto block_784;
}
else
{
lean_dec(x_797);
x_771 = x_785;
x_772 = x_786;
x_773 = x_787;
x_774 = x_788;
x_775 = x_795;
x_776 = x_789;
x_777 = x_790;
x_778 = x_791;
x_779 = x_793;
x_780 = x_796;
x_781 = x_798;
goto block_784;
}
}
}
else
{
lean_object* x_800; 
lean_dec(x_792);
lean_dec(x_791);
lean_dec(x_785);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_800 = lean_ctor_get(x_794, 0);
lean_inc(x_800);
lean_dec_ref(x_794);
x_714 = x_786;
x_715 = x_787;
x_716 = x_788;
x_717 = x_789;
x_718 = x_790;
x_719 = x_793;
x_720 = x_800;
goto block_722;
}
}
block_815:
{
uint8_t x_812; lean_object* x_813; 
x_812 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_808);
x_813 = l_List_appendTR___redArg(x_811, x_808);
if (x_812 == 0)
{
x_745 = x_802;
x_746 = x_803;
x_747 = x_804;
x_748 = x_805;
x_749 = x_806;
x_750 = x_807;
x_751 = x_813;
x_752 = x_808;
x_753 = x_809;
x_754 = x_810;
goto block_758;
}
else
{
uint8_t x_814; 
x_814 = l_List_isEmpty___redArg(x_808);
if (x_814 == 0)
{
x_785 = x_802;
x_786 = x_803;
x_787 = x_804;
x_788 = x_805;
x_789 = x_806;
x_790 = x_807;
x_791 = x_808;
x_792 = x_813;
x_793 = x_809;
goto block_801;
}
else
{
if (x_22 == 0)
{
x_745 = x_802;
x_746 = x_803;
x_747 = x_804;
x_748 = x_805;
x_749 = x_806;
x_750 = x_807;
x_751 = x_813;
x_752 = x_808;
x_753 = x_809;
x_754 = x_810;
goto block_758;
}
else
{
x_785 = x_802;
x_786 = x_803;
x_787 = x_804;
x_788 = x_805;
x_789 = x_806;
x_790 = x_807;
x_791 = x_808;
x_792 = x_813;
x_793 = x_809;
goto block_801;
}
}
}
}
block_840:
{
lean_object* x_824; 
x_824 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_824) == 0)
{
if (x_823 == 0)
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_825 = lean_ctor_get(x_824, 0);
lean_inc(x_825);
lean_dec_ref(x_824);
x_826 = lean_io_mono_nanos_now();
x_827 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_823, x_22, x_5, x_817, x_8);
if (lean_obj_tag(x_827) == 0)
{
lean_object* x_828; lean_object* x_829; 
x_828 = lean_ctor_get(x_827, 0);
lean_inc(x_828);
lean_dec_ref(x_827);
x_829 = l_List_reverse___redArg(x_828);
x_663 = x_816;
x_664 = x_825;
x_665 = x_826;
x_666 = x_818;
x_667 = x_819;
x_668 = x_820;
x_669 = x_821;
x_670 = x_822;
x_671 = x_823;
x_672 = x_829;
goto block_676;
}
else
{
if (lean_obj_tag(x_827) == 0)
{
lean_object* x_830; 
x_830 = lean_ctor_get(x_827, 0);
lean_inc(x_830);
lean_dec_ref(x_827);
x_663 = x_816;
x_664 = x_825;
x_665 = x_826;
x_666 = x_818;
x_667 = x_819;
x_668 = x_820;
x_669 = x_821;
x_670 = x_822;
x_671 = x_823;
x_672 = x_830;
goto block_676;
}
else
{
lean_object* x_831; 
lean_dec(x_821);
lean_dec(x_816);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_831 = lean_ctor_get(x_827, 0);
lean_inc(x_831);
lean_dec_ref(x_827);
x_577 = x_826;
x_578 = x_825;
x_579 = x_818;
x_580 = x_819;
x_581 = x_820;
x_582 = x_822;
x_583 = x_831;
goto block_585;
}
}
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_832 = lean_ctor_get(x_824, 0);
lean_inc(x_832);
lean_dec_ref(x_824);
x_833 = lean_io_get_num_heartbeats();
x_834 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_823, x_22, x_5, x_817, x_8);
if (lean_obj_tag(x_834) == 0)
{
lean_object* x_835; lean_object* x_836; 
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
lean_dec_ref(x_834);
x_836 = l_List_reverse___redArg(x_835);
x_802 = x_816;
x_803 = x_832;
x_804 = x_818;
x_805 = x_819;
x_806 = x_820;
x_807 = x_833;
x_808 = x_821;
x_809 = x_822;
x_810 = x_823;
x_811 = x_836;
goto block_815;
}
else
{
if (lean_obj_tag(x_834) == 0)
{
lean_object* x_837; 
x_837 = lean_ctor_get(x_834, 0);
lean_inc(x_837);
lean_dec_ref(x_834);
x_802 = x_816;
x_803 = x_832;
x_804 = x_818;
x_805 = x_819;
x_806 = x_820;
x_807 = x_833;
x_808 = x_821;
x_809 = x_822;
x_810 = x_823;
x_811 = x_837;
goto block_815;
}
else
{
lean_object* x_838; 
lean_dec(x_821);
lean_dec(x_816);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_838 = lean_ctor_get(x_834, 0);
lean_inc(x_838);
lean_dec_ref(x_834);
x_714 = x_832;
x_715 = x_818;
x_716 = x_819;
x_717 = x_820;
x_718 = x_833;
x_719 = x_822;
x_720 = x_838;
goto block_722;
}
}
}
}
else
{
lean_object* x_839; 
lean_dec(x_821);
lean_dec_ref(x_818);
lean_dec(x_817);
lean_dec(x_816);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_839 = lean_ctor_get(x_824, 0);
lean_inc(x_839);
lean_dec_ref(x_824);
x_526 = x_819;
x_527 = x_820;
x_528 = x_839;
goto block_530;
}
}
block_845:
{
lean_object* x_843; lean_object* x_844; 
x_843 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
x_844 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_843, x_7, x_8, x_9, x_10);
x_531 = x_841;
x_532 = x_842;
x_533 = x_844;
goto block_536;
}
block_856:
{
uint8_t x_852; 
x_852 = l_List_isEmpty___redArg(x_846);
lean_dec(x_846);
if (x_852 == 0)
{
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_841 = x_847;
x_842 = x_848;
goto block_845;
}
else
{
if (x_851 == 0)
{
lean_object* x_853; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_853 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_849, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
lean_dec_ref(x_853);
x_855 = l_List_appendTR___redArg(x_850, x_854);
x_513 = x_847;
x_514 = x_848;
x_515 = x_855;
goto block_517;
}
else
{
lean_dec(x_850);
x_531 = x_847;
x_532 = x_848;
x_533 = x_853;
goto block_536;
}
}
else
{
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_841 = x_847;
x_842 = x_848;
goto block_845;
}
}
}
block_864:
{
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; 
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
lean_dec_ref(x_861);
x_518 = x_857;
x_519 = x_858;
x_520 = x_859;
x_521 = x_860;
x_522 = x_862;
goto block_525;
}
else
{
lean_object* x_863; 
lean_dec(x_860);
lean_dec(x_857);
x_863 = lean_ctor_get(x_861, 0);
lean_inc(x_863);
lean_dec_ref(x_861);
x_526 = x_858;
x_527 = x_859;
x_528 = x_863;
goto block_530;
}
}
block_874:
{
if (x_871 == 0)
{
lean_object* x_872; 
lean_dec_ref(x_867);
x_872 = l_Lean_Meta_SavedState_restore___redArg(x_870, x_8, x_10);
lean_dec_ref(x_870);
if (lean_obj_tag(x_872) == 0)
{
lean_dec_ref(x_872);
x_518 = x_865;
x_519 = x_866;
x_520 = x_868;
x_521 = x_869;
x_522 = x_19;
goto block_525;
}
else
{
lean_object* x_873; 
lean_dec(x_869);
lean_dec(x_865);
lean_dec(x_19);
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
lean_dec_ref(x_872);
x_526 = x_866;
x_527 = x_868;
x_528 = x_873;
goto block_530;
}
}
else
{
lean_dec_ref(x_870);
lean_dec(x_19);
x_857 = x_865;
x_858 = x_866;
x_859 = x_868;
x_860 = x_869;
x_861 = x_867;
goto block_864;
}
}
block_887:
{
lean_object* x_880; 
x_880 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; lean_object* x_882; 
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
lean_dec_ref(x_880);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_19);
lean_inc(x_2);
x_882 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_878, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_882) == 0)
{
lean_dec(x_881);
lean_dec(x_19);
x_857 = x_875;
x_858 = x_876;
x_859 = x_877;
x_860 = x_879;
x_861 = x_882;
goto block_864;
}
else
{
lean_object* x_883; uint8_t x_884; 
x_883 = lean_ctor_get(x_882, 0);
lean_inc(x_883);
x_884 = l_Lean_Exception_isInterrupt(x_883);
if (x_884 == 0)
{
uint8_t x_885; 
x_885 = l_Lean_Exception_isRuntime(x_883);
x_865 = x_875;
x_866 = x_876;
x_867 = x_882;
x_868 = x_877;
x_869 = x_879;
x_870 = x_881;
x_871 = x_885;
goto block_874;
}
else
{
lean_dec(x_883);
x_865 = x_875;
x_866 = x_876;
x_867 = x_882;
x_868 = x_877;
x_869 = x_879;
x_870 = x_881;
x_871 = x_884;
goto block_874;
}
}
}
else
{
lean_object* x_886; 
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_875);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_886 = lean_ctor_get(x_880, 0);
lean_inc(x_886);
lean_dec_ref(x_880);
x_526 = x_876;
x_527 = x_877;
x_528 = x_886;
goto block_530;
}
}
block_897:
{
uint8_t x_894; lean_object* x_895; 
x_894 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_891);
x_895 = l_List_appendTR___redArg(x_893, x_891);
if (x_894 == 0)
{
x_846 = x_888;
x_847 = x_889;
x_848 = x_890;
x_849 = x_895;
x_850 = x_891;
x_851 = x_892;
goto block_856;
}
else
{
uint8_t x_896; 
x_896 = l_List_isEmpty___redArg(x_891);
if (x_896 == 0)
{
x_875 = x_888;
x_876 = x_889;
x_877 = x_890;
x_878 = x_895;
x_879 = x_891;
goto block_887;
}
else
{
if (x_892 == 0)
{
x_846 = x_888;
x_847 = x_889;
x_848 = x_890;
x_849 = x_895;
x_850 = x_891;
x_851 = x_892;
goto block_856;
}
else
{
x_875 = x_888;
x_876 = x_889;
x_877 = x_890;
x_878 = x_895;
x_879 = x_891;
goto block_887;
}
}
}
}
block_954:
{
lean_object* x_898; 
x_898 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; uint8_t x_901; 
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
lean_dec_ref(x_898);
x_900 = l_Lean_trace_profiler_useHeartbeats;
x_901 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_23, x_900);
if (x_901 == 0)
{
lean_object* x_902; lean_object* x_903; 
x_902 = lean_io_mono_nanos_now();
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_903 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_18, x_25, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
lean_dec_ref(x_903);
x_905 = lean_ctor_get(x_904, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_904, 1);
lean_inc(x_906);
lean_dec(x_904);
lean_inc(x_2);
x_907 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; uint8_t x_912; 
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
lean_dec_ref(x_907);
x_909 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_906, x_15);
lean_inc(x_909);
lean_inc(x_905);
x_910 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(x_910, 0, x_905);
lean_closure_set(x_910, 1, x_909);
x_911 = lean_box(0);
x_912 = lean_unbox(x_908);
if (x_912 == 0)
{
lean_object* x_913; uint8_t x_914; 
x_913 = l_Lean_trace_profiler;
x_914 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_23, x_913);
if (x_914 == 0)
{
lean_object* x_915; 
lean_dec_ref(x_910);
lean_dec(x_908);
x_915 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_24, x_901, x_5, x_911, x_8);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
lean_dec_ref(x_915);
x_917 = l_List_reverse___redArg(x_916);
x_490 = x_902;
x_491 = x_899;
x_492 = x_905;
x_493 = x_909;
x_494 = x_914;
x_495 = x_917;
goto block_499;
}
else
{
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_918; 
x_918 = lean_ctor_get(x_915, 0);
lean_inc(x_918);
lean_dec_ref(x_915);
x_490 = x_902;
x_491 = x_899;
x_492 = x_905;
x_493 = x_909;
x_494 = x_914;
x_495 = x_918;
goto block_499;
}
else
{
lean_object* x_919; 
lean_dec(x_909);
lean_dec(x_905);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_919 = lean_ctor_get(x_915, 0);
lean_inc(x_919);
lean_dec_ref(x_915);
x_127 = x_902;
x_128 = x_899;
x_129 = x_919;
goto block_131;
}
}
}
else
{
uint8_t x_920; 
x_920 = lean_unbox(x_908);
lean_dec(x_908);
x_449 = x_902;
x_450 = x_920;
x_451 = x_899;
x_452 = x_905;
x_453 = x_910;
x_454 = x_909;
x_455 = x_901;
x_456 = x_911;
goto block_473;
}
}
else
{
uint8_t x_921; 
x_921 = lean_unbox(x_908);
lean_dec(x_908);
x_449 = x_902;
x_450 = x_921;
x_451 = x_899;
x_452 = x_905;
x_453 = x_910;
x_454 = x_909;
x_455 = x_901;
x_456 = x_911;
goto block_473;
}
}
else
{
lean_object* x_922; 
lean_dec(x_906);
lean_dec(x_905);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_922 = lean_ctor_get(x_907, 0);
lean_inc(x_922);
lean_dec_ref(x_907);
x_127 = x_902;
x_128 = x_899;
x_129 = x_922;
goto block_131;
}
}
else
{
lean_object* x_923; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_923 = lean_ctor_get(x_903, 0);
lean_inc(x_923);
lean_dec_ref(x_903);
x_127 = x_902;
x_128 = x_899;
x_129 = x_923;
goto block_131;
}
}
else
{
lean_object* x_924; lean_object* x_925; 
lean_del_object(x_20);
x_924 = lean_io_get_num_heartbeats();
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_925 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_18, x_25, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_925) == 0)
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
lean_dec_ref(x_925);
x_927 = lean_ctor_get(x_926, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_926, 1);
lean_inc(x_928);
lean_dec(x_926);
lean_inc(x_2);
x_929 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; uint8_t x_934; 
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
lean_dec_ref(x_929);
x_931 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_928, x_15);
lean_inc(x_931);
lean_inc(x_927);
x_932 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(x_932, 0, x_927);
lean_closure_set(x_932, 1, x_931);
x_933 = lean_box(0);
x_934 = lean_unbox(x_930);
if (x_934 == 0)
{
lean_object* x_935; uint8_t x_936; 
x_935 = l_Lean_trace_profiler;
x_936 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_23, x_935);
if (x_936 == 0)
{
lean_object* x_937; 
lean_dec_ref(x_932);
lean_dec(x_930);
x_937 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_901, x_22, x_5, x_933, x_8);
if (lean_obj_tag(x_937) == 0)
{
lean_object* x_938; lean_object* x_939; 
x_938 = lean_ctor_get(x_937, 0);
lean_inc(x_938);
lean_dec_ref(x_937);
x_939 = l_List_reverse___redArg(x_938);
x_888 = x_927;
x_889 = x_899;
x_890 = x_924;
x_891 = x_931;
x_892 = x_936;
x_893 = x_939;
goto block_897;
}
else
{
if (lean_obj_tag(x_937) == 0)
{
lean_object* x_940; 
x_940 = lean_ctor_get(x_937, 0);
lean_inc(x_940);
lean_dec_ref(x_937);
x_888 = x_927;
x_889 = x_899;
x_890 = x_924;
x_891 = x_931;
x_892 = x_936;
x_893 = x_940;
goto block_897;
}
else
{
lean_object* x_941; 
lean_dec(x_931);
lean_dec(x_927);
lean_dec(x_19);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_941 = lean_ctor_get(x_937, 0);
lean_inc(x_941);
lean_dec_ref(x_937);
x_526 = x_899;
x_527 = x_924;
x_528 = x_941;
goto block_530;
}
}
}
else
{
uint8_t x_942; 
x_942 = lean_unbox(x_930);
lean_dec(x_930);
x_816 = x_927;
x_817 = x_933;
x_818 = x_932;
x_819 = x_899;
x_820 = x_924;
x_821 = x_931;
x_822 = x_942;
x_823 = x_901;
goto block_840;
}
}
else
{
uint8_t x_943; 
x_943 = lean_unbox(x_930);
lean_dec(x_930);
x_816 = x_927;
x_817 = x_933;
x_818 = x_932;
x_819 = x_899;
x_820 = x_924;
x_821 = x_931;
x_822 = x_943;
x_823 = x_901;
goto block_840;
}
}
else
{
lean_object* x_944; 
lean_dec(x_928);
lean_dec(x_927);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_944 = lean_ctor_get(x_929, 0);
lean_inc(x_944);
lean_dec_ref(x_929);
x_526 = x_899;
x_527 = x_924;
x_528 = x_944;
goto block_530;
}
}
else
{
lean_object* x_945; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_945 = lean_ctor_get(x_925, 0);
lean_inc(x_945);
lean_dec_ref(x_925);
x_526 = x_899;
x_527 = x_924;
x_528 = x_945;
goto block_530;
}
}
}
else
{
lean_object* x_946; lean_object* x_947; uint8_t x_948; uint8_t x_953; 
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_946 = lean_ctor_get(x_898, 0);
x_953 = !lean_is_exclusive(x_898);
if (x_953 == 0)
{
x_947 = x_898;
x_948 = x_953;
goto block_952;
}
else
{
lean_inc(x_946);
lean_dec(x_898);
x_947 = lean_box(0);
x_948 = x_953;
goto block_952;
}
block_952:
{
lean_object* x_949; 
if (x_948 == 0)
{
x_949 = x_947;
goto block_950;
}
else
{
lean_object* x_951; 
x_951 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_951, 0, x_946);
x_949 = x_951;
goto block_950;
}
block_950:
{
return x_949;
}
}
}
}
}
else
{
lean_object* x_1249; lean_object* x_1250; uint8_t x_1251; uint8_t x_1256; 
lean_dec_ref(x_25);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1249 = lean_ctor_get(x_105, 0);
x_1256 = !lean_is_exclusive(x_105);
if (x_1256 == 0)
{
x_1250 = x_105;
x_1251 = x_1256;
goto block_1255;
}
else
{
lean_inc(x_1249);
lean_dec(x_105);
x_1250 = lean_box(0);
x_1251 = x_1256;
goto block_1255;
}
block_1255:
{
lean_object* x_1252; 
if (x_1251 == 0)
{
x_1252 = x_1250;
goto block_1253;
}
else
{
lean_object* x_1254; 
x_1254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1254, 0, x_1249);
x_1252 = x_1254;
goto block_1253;
}
block_1253:
{
return x_1252;
}
}
}
}
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; 
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
x_1257 = lean_ctor_get(x_1, 0);
lean_inc(x_1257);
x_1258 = lean_box(0);
x_1259 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1257, x_6, x_1258, x_7, x_8, x_9, x_10);
return x_1259;
}
}
}
else
{
lean_object* x_1262; lean_object* x_1263; uint8_t x_1264; uint8_t x_1269; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1262 = lean_ctor_get(x_16, 0);
x_1269 = !lean_is_exclusive(x_16);
if (x_1269 == 0)
{
x_1263 = x_16;
x_1264 = x_1269;
goto block_1268;
}
else
{
lean_inc(x_1262);
lean_dec(x_16);
x_1263 = lean_box(0);
x_1264 = x_1269;
goto block_1268;
}
block_1268:
{
lean_object* x_1265; 
if (x_1264 == 0)
{
x_1265 = x_1263;
goto block_1266;
}
else
{
lean_object* x_1267; 
x_1267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1267, 0, x_1262);
x_1265 = x_1267;
goto block_1266;
}
block_1266:
{
return x_1265;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1);
x_13 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_12, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_1, x_2, x_3, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_1, x_2, x_3, x_4, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_2);
x_12 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_mapM_loop___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Meta_Iterator_firstM___redArg(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_12 = lean_ctor_get(x_9, 0);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
x_13 = x_9;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Backtrack_backtrack___lam__0___boxed), 8, 1);
lean_closure_set(x_10, 0, x_3);
lean_inc_n(x_4, 2);
x_11 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_10, x_4, x_4, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Tactic_Backtrack_backtrack(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
res = runtime_initialize_Lean_Meta_Iterator(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_IndependentOf(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
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
res = initialize_Lean_Meta_Iterator(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_IndependentOf(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Backtrack(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Backtrack(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Backtrack(builtin);
}
#ifdef __cplusplus
}
#endif

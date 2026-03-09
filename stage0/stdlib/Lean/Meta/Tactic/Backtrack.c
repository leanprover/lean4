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
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " success!"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1;
lean_object* l_Lean_exceptEmoji___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = " discarding already assigned goal "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = " BacktrackConfig.proc failed: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " working on: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___boxed(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3;
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "failed: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", new: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3;
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "independent goals "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = " working on them before "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5;
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
static const lean_array_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_exceptEmoji___redArg(x_1);
x_8 = l_Lean_stringToMessageData(x_7);
x_9 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_exceptEmoji___redArg(x_2);
x_9 = l_Lean_stringToMessageData(x_8);
x_10 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__1);
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
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10___redArg(x_1, x_2);
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
x_7 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10___redArg(x_6, x_1);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_exceptEmoji___redArg(x_2);
x_9 = l_Lean_stringToMessageData(x_8);
x_10 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Exception_toMessageData(x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_22; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(x_8, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
x_11 = x_9;
x_12 = x_22;
goto block_21;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_exceptEmoji___redArg(x_2);
x_14 = l_Lean_stringToMessageData(x_13);
x_15 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_17);
x_18 = x_11;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4_spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4_spec__7(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_36 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4_spec__7(x_34, x_35, x_33);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_51; double x_82; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec_ref(x_8);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_dec(x_15);
x_36 = l_Lean_trace_profiler;
x_37 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_4, x_36);
if (x_37 == 0)
{
x_51 = x_37;
goto block_81;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = l_Lean_trace_profiler_useHeartbeats;
x_89 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_4, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; double x_92; double x_93; double x_94; 
x_90 = l_Lean_trace_profiler_threshold;
x_91 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(x_4, x_90);
x_92 = lean_float_of_nat(x_91);
x_93 = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3);
x_94 = lean_float_div(x_92, x_93);
x_82 = x_94;
goto block_87;
}
else
{
lean_object* x_95; lean_object* x_96; double x_97; 
x_95 = l_Lean_trace_profiler_threshold;
x_96 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(x_4, x_95);
x_97 = lean_float_of_nat(x_96);
x_82 = x_97;
goto block_87;
}
}
block_33:
{
lean_object* x_23; 
x_23 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(x_6, x_18, x_17, x_16, x_19, x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec_ref(x_23);
x_24 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(x_14);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_14);
x_25 = lean_ctor_get(x_23, 0);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
x_26 = x_23;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
block_45:
{
double x_40; lean_object* x_41; 
x_40 = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0);
lean_inc_ref(x_3);
lean_inc(x_1);
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_3);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_2);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_3);
lean_dec(x_1);
x_16 = x_39;
x_17 = x_38;
x_18 = x_41;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
goto block_33;
}
else
{
lean_object* x_42; double x_43; double x_44; 
lean_dec_ref(x_41);
x_42 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_3);
x_43 = lean_unbox_float(x_34);
lean_dec(x_34);
lean_ctor_set_float(x_42, sizeof(void*)*2, x_43);
x_44 = lean_unbox_float(x_35);
lean_dec(x_35);
lean_ctor_set_float(x_42, sizeof(void*)*2 + 8, x_44);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 16, x_2);
x_16 = x_39;
x_17 = x_38;
x_18 = x_42;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
goto block_33;
}
}
block_50:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_11, 5);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_14);
x_47 = lean_apply_6(x_7, x_14, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc(x_46);
x_38 = x_46;
x_39 = x_48;
goto block_45;
}
else
{
lean_object* x_49; 
lean_dec_ref(x_47);
x_49 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2);
lean_inc(x_46);
x_38 = x_46;
x_39 = x_49;
goto block_45;
}
}
block_81:
{
if (x_5 == 0)
{
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_80; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_52 = lean_st_ref_take(x_12);
x_53 = lean_ctor_get(x_52, 4);
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_ctor_get(x_52, 2);
x_57 = lean_ctor_get(x_52, 3);
x_58 = lean_ctor_get(x_52, 5);
x_59 = lean_ctor_get(x_52, 6);
x_60 = lean_ctor_get(x_52, 7);
x_61 = lean_ctor_get(x_52, 8);
x_80 = !lean_is_exclusive(x_52);
if (x_80 == 0)
{
x_62 = x_52;
x_63 = x_80;
goto block_79;
}
else
{
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_53);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_62 = lean_box(0);
x_63 = x_80;
goto block_79;
}
block_79:
{
uint64_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_78; 
x_64 = lean_ctor_get_uint64(x_53, sizeof(void*)*1);
x_65 = lean_ctor_get(x_53, 0);
x_78 = !lean_is_exclusive(x_53);
if (x_78 == 0)
{
x_66 = x_53;
x_67 = x_78;
goto block_77;
}
else
{
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_box(0);
x_67 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_PersistentArray_append___redArg(x_6, x_65);
lean_dec_ref(x_65);
if (x_67 == 0)
{
lean_ctor_set(x_66, 0, x_68);
x_69 = x_66;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set_uint64(x_76, sizeof(void*)*1, x_64);
x_69 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_70; 
if (x_63 == 0)
{
lean_ctor_set(x_62, 4, x_69);
x_70 = x_62;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_74, 0, x_54);
lean_ctor_set(x_74, 1, x_55);
lean_ctor_set(x_74, 2, x_56);
lean_ctor_set(x_74, 3, x_57);
lean_ctor_set(x_74, 4, x_69);
lean_ctor_set(x_74, 5, x_58);
lean_ctor_set(x_74, 6, x_59);
lean_ctor_set(x_74, 7, x_60);
lean_ctor_set(x_74, 8, x_61);
x_70 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_st_ref_set(x_12, x_70);
lean_dec(x_12);
x_72 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(x_14);
return x_72;
}
}
}
}
}
else
{
goto block_50;
}
}
else
{
goto block_50;
}
}
block_87:
{
double x_83; double x_84; double x_85; uint8_t x_86; 
x_83 = lean_unbox_float(x_35);
x_84 = lean_unbox_float(x_34);
x_85 = lean_float_sub(x_83, x_84);
x_86 = lean_float_decLt(x_82, x_85);
x_51 = x_86;
goto block_81;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_5);
x_16 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_16;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_241; uint8_t x_242; 
x_241 = lean_unsigned_to_nat(0u);
x_242 = lean_nat_dec_eq(x_5, x_241);
if (x_242 == 1)
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_243 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
x_244 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_243, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; uint8_t x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_464; lean_object* x_465; uint8_t x_466; lean_object* x_467; uint8_t x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; lean_object* x_489; uint8_t x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; lean_object* x_502; lean_object* x_503; lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; uint8_t x_528; lean_object* x_529; lean_object* x_530; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; uint8_t x_544; lean_object* x_545; uint8_t x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; uint8_t x_552; lean_object* x_553; lean_object* x_554; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; uint8_t x_572; uint8_t x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; uint8_t x_580; lean_object* x_581; lean_object* x_582; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_633; lean_object* x_634; uint8_t x_635; lean_object* x_636; lean_object* x_637; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_660; lean_object* x_661; uint8_t x_662; lean_object* x_663; lean_object* x_664; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; uint8_t x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; lean_object* x_685; uint8_t x_686; lean_object* x_687; lean_object* x_688; lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; uint8_t x_711; lean_object* x_712; uint8_t x_713; lean_object* x_714; lean_object* x_715; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; uint8_t x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; uint8_t x_737; lean_object* x_738; uint8_t x_739; lean_object* x_740; lean_object* x_781; lean_object* x_782; lean_object* x_783; uint8_t x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; uint8_t x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_804; lean_object* x_805; lean_object* x_806; uint8_t x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; uint8_t x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; uint8_t x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; uint8_t x_832; lean_object* x_833; lean_object* x_834; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; uint8_t x_882; uint8_t x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; uint8_t x_902; uint8_t x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; uint8_t x_926; lean_object* x_927; uint8_t x_928; lean_object* x_929; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; uint8_t x_946; lean_object* x_947; uint8_t x_948; lean_object* x_949; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; uint8_t x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; uint8_t x_972; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; uint8_t x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; uint8_t x_1023; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; uint8_t x_1066; uint8_t x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; uint8_t x_1071; lean_object* x_1072; uint8_t x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; uint8_t x_1121; uint8_t x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; uint8_t x_1130; lean_object* x_1131; uint8_t x_1132; lean_object* x_1157; uint8_t x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; uint8_t x_1162; uint8_t x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; uint8_t x_1169; lean_object* x_1170; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; uint8_t x_1215; uint8_t x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; uint8_t x_1225; lean_object* x_1226; uint8_t x_1227; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; uint8_t x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; uint8_t x_1265; lean_object* x_1266; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; uint8_t x_1318; uint8_t x_1319; lean_object* x_1320; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; uint8_t x_1368; lean_object* x_1369; lean_object* x_1370; uint8_t x_1371; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; uint8_t x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1510; lean_object* x_1521; 
x_245 = lean_ctor_get(x_1, 1);
x_246 = lean_ctor_get(x_1, 2);
x_247 = lean_ctor_get(x_1, 3);
x_248 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
x_356 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
x_464 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
x_1014 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
x_1060 = lean_unsigned_to_nat(1u);
x_1061 = lean_nat_sub(x_5, x_1060);
lean_dec(x_5);
lean_inc_ref(x_245);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_1521 = lean_apply_7(x_245, x_4, x_6, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1521) == 0)
{
lean_object* x_1522; 
x_1522 = lean_ctor_get(x_1521, 0);
lean_inc(x_1522);
lean_dec_ref(x_1521);
x_1451 = x_1522;
x_1452 = x_8;
x_1453 = x_9;
x_1454 = x_10;
x_1455 = x_11;
goto block_1509;
}
else
{
lean_object* x_1523; lean_object* x_1524; uint8_t x_1525; uint8_t x_1595; 
x_1523 = lean_ctor_get(x_1521, 0);
x_1595 = !lean_is_exclusive(x_1521);
if (x_1595 == 0)
{
x_1524 = x_1521;
x_1525 = x_1595;
goto block_1594;
}
else
{
lean_inc(x_1523);
lean_dec(x_1521);
x_1524 = lean_box(0);
x_1525 = x_1595;
goto block_1594;
}
block_1594:
{
lean_object* x_1526; uint8_t x_1527; uint8_t x_1528; lean_object* x_1529; lean_object* x_1530; uint8_t x_1567; uint8_t x_1592; 
lean_inc(x_1523);
x_1526 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(x_1526, 0, x_1523);
x_1592 = l_Lean_Exception_isInterrupt(x_1523);
if (x_1592 == 0)
{
uint8_t x_1593; 
lean_inc(x_1523);
x_1593 = l_Lean_Exception_isRuntime(x_1523);
x_1567 = x_1593;
goto block_1591;
}
else
{
x_1567 = x_1592;
goto block_1591;
}
block_1566:
{
lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; uint8_t x_1534; uint8_t x_1565; 
x_1531 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
x_1532 = lean_ctor_get(x_1531, 0);
x_1565 = !lean_is_exclusive(x_1531);
if (x_1565 == 0)
{
x_1533 = x_1531;
x_1534 = x_1565;
goto block_1564;
}
else
{
lean_inc(x_1532);
lean_dec(x_1531);
x_1533 = lean_box(0);
x_1534 = x_1565;
goto block_1564;
}
block_1564:
{
lean_object* x_1535; uint8_t x_1536; 
x_1535 = l_Lean_trace_profiler_useHeartbeats;
x_1536 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1529, x_1535);
if (x_1536 == 0)
{
lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; 
x_1537 = lean_io_mono_nanos_now();
x_1538 = lean_io_mono_nanos_now();
if (x_1534 == 0)
{
lean_ctor_set(x_1533, 0, x_1523);
x_1539 = x_1533;
goto block_1550;
}
else
{
lean_object* x_1551; 
x_1551 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1551, 0, x_1523);
x_1539 = x_1551;
goto block_1550;
}
block_1550:
{
double x_1540; double x_1541; double x_1542; double x_1543; double x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; 
x_1540 = lean_float_of_nat(x_1537);
x_1541 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_1542 = lean_float_div(x_1540, x_1541);
x_1543 = lean_float_of_nat(x_1538);
x_1544 = lean_float_div(x_1543, x_1541);
x_1545 = lean_box_float(x_1542);
x_1546 = lean_box_float(x_1544);
x_1547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1547, 0, x_1545);
lean_ctor_set(x_1547, 1, x_1546);
x_1548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1548, 0, x_1539);
lean_ctor_set(x_1548, 1, x_1547);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1549 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1528, x_1530, x_1529, x_1527, x_1532, x_1526, x_1548, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1529);
x_1510 = x_1549;
goto block_1520;
}
}
else
{
lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; 
x_1552 = lean_io_get_num_heartbeats();
x_1553 = lean_io_get_num_heartbeats();
if (x_1534 == 0)
{
lean_ctor_set(x_1533, 0, x_1523);
x_1554 = x_1533;
goto block_1562;
}
else
{
lean_object* x_1563; 
x_1563 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1563, 0, x_1523);
x_1554 = x_1563;
goto block_1562;
}
block_1562:
{
double x_1555; double x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; 
x_1555 = lean_float_of_nat(x_1552);
x_1556 = lean_float_of_nat(x_1553);
x_1557 = lean_box_float(x_1555);
x_1558 = lean_box_float(x_1556);
x_1559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1559, 0, x_1557);
lean_ctor_set(x_1559, 1, x_1558);
x_1560 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1560, 0, x_1554);
lean_ctor_set(x_1560, 1, x_1559);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1561 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1528, x_1530, x_1529, x_1527, x_1532, x_1526, x_1560, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1529);
x_1510 = x_1561;
goto block_1520;
}
}
}
}
block_1591:
{
if (x_1567 == 0)
{
lean_object* x_1568; uint8_t x_1569; 
x_1568 = lean_ctor_get(x_10, 2);
x_1569 = lean_ctor_get_uint8(x_1568, sizeof(void*)*1);
if (x_1569 == 0)
{
lean_object* x_1570; 
lean_dec_ref(x_1526);
lean_dec(x_1061);
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
if (x_1525 == 0)
{
x_1570 = x_1524;
goto block_1571;
}
else
{
lean_object* x_1572; 
x_1572 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1572, 0, x_1523);
x_1570 = x_1572;
goto block_1571;
}
block_1571:
{
return x_1570;
}
}
else
{
lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; uint8_t x_1576; uint8_t x_1587; 
lean_del_object(x_1524);
lean_inc(x_2);
x_1573 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1574 = lean_ctor_get(x_1573, 0);
x_1587 = !lean_is_exclusive(x_1573);
if (x_1587 == 0)
{
x_1575 = x_1573;
x_1576 = x_1587;
goto block_1586;
}
else
{
lean_inc(x_1574);
lean_dec(x_1573);
x_1575 = lean_box(0);
x_1576 = x_1587;
goto block_1586;
}
block_1586:
{
lean_object* x_1577; uint8_t x_1578; 
x_1577 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1578 = lean_unbox(x_1574);
if (x_1578 == 0)
{
lean_object* x_1579; uint8_t x_1580; 
x_1579 = l_Lean_trace_profiler;
x_1580 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1568, x_1579);
if (x_1580 == 0)
{
lean_object* x_1581; 
lean_dec(x_1574);
lean_dec_ref(x_1526);
lean_dec(x_1061);
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
if (x_1576 == 0)
{
lean_ctor_set_tag(x_1575, 1);
lean_ctor_set(x_1575, 0, x_1523);
x_1581 = x_1575;
goto block_1582;
}
else
{
lean_object* x_1583; 
x_1583 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1583, 0, x_1523);
x_1581 = x_1583;
goto block_1582;
}
block_1582:
{
return x_1581;
}
}
else
{
uint8_t x_1584; 
lean_del_object(x_1575);
x_1584 = lean_unbox(x_1574);
lean_dec(x_1574);
lean_inc_ref(x_1568);
x_1527 = x_1584;
x_1528 = x_1569;
x_1529 = x_1568;
x_1530 = x_1577;
goto block_1566;
}
}
else
{
uint8_t x_1585; 
lean_del_object(x_1575);
x_1585 = lean_unbox(x_1574);
lean_dec(x_1574);
lean_inc_ref(x_1568);
x_1527 = x_1585;
x_1528 = x_1569;
x_1529 = x_1568;
x_1530 = x_1577;
goto block_1566;
}
}
}
}
else
{
lean_object* x_1588; 
lean_dec_ref(x_1526);
lean_dec(x_1061);
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
if (x_1525 == 0)
{
x_1588 = x_1524;
goto block_1589;
}
else
{
lean_object* x_1590; 
x_1590 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1590, 0, x_1523);
x_1588 = x_1590;
goto block_1589;
}
block_1589:
{
return x_1588;
}
}
}
}
}
block_275:
{
lean_object* x_264; double x_265; double x_266; double x_267; double x_268; double x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_264 = lean_io_mono_nanos_now();
x_265 = lean_float_of_nat(x_259);
x_266 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_267 = lean_float_div(x_265, x_266);
x_268 = lean_float_of_nat(x_264);
x_269 = lean_float_div(x_268, x_266);
x_270 = lean_box_float(x_267);
x_271 = lean_box_float(x_269);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_263);
lean_ctor_set(x_273, 1, x_272);
lean_inc(x_255);
lean_inc_ref(x_256);
lean_inc(x_260);
lean_inc_ref(x_254);
lean_inc_ref(x_257);
lean_inc(x_2);
x_274 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_253, x_257, x_251, x_258, x_252, x_248, x_273, x_254, x_260, x_256, x_255);
x_159 = x_255;
x_160 = x_256;
x_161 = x_257;
x_162 = x_249;
x_163 = x_250;
x_164 = x_251;
x_165 = x_254;
x_166 = x_253;
x_167 = x_260;
x_168 = x_261;
x_169 = x_262;
x_170 = x_274;
goto block_173;
}
block_299:
{
lean_object* x_291; double x_292; double x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_291 = lean_io_get_num_heartbeats();
x_292 = lean_float_of_nat(x_280);
x_293 = lean_float_of_nat(x_291);
x_294 = lean_box_float(x_292);
x_295 = lean_box_float(x_293);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_290);
lean_ctor_set(x_297, 1, x_296);
lean_inc(x_283);
lean_inc_ref(x_284);
lean_inc(x_287);
lean_inc_ref(x_282);
lean_inc_ref(x_285);
lean_inc(x_2);
x_298 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_281, x_285, x_278, x_286, x_279, x_248, x_297, x_282, x_287, x_284, x_283);
x_159 = x_283;
x_160 = x_284;
x_161 = x_285;
x_162 = x_276;
x_163 = x_277;
x_164 = x_278;
x_165 = x_282;
x_166 = x_281;
x_167 = x_287;
x_168 = x_288;
x_169 = x_289;
x_170 = x_298;
goto block_173;
}
block_355:
{
lean_object* x_316; 
x_316 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_307);
if (x_304 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
lean_dec_ref(x_316);
x_318 = lean_io_mono_nanos_now();
lean_inc(x_307);
lean_inc_ref(x_308);
lean_inc(x_313);
lean_inc_ref(x_303);
lean_inc(x_2);
x_319 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_306, x_310, x_311, x_303, x_313, x_308, x_307);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; uint8_t x_322; uint8_t x_327; 
x_320 = lean_ctor_get(x_319, 0);
x_327 = !lean_is_exclusive(x_319);
if (x_327 == 0)
{
x_321 = x_319;
x_322 = x_327;
goto block_326;
}
else
{
lean_inc(x_320);
lean_dec(x_319);
x_321 = lean_box(0);
x_322 = x_327;
goto block_326;
}
block_326:
{
lean_object* x_323; 
if (x_322 == 0)
{
lean_ctor_set_tag(x_321, 1);
x_323 = x_321;
goto block_324;
}
else
{
lean_object* x_325; 
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_320);
x_323 = x_325;
goto block_324;
}
block_324:
{
x_249 = x_300;
x_250 = x_301;
x_251 = x_302;
x_252 = x_317;
x_253 = x_305;
x_254 = x_303;
x_255 = x_307;
x_256 = x_308;
x_257 = x_309;
x_258 = x_312;
x_259 = x_318;
x_260 = x_313;
x_261 = x_314;
x_262 = x_315;
x_263 = x_323;
goto block_275;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_335; 
x_328 = lean_ctor_get(x_319, 0);
x_335 = !lean_is_exclusive(x_319);
if (x_335 == 0)
{
x_329 = x_319;
x_330 = x_335;
goto block_334;
}
else
{
lean_inc(x_328);
lean_dec(x_319);
x_329 = lean_box(0);
x_330 = x_335;
goto block_334;
}
block_334:
{
lean_object* x_331; 
if (x_330 == 0)
{
lean_ctor_set_tag(x_329, 0);
x_331 = x_329;
goto block_332;
}
else
{
lean_object* x_333; 
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_328);
x_331 = x_333;
goto block_332;
}
block_332:
{
x_249 = x_300;
x_250 = x_301;
x_251 = x_302;
x_252 = x_317;
x_253 = x_305;
x_254 = x_303;
x_255 = x_307;
x_256 = x_308;
x_257 = x_309;
x_258 = x_312;
x_259 = x_318;
x_260 = x_313;
x_261 = x_314;
x_262 = x_315;
x_263 = x_331;
goto block_275;
}
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_316, 0);
lean_inc(x_336);
lean_dec_ref(x_316);
x_337 = lean_io_get_num_heartbeats();
lean_inc(x_307);
lean_inc_ref(x_308);
lean_inc(x_313);
lean_inc_ref(x_303);
lean_inc(x_2);
x_338 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_306, x_310, x_311, x_303, x_313, x_308, x_307);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; uint8_t x_341; uint8_t x_346; 
x_339 = lean_ctor_get(x_338, 0);
x_346 = !lean_is_exclusive(x_338);
if (x_346 == 0)
{
x_340 = x_338;
x_341 = x_346;
goto block_345;
}
else
{
lean_inc(x_339);
lean_dec(x_338);
x_340 = lean_box(0);
x_341 = x_346;
goto block_345;
}
block_345:
{
lean_object* x_342; 
if (x_341 == 0)
{
lean_ctor_set_tag(x_340, 1);
x_342 = x_340;
goto block_343;
}
else
{
lean_object* x_344; 
x_344 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_344, 0, x_339);
x_342 = x_344;
goto block_343;
}
block_343:
{
x_276 = x_300;
x_277 = x_301;
x_278 = x_302;
x_279 = x_336;
x_280 = x_337;
x_281 = x_305;
x_282 = x_303;
x_283 = x_307;
x_284 = x_308;
x_285 = x_309;
x_286 = x_312;
x_287 = x_313;
x_288 = x_314;
x_289 = x_315;
x_290 = x_342;
goto block_299;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_354; 
x_347 = lean_ctor_get(x_338, 0);
x_354 = !lean_is_exclusive(x_338);
if (x_354 == 0)
{
x_348 = x_338;
x_349 = x_354;
goto block_353;
}
else
{
lean_inc(x_347);
lean_dec(x_338);
x_348 = lean_box(0);
x_349 = x_354;
goto block_353;
}
block_353:
{
lean_object* x_350; 
if (x_349 == 0)
{
lean_ctor_set_tag(x_348, 0);
x_350 = x_348;
goto block_351;
}
else
{
lean_object* x_352; 
x_352 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_352, 0, x_347);
x_350 = x_352;
goto block_351;
}
block_351:
{
x_276 = x_300;
x_277 = x_301;
x_278 = x_302;
x_279 = x_336;
x_280 = x_337;
x_281 = x_305;
x_282 = x_303;
x_283 = x_307;
x_284 = x_308;
x_285 = x_309;
x_286 = x_312;
x_287 = x_313;
x_288 = x_314;
x_289 = x_315;
x_290 = x_350;
goto block_299;
}
}
}
}
}
block_383:
{
lean_object* x_372; double x_373; double x_374; double x_375; double x_376; double x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_372 = lean_io_mono_nanos_now();
x_373 = lean_float_of_nat(x_357);
x_374 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_375 = lean_float_div(x_373, x_374);
x_376 = lean_float_of_nat(x_372);
x_377 = lean_float_div(x_376, x_374);
x_378 = lean_box_float(x_375);
x_379 = lean_box_float(x_377);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_371);
lean_ctor_set(x_381, 1, x_380);
lean_inc(x_363);
lean_inc_ref(x_364);
lean_inc(x_368);
lean_inc_ref(x_362);
lean_inc_ref(x_365);
lean_inc(x_2);
x_382 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_361, x_365, x_360, x_358, x_366, x_356, x_381, x_362, x_368, x_364, x_363);
x_226 = x_363;
x_227 = x_364;
x_228 = x_365;
x_229 = x_359;
x_230 = x_367;
x_231 = x_360;
x_232 = x_362;
x_233 = x_361;
x_234 = x_368;
x_235 = x_369;
x_236 = x_370;
x_237 = x_382;
goto block_240;
}
block_407:
{
lean_object* x_399; double x_400; double x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_399 = lean_io_get_num_heartbeats();
x_400 = lean_float_of_nat(x_386);
x_401 = lean_float_of_nat(x_399);
x_402 = lean_box_float(x_400);
x_403 = lean_box_float(x_401);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_398);
lean_ctor_set(x_405, 1, x_404);
lean_inc(x_390);
lean_inc_ref(x_391);
lean_inc(x_395);
lean_inc_ref(x_389);
lean_inc_ref(x_392);
lean_inc(x_2);
x_406 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_388, x_392, x_387, x_384, x_393, x_356, x_405, x_389, x_395, x_391, x_390);
x_226 = x_390;
x_227 = x_391;
x_228 = x_392;
x_229 = x_385;
x_230 = x_394;
x_231 = x_387;
x_232 = x_389;
x_233 = x_388;
x_234 = x_395;
x_235 = x_396;
x_236 = x_397;
x_237 = x_406;
goto block_240;
}
block_463:
{
lean_object* x_424; 
x_424 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_415);
if (x_413 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
lean_dec_ref(x_424);
x_426 = lean_io_mono_nanos_now();
lean_inc(x_415);
lean_inc_ref(x_417);
lean_inc(x_421);
lean_inc_ref(x_412);
lean_inc(x_2);
x_427 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_410, x_419, x_416, x_412, x_421, x_417, x_415);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; uint8_t x_430; uint8_t x_435; 
x_428 = lean_ctor_get(x_427, 0);
x_435 = !lean_is_exclusive(x_427);
if (x_435 == 0)
{
x_429 = x_427;
x_430 = x_435;
goto block_434;
}
else
{
lean_inc(x_428);
lean_dec(x_427);
x_429 = lean_box(0);
x_430 = x_435;
goto block_434;
}
block_434:
{
lean_object* x_431; 
if (x_430 == 0)
{
lean_ctor_set_tag(x_429, 1);
x_431 = x_429;
goto block_432;
}
else
{
lean_object* x_433; 
x_433 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_433, 0, x_428);
x_431 = x_433;
goto block_432;
}
block_432:
{
x_357 = x_426;
x_358 = x_408;
x_359 = x_409;
x_360 = x_411;
x_361 = x_414;
x_362 = x_412;
x_363 = x_415;
x_364 = x_417;
x_365 = x_418;
x_366 = x_425;
x_367 = x_420;
x_368 = x_421;
x_369 = x_422;
x_370 = x_423;
x_371 = x_431;
goto block_383;
}
}
}
else
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; uint8_t x_443; 
x_436 = lean_ctor_get(x_427, 0);
x_443 = !lean_is_exclusive(x_427);
if (x_443 == 0)
{
x_437 = x_427;
x_438 = x_443;
goto block_442;
}
else
{
lean_inc(x_436);
lean_dec(x_427);
x_437 = lean_box(0);
x_438 = x_443;
goto block_442;
}
block_442:
{
lean_object* x_439; 
if (x_438 == 0)
{
lean_ctor_set_tag(x_437, 0);
x_439 = x_437;
goto block_440;
}
else
{
lean_object* x_441; 
x_441 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_441, 0, x_436);
x_439 = x_441;
goto block_440;
}
block_440:
{
x_357 = x_426;
x_358 = x_408;
x_359 = x_409;
x_360 = x_411;
x_361 = x_414;
x_362 = x_412;
x_363 = x_415;
x_364 = x_417;
x_365 = x_418;
x_366 = x_425;
x_367 = x_420;
x_368 = x_421;
x_369 = x_422;
x_370 = x_423;
x_371 = x_439;
goto block_383;
}
}
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_424, 0);
lean_inc(x_444);
lean_dec_ref(x_424);
x_445 = lean_io_get_num_heartbeats();
lean_inc(x_415);
lean_inc_ref(x_417);
lean_inc(x_421);
lean_inc_ref(x_412);
lean_inc(x_2);
x_446 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_410, x_419, x_416, x_412, x_421, x_417, x_415);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; uint8_t x_449; uint8_t x_454; 
x_447 = lean_ctor_get(x_446, 0);
x_454 = !lean_is_exclusive(x_446);
if (x_454 == 0)
{
x_448 = x_446;
x_449 = x_454;
goto block_453;
}
else
{
lean_inc(x_447);
lean_dec(x_446);
x_448 = lean_box(0);
x_449 = x_454;
goto block_453;
}
block_453:
{
lean_object* x_450; 
if (x_449 == 0)
{
lean_ctor_set_tag(x_448, 1);
x_450 = x_448;
goto block_451;
}
else
{
lean_object* x_452; 
x_452 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_452, 0, x_447);
x_450 = x_452;
goto block_451;
}
block_451:
{
x_384 = x_408;
x_385 = x_409;
x_386 = x_445;
x_387 = x_411;
x_388 = x_414;
x_389 = x_412;
x_390 = x_415;
x_391 = x_417;
x_392 = x_418;
x_393 = x_444;
x_394 = x_420;
x_395 = x_421;
x_396 = x_422;
x_397 = x_423;
x_398 = x_450;
goto block_407;
}
}
}
else
{
lean_object* x_455; lean_object* x_456; uint8_t x_457; uint8_t x_462; 
x_455 = lean_ctor_get(x_446, 0);
x_462 = !lean_is_exclusive(x_446);
if (x_462 == 0)
{
x_456 = x_446;
x_457 = x_462;
goto block_461;
}
else
{
lean_inc(x_455);
lean_dec(x_446);
x_456 = lean_box(0);
x_457 = x_462;
goto block_461;
}
block_461:
{
lean_object* x_458; 
if (x_457 == 0)
{
lean_ctor_set_tag(x_456, 0);
x_458 = x_456;
goto block_459;
}
else
{
lean_object* x_460; 
x_460 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_460, 0, x_455);
x_458 = x_460;
goto block_459;
}
block_459:
{
x_384 = x_408;
x_385 = x_409;
x_386 = x_445;
x_387 = x_411;
x_388 = x_414;
x_389 = x_412;
x_390 = x_415;
x_391 = x_417;
x_392 = x_418;
x_393 = x_444;
x_394 = x_420;
x_395 = x_421;
x_396 = x_422;
x_397 = x_423;
x_398 = x_458;
goto block_407;
}
}
}
}
}
block_488:
{
lean_object* x_480; double x_481; double x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_480 = lean_io_get_num_heartbeats();
x_481 = lean_float_of_nat(x_470);
x_482 = lean_float_of_nat(x_480);
x_483 = lean_box_float(x_481);
x_484 = lean_box_float(x_482);
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_479);
lean_ctor_set(x_486, 1, x_485);
lean_inc(x_472);
lean_inc_ref(x_473);
lean_inc(x_476);
lean_inc_ref(x_469);
lean_inc_ref(x_474);
lean_inc(x_2);
x_487 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_468, x_474, x_467, x_466, x_471, x_464, x_486, x_469, x_476, x_473, x_472);
x_226 = x_472;
x_227 = x_473;
x_228 = x_474;
x_229 = x_465;
x_230 = x_475;
x_231 = x_467;
x_232 = x_469;
x_233 = x_468;
x_234 = x_476;
x_235 = x_477;
x_236 = x_478;
x_237 = x_487;
goto block_240;
}
block_515:
{
lean_object* x_504; double x_505; double x_506; double x_507; double x_508; double x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_504 = lean_io_mono_nanos_now();
x_505 = lean_float_of_nat(x_491);
x_506 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_507 = lean_float_div(x_505, x_506);
x_508 = lean_float_of_nat(x_504);
x_509 = lean_float_div(x_508, x_506);
x_510 = lean_box_float(x_507);
x_511 = lean_box_float(x_509);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_503);
lean_ctor_set(x_513, 1, x_512);
lean_inc(x_496);
lean_inc_ref(x_497);
lean_inc(x_500);
lean_inc_ref(x_494);
lean_inc_ref(x_498);
lean_inc(x_2);
x_514 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_493, x_498, x_492, x_490, x_495, x_464, x_513, x_494, x_500, x_497, x_496);
x_226 = x_496;
x_227 = x_497;
x_228 = x_498;
x_229 = x_489;
x_230 = x_499;
x_231 = x_492;
x_232 = x_494;
x_233 = x_493;
x_234 = x_500;
x_235 = x_501;
x_236 = x_502;
x_237 = x_514;
goto block_240;
}
block_539:
{
lean_object* x_531; double x_532; double x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_531 = lean_io_get_num_heartbeats();
x_532 = lean_float_of_nat(x_521);
x_533 = lean_float_of_nat(x_531);
x_534 = lean_box_float(x_532);
x_535 = lean_box_float(x_533);
x_536 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_535);
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_530);
lean_ctor_set(x_537, 1, x_536);
lean_inc(x_523);
lean_inc_ref(x_524);
lean_inc(x_527);
lean_inc_ref(x_520);
lean_inc_ref(x_525);
lean_inc(x_2);
x_538 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_519, x_525, x_518, x_522, x_516, x_248, x_537, x_520, x_527, x_524, x_523);
x_226 = x_523;
x_227 = x_524;
x_228 = x_525;
x_229 = x_517;
x_230 = x_526;
x_231 = x_518;
x_232 = x_520;
x_233 = x_519;
x_234 = x_527;
x_235 = x_528;
x_236 = x_529;
x_237 = x_538;
goto block_240;
}
block_566:
{
lean_object* x_555; double x_556; double x_557; double x_558; double x_559; double x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_555 = lean_io_mono_nanos_now();
x_556 = lean_float_of_nat(x_541);
x_557 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_558 = lean_float_div(x_556, x_557);
x_559 = lean_float_of_nat(x_555);
x_560 = lean_float_div(x_559, x_557);
x_561 = lean_box_float(x_558);
x_562 = lean_box_float(x_560);
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
x_564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_564, 0, x_554);
lean_ctor_set(x_564, 1, x_563);
lean_inc(x_547);
lean_inc_ref(x_548);
lean_inc(x_551);
lean_inc_ref(x_545);
lean_inc_ref(x_549);
lean_inc(x_2);
x_565 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_544, x_549, x_543, x_546, x_540, x_248, x_564, x_545, x_551, x_548, x_547);
x_226 = x_547;
x_227 = x_548;
x_228 = x_549;
x_229 = x_542;
x_230 = x_550;
x_231 = x_543;
x_232 = x_545;
x_233 = x_544;
x_234 = x_551;
x_235 = x_552;
x_236 = x_553;
x_237 = x_565;
goto block_240;
}
block_622:
{
lean_object* x_583; 
x_583 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_574);
if (x_571 == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
lean_dec_ref(x_583);
x_585 = lean_io_mono_nanos_now();
lean_inc(x_574);
lean_inc_ref(x_575);
lean_inc(x_579);
lean_inc_ref(x_570);
lean_inc(x_2);
x_586 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_581, x_577, x_567, x_570, x_579, x_575, x_574);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; uint8_t x_589; uint8_t x_594; 
x_587 = lean_ctor_get(x_586, 0);
x_594 = !lean_is_exclusive(x_586);
if (x_594 == 0)
{
x_588 = x_586;
x_589 = x_594;
goto block_593;
}
else
{
lean_inc(x_587);
lean_dec(x_586);
x_588 = lean_box(0);
x_589 = x_594;
goto block_593;
}
block_593:
{
lean_object* x_590; 
if (x_589 == 0)
{
lean_ctor_set_tag(x_588, 1);
x_590 = x_588;
goto block_591;
}
else
{
lean_object* x_592; 
x_592 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_592, 0, x_587);
x_590 = x_592;
goto block_591;
}
block_591:
{
x_540 = x_584;
x_541 = x_585;
x_542 = x_568;
x_543 = x_569;
x_544 = x_572;
x_545 = x_570;
x_546 = x_573;
x_547 = x_574;
x_548 = x_575;
x_549 = x_576;
x_550 = x_578;
x_551 = x_579;
x_552 = x_580;
x_553 = x_582;
x_554 = x_590;
goto block_566;
}
}
}
else
{
lean_object* x_595; lean_object* x_596; uint8_t x_597; uint8_t x_602; 
x_595 = lean_ctor_get(x_586, 0);
x_602 = !lean_is_exclusive(x_586);
if (x_602 == 0)
{
x_596 = x_586;
x_597 = x_602;
goto block_601;
}
else
{
lean_inc(x_595);
lean_dec(x_586);
x_596 = lean_box(0);
x_597 = x_602;
goto block_601;
}
block_601:
{
lean_object* x_598; 
if (x_597 == 0)
{
lean_ctor_set_tag(x_596, 0);
x_598 = x_596;
goto block_599;
}
else
{
lean_object* x_600; 
x_600 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_600, 0, x_595);
x_598 = x_600;
goto block_599;
}
block_599:
{
x_540 = x_584;
x_541 = x_585;
x_542 = x_568;
x_543 = x_569;
x_544 = x_572;
x_545 = x_570;
x_546 = x_573;
x_547 = x_574;
x_548 = x_575;
x_549 = x_576;
x_550 = x_578;
x_551 = x_579;
x_552 = x_580;
x_553 = x_582;
x_554 = x_598;
goto block_566;
}
}
}
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_583, 0);
lean_inc(x_603);
lean_dec_ref(x_583);
x_604 = lean_io_get_num_heartbeats();
lean_inc(x_574);
lean_inc_ref(x_575);
lean_inc(x_579);
lean_inc_ref(x_570);
lean_inc(x_2);
x_605 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_581, x_577, x_567, x_570, x_579, x_575, x_574);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; uint8_t x_608; uint8_t x_613; 
x_606 = lean_ctor_get(x_605, 0);
x_613 = !lean_is_exclusive(x_605);
if (x_613 == 0)
{
x_607 = x_605;
x_608 = x_613;
goto block_612;
}
else
{
lean_inc(x_606);
lean_dec(x_605);
x_607 = lean_box(0);
x_608 = x_613;
goto block_612;
}
block_612:
{
lean_object* x_609; 
if (x_608 == 0)
{
lean_ctor_set_tag(x_607, 1);
x_609 = x_607;
goto block_610;
}
else
{
lean_object* x_611; 
x_611 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_611, 0, x_606);
x_609 = x_611;
goto block_610;
}
block_610:
{
x_516 = x_603;
x_517 = x_568;
x_518 = x_569;
x_519 = x_572;
x_520 = x_570;
x_521 = x_604;
x_522 = x_573;
x_523 = x_574;
x_524 = x_575;
x_525 = x_576;
x_526 = x_578;
x_527 = x_579;
x_528 = x_580;
x_529 = x_582;
x_530 = x_609;
goto block_539;
}
}
}
else
{
lean_object* x_614; lean_object* x_615; uint8_t x_616; uint8_t x_621; 
x_614 = lean_ctor_get(x_605, 0);
x_621 = !lean_is_exclusive(x_605);
if (x_621 == 0)
{
x_615 = x_605;
x_616 = x_621;
goto block_620;
}
else
{
lean_inc(x_614);
lean_dec(x_605);
x_615 = lean_box(0);
x_616 = x_621;
goto block_620;
}
block_620:
{
lean_object* x_617; 
if (x_616 == 0)
{
lean_ctor_set_tag(x_615, 0);
x_617 = x_615;
goto block_618;
}
else
{
lean_object* x_619; 
x_619 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_619, 0, x_614);
x_617 = x_619;
goto block_618;
}
block_618:
{
x_516 = x_603;
x_517 = x_568;
x_518 = x_569;
x_519 = x_572;
x_520 = x_570;
x_521 = x_604;
x_522 = x_573;
x_523 = x_574;
x_524 = x_575;
x_525 = x_576;
x_526 = x_578;
x_527 = x_579;
x_528 = x_580;
x_529 = x_582;
x_530 = x_617;
goto block_539;
}
}
}
}
}
block_649:
{
lean_object* x_638; double x_639; double x_640; double x_641; double x_642; double x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_638 = lean_io_mono_nanos_now();
x_639 = lean_float_of_nat(x_629);
x_640 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_641 = lean_float_div(x_639, x_640);
x_642 = lean_float_of_nat(x_638);
x_643 = lean_float_div(x_642, x_640);
x_644 = lean_box_float(x_641);
x_645 = lean_box_float(x_643);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_644);
lean_ctor_set(x_646, 1, x_645);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_637);
lean_ctor_set(x_647, 1, x_646);
lean_inc(x_630);
lean_inc_ref(x_631);
lean_inc(x_634);
lean_inc_ref(x_628);
lean_inc_ref(x_632);
lean_inc(x_2);
x_648 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_627, x_632, x_626, x_633, x_623, x_464, x_647, x_628, x_634, x_631, x_630);
x_159 = x_630;
x_160 = x_631;
x_161 = x_632;
x_162 = x_624;
x_163 = x_625;
x_164 = x_626;
x_165 = x_628;
x_166 = x_627;
x_167 = x_634;
x_168 = x_635;
x_169 = x_636;
x_170 = x_648;
goto block_173;
}
block_673:
{
lean_object* x_665; double x_666; double x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_665 = lean_io_get_num_heartbeats();
x_666 = lean_float_of_nat(x_654);
x_667 = lean_float_of_nat(x_665);
x_668 = lean_box_float(x_666);
x_669 = lean_box_float(x_667);
x_670 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_670, 0, x_668);
lean_ctor_set(x_670, 1, x_669);
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_664);
lean_ctor_set(x_671, 1, x_670);
lean_inc(x_657);
lean_inc_ref(x_658);
lean_inc(x_661);
lean_inc_ref(x_656);
lean_inc_ref(x_659);
lean_inc(x_2);
x_672 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_655, x_659, x_653, x_660, x_650, x_464, x_671, x_656, x_661, x_658, x_657);
x_159 = x_657;
x_160 = x_658;
x_161 = x_659;
x_162 = x_651;
x_163 = x_652;
x_164 = x_653;
x_165 = x_656;
x_166 = x_655;
x_167 = x_661;
x_168 = x_662;
x_169 = x_663;
x_170 = x_672;
goto block_173;
}
block_700:
{
lean_object* x_689; double x_690; double x_691; double x_692; double x_693; double x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_689 = lean_io_mono_nanos_now();
x_690 = lean_float_of_nat(x_674);
x_691 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_692 = lean_float_div(x_690, x_691);
x_693 = lean_float_of_nat(x_689);
x_694 = lean_float_div(x_693, x_691);
x_695 = lean_box_float(x_692);
x_696 = lean_box_float(x_694);
x_697 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set(x_697, 1, x_696);
x_698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_698, 0, x_688);
lean_ctor_set(x_698, 1, x_697);
lean_inc(x_681);
lean_inc_ref(x_682);
lean_inc(x_685);
lean_inc_ref(x_679);
lean_inc_ref(x_683);
lean_inc(x_2);
x_699 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_678, x_683, x_677, x_684, x_680, x_356, x_698, x_679, x_685, x_682, x_681);
x_159 = x_681;
x_160 = x_682;
x_161 = x_683;
x_162 = x_675;
x_163 = x_676;
x_164 = x_677;
x_165 = x_679;
x_166 = x_678;
x_167 = x_685;
x_168 = x_686;
x_169 = x_687;
x_170 = x_699;
goto block_173;
}
block_724:
{
lean_object* x_716; double x_717; double x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_716 = lean_io_get_num_heartbeats();
x_717 = lean_float_of_nat(x_706);
x_718 = lean_float_of_nat(x_716);
x_719 = lean_box_float(x_717);
x_720 = lean_box_float(x_718);
x_721 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_721, 0, x_719);
lean_ctor_set(x_721, 1, x_720);
x_722 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_722, 0, x_715);
lean_ctor_set(x_722, 1, x_721);
lean_inc(x_708);
lean_inc_ref(x_709);
lean_inc(x_712);
lean_inc_ref(x_705);
lean_inc_ref(x_710);
lean_inc(x_2);
x_723 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_704, x_710, x_703, x_711, x_707, x_356, x_722, x_705, x_712, x_709, x_708);
x_159 = x_708;
x_160 = x_709;
x_161 = x_710;
x_162 = x_701;
x_163 = x_702;
x_164 = x_703;
x_165 = x_705;
x_166 = x_704;
x_167 = x_712;
x_168 = x_713;
x_169 = x_714;
x_170 = x_723;
goto block_173;
}
block_780:
{
lean_object* x_741; 
x_741 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_732);
if (x_729 == 0)
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
lean_dec_ref(x_741);
x_743 = lean_io_mono_nanos_now();
lean_inc(x_732);
lean_inc_ref(x_734);
lean_inc(x_738);
lean_inc_ref(x_728);
lean_inc(x_2);
x_744 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_733, x_736, x_731, x_728, x_738, x_734, x_732);
if (lean_obj_tag(x_744) == 0)
{
lean_object* x_745; lean_object* x_746; uint8_t x_747; uint8_t x_752; 
x_745 = lean_ctor_get(x_744, 0);
x_752 = !lean_is_exclusive(x_744);
if (x_752 == 0)
{
x_746 = x_744;
x_747 = x_752;
goto block_751;
}
else
{
lean_inc(x_745);
lean_dec(x_744);
x_746 = lean_box(0);
x_747 = x_752;
goto block_751;
}
block_751:
{
lean_object* x_748; 
if (x_747 == 0)
{
lean_ctor_set_tag(x_746, 1);
x_748 = x_746;
goto block_749;
}
else
{
lean_object* x_750; 
x_750 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_750, 0, x_745);
x_748 = x_750;
goto block_749;
}
block_749:
{
x_674 = x_743;
x_675 = x_725;
x_676 = x_726;
x_677 = x_727;
x_678 = x_730;
x_679 = x_728;
x_680 = x_742;
x_681 = x_732;
x_682 = x_734;
x_683 = x_735;
x_684 = x_737;
x_685 = x_738;
x_686 = x_739;
x_687 = x_740;
x_688 = x_748;
goto block_700;
}
}
}
else
{
lean_object* x_753; lean_object* x_754; uint8_t x_755; uint8_t x_760; 
x_753 = lean_ctor_get(x_744, 0);
x_760 = !lean_is_exclusive(x_744);
if (x_760 == 0)
{
x_754 = x_744;
x_755 = x_760;
goto block_759;
}
else
{
lean_inc(x_753);
lean_dec(x_744);
x_754 = lean_box(0);
x_755 = x_760;
goto block_759;
}
block_759:
{
lean_object* x_756; 
if (x_755 == 0)
{
lean_ctor_set_tag(x_754, 0);
x_756 = x_754;
goto block_757;
}
else
{
lean_object* x_758; 
x_758 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_758, 0, x_753);
x_756 = x_758;
goto block_757;
}
block_757:
{
x_674 = x_743;
x_675 = x_725;
x_676 = x_726;
x_677 = x_727;
x_678 = x_730;
x_679 = x_728;
x_680 = x_742;
x_681 = x_732;
x_682 = x_734;
x_683 = x_735;
x_684 = x_737;
x_685 = x_738;
x_686 = x_739;
x_687 = x_740;
x_688 = x_756;
goto block_700;
}
}
}
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; 
x_761 = lean_ctor_get(x_741, 0);
lean_inc(x_761);
lean_dec_ref(x_741);
x_762 = lean_io_get_num_heartbeats();
lean_inc(x_732);
lean_inc_ref(x_734);
lean_inc(x_738);
lean_inc_ref(x_728);
lean_inc(x_2);
x_763 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_733, x_736, x_731, x_728, x_738, x_734, x_732);
if (lean_obj_tag(x_763) == 0)
{
lean_object* x_764; lean_object* x_765; uint8_t x_766; uint8_t x_771; 
x_764 = lean_ctor_get(x_763, 0);
x_771 = !lean_is_exclusive(x_763);
if (x_771 == 0)
{
x_765 = x_763;
x_766 = x_771;
goto block_770;
}
else
{
lean_inc(x_764);
lean_dec(x_763);
x_765 = lean_box(0);
x_766 = x_771;
goto block_770;
}
block_770:
{
lean_object* x_767; 
if (x_766 == 0)
{
lean_ctor_set_tag(x_765, 1);
x_767 = x_765;
goto block_768;
}
else
{
lean_object* x_769; 
x_769 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_769, 0, x_764);
x_767 = x_769;
goto block_768;
}
block_768:
{
x_701 = x_725;
x_702 = x_726;
x_703 = x_727;
x_704 = x_730;
x_705 = x_728;
x_706 = x_762;
x_707 = x_761;
x_708 = x_732;
x_709 = x_734;
x_710 = x_735;
x_711 = x_737;
x_712 = x_738;
x_713 = x_739;
x_714 = x_740;
x_715 = x_767;
goto block_724;
}
}
}
else
{
lean_object* x_772; lean_object* x_773; uint8_t x_774; uint8_t x_779; 
x_772 = lean_ctor_get(x_763, 0);
x_779 = !lean_is_exclusive(x_763);
if (x_779 == 0)
{
x_773 = x_763;
x_774 = x_779;
goto block_778;
}
else
{
lean_inc(x_772);
lean_dec(x_763);
x_773 = lean_box(0);
x_774 = x_779;
goto block_778;
}
block_778:
{
lean_object* x_775; 
if (x_774 == 0)
{
lean_ctor_set_tag(x_773, 0);
x_775 = x_773;
goto block_776;
}
else
{
lean_object* x_777; 
x_777 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_777, 0, x_772);
x_775 = x_777;
goto block_776;
}
block_776:
{
x_701 = x_725;
x_702 = x_726;
x_703 = x_727;
x_704 = x_730;
x_705 = x_728;
x_706 = x_762;
x_707 = x_761;
x_708 = x_732;
x_709 = x_734;
x_710 = x_735;
x_711 = x_737;
x_712 = x_738;
x_713 = x_739;
x_714 = x_740;
x_715 = x_775;
goto block_724;
}
}
}
}
}
block_803:
{
lean_object* x_792; double x_793; double x_794; double x_795; double x_796; double x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_792 = lean_io_mono_nanos_now();
x_793 = lean_float_of_nat(x_785);
x_794 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_795 = lean_float_div(x_793, x_794);
x_796 = lean_float_of_nat(x_792);
x_797 = lean_float_div(x_796, x_794);
x_798 = lean_box_float(x_795);
x_799 = lean_box_float(x_797);
x_800 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_800, 0, x_798);
lean_ctor_set(x_800, 1, x_799);
x_801 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_801, 0, x_791);
lean_ctor_set(x_801, 1, x_800);
x_802 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_788, x_786, x_787, x_784, x_790, x_356, x_801, x_783, x_782, x_781, x_789);
lean_dec_ref(x_787);
return x_802;
}
block_823:
{
lean_object* x_815; double x_816; double x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_815 = lean_io_get_num_heartbeats();
x_816 = lean_float_of_nat(x_808);
x_817 = lean_float_of_nat(x_815);
x_818 = lean_box_float(x_816);
x_819 = lean_box_float(x_817);
x_820 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_820, 0, x_818);
lean_ctor_set(x_820, 1, x_819);
x_821 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_821, 0, x_814);
lean_ctor_set(x_821, 1, x_820);
x_822 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_811, x_809, x_810, x_807, x_813, x_356, x_821, x_806, x_805, x_804, x_812);
lean_dec_ref(x_810);
return x_822;
}
block_875:
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; uint8_t x_838; 
x_835 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_834);
x_836 = lean_ctor_get(x_835, 0);
lean_inc(x_836);
lean_dec_ref(x_835);
x_837 = l_Lean_trace_profiler_useHeartbeats;
x_838 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_833, x_837);
if (x_838 == 0)
{
lean_object* x_839; lean_object* x_840; 
x_839 = lean_io_mono_nanos_now();
lean_inc(x_834);
lean_inc_ref(x_825);
lean_inc(x_826);
lean_inc_ref(x_827);
lean_inc(x_2);
x_840 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_829, x_824, x_830, x_827, x_826, x_825, x_834);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_841; lean_object* x_842; uint8_t x_843; uint8_t x_848; 
x_841 = lean_ctor_get(x_840, 0);
x_848 = !lean_is_exclusive(x_840);
if (x_848 == 0)
{
x_842 = x_840;
x_843 = x_848;
goto block_847;
}
else
{
lean_inc(x_841);
lean_dec(x_840);
x_842 = lean_box(0);
x_843 = x_848;
goto block_847;
}
block_847:
{
lean_object* x_844; 
if (x_843 == 0)
{
lean_ctor_set_tag(x_842, 1);
x_844 = x_842;
goto block_845;
}
else
{
lean_object* x_846; 
x_846 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_846, 0, x_841);
x_844 = x_846;
goto block_845;
}
block_845:
{
x_781 = x_825;
x_782 = x_826;
x_783 = x_827;
x_784 = x_828;
x_785 = x_839;
x_786 = x_831;
x_787 = x_833;
x_788 = x_832;
x_789 = x_834;
x_790 = x_836;
x_791 = x_844;
goto block_803;
}
}
}
else
{
lean_object* x_849; lean_object* x_850; uint8_t x_851; uint8_t x_856; 
x_849 = lean_ctor_get(x_840, 0);
x_856 = !lean_is_exclusive(x_840);
if (x_856 == 0)
{
x_850 = x_840;
x_851 = x_856;
goto block_855;
}
else
{
lean_inc(x_849);
lean_dec(x_840);
x_850 = lean_box(0);
x_851 = x_856;
goto block_855;
}
block_855:
{
lean_object* x_852; 
if (x_851 == 0)
{
lean_ctor_set_tag(x_850, 0);
x_852 = x_850;
goto block_853;
}
else
{
lean_object* x_854; 
x_854 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_854, 0, x_849);
x_852 = x_854;
goto block_853;
}
block_853:
{
x_781 = x_825;
x_782 = x_826;
x_783 = x_827;
x_784 = x_828;
x_785 = x_839;
x_786 = x_831;
x_787 = x_833;
x_788 = x_832;
x_789 = x_834;
x_790 = x_836;
x_791 = x_852;
goto block_803;
}
}
}
}
else
{
lean_object* x_857; lean_object* x_858; 
x_857 = lean_io_get_num_heartbeats();
lean_inc(x_834);
lean_inc_ref(x_825);
lean_inc(x_826);
lean_inc_ref(x_827);
lean_inc(x_2);
x_858 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_829, x_824, x_830, x_827, x_826, x_825, x_834);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_859; lean_object* x_860; uint8_t x_861; uint8_t x_866; 
x_859 = lean_ctor_get(x_858, 0);
x_866 = !lean_is_exclusive(x_858);
if (x_866 == 0)
{
x_860 = x_858;
x_861 = x_866;
goto block_865;
}
else
{
lean_inc(x_859);
lean_dec(x_858);
x_860 = lean_box(0);
x_861 = x_866;
goto block_865;
}
block_865:
{
lean_object* x_862; 
if (x_861 == 0)
{
lean_ctor_set_tag(x_860, 1);
x_862 = x_860;
goto block_863;
}
else
{
lean_object* x_864; 
x_864 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_864, 0, x_859);
x_862 = x_864;
goto block_863;
}
block_863:
{
x_804 = x_825;
x_805 = x_826;
x_806 = x_827;
x_807 = x_828;
x_808 = x_857;
x_809 = x_831;
x_810 = x_833;
x_811 = x_832;
x_812 = x_834;
x_813 = x_836;
x_814 = x_862;
goto block_823;
}
}
}
else
{
lean_object* x_867; lean_object* x_868; uint8_t x_869; uint8_t x_874; 
x_867 = lean_ctor_get(x_858, 0);
x_874 = !lean_is_exclusive(x_858);
if (x_874 == 0)
{
x_868 = x_858;
x_869 = x_874;
goto block_873;
}
else
{
lean_inc(x_867);
lean_dec(x_858);
x_868 = lean_box(0);
x_869 = x_874;
goto block_873;
}
block_873:
{
lean_object* x_870; 
if (x_869 == 0)
{
lean_ctor_set_tag(x_868, 0);
x_870 = x_868;
goto block_871;
}
else
{
lean_object* x_872; 
x_872 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_872, 0, x_867);
x_870 = x_872;
goto block_871;
}
block_871:
{
x_804 = x_825;
x_805 = x_826;
x_806 = x_827;
x_807 = x_828;
x_808 = x_857;
x_809 = x_831;
x_810 = x_833;
x_811 = x_832;
x_812 = x_834;
x_813 = x_836;
x_814 = x_870;
goto block_823;
}
}
}
}
}
block_895:
{
lean_object* x_887; double x_888; double x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_887 = lean_io_get_num_heartbeats();
x_888 = lean_float_of_nat(x_881);
x_889 = lean_float_of_nat(x_887);
x_890 = lean_box_float(x_888);
x_891 = lean_box_float(x_889);
x_892 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_892, 0, x_890);
lean_ctor_set(x_892, 1, x_891);
x_893 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_893, 0, x_886);
lean_ctor_set(x_893, 1, x_892);
x_894 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_883, x_877, x_876, x_882, x_885, x_464, x_893, x_880, x_879, x_878, x_884);
lean_dec_ref(x_876);
return x_894;
}
block_918:
{
lean_object* x_907; double x_908; double x_909; double x_910; double x_911; double x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_907 = lean_io_mono_nanos_now();
x_908 = lean_float_of_nat(x_896);
x_909 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_910 = lean_float_div(x_908, x_909);
x_911 = lean_float_of_nat(x_907);
x_912 = lean_float_div(x_911, x_909);
x_913 = lean_box_float(x_910);
x_914 = lean_box_float(x_912);
x_915 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_915, 0, x_913);
lean_ctor_set(x_915, 1, x_914);
x_916 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_916, 0, x_906);
lean_ctor_set(x_916, 1, x_915);
x_917 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_903, x_898, x_897, x_902, x_905, x_464, x_916, x_901, x_900, x_899, x_904);
lean_dec_ref(x_897);
return x_917;
}
block_938:
{
lean_object* x_930; double x_931; double x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; 
x_930 = lean_io_get_num_heartbeats();
x_931 = lean_float_of_nat(x_919);
x_932 = lean_float_of_nat(x_930);
x_933 = lean_box_float(x_931);
x_934 = lean_box_float(x_932);
x_935 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_935, 0, x_933);
lean_ctor_set(x_935, 1, x_934);
x_936 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_936, 0, x_929);
lean_ctor_set(x_936, 1, x_935);
x_937 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_926, x_925, x_924, x_928, x_923, x_248, x_936, x_922, x_921, x_920, x_927);
lean_dec_ref(x_924);
return x_937;
}
block_961:
{
lean_object* x_950; double x_951; double x_952; double x_953; double x_954; double x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_950 = lean_io_mono_nanos_now();
x_951 = lean_float_of_nat(x_943);
x_952 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_953 = lean_float_div(x_951, x_952);
x_954 = lean_float_of_nat(x_950);
x_955 = lean_float_div(x_954, x_952);
x_956 = lean_box_float(x_953);
x_957 = lean_box_float(x_955);
x_958 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_958, 0, x_956);
lean_ctor_set(x_958, 1, x_957);
x_959 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_959, 0, x_949);
lean_ctor_set(x_959, 1, x_958);
x_960 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_946, x_945, x_944, x_948, x_942, x_248, x_959, x_941, x_940, x_939, x_947);
lean_dec_ref(x_944);
return x_960;
}
block_1013:
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; uint8_t x_976; 
x_973 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_969);
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
lean_dec_ref(x_973);
x_975 = l_Lean_trace_profiler_useHeartbeats;
x_976 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_967, x_975);
if (x_976 == 0)
{
lean_object* x_977; lean_object* x_978; 
x_977 = lean_io_mono_nanos_now();
lean_inc(x_969);
lean_inc_ref(x_963);
lean_inc(x_964);
lean_inc_ref(x_965);
lean_inc(x_2);
x_978 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_971, x_962, x_970, x_965, x_964, x_963, x_969);
if (lean_obj_tag(x_978) == 0)
{
lean_object* x_979; lean_object* x_980; uint8_t x_981; uint8_t x_986; 
x_979 = lean_ctor_get(x_978, 0);
x_986 = !lean_is_exclusive(x_978);
if (x_986 == 0)
{
x_980 = x_978;
x_981 = x_986;
goto block_985;
}
else
{
lean_inc(x_979);
lean_dec(x_978);
x_980 = lean_box(0);
x_981 = x_986;
goto block_985;
}
block_985:
{
lean_object* x_982; 
if (x_981 == 0)
{
lean_ctor_set_tag(x_980, 1);
x_982 = x_980;
goto block_983;
}
else
{
lean_object* x_984; 
x_984 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_984, 0, x_979);
x_982 = x_984;
goto block_983;
}
block_983:
{
x_939 = x_963;
x_940 = x_964;
x_941 = x_965;
x_942 = x_974;
x_943 = x_977;
x_944 = x_967;
x_945 = x_966;
x_946 = x_968;
x_947 = x_969;
x_948 = x_972;
x_949 = x_982;
goto block_961;
}
}
}
else
{
lean_object* x_987; lean_object* x_988; uint8_t x_989; uint8_t x_994; 
x_987 = lean_ctor_get(x_978, 0);
x_994 = !lean_is_exclusive(x_978);
if (x_994 == 0)
{
x_988 = x_978;
x_989 = x_994;
goto block_993;
}
else
{
lean_inc(x_987);
lean_dec(x_978);
x_988 = lean_box(0);
x_989 = x_994;
goto block_993;
}
block_993:
{
lean_object* x_990; 
if (x_989 == 0)
{
lean_ctor_set_tag(x_988, 0);
x_990 = x_988;
goto block_991;
}
else
{
lean_object* x_992; 
x_992 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_992, 0, x_987);
x_990 = x_992;
goto block_991;
}
block_991:
{
x_939 = x_963;
x_940 = x_964;
x_941 = x_965;
x_942 = x_974;
x_943 = x_977;
x_944 = x_967;
x_945 = x_966;
x_946 = x_968;
x_947 = x_969;
x_948 = x_972;
x_949 = x_990;
goto block_961;
}
}
}
}
else
{
lean_object* x_995; lean_object* x_996; 
x_995 = lean_io_get_num_heartbeats();
lean_inc(x_969);
lean_inc_ref(x_963);
lean_inc(x_964);
lean_inc_ref(x_965);
lean_inc(x_2);
x_996 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_971, x_962, x_970, x_965, x_964, x_963, x_969);
if (lean_obj_tag(x_996) == 0)
{
lean_object* x_997; lean_object* x_998; uint8_t x_999; uint8_t x_1004; 
x_997 = lean_ctor_get(x_996, 0);
x_1004 = !lean_is_exclusive(x_996);
if (x_1004 == 0)
{
x_998 = x_996;
x_999 = x_1004;
goto block_1003;
}
else
{
lean_inc(x_997);
lean_dec(x_996);
x_998 = lean_box(0);
x_999 = x_1004;
goto block_1003;
}
block_1003:
{
lean_object* x_1000; 
if (x_999 == 0)
{
lean_ctor_set_tag(x_998, 1);
x_1000 = x_998;
goto block_1001;
}
else
{
lean_object* x_1002; 
x_1002 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1002, 0, x_997);
x_1000 = x_1002;
goto block_1001;
}
block_1001:
{
x_919 = x_995;
x_920 = x_963;
x_921 = x_964;
x_922 = x_965;
x_923 = x_974;
x_924 = x_967;
x_925 = x_966;
x_926 = x_968;
x_927 = x_969;
x_928 = x_972;
x_929 = x_1000;
goto block_938;
}
}
}
else
{
lean_object* x_1005; lean_object* x_1006; uint8_t x_1007; uint8_t x_1012; 
x_1005 = lean_ctor_get(x_996, 0);
x_1012 = !lean_is_exclusive(x_996);
if (x_1012 == 0)
{
x_1006 = x_996;
x_1007 = x_1012;
goto block_1011;
}
else
{
lean_inc(x_1005);
lean_dec(x_996);
x_1006 = lean_box(0);
x_1007 = x_1012;
goto block_1011;
}
block_1011:
{
lean_object* x_1008; 
if (x_1007 == 0)
{
lean_ctor_set_tag(x_1006, 0);
x_1008 = x_1006;
goto block_1009;
}
else
{
lean_object* x_1010; 
x_1010 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1010, 0, x_1005);
x_1008 = x_1010;
goto block_1009;
}
block_1009:
{
x_919 = x_995;
x_920 = x_963;
x_921 = x_964;
x_922 = x_965;
x_923 = x_974;
x_924 = x_967;
x_925 = x_966;
x_926 = x_968;
x_927 = x_969;
x_928 = x_972;
x_929 = x_1008;
goto block_938;
}
}
}
}
}
block_1059:
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; uint8_t x_1027; uint8_t x_1058; 
x_1024 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1016);
x_1025 = lean_ctor_get(x_1024, 0);
x_1058 = !lean_is_exclusive(x_1024);
if (x_1058 == 0)
{
x_1026 = x_1024;
x_1027 = x_1058;
goto block_1057;
}
else
{
lean_inc(x_1025);
lean_dec(x_1024);
x_1026 = lean_box(0);
x_1027 = x_1058;
goto block_1057;
}
block_1057:
{
lean_object* x_1028; uint8_t x_1029; 
x_1028 = l_Lean_trace_profiler_useHeartbeats;
x_1029 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1018, x_1028);
if (x_1029 == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1030 = lean_io_mono_nanos_now();
x_1031 = lean_io_mono_nanos_now();
if (x_1027 == 0)
{
lean_ctor_set_tag(x_1026, 1);
lean_ctor_set(x_1026, 0, x_1020);
x_1032 = x_1026;
goto block_1043;
}
else
{
lean_object* x_1044; 
x_1044 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1044, 0, x_1020);
x_1032 = x_1044;
goto block_1043;
}
block_1043:
{
double x_1033; double x_1034; double x_1035; double x_1036; double x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1033 = lean_float_of_nat(x_1030);
x_1034 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_1035 = lean_float_div(x_1033, x_1034);
x_1036 = lean_float_of_nat(x_1031);
x_1037 = lean_float_div(x_1036, x_1034);
x_1038 = lean_box_float(x_1035);
x_1039 = lean_box_float(x_1037);
x_1040 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1040, 0, x_1038);
lean_ctor_set(x_1040, 1, x_1039);
x_1041 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1041, 0, x_1032);
lean_ctor_set(x_1041, 1, x_1040);
x_1042 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1019, x_1015, x_1018, x_1023, x_1025, x_1014, x_1041, x_1021, x_1022, x_1017, x_1016);
lean_dec_ref(x_1018);
return x_1042;
}
}
else
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
x_1045 = lean_io_get_num_heartbeats();
x_1046 = lean_io_get_num_heartbeats();
if (x_1027 == 0)
{
lean_ctor_set_tag(x_1026, 1);
lean_ctor_set(x_1026, 0, x_1020);
x_1047 = x_1026;
goto block_1055;
}
else
{
lean_object* x_1056; 
x_1056 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1056, 0, x_1020);
x_1047 = x_1056;
goto block_1055;
}
block_1055:
{
double x_1048; double x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
x_1048 = lean_float_of_nat(x_1045);
x_1049 = lean_float_of_nat(x_1046);
x_1050 = lean_box_float(x_1048);
x_1051 = lean_box_float(x_1049);
x_1052 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1052, 0, x_1050);
lean_ctor_set(x_1052, 1, x_1051);
x_1053 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1053, 0, x_1047);
lean_ctor_set(x_1053, 1, x_1052);
x_1054 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1019, x_1015, x_1018, x_1023, x_1025, x_1014, x_1053, x_1021, x_1022, x_1017, x_1016);
lean_dec_ref(x_1018);
return x_1054;
}
}
}
}
block_1115:
{
lean_object* x_1076; 
x_1076 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1068);
if (x_1066 == 0)
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1077 = lean_ctor_get(x_1076, 0);
lean_inc(x_1077);
lean_dec_ref(x_1076);
x_1078 = lean_io_mono_nanos_now();
lean_inc(x_1068);
lean_inc_ref(x_1069);
lean_inc(x_1072);
lean_inc_ref(x_1065);
lean_inc(x_2);
x_1079 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1061, x_1074, x_7, x_1065, x_1072, x_1069, x_1068);
if (lean_obj_tag(x_1079) == 0)
{
lean_object* x_1080; lean_object* x_1081; uint8_t x_1082; uint8_t x_1087; 
x_1080 = lean_ctor_get(x_1079, 0);
x_1087 = !lean_is_exclusive(x_1079);
if (x_1087 == 0)
{
x_1081 = x_1079;
x_1082 = x_1087;
goto block_1086;
}
else
{
lean_inc(x_1080);
lean_dec(x_1079);
x_1081 = lean_box(0);
x_1082 = x_1087;
goto block_1086;
}
block_1086:
{
lean_object* x_1083; 
if (x_1082 == 0)
{
lean_ctor_set_tag(x_1081, 1);
x_1083 = x_1081;
goto block_1084;
}
else
{
lean_object* x_1085; 
x_1085 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1085, 0, x_1080);
x_1083 = x_1085;
goto block_1084;
}
block_1084:
{
x_623 = x_1077;
x_624 = x_1062;
x_625 = x_1063;
x_626 = x_1064;
x_627 = x_1067;
x_628 = x_1065;
x_629 = x_1078;
x_630 = x_1068;
x_631 = x_1069;
x_632 = x_1070;
x_633 = x_1071;
x_634 = x_1072;
x_635 = x_1073;
x_636 = x_1075;
x_637 = x_1083;
goto block_649;
}
}
}
else
{
lean_object* x_1088; lean_object* x_1089; uint8_t x_1090; uint8_t x_1095; 
x_1088 = lean_ctor_get(x_1079, 0);
x_1095 = !lean_is_exclusive(x_1079);
if (x_1095 == 0)
{
x_1089 = x_1079;
x_1090 = x_1095;
goto block_1094;
}
else
{
lean_inc(x_1088);
lean_dec(x_1079);
x_1089 = lean_box(0);
x_1090 = x_1095;
goto block_1094;
}
block_1094:
{
lean_object* x_1091; 
if (x_1090 == 0)
{
lean_ctor_set_tag(x_1089, 0);
x_1091 = x_1089;
goto block_1092;
}
else
{
lean_object* x_1093; 
x_1093 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1093, 0, x_1088);
x_1091 = x_1093;
goto block_1092;
}
block_1092:
{
x_623 = x_1077;
x_624 = x_1062;
x_625 = x_1063;
x_626 = x_1064;
x_627 = x_1067;
x_628 = x_1065;
x_629 = x_1078;
x_630 = x_1068;
x_631 = x_1069;
x_632 = x_1070;
x_633 = x_1071;
x_634 = x_1072;
x_635 = x_1073;
x_636 = x_1075;
x_637 = x_1091;
goto block_649;
}
}
}
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1096 = lean_ctor_get(x_1076, 0);
lean_inc(x_1096);
lean_dec_ref(x_1076);
x_1097 = lean_io_get_num_heartbeats();
lean_inc(x_1068);
lean_inc_ref(x_1069);
lean_inc(x_1072);
lean_inc_ref(x_1065);
lean_inc(x_2);
x_1098 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1061, x_1074, x_7, x_1065, x_1072, x_1069, x_1068);
if (lean_obj_tag(x_1098) == 0)
{
lean_object* x_1099; lean_object* x_1100; uint8_t x_1101; uint8_t x_1106; 
x_1099 = lean_ctor_get(x_1098, 0);
x_1106 = !lean_is_exclusive(x_1098);
if (x_1106 == 0)
{
x_1100 = x_1098;
x_1101 = x_1106;
goto block_1105;
}
else
{
lean_inc(x_1099);
lean_dec(x_1098);
x_1100 = lean_box(0);
x_1101 = x_1106;
goto block_1105;
}
block_1105:
{
lean_object* x_1102; 
if (x_1101 == 0)
{
lean_ctor_set_tag(x_1100, 1);
x_1102 = x_1100;
goto block_1103;
}
else
{
lean_object* x_1104; 
x_1104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1104, 0, x_1099);
x_1102 = x_1104;
goto block_1103;
}
block_1103:
{
x_650 = x_1096;
x_651 = x_1062;
x_652 = x_1063;
x_653 = x_1064;
x_654 = x_1097;
x_655 = x_1067;
x_656 = x_1065;
x_657 = x_1068;
x_658 = x_1069;
x_659 = x_1070;
x_660 = x_1071;
x_661 = x_1072;
x_662 = x_1073;
x_663 = x_1075;
x_664 = x_1102;
goto block_673;
}
}
}
else
{
lean_object* x_1107; lean_object* x_1108; uint8_t x_1109; uint8_t x_1114; 
x_1107 = lean_ctor_get(x_1098, 0);
x_1114 = !lean_is_exclusive(x_1098);
if (x_1114 == 0)
{
x_1108 = x_1098;
x_1109 = x_1114;
goto block_1113;
}
else
{
lean_inc(x_1107);
lean_dec(x_1098);
x_1108 = lean_box(0);
x_1109 = x_1114;
goto block_1113;
}
block_1113:
{
lean_object* x_1110; 
if (x_1109 == 0)
{
lean_ctor_set_tag(x_1108, 0);
x_1110 = x_1108;
goto block_1111;
}
else
{
lean_object* x_1112; 
x_1112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1112, 0, x_1107);
x_1110 = x_1112;
goto block_1111;
}
block_1111:
{
x_650 = x_1096;
x_651 = x_1062;
x_652 = x_1063;
x_653 = x_1064;
x_654 = x_1097;
x_655 = x_1067;
x_656 = x_1065;
x_657 = x_1068;
x_658 = x_1069;
x_659 = x_1070;
x_660 = x_1071;
x_661 = x_1072;
x_662 = x_1073;
x_663 = x_1075;
x_664 = x_1110;
goto block_673;
}
}
}
}
}
block_1156:
{
if (x_1132 == 0)
{
lean_object* x_1133; 
lean_dec_ref(x_1126);
lean_inc(x_1123);
lean_inc_ref(x_1124);
lean_inc(x_1129);
lean_inc_ref(x_1120);
lean_inc(x_1128);
x_1133 = lean_apply_6(x_1118, x_1128, x_1120, x_1129, x_1124, x_1123, lean_box(0));
if (lean_obj_tag(x_1133) == 0)
{
lean_object* x_1134; 
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
lean_dec_ref(x_1133);
if (lean_obj_tag(x_1134) == 0)
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; uint8_t x_1139; 
lean_inc(x_2);
x_1135 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1124);
x_1136 = lean_ctor_get(x_1135, 0);
lean_inc(x_1136);
lean_dec_ref(x_1135);
x_1137 = lean_nat_add(x_1061, x_1060);
lean_dec(x_1061);
x_1138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1138, 0, x_1128);
lean_ctor_set(x_1138, 1, x_7);
x_1139 = lean_unbox(x_1136);
if (x_1139 == 0)
{
lean_object* x_1140; uint8_t x_1141; 
x_1140 = l_Lean_trace_profiler;
x_1141 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1119, x_1140);
if (x_1141 == 0)
{
lean_object* x_1142; 
lean_dec(x_1136);
lean_inc(x_1123);
lean_inc_ref(x_1124);
lean_inc(x_1129);
lean_inc_ref(x_1120);
lean_inc(x_2);
x_1142 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1137, x_1127, x_1138, x_1120, x_1129, x_1124, x_1123);
x_159 = x_1123;
x_160 = x_1124;
x_161 = x_1125;
x_162 = x_1116;
x_163 = x_1117;
x_164 = x_1119;
x_165 = x_1120;
x_166 = x_1122;
x_167 = x_1129;
x_168 = x_1130;
x_169 = x_1131;
x_170 = x_1142;
goto block_173;
}
else
{
uint8_t x_1143; 
x_1143 = lean_unbox(x_1136);
lean_dec(x_1136);
x_725 = x_1116;
x_726 = x_1117;
x_727 = x_1119;
x_728 = x_1120;
x_729 = x_1121;
x_730 = x_1122;
x_731 = x_1138;
x_732 = x_1123;
x_733 = x_1137;
x_734 = x_1124;
x_735 = x_1125;
x_736 = x_1127;
x_737 = x_1143;
x_738 = x_1129;
x_739 = x_1130;
x_740 = x_1131;
goto block_780;
}
}
else
{
uint8_t x_1144; 
x_1144 = lean_unbox(x_1136);
lean_dec(x_1136);
x_725 = x_1116;
x_726 = x_1117;
x_727 = x_1119;
x_728 = x_1120;
x_729 = x_1121;
x_730 = x_1122;
x_731 = x_1138;
x_732 = x_1123;
x_733 = x_1137;
x_734 = x_1124;
x_735 = x_1125;
x_736 = x_1127;
x_737 = x_1144;
x_738 = x_1129;
x_739 = x_1130;
x_740 = x_1131;
goto block_780;
}
}
else
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; uint8_t x_1149; 
lean_dec(x_1128);
x_1145 = lean_ctor_get(x_1134, 0);
lean_inc(x_1145);
lean_dec_ref(x_1134);
lean_inc(x_2);
x_1146 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1124);
x_1147 = lean_ctor_get(x_1146, 0);
lean_inc(x_1147);
lean_dec_ref(x_1146);
x_1148 = l_List_appendTR___redArg(x_1145, x_1127);
x_1149 = lean_unbox(x_1147);
if (x_1149 == 0)
{
lean_object* x_1150; uint8_t x_1151; 
x_1150 = l_Lean_trace_profiler;
x_1151 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1119, x_1150);
if (x_1151 == 0)
{
lean_object* x_1152; 
lean_dec(x_1147);
lean_inc(x_1123);
lean_inc_ref(x_1124);
lean_inc(x_1129);
lean_inc_ref(x_1120);
lean_inc(x_2);
x_1152 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1061, x_1148, x_7, x_1120, x_1129, x_1124, x_1123);
x_159 = x_1123;
x_160 = x_1124;
x_161 = x_1125;
x_162 = x_1116;
x_163 = x_1117;
x_164 = x_1119;
x_165 = x_1120;
x_166 = x_1122;
x_167 = x_1129;
x_168 = x_1130;
x_169 = x_1131;
x_170 = x_1152;
goto block_173;
}
else
{
uint8_t x_1153; 
x_1153 = lean_unbox(x_1147);
lean_dec(x_1147);
x_1062 = x_1116;
x_1063 = x_1117;
x_1064 = x_1119;
x_1065 = x_1120;
x_1066 = x_1121;
x_1067 = x_1122;
x_1068 = x_1123;
x_1069 = x_1124;
x_1070 = x_1125;
x_1071 = x_1153;
x_1072 = x_1129;
x_1073 = x_1130;
x_1074 = x_1148;
x_1075 = x_1131;
goto block_1115;
}
}
else
{
uint8_t x_1154; 
x_1154 = lean_unbox(x_1147);
lean_dec(x_1147);
x_1062 = x_1116;
x_1063 = x_1117;
x_1064 = x_1119;
x_1065 = x_1120;
x_1066 = x_1121;
x_1067 = x_1122;
x_1068 = x_1123;
x_1069 = x_1124;
x_1070 = x_1125;
x_1071 = x_1154;
x_1072 = x_1129;
x_1073 = x_1130;
x_1074 = x_1148;
x_1075 = x_1131;
goto block_1115;
}
}
}
else
{
lean_object* x_1155; 
lean_dec(x_1128);
lean_dec(x_1127);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1155 = lean_ctor_get(x_1133, 0);
lean_inc(x_1155);
lean_dec_ref(x_1133);
x_145 = x_1123;
x_146 = x_1124;
x_147 = x_1116;
x_148 = x_1125;
x_149 = x_1117;
x_150 = x_1119;
x_151 = x_1122;
x_152 = x_1120;
x_153 = x_1129;
x_154 = x_1130;
x_155 = x_1131;
x_156 = x_1155;
goto block_158;
}
}
else
{
lean_dec(x_1128);
lean_dec(x_1127);
lean_dec_ref(x_1118);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_145 = x_1123;
x_146 = x_1124;
x_147 = x_1116;
x_148 = x_1125;
x_149 = x_1117;
x_150 = x_1119;
x_151 = x_1122;
x_152 = x_1120;
x_153 = x_1129;
x_154 = x_1130;
x_155 = x_1131;
x_156 = x_1126;
goto block_158;
}
}
block_1210:
{
lean_object* x_1171; 
x_1171 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1164);
if (x_1162 == 0)
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
x_1172 = lean_ctor_get(x_1171, 0);
lean_inc(x_1172);
lean_dec_ref(x_1171);
x_1173 = lean_io_mono_nanos_now();
lean_inc(x_1164);
lean_inc_ref(x_1165);
lean_inc(x_1168);
lean_inc_ref(x_1161);
lean_inc(x_2);
x_1174 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1061, x_1159, x_7, x_1161, x_1168, x_1165, x_1164);
if (lean_obj_tag(x_1174) == 0)
{
lean_object* x_1175; lean_object* x_1176; uint8_t x_1177; uint8_t x_1182; 
x_1175 = lean_ctor_get(x_1174, 0);
x_1182 = !lean_is_exclusive(x_1174);
if (x_1182 == 0)
{
x_1176 = x_1174;
x_1177 = x_1182;
goto block_1181;
}
else
{
lean_inc(x_1175);
lean_dec(x_1174);
x_1176 = lean_box(0);
x_1177 = x_1182;
goto block_1181;
}
block_1181:
{
lean_object* x_1178; 
if (x_1177 == 0)
{
lean_ctor_set_tag(x_1176, 1);
x_1178 = x_1176;
goto block_1179;
}
else
{
lean_object* x_1180; 
x_1180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1180, 0, x_1175);
x_1178 = x_1180;
goto block_1179;
}
block_1179:
{
x_489 = x_1157;
x_490 = x_1158;
x_491 = x_1173;
x_492 = x_1160;
x_493 = x_1163;
x_494 = x_1161;
x_495 = x_1172;
x_496 = x_1164;
x_497 = x_1165;
x_498 = x_1166;
x_499 = x_1167;
x_500 = x_1168;
x_501 = x_1169;
x_502 = x_1170;
x_503 = x_1178;
goto block_515;
}
}
}
else
{
lean_object* x_1183; lean_object* x_1184; uint8_t x_1185; uint8_t x_1190; 
x_1183 = lean_ctor_get(x_1174, 0);
x_1190 = !lean_is_exclusive(x_1174);
if (x_1190 == 0)
{
x_1184 = x_1174;
x_1185 = x_1190;
goto block_1189;
}
else
{
lean_inc(x_1183);
lean_dec(x_1174);
x_1184 = lean_box(0);
x_1185 = x_1190;
goto block_1189;
}
block_1189:
{
lean_object* x_1186; 
if (x_1185 == 0)
{
lean_ctor_set_tag(x_1184, 0);
x_1186 = x_1184;
goto block_1187;
}
else
{
lean_object* x_1188; 
x_1188 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1188, 0, x_1183);
x_1186 = x_1188;
goto block_1187;
}
block_1187:
{
x_489 = x_1157;
x_490 = x_1158;
x_491 = x_1173;
x_492 = x_1160;
x_493 = x_1163;
x_494 = x_1161;
x_495 = x_1172;
x_496 = x_1164;
x_497 = x_1165;
x_498 = x_1166;
x_499 = x_1167;
x_500 = x_1168;
x_501 = x_1169;
x_502 = x_1170;
x_503 = x_1186;
goto block_515;
}
}
}
}
else
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; 
x_1191 = lean_ctor_get(x_1171, 0);
lean_inc(x_1191);
lean_dec_ref(x_1171);
x_1192 = lean_io_get_num_heartbeats();
lean_inc(x_1164);
lean_inc_ref(x_1165);
lean_inc(x_1168);
lean_inc_ref(x_1161);
lean_inc(x_2);
x_1193 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1061, x_1159, x_7, x_1161, x_1168, x_1165, x_1164);
if (lean_obj_tag(x_1193) == 0)
{
lean_object* x_1194; lean_object* x_1195; uint8_t x_1196; uint8_t x_1201; 
x_1194 = lean_ctor_get(x_1193, 0);
x_1201 = !lean_is_exclusive(x_1193);
if (x_1201 == 0)
{
x_1195 = x_1193;
x_1196 = x_1201;
goto block_1200;
}
else
{
lean_inc(x_1194);
lean_dec(x_1193);
x_1195 = lean_box(0);
x_1196 = x_1201;
goto block_1200;
}
block_1200:
{
lean_object* x_1197; 
if (x_1196 == 0)
{
lean_ctor_set_tag(x_1195, 1);
x_1197 = x_1195;
goto block_1198;
}
else
{
lean_object* x_1199; 
x_1199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1199, 0, x_1194);
x_1197 = x_1199;
goto block_1198;
}
block_1198:
{
x_465 = x_1157;
x_466 = x_1158;
x_467 = x_1160;
x_468 = x_1163;
x_469 = x_1161;
x_470 = x_1192;
x_471 = x_1191;
x_472 = x_1164;
x_473 = x_1165;
x_474 = x_1166;
x_475 = x_1167;
x_476 = x_1168;
x_477 = x_1169;
x_478 = x_1170;
x_479 = x_1197;
goto block_488;
}
}
}
else
{
lean_object* x_1202; lean_object* x_1203; uint8_t x_1204; uint8_t x_1209; 
x_1202 = lean_ctor_get(x_1193, 0);
x_1209 = !lean_is_exclusive(x_1193);
if (x_1209 == 0)
{
x_1203 = x_1193;
x_1204 = x_1209;
goto block_1208;
}
else
{
lean_inc(x_1202);
lean_dec(x_1193);
x_1203 = lean_box(0);
x_1204 = x_1209;
goto block_1208;
}
block_1208:
{
lean_object* x_1205; 
if (x_1204 == 0)
{
lean_ctor_set_tag(x_1203, 0);
x_1205 = x_1203;
goto block_1206;
}
else
{
lean_object* x_1207; 
x_1207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1207, 0, x_1202);
x_1205 = x_1207;
goto block_1206;
}
block_1206:
{
x_465 = x_1157;
x_466 = x_1158;
x_467 = x_1160;
x_468 = x_1163;
x_469 = x_1161;
x_470 = x_1192;
x_471 = x_1191;
x_472 = x_1164;
x_473 = x_1165;
x_474 = x_1166;
x_475 = x_1167;
x_476 = x_1168;
x_477 = x_1169;
x_478 = x_1170;
x_479 = x_1205;
goto block_488;
}
}
}
}
}
block_1251:
{
if (x_1227 == 0)
{
lean_object* x_1228; 
lean_dec_ref(x_1217);
lean_inc(x_1218);
lean_inc_ref(x_1219);
lean_inc(x_1224);
lean_inc_ref(x_1214);
lean_inc(x_1223);
x_1228 = lean_apply_6(x_1212, x_1223, x_1214, x_1224, x_1219, x_1218, lean_box(0));
if (lean_obj_tag(x_1228) == 0)
{
lean_object* x_1229; 
x_1229 = lean_ctor_get(x_1228, 0);
lean_inc(x_1229);
lean_dec_ref(x_1228);
if (lean_obj_tag(x_1229) == 0)
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; uint8_t x_1234; 
lean_inc(x_2);
x_1230 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1219);
x_1231 = lean_ctor_get(x_1230, 0);
lean_inc(x_1231);
lean_dec_ref(x_1230);
x_1232 = lean_nat_add(x_1061, x_1060);
lean_dec(x_1061);
x_1233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1233, 0, x_1223);
lean_ctor_set(x_1233, 1, x_7);
x_1234 = lean_unbox(x_1231);
if (x_1234 == 0)
{
lean_object* x_1235; uint8_t x_1236; 
x_1235 = l_Lean_trace_profiler;
x_1236 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1213, x_1235);
if (x_1236 == 0)
{
lean_object* x_1237; 
lean_dec(x_1231);
lean_inc(x_1218);
lean_inc_ref(x_1219);
lean_inc(x_1224);
lean_inc_ref(x_1214);
lean_inc(x_2);
x_1237 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1232, x_1221, x_1233, x_1214, x_1224, x_1219, x_1218);
x_226 = x_1218;
x_227 = x_1219;
x_228 = x_1220;
x_229 = x_1211;
x_230 = x_1222;
x_231 = x_1213;
x_232 = x_1214;
x_233 = x_1216;
x_234 = x_1224;
x_235 = x_1225;
x_236 = x_1226;
x_237 = x_1237;
goto block_240;
}
else
{
uint8_t x_1238; 
x_1238 = lean_unbox(x_1231);
lean_dec(x_1231);
x_408 = x_1238;
x_409 = x_1211;
x_410 = x_1232;
x_411 = x_1213;
x_412 = x_1214;
x_413 = x_1215;
x_414 = x_1216;
x_415 = x_1218;
x_416 = x_1233;
x_417 = x_1219;
x_418 = x_1220;
x_419 = x_1221;
x_420 = x_1222;
x_421 = x_1224;
x_422 = x_1225;
x_423 = x_1226;
goto block_463;
}
}
else
{
uint8_t x_1239; 
x_1239 = lean_unbox(x_1231);
lean_dec(x_1231);
x_408 = x_1239;
x_409 = x_1211;
x_410 = x_1232;
x_411 = x_1213;
x_412 = x_1214;
x_413 = x_1215;
x_414 = x_1216;
x_415 = x_1218;
x_416 = x_1233;
x_417 = x_1219;
x_418 = x_1220;
x_419 = x_1221;
x_420 = x_1222;
x_421 = x_1224;
x_422 = x_1225;
x_423 = x_1226;
goto block_463;
}
}
else
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; uint8_t x_1244; 
lean_dec(x_1223);
x_1240 = lean_ctor_get(x_1229, 0);
lean_inc(x_1240);
lean_dec_ref(x_1229);
lean_inc(x_2);
x_1241 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1219);
x_1242 = lean_ctor_get(x_1241, 0);
lean_inc(x_1242);
lean_dec_ref(x_1241);
x_1243 = l_List_appendTR___redArg(x_1240, x_1221);
x_1244 = lean_unbox(x_1242);
if (x_1244 == 0)
{
lean_object* x_1245; uint8_t x_1246; 
x_1245 = l_Lean_trace_profiler;
x_1246 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1213, x_1245);
if (x_1246 == 0)
{
lean_object* x_1247; 
lean_dec(x_1242);
lean_inc(x_1218);
lean_inc_ref(x_1219);
lean_inc(x_1224);
lean_inc_ref(x_1214);
lean_inc(x_2);
x_1247 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1061, x_1243, x_7, x_1214, x_1224, x_1219, x_1218);
x_226 = x_1218;
x_227 = x_1219;
x_228 = x_1220;
x_229 = x_1211;
x_230 = x_1222;
x_231 = x_1213;
x_232 = x_1214;
x_233 = x_1216;
x_234 = x_1224;
x_235 = x_1225;
x_236 = x_1226;
x_237 = x_1247;
goto block_240;
}
else
{
uint8_t x_1248; 
x_1248 = lean_unbox(x_1242);
lean_dec(x_1242);
x_1157 = x_1211;
x_1158 = x_1248;
x_1159 = x_1243;
x_1160 = x_1213;
x_1161 = x_1214;
x_1162 = x_1215;
x_1163 = x_1216;
x_1164 = x_1218;
x_1165 = x_1219;
x_1166 = x_1220;
x_1167 = x_1222;
x_1168 = x_1224;
x_1169 = x_1225;
x_1170 = x_1226;
goto block_1210;
}
}
else
{
uint8_t x_1249; 
x_1249 = lean_unbox(x_1242);
lean_dec(x_1242);
x_1157 = x_1211;
x_1158 = x_1249;
x_1159 = x_1243;
x_1160 = x_1213;
x_1161 = x_1214;
x_1162 = x_1215;
x_1163 = x_1216;
x_1164 = x_1218;
x_1165 = x_1219;
x_1166 = x_1220;
x_1167 = x_1222;
x_1168 = x_1224;
x_1169 = x_1225;
x_1170 = x_1226;
goto block_1210;
}
}
}
else
{
lean_object* x_1250; 
lean_dec(x_1223);
lean_dec(x_1221);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1250 = lean_ctor_get(x_1228, 0);
lean_inc(x_1250);
lean_dec_ref(x_1228);
x_212 = x_1218;
x_213 = x_1219;
x_214 = x_1220;
x_215 = x_1211;
x_216 = x_1222;
x_217 = x_1213;
x_218 = x_1216;
x_219 = x_1214;
x_220 = x_1224;
x_221 = x_1225;
x_222 = x_1226;
x_223 = x_1250;
goto block_225;
}
}
else
{
lean_dec(x_1223);
lean_dec(x_1221);
lean_dec_ref(x_1212);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_212 = x_1218;
x_213 = x_1219;
x_214 = x_1220;
x_215 = x_1211;
x_216 = x_1222;
x_217 = x_1213;
x_218 = x_1216;
x_219 = x_1214;
x_220 = x_1224;
x_221 = x_1225;
x_222 = x_1226;
x_223 = x_1217;
goto block_225;
}
}
block_1311:
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; uint8_t x_1270; 
x_1267 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1259);
x_1268 = lean_ctor_get(x_1267, 0);
lean_inc(x_1268);
lean_dec_ref(x_1267);
x_1269 = l_Lean_trace_profiler_useHeartbeats;
x_1270 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1256, x_1269);
if (x_1270 == 0)
{
lean_object* x_1271; lean_object* x_1272; 
lean_dec_ref(x_1252);
x_1271 = lean_io_mono_nanos_now();
lean_inc(x_1259);
lean_inc_ref(x_1260);
lean_inc(x_1264);
lean_inc_ref(x_1257);
lean_inc(x_1263);
x_1272 = lean_apply_6(x_1266, x_1263, x_1257, x_1264, x_1260, x_1259, lean_box(0));
if (lean_obj_tag(x_1272) == 0)
{
lean_object* x_1273; uint8_t x_1274; 
x_1273 = lean_ctor_get(x_1272, 0);
lean_inc(x_1273);
lean_dec_ref(x_1272);
x_1274 = lean_unbox(x_1273);
lean_dec(x_1273);
if (x_1274 == 0)
{
lean_object* x_1275; 
lean_inc_ref(x_3);
lean_inc(x_1259);
lean_inc_ref(x_1260);
lean_inc(x_1264);
lean_inc_ref(x_1257);
lean_inc(x_1263);
x_1275 = lean_apply_7(x_3, x_1263, x_1253, x_1257, x_1264, x_1260, x_1259, lean_box(0));
if (lean_obj_tag(x_1275) == 0)
{
lean_object* x_1276; 
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec_ref(x_1255);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1276 = lean_ctor_get(x_1275, 0);
lean_inc(x_1276);
lean_dec_ref(x_1275);
x_198 = x_1259;
x_199 = x_1260;
x_200 = x_1261;
x_201 = x_1254;
x_202 = x_1271;
x_203 = x_1256;
x_204 = x_1258;
x_205 = x_1257;
x_206 = x_1264;
x_207 = x_1265;
x_208 = x_1268;
x_209 = x_1276;
goto block_211;
}
else
{
lean_object* x_1277; uint8_t x_1278; 
x_1277 = lean_ctor_get(x_1275, 0);
lean_inc(x_1277);
lean_dec_ref(x_1275);
x_1278 = l_Lean_Exception_isInterrupt(x_1277);
if (x_1278 == 0)
{
uint8_t x_1279; 
lean_inc(x_1277);
x_1279 = l_Lean_Exception_isRuntime(x_1277);
x_1211 = x_1254;
x_1212 = x_1255;
x_1213 = x_1256;
x_1214 = x_1257;
x_1215 = x_1270;
x_1216 = x_1258;
x_1217 = x_1277;
x_1218 = x_1259;
x_1219 = x_1260;
x_1220 = x_1261;
x_1221 = x_1262;
x_1222 = x_1271;
x_1223 = x_1263;
x_1224 = x_1264;
x_1225 = x_1265;
x_1226 = x_1268;
x_1227 = x_1279;
goto block_1251;
}
else
{
x_1211 = x_1254;
x_1212 = x_1255;
x_1213 = x_1256;
x_1214 = x_1257;
x_1215 = x_1270;
x_1216 = x_1258;
x_1217 = x_1277;
x_1218 = x_1259;
x_1219 = x_1260;
x_1220 = x_1261;
x_1221 = x_1262;
x_1222 = x_1271;
x_1223 = x_1263;
x_1224 = x_1264;
x_1225 = x_1265;
x_1226 = x_1268;
x_1227 = x_1278;
goto block_1251;
}
}
}
else
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; uint8_t x_1284; 
lean_dec_ref(x_1255);
lean_dec_ref(x_1253);
lean_inc(x_2);
x_1280 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1260);
x_1281 = lean_ctor_get(x_1280, 0);
lean_inc(x_1281);
lean_dec_ref(x_1280);
x_1282 = lean_nat_add(x_1061, x_1060);
lean_dec(x_1061);
x_1283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1283, 0, x_1263);
lean_ctor_set(x_1283, 1, x_7);
x_1284 = lean_unbox(x_1281);
if (x_1284 == 0)
{
lean_object* x_1285; uint8_t x_1286; 
x_1285 = l_Lean_trace_profiler;
x_1286 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1256, x_1285);
if (x_1286 == 0)
{
lean_object* x_1287; 
lean_dec(x_1281);
lean_inc(x_1259);
lean_inc_ref(x_1260);
lean_inc(x_1264);
lean_inc_ref(x_1257);
lean_inc(x_2);
x_1287 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1282, x_1262, x_1283, x_1257, x_1264, x_1260, x_1259);
x_226 = x_1259;
x_227 = x_1260;
x_228 = x_1261;
x_229 = x_1254;
x_230 = x_1271;
x_231 = x_1256;
x_232 = x_1257;
x_233 = x_1258;
x_234 = x_1264;
x_235 = x_1265;
x_236 = x_1268;
x_237 = x_1287;
goto block_240;
}
else
{
uint8_t x_1288; 
x_1288 = lean_unbox(x_1281);
lean_dec(x_1281);
x_567 = x_1283;
x_568 = x_1254;
x_569 = x_1256;
x_570 = x_1257;
x_571 = x_1270;
x_572 = x_1258;
x_573 = x_1288;
x_574 = x_1259;
x_575 = x_1260;
x_576 = x_1261;
x_577 = x_1262;
x_578 = x_1271;
x_579 = x_1264;
x_580 = x_1265;
x_581 = x_1282;
x_582 = x_1268;
goto block_622;
}
}
else
{
uint8_t x_1289; 
x_1289 = lean_unbox(x_1281);
lean_dec(x_1281);
x_567 = x_1283;
x_568 = x_1254;
x_569 = x_1256;
x_570 = x_1257;
x_571 = x_1270;
x_572 = x_1258;
x_573 = x_1289;
x_574 = x_1259;
x_575 = x_1260;
x_576 = x_1261;
x_577 = x_1262;
x_578 = x_1271;
x_579 = x_1264;
x_580 = x_1265;
x_581 = x_1282;
x_582 = x_1268;
goto block_622;
}
}
}
else
{
lean_object* x_1290; 
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec_ref(x_1255);
lean_dec_ref(x_1253);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1290 = lean_ctor_get(x_1272, 0);
lean_inc(x_1290);
lean_dec_ref(x_1272);
x_212 = x_1259;
x_213 = x_1260;
x_214 = x_1261;
x_215 = x_1254;
x_216 = x_1271;
x_217 = x_1256;
x_218 = x_1258;
x_219 = x_1257;
x_220 = x_1264;
x_221 = x_1265;
x_222 = x_1268;
x_223 = x_1290;
goto block_225;
}
}
else
{
lean_object* x_1291; lean_object* x_1292; 
lean_dec_ref(x_1253);
x_1291 = lean_io_get_num_heartbeats();
lean_inc(x_1259);
lean_inc_ref(x_1260);
lean_inc(x_1264);
lean_inc_ref(x_1257);
lean_inc(x_1263);
x_1292 = lean_apply_6(x_1266, x_1263, x_1257, x_1264, x_1260, x_1259, lean_box(0));
if (lean_obj_tag(x_1292) == 0)
{
lean_object* x_1293; uint8_t x_1294; 
x_1293 = lean_ctor_get(x_1292, 0);
lean_inc(x_1293);
lean_dec_ref(x_1292);
x_1294 = lean_unbox(x_1293);
lean_dec(x_1293);
if (x_1294 == 0)
{
lean_object* x_1295; 
lean_inc_ref(x_3);
lean_inc(x_1259);
lean_inc_ref(x_1260);
lean_inc(x_1264);
lean_inc_ref(x_1257);
lean_inc(x_1263);
x_1295 = lean_apply_7(x_3, x_1263, x_1252, x_1257, x_1264, x_1260, x_1259, lean_box(0));
if (lean_obj_tag(x_1295) == 0)
{
lean_object* x_1296; 
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec_ref(x_1255);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
lean_dec_ref(x_1295);
x_131 = x_1259;
x_132 = x_1260;
x_133 = x_1291;
x_134 = x_1261;
x_135 = x_1254;
x_136 = x_1256;
x_137 = x_1258;
x_138 = x_1257;
x_139 = x_1264;
x_140 = x_1265;
x_141 = x_1268;
x_142 = x_1296;
goto block_144;
}
else
{
lean_object* x_1297; uint8_t x_1298; 
x_1297 = lean_ctor_get(x_1295, 0);
lean_inc(x_1297);
lean_dec_ref(x_1295);
x_1298 = l_Lean_Exception_isInterrupt(x_1297);
if (x_1298 == 0)
{
uint8_t x_1299; 
lean_inc(x_1297);
x_1299 = l_Lean_Exception_isRuntime(x_1297);
x_1116 = x_1291;
x_1117 = x_1254;
x_1118 = x_1255;
x_1119 = x_1256;
x_1120 = x_1257;
x_1121 = x_1270;
x_1122 = x_1258;
x_1123 = x_1259;
x_1124 = x_1260;
x_1125 = x_1261;
x_1126 = x_1297;
x_1127 = x_1262;
x_1128 = x_1263;
x_1129 = x_1264;
x_1130 = x_1265;
x_1131 = x_1268;
x_1132 = x_1299;
goto block_1156;
}
else
{
x_1116 = x_1291;
x_1117 = x_1254;
x_1118 = x_1255;
x_1119 = x_1256;
x_1120 = x_1257;
x_1121 = x_1270;
x_1122 = x_1258;
x_1123 = x_1259;
x_1124 = x_1260;
x_1125 = x_1261;
x_1126 = x_1297;
x_1127 = x_1262;
x_1128 = x_1263;
x_1129 = x_1264;
x_1130 = x_1265;
x_1131 = x_1268;
x_1132 = x_1298;
goto block_1156;
}
}
}
else
{
lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; uint8_t x_1304; 
lean_dec_ref(x_1255);
lean_dec_ref(x_1252);
lean_inc(x_2);
x_1300 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1260);
x_1301 = lean_ctor_get(x_1300, 0);
lean_inc(x_1301);
lean_dec_ref(x_1300);
x_1302 = lean_nat_add(x_1061, x_1060);
lean_dec(x_1061);
x_1303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1303, 0, x_1263);
lean_ctor_set(x_1303, 1, x_7);
x_1304 = lean_unbox(x_1301);
if (x_1304 == 0)
{
lean_object* x_1305; uint8_t x_1306; 
x_1305 = l_Lean_trace_profiler;
x_1306 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1256, x_1305);
if (x_1306 == 0)
{
lean_object* x_1307; 
lean_dec(x_1301);
lean_inc(x_1259);
lean_inc_ref(x_1260);
lean_inc(x_1264);
lean_inc_ref(x_1257);
lean_inc(x_2);
x_1307 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1302, x_1262, x_1303, x_1257, x_1264, x_1260, x_1259);
x_159 = x_1259;
x_160 = x_1260;
x_161 = x_1261;
x_162 = x_1291;
x_163 = x_1254;
x_164 = x_1256;
x_165 = x_1257;
x_166 = x_1258;
x_167 = x_1264;
x_168 = x_1265;
x_169 = x_1268;
x_170 = x_1307;
goto block_173;
}
else
{
uint8_t x_1308; 
x_1308 = lean_unbox(x_1301);
lean_dec(x_1301);
x_300 = x_1291;
x_301 = x_1254;
x_302 = x_1256;
x_303 = x_1257;
x_304 = x_1270;
x_305 = x_1258;
x_306 = x_1302;
x_307 = x_1259;
x_308 = x_1260;
x_309 = x_1261;
x_310 = x_1262;
x_311 = x_1303;
x_312 = x_1308;
x_313 = x_1264;
x_314 = x_1265;
x_315 = x_1268;
goto block_355;
}
}
else
{
uint8_t x_1309; 
x_1309 = lean_unbox(x_1301);
lean_dec(x_1301);
x_300 = x_1291;
x_301 = x_1254;
x_302 = x_1256;
x_303 = x_1257;
x_304 = x_1270;
x_305 = x_1258;
x_306 = x_1302;
x_307 = x_1259;
x_308 = x_1260;
x_309 = x_1261;
x_310 = x_1262;
x_311 = x_1303;
x_312 = x_1309;
x_313 = x_1264;
x_314 = x_1265;
x_315 = x_1268;
goto block_355;
}
}
}
else
{
lean_object* x_1310; 
lean_dec(x_1263);
lean_dec(x_1262);
lean_dec_ref(x_1255);
lean_dec_ref(x_1252);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1310 = lean_ctor_get(x_1292, 0);
lean_inc(x_1310);
lean_dec_ref(x_1292);
x_145 = x_1259;
x_146 = x_1260;
x_147 = x_1291;
x_148 = x_1261;
x_149 = x_1254;
x_150 = x_1256;
x_151 = x_1258;
x_152 = x_1257;
x_153 = x_1264;
x_154 = x_1265;
x_155 = x_1268;
x_156 = x_1310;
goto block_158;
}
}
}
block_1361:
{
lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; uint8_t x_1324; 
x_1321 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1320);
x_1322 = lean_ctor_get(x_1321, 0);
lean_inc(x_1322);
lean_dec_ref(x_1321);
x_1323 = l_Lean_trace_profiler_useHeartbeats;
x_1324 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1312, x_1323);
if (x_1324 == 0)
{
lean_object* x_1325; lean_object* x_1326; 
x_1325 = lean_io_mono_nanos_now();
lean_inc(x_1320);
lean_inc_ref(x_1315);
lean_inc(x_1316);
lean_inc_ref(x_1317);
lean_inc(x_2);
x_1326 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1061, x_1314, x_7, x_1317, x_1316, x_1315, x_1320);
if (lean_obj_tag(x_1326) == 0)
{
lean_object* x_1327; lean_object* x_1328; uint8_t x_1329; uint8_t x_1334; 
x_1327 = lean_ctor_get(x_1326, 0);
x_1334 = !lean_is_exclusive(x_1326);
if (x_1334 == 0)
{
x_1328 = x_1326;
x_1329 = x_1334;
goto block_1333;
}
else
{
lean_inc(x_1327);
lean_dec(x_1326);
x_1328 = lean_box(0);
x_1329 = x_1334;
goto block_1333;
}
block_1333:
{
lean_object* x_1330; 
if (x_1329 == 0)
{
lean_ctor_set_tag(x_1328, 1);
x_1330 = x_1328;
goto block_1331;
}
else
{
lean_object* x_1332; 
x_1332 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1332, 0, x_1327);
x_1330 = x_1332;
goto block_1331;
}
block_1331:
{
x_896 = x_1325;
x_897 = x_1312;
x_898 = x_1313;
x_899 = x_1315;
x_900 = x_1316;
x_901 = x_1317;
x_902 = x_1319;
x_903 = x_1318;
x_904 = x_1320;
x_905 = x_1322;
x_906 = x_1330;
goto block_918;
}
}
}
else
{
lean_object* x_1335; lean_object* x_1336; uint8_t x_1337; uint8_t x_1342; 
x_1335 = lean_ctor_get(x_1326, 0);
x_1342 = !lean_is_exclusive(x_1326);
if (x_1342 == 0)
{
x_1336 = x_1326;
x_1337 = x_1342;
goto block_1341;
}
else
{
lean_inc(x_1335);
lean_dec(x_1326);
x_1336 = lean_box(0);
x_1337 = x_1342;
goto block_1341;
}
block_1341:
{
lean_object* x_1338; 
if (x_1337 == 0)
{
lean_ctor_set_tag(x_1336, 0);
x_1338 = x_1336;
goto block_1339;
}
else
{
lean_object* x_1340; 
x_1340 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1340, 0, x_1335);
x_1338 = x_1340;
goto block_1339;
}
block_1339:
{
x_896 = x_1325;
x_897 = x_1312;
x_898 = x_1313;
x_899 = x_1315;
x_900 = x_1316;
x_901 = x_1317;
x_902 = x_1319;
x_903 = x_1318;
x_904 = x_1320;
x_905 = x_1322;
x_906 = x_1338;
goto block_918;
}
}
}
}
else
{
lean_object* x_1343; lean_object* x_1344; 
x_1343 = lean_io_get_num_heartbeats();
lean_inc(x_1320);
lean_inc_ref(x_1315);
lean_inc(x_1316);
lean_inc_ref(x_1317);
lean_inc(x_2);
x_1344 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1061, x_1314, x_7, x_1317, x_1316, x_1315, x_1320);
if (lean_obj_tag(x_1344) == 0)
{
lean_object* x_1345; lean_object* x_1346; uint8_t x_1347; uint8_t x_1352; 
x_1345 = lean_ctor_get(x_1344, 0);
x_1352 = !lean_is_exclusive(x_1344);
if (x_1352 == 0)
{
x_1346 = x_1344;
x_1347 = x_1352;
goto block_1351;
}
else
{
lean_inc(x_1345);
lean_dec(x_1344);
x_1346 = lean_box(0);
x_1347 = x_1352;
goto block_1351;
}
block_1351:
{
lean_object* x_1348; 
if (x_1347 == 0)
{
lean_ctor_set_tag(x_1346, 1);
x_1348 = x_1346;
goto block_1349;
}
else
{
lean_object* x_1350; 
x_1350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1350, 0, x_1345);
x_1348 = x_1350;
goto block_1349;
}
block_1349:
{
x_876 = x_1312;
x_877 = x_1313;
x_878 = x_1315;
x_879 = x_1316;
x_880 = x_1317;
x_881 = x_1343;
x_882 = x_1319;
x_883 = x_1318;
x_884 = x_1320;
x_885 = x_1322;
x_886 = x_1348;
goto block_895;
}
}
}
else
{
lean_object* x_1353; lean_object* x_1354; uint8_t x_1355; uint8_t x_1360; 
x_1353 = lean_ctor_get(x_1344, 0);
x_1360 = !lean_is_exclusive(x_1344);
if (x_1360 == 0)
{
x_1354 = x_1344;
x_1355 = x_1360;
goto block_1359;
}
else
{
lean_inc(x_1353);
lean_dec(x_1344);
x_1354 = lean_box(0);
x_1355 = x_1360;
goto block_1359;
}
block_1359:
{
lean_object* x_1356; 
if (x_1355 == 0)
{
lean_ctor_set_tag(x_1354, 0);
x_1356 = x_1354;
goto block_1357;
}
else
{
lean_object* x_1358; 
x_1358 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1358, 0, x_1353);
x_1356 = x_1358;
goto block_1357;
}
block_1357:
{
x_876 = x_1312;
x_877 = x_1313;
x_878 = x_1315;
x_879 = x_1316;
x_880 = x_1317;
x_881 = x_1343;
x_882 = x_1319;
x_883 = x_1318;
x_884 = x_1320;
x_885 = x_1322;
x_886 = x_1356;
goto block_895;
}
}
}
}
}
block_1410:
{
if (x_1371 == 0)
{
lean_object* x_1372; 
lean_dec_ref(x_1367);
lean_inc(x_1370);
lean_inc_ref(x_1363);
lean_inc(x_1364);
lean_inc_ref(x_1365);
lean_inc(x_1369);
x_1372 = lean_apply_6(x_1366, x_1369, x_1365, x_1364, x_1363, x_1370, lean_box(0));
if (lean_obj_tag(x_1372) == 0)
{
lean_object* x_1373; 
x_1373 = lean_ctor_get(x_1372, 0);
lean_inc(x_1373);
lean_dec_ref(x_1372);
if (lean_obj_tag(x_1373) == 0)
{
lean_object* x_1374; uint8_t x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1374 = lean_ctor_get(x_1363, 2);
x_1375 = lean_ctor_get_uint8(x_1374, sizeof(void*)*1);
x_1376 = lean_nat_add(x_1061, x_1060);
lean_dec(x_1061);
x_1377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1377, 0, x_1369);
lean_ctor_set(x_1377, 1, x_7);
if (x_1375 == 0)
{
x_5 = x_1376;
x_6 = x_1362;
x_7 = x_1377;
x_8 = x_1365;
x_9 = x_1364;
x_10 = x_1363;
x_11 = x_1370;
goto _start;
}
else
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; uint8_t x_1382; 
lean_inc(x_2);
x_1379 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1363);
x_1380 = lean_ctor_get(x_1379, 0);
lean_inc(x_1380);
lean_dec_ref(x_1379);
x_1381 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1382 = lean_unbox(x_1380);
if (x_1382 == 0)
{
lean_object* x_1383; uint8_t x_1384; 
x_1383 = l_Lean_trace_profiler;
x_1384 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1374, x_1383);
if (x_1384 == 0)
{
lean_dec(x_1380);
x_5 = x_1376;
x_6 = x_1362;
x_7 = x_1377;
x_8 = x_1365;
x_9 = x_1364;
x_10 = x_1363;
x_11 = x_1370;
goto _start;
}
else
{
uint8_t x_1386; 
lean_inc_ref(x_1374);
x_1386 = lean_unbox(x_1380);
lean_dec(x_1380);
x_824 = x_1362;
x_825 = x_1363;
x_826 = x_1364;
x_827 = x_1365;
x_828 = x_1386;
x_829 = x_1376;
x_830 = x_1377;
x_831 = x_1381;
x_832 = x_1368;
x_833 = x_1374;
x_834 = x_1370;
goto block_875;
}
}
else
{
uint8_t x_1387; 
lean_inc_ref(x_1374);
x_1387 = lean_unbox(x_1380);
lean_dec(x_1380);
x_824 = x_1362;
x_825 = x_1363;
x_826 = x_1364;
x_827 = x_1365;
x_828 = x_1387;
x_829 = x_1376;
x_830 = x_1377;
x_831 = x_1381;
x_832 = x_1368;
x_833 = x_1374;
x_834 = x_1370;
goto block_875;
}
}
}
else
{
lean_object* x_1388; lean_object* x_1389; uint8_t x_1390; lean_object* x_1391; 
lean_dec(x_1369);
x_1388 = lean_ctor_get(x_1363, 2);
x_1389 = lean_ctor_get(x_1373, 0);
lean_inc(x_1389);
lean_dec_ref(x_1373);
x_1390 = lean_ctor_get_uint8(x_1388, sizeof(void*)*1);
x_1391 = l_List_appendTR___redArg(x_1389, x_1362);
if (x_1390 == 0)
{
x_5 = x_1061;
x_6 = x_1391;
x_8 = x_1365;
x_9 = x_1364;
x_10 = x_1363;
x_11 = x_1370;
goto _start;
}
else
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; uint8_t x_1396; 
lean_inc(x_2);
x_1393 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1363);
x_1394 = lean_ctor_get(x_1393, 0);
lean_inc(x_1394);
lean_dec_ref(x_1393);
x_1395 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1396 = lean_unbox(x_1394);
if (x_1396 == 0)
{
lean_object* x_1397; uint8_t x_1398; 
x_1397 = l_Lean_trace_profiler;
x_1398 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1388, x_1397);
if (x_1398 == 0)
{
lean_dec(x_1394);
x_5 = x_1061;
x_6 = x_1391;
x_8 = x_1365;
x_9 = x_1364;
x_10 = x_1363;
x_11 = x_1370;
goto _start;
}
else
{
uint8_t x_1400; 
lean_inc_ref(x_1388);
x_1400 = lean_unbox(x_1394);
lean_dec(x_1394);
x_1312 = x_1388;
x_1313 = x_1395;
x_1314 = x_1391;
x_1315 = x_1363;
x_1316 = x_1364;
x_1317 = x_1365;
x_1318 = x_1368;
x_1319 = x_1400;
x_1320 = x_1370;
goto block_1361;
}
}
else
{
uint8_t x_1401; 
lean_inc_ref(x_1388);
x_1401 = lean_unbox(x_1394);
lean_dec(x_1394);
x_1312 = x_1388;
x_1313 = x_1395;
x_1314 = x_1391;
x_1315 = x_1363;
x_1316 = x_1364;
x_1317 = x_1365;
x_1318 = x_1368;
x_1319 = x_1401;
x_1320 = x_1370;
goto block_1361;
}
}
}
}
else
{
lean_object* x_1402; lean_object* x_1403; uint8_t x_1404; uint8_t x_1409; 
lean_dec(x_1370);
lean_dec(x_1369);
lean_dec_ref(x_1365);
lean_dec(x_1364);
lean_dec_ref(x_1363);
lean_dec(x_1362);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1402 = lean_ctor_get(x_1372, 0);
x_1409 = !lean_is_exclusive(x_1372);
if (x_1409 == 0)
{
x_1403 = x_1372;
x_1404 = x_1409;
goto block_1408;
}
else
{
lean_inc(x_1402);
lean_dec(x_1372);
x_1403 = lean_box(0);
x_1404 = x_1409;
goto block_1408;
}
block_1408:
{
lean_object* x_1405; 
if (x_1404 == 0)
{
x_1405 = x_1403;
goto block_1406;
}
else
{
lean_object* x_1407; 
x_1407 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1407, 0, x_1402);
x_1405 = x_1407;
goto block_1406;
}
block_1406:
{
return x_1405;
}
}
}
}
else
{
lean_dec(x_1370);
lean_dec(x_1369);
lean_dec_ref(x_1366);
lean_dec_ref(x_1365);
lean_dec(x_1364);
lean_dec_ref(x_1363);
lean_dec(x_1362);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1367;
}
}
block_1450:
{
lean_object* x_1421; 
lean_inc(x_1420);
lean_inc_ref(x_1419);
lean_inc(x_1418);
lean_inc_ref(x_1417);
lean_inc(x_1415);
x_1421 = lean_apply_6(x_1416, x_1415, x_1417, x_1418, x_1419, x_1420, lean_box(0));
if (lean_obj_tag(x_1421) == 0)
{
lean_object* x_1422; uint8_t x_1423; 
x_1422 = lean_ctor_get(x_1421, 0);
lean_inc(x_1422);
lean_dec_ref(x_1421);
x_1423 = lean_unbox(x_1422);
lean_dec(x_1422);
if (x_1423 == 0)
{
lean_object* x_1424; 
lean_inc_ref(x_3);
lean_inc(x_1420);
lean_inc_ref(x_1419);
lean_inc(x_1418);
lean_inc_ref(x_1417);
lean_inc(x_1415);
x_1424 = lean_apply_7(x_3, x_1415, x_1413, x_1417, x_1418, x_1419, x_1420, lean_box(0));
if (lean_obj_tag(x_1424) == 0)
{
lean_dec(x_1420);
lean_dec_ref(x_1419);
lean_dec(x_1418);
lean_dec_ref(x_1417);
lean_dec(x_1415);
lean_dec_ref(x_1412);
lean_dec(x_1411);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1424;
}
else
{
lean_object* x_1425; uint8_t x_1426; 
x_1425 = lean_ctor_get(x_1424, 0);
lean_inc(x_1425);
x_1426 = l_Lean_Exception_isInterrupt(x_1425);
if (x_1426 == 0)
{
uint8_t x_1427; 
x_1427 = l_Lean_Exception_isRuntime(x_1425);
x_1362 = x_1411;
x_1363 = x_1419;
x_1364 = x_1418;
x_1365 = x_1417;
x_1366 = x_1412;
x_1367 = x_1424;
x_1368 = x_1414;
x_1369 = x_1415;
x_1370 = x_1420;
x_1371 = x_1427;
goto block_1410;
}
else
{
lean_dec(x_1425);
x_1362 = x_1411;
x_1363 = x_1419;
x_1364 = x_1418;
x_1365 = x_1417;
x_1366 = x_1412;
x_1367 = x_1424;
x_1368 = x_1414;
x_1369 = x_1415;
x_1370 = x_1420;
x_1371 = x_1426;
goto block_1410;
}
}
}
else
{
lean_object* x_1428; uint8_t x_1429; lean_object* x_1430; lean_object* x_1431; 
lean_dec_ref(x_1413);
lean_dec_ref(x_1412);
x_1428 = lean_ctor_get(x_1419, 2);
x_1429 = lean_ctor_get_uint8(x_1428, sizeof(void*)*1);
x_1430 = lean_nat_add(x_1061, x_1060);
lean_dec(x_1061);
x_1431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1431, 0, x_1415);
lean_ctor_set(x_1431, 1, x_7);
if (x_1429 == 0)
{
x_5 = x_1430;
x_6 = x_1411;
x_7 = x_1431;
x_8 = x_1417;
x_9 = x_1418;
x_10 = x_1419;
x_11 = x_1420;
goto _start;
}
else
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; uint8_t x_1436; 
lean_inc(x_2);
x_1433 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1419);
x_1434 = lean_ctor_get(x_1433, 0);
lean_inc(x_1434);
lean_dec_ref(x_1433);
x_1435 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1436 = lean_unbox(x_1434);
if (x_1436 == 0)
{
lean_object* x_1437; uint8_t x_1438; 
x_1437 = l_Lean_trace_profiler;
x_1438 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1428, x_1437);
if (x_1438 == 0)
{
lean_dec(x_1434);
x_5 = x_1430;
x_6 = x_1411;
x_7 = x_1431;
x_8 = x_1417;
x_9 = x_1418;
x_10 = x_1419;
x_11 = x_1420;
goto _start;
}
else
{
uint8_t x_1440; 
lean_inc_ref(x_1428);
x_1440 = lean_unbox(x_1434);
lean_dec(x_1434);
x_962 = x_1411;
x_963 = x_1419;
x_964 = x_1418;
x_965 = x_1417;
x_966 = x_1435;
x_967 = x_1428;
x_968 = x_1414;
x_969 = x_1420;
x_970 = x_1431;
x_971 = x_1430;
x_972 = x_1440;
goto block_1013;
}
}
else
{
uint8_t x_1441; 
lean_inc_ref(x_1428);
x_1441 = lean_unbox(x_1434);
lean_dec(x_1434);
x_962 = x_1411;
x_963 = x_1419;
x_964 = x_1418;
x_965 = x_1417;
x_966 = x_1435;
x_967 = x_1428;
x_968 = x_1414;
x_969 = x_1420;
x_970 = x_1431;
x_971 = x_1430;
x_972 = x_1441;
goto block_1013;
}
}
}
}
else
{
lean_object* x_1442; lean_object* x_1443; uint8_t x_1444; uint8_t x_1449; 
lean_dec(x_1420);
lean_dec_ref(x_1419);
lean_dec(x_1418);
lean_dec_ref(x_1417);
lean_dec(x_1415);
lean_dec_ref(x_1413);
lean_dec_ref(x_1412);
lean_dec(x_1411);
lean_dec(x_1061);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1442 = lean_ctor_get(x_1421, 0);
x_1449 = !lean_is_exclusive(x_1421);
if (x_1449 == 0)
{
x_1443 = x_1421;
x_1444 = x_1449;
goto block_1448;
}
else
{
lean_inc(x_1442);
lean_dec(x_1421);
x_1443 = lean_box(0);
x_1444 = x_1449;
goto block_1448;
}
block_1448:
{
lean_object* x_1445; 
if (x_1444 == 0)
{
x_1445 = x_1443;
goto block_1446;
}
else
{
lean_object* x_1447; 
x_1447 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1447, 0, x_1442);
x_1445 = x_1447;
goto block_1446;
}
block_1446:
{
return x_1445;
}
}
}
}
block_1509:
{
if (lean_obj_tag(x_1451) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_1456; uint8_t x_1457; lean_object* x_1458; 
lean_dec(x_1061);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1456 = lean_ctor_get(x_1454, 2);
lean_inc_ref(x_1456);
x_1457 = lean_ctor_get_uint8(x_1456, sizeof(void*)*1);
x_1458 = l_List_reverse___redArg(x_7);
if (x_1457 == 0)
{
lean_object* x_1459; 
lean_dec_ref(x_1456);
lean_dec(x_1455);
lean_dec_ref(x_1454);
lean_dec(x_1453);
lean_dec_ref(x_1452);
lean_dec(x_2);
x_1459 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1459, 0, x_1458);
return x_1459;
}
else
{
lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; uint8_t x_1463; uint8_t x_1474; 
lean_inc(x_2);
x_1460 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1454);
x_1461 = lean_ctor_get(x_1460, 0);
x_1474 = !lean_is_exclusive(x_1460);
if (x_1474 == 0)
{
x_1462 = x_1460;
x_1463 = x_1474;
goto block_1473;
}
else
{
lean_inc(x_1461);
lean_dec(x_1460);
x_1462 = lean_box(0);
x_1463 = x_1474;
goto block_1473;
}
block_1473:
{
lean_object* x_1464; uint8_t x_1465; 
x_1464 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1465 = lean_unbox(x_1461);
if (x_1465 == 0)
{
lean_object* x_1466; uint8_t x_1467; 
x_1466 = l_Lean_trace_profiler;
x_1467 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1456, x_1466);
if (x_1467 == 0)
{
lean_object* x_1468; 
lean_dec(x_1461);
lean_dec_ref(x_1456);
lean_dec(x_1455);
lean_dec_ref(x_1454);
lean_dec(x_1453);
lean_dec_ref(x_1452);
lean_dec(x_2);
if (x_1463 == 0)
{
lean_ctor_set(x_1462, 0, x_1458);
x_1468 = x_1462;
goto block_1469;
}
else
{
lean_object* x_1470; 
x_1470 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1470, 0, x_1458);
x_1468 = x_1470;
goto block_1469;
}
block_1469:
{
return x_1468;
}
}
else
{
uint8_t x_1471; 
lean_del_object(x_1462);
x_1471 = lean_unbox(x_1461);
lean_dec(x_1461);
x_1015 = x_1464;
x_1016 = x_1455;
x_1017 = x_1454;
x_1018 = x_1456;
x_1019 = x_1457;
x_1020 = x_1458;
x_1021 = x_1452;
x_1022 = x_1453;
x_1023 = x_1471;
goto block_1059;
}
}
else
{
uint8_t x_1472; 
lean_del_object(x_1462);
x_1472 = lean_unbox(x_1461);
lean_dec(x_1461);
x_1015 = x_1464;
x_1016 = x_1455;
x_1017 = x_1454;
x_1018 = x_1456;
x_1019 = x_1457;
x_1020 = x_1458;
x_1021 = x_1452;
x_1022 = x_1453;
x_1023 = x_1472;
goto block_1059;
}
}
}
}
else
{
lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; uint8_t x_1479; uint8_t x_1480; 
x_1475 = lean_ctor_get(x_6, 0);
lean_inc(x_1475);
x_1476 = lean_ctor_get(x_6, 1);
lean_inc(x_1476);
lean_dec_ref(x_6);
x_1477 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_1475, x_1453);
x_1478 = lean_ctor_get(x_1477, 0);
lean_inc(x_1478);
lean_dec_ref(x_1477);
x_1479 = 1;
x_1480 = lean_unbox(x_1478);
lean_dec(x_1478);
if (x_1480 == 0)
{
lean_object* x_1481; uint8_t x_1482; lean_object* x_1483; 
x_1481 = lean_ctor_get(x_1454, 2);
x_1482 = lean_ctor_get_uint8(x_1481, sizeof(void*)*1);
lean_inc(x_7);
lean_inc(x_1061);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc(x_1476);
x_1483 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed), 13, 7);
lean_closure_set(x_1483, 0, x_1476);
lean_closure_set(x_1483, 1, x_1);
lean_closure_set(x_1483, 2, x_2);
lean_closure_set(x_1483, 3, x_3);
lean_closure_set(x_1483, 4, x_4);
lean_closure_set(x_1483, 5, x_1061);
lean_closure_set(x_1483, 6, x_7);
if (x_1482 == 0)
{
lean_inc_ref(x_246);
lean_inc_ref(x_247);
x_1411 = x_1476;
x_1412 = x_247;
x_1413 = x_1483;
x_1414 = x_1479;
x_1415 = x_1475;
x_1416 = x_246;
x_1417 = x_1452;
x_1418 = x_1453;
x_1419 = x_1454;
x_1420 = x_1455;
goto block_1450;
}
else
{
lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; uint8_t x_1488; 
lean_inc(x_2);
x_1484 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1454);
x_1485 = lean_ctor_get(x_1484, 0);
lean_inc(x_1485);
lean_dec_ref(x_1484);
lean_inc(x_1475);
x_1486 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(x_1486, 0, x_1475);
x_1487 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1488 = lean_unbox(x_1485);
if (x_1488 == 0)
{
lean_object* x_1489; uint8_t x_1490; 
x_1489 = l_Lean_trace_profiler;
x_1490 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1481, x_1489);
if (x_1490 == 0)
{
lean_dec_ref(x_1486);
lean_dec(x_1485);
lean_inc_ref(x_246);
lean_inc_ref(x_247);
x_1411 = x_1476;
x_1412 = x_247;
x_1413 = x_1483;
x_1414 = x_1479;
x_1415 = x_1475;
x_1416 = x_246;
x_1417 = x_1452;
x_1418 = x_1453;
x_1419 = x_1454;
x_1420 = x_1455;
goto block_1450;
}
else
{
uint8_t x_1491; 
lean_inc_ref(x_1481);
x_1491 = lean_unbox(x_1485);
lean_dec(x_1485);
lean_inc_ref(x_246);
lean_inc_ref(x_247);
lean_inc_ref(x_1483);
x_1252 = x_1483;
x_1253 = x_1483;
x_1254 = x_1486;
x_1255 = x_247;
x_1256 = x_1481;
x_1257 = x_1452;
x_1258 = x_1479;
x_1259 = x_1455;
x_1260 = x_1454;
x_1261 = x_1487;
x_1262 = x_1476;
x_1263 = x_1475;
x_1264 = x_1453;
x_1265 = x_1491;
x_1266 = x_246;
goto block_1311;
}
}
else
{
uint8_t x_1492; 
lean_inc_ref(x_1481);
x_1492 = lean_unbox(x_1485);
lean_dec(x_1485);
lean_inc_ref(x_246);
lean_inc_ref(x_247);
lean_inc_ref(x_1483);
x_1252 = x_1483;
x_1253 = x_1483;
x_1254 = x_1486;
x_1255 = x_247;
x_1256 = x_1481;
x_1257 = x_1452;
x_1258 = x_1479;
x_1259 = x_1455;
x_1260 = x_1454;
x_1261 = x_1487;
x_1262 = x_1476;
x_1263 = x_1475;
x_1264 = x_1453;
x_1265 = x_1492;
x_1266 = x_246;
goto block_1311;
}
}
}
else
{
lean_object* x_1493; uint8_t x_1494; lean_object* x_1495; 
x_1493 = lean_ctor_get(x_1454, 2);
x_1494 = lean_ctor_get_uint8(x_1493, sizeof(void*)*1);
x_1495 = lean_nat_add(x_1061, x_1060);
lean_dec(x_1061);
if (x_1494 == 0)
{
lean_dec(x_1475);
x_5 = x_1495;
x_6 = x_1476;
x_8 = x_1452;
x_9 = x_1453;
x_10 = x_1454;
x_11 = x_1455;
goto _start;
}
else
{
lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; uint8_t x_1501; 
lean_inc(x_2);
x_1497 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1454);
x_1498 = lean_ctor_get(x_1497, 0);
lean_inc(x_1498);
lean_dec_ref(x_1497);
x_1499 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(x_1499, 0, x_1475);
x_1500 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1501 = lean_unbox(x_1498);
if (x_1501 == 0)
{
lean_object* x_1502; uint8_t x_1503; 
x_1502 = l_Lean_trace_profiler;
x_1503 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1493, x_1502);
if (x_1503 == 0)
{
lean_dec_ref(x_1499);
lean_dec(x_1498);
x_5 = x_1495;
x_6 = x_1476;
x_8 = x_1452;
x_9 = x_1453;
x_10 = x_1454;
x_11 = x_1455;
goto _start;
}
else
{
uint8_t x_1505; 
lean_inc_ref(x_1493);
x_1505 = lean_unbox(x_1498);
lean_dec(x_1498);
x_58 = x_1455;
x_59 = x_1454;
x_60 = x_1493;
x_61 = x_1476;
x_62 = x_1499;
x_63 = x_1500;
x_64 = x_1505;
x_65 = x_1479;
x_66 = x_1452;
x_67 = x_1453;
x_68 = x_1495;
goto block_109;
}
}
else
{
uint8_t x_1506; 
lean_inc_ref(x_1493);
x_1506 = lean_unbox(x_1498);
lean_dec(x_1498);
x_58 = x_1455;
x_59 = x_1454;
x_60 = x_1493;
x_61 = x_1476;
x_62 = x_1499;
x_63 = x_1500;
x_64 = x_1506;
x_65 = x_1479;
x_66 = x_1452;
x_67 = x_1453;
x_68 = x_1495;
goto block_109;
}
}
}
}
}
else
{
lean_object* x_1507; 
lean_dec(x_6);
x_1507 = lean_ctor_get(x_1451, 0);
lean_inc(x_1507);
lean_dec_ref(x_1451);
x_5 = x_1061;
x_6 = x_1507;
x_8 = x_1452;
x_9 = x_1453;
x_10 = x_1454;
x_11 = x_1455;
goto _start;
}
}
block_1520:
{
if (lean_obj_tag(x_1510) == 0)
{
lean_object* x_1511; 
x_1511 = lean_ctor_get(x_1510, 0);
lean_inc(x_1511);
lean_dec_ref(x_1510);
x_1451 = x_1511;
x_1452 = x_8;
x_1453 = x_9;
x_1454 = x_10;
x_1455 = x_11;
goto block_1509;
}
else
{
lean_object* x_1512; lean_object* x_1513; uint8_t x_1514; uint8_t x_1519; 
lean_dec(x_1061);
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
x_1512 = lean_ctor_get(x_1510, 0);
x_1519 = !lean_is_exclusive(x_1510);
if (x_1519 == 0)
{
x_1513 = x_1510;
x_1514 = x_1519;
goto block_1518;
}
else
{
lean_inc(x_1512);
lean_dec(x_1510);
x_1513 = lean_box(0);
x_1514 = x_1519;
goto block_1518;
}
block_1518:
{
lean_object* x_1515; 
if (x_1514 == 0)
{
x_1515 = x_1513;
goto block_1516;
}
else
{
lean_object* x_1517; 
x_1517 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1517, 0, x_1512);
x_1515 = x_1517;
goto block_1516;
}
block_1516:
{
return x_1515;
}
}
}
}
}
block_33:
{
lean_object* x_25; double x_26; double x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_io_get_num_heartbeats();
x_26 = lean_float_of_nat(x_20);
x_27 = lean_float_of_nat(x_25);
x_28 = lean_box_float(x_26);
x_29 = lean_box_float(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_22, x_18, x_15, x_19, x_17, x_16, x_31, x_21, x_23, x_14, x_13);
lean_dec_ref(x_15);
return x_32;
}
block_57:
{
lean_object* x_46; double x_47; double x_48; double x_49; double x_50; double x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_io_mono_nanos_now();
x_47 = lean_float_of_nat(x_34);
x_48 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_49 = lean_float_div(x_47, x_48);
x_50 = lean_float_of_nat(x_46);
x_51 = lean_float_div(x_50, x_48);
x_52 = lean_box_float(x_49);
x_53 = lean_box_float(x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_43, x_40, x_37, x_41, x_39, x_38, x_55, x_42, x_44, x_36, x_35);
lean_dec_ref(x_37);
return x_56;
}
block_109:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_58);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l_Lean_trace_profiler_useHeartbeats;
x_72 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_60, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_io_mono_nanos_now();
lean_inc(x_58);
lean_inc_ref(x_59);
lean_inc(x_67);
lean_inc_ref(x_66);
lean_inc(x_2);
x_74 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_68, x_61, x_7, x_66, x_67, x_59, x_58);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_82; 
x_75 = lean_ctor_get(x_74, 0);
x_82 = !lean_is_exclusive(x_74);
if (x_82 == 0)
{
x_76 = x_74;
x_77 = x_82;
goto block_81;
}
else
{
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_box(0);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_77 == 0)
{
lean_ctor_set_tag(x_76, 1);
x_78 = x_76;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_78 = x_80;
goto block_79;
}
block_79:
{
x_34 = x_73;
x_35 = x_58;
x_36 = x_59;
x_37 = x_60;
x_38 = x_62;
x_39 = x_70;
x_40 = x_63;
x_41 = x_64;
x_42 = x_66;
x_43 = x_65;
x_44 = x_67;
x_45 = x_78;
goto block_57;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_90; 
x_83 = lean_ctor_get(x_74, 0);
x_90 = !lean_is_exclusive(x_74);
if (x_90 == 0)
{
x_84 = x_74;
x_85 = x_90;
goto block_89;
}
else
{
lean_inc(x_83);
lean_dec(x_74);
x_84 = lean_box(0);
x_85 = x_90;
goto block_89;
}
block_89:
{
lean_object* x_86; 
if (x_85 == 0)
{
lean_ctor_set_tag(x_84, 0);
x_86 = x_84;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_83);
x_86 = x_88;
goto block_87;
}
block_87:
{
x_34 = x_73;
x_35 = x_58;
x_36 = x_59;
x_37 = x_60;
x_38 = x_62;
x_39 = x_70;
x_40 = x_63;
x_41 = x_64;
x_42 = x_66;
x_43 = x_65;
x_44 = x_67;
x_45 = x_86;
goto block_57;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_io_get_num_heartbeats();
lean_inc(x_58);
lean_inc_ref(x_59);
lean_inc(x_67);
lean_inc_ref(x_66);
lean_inc(x_2);
x_92 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_68, x_61, x_7, x_66, x_67, x_59, x_58);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_100; 
x_93 = lean_ctor_get(x_92, 0);
x_100 = !lean_is_exclusive(x_92);
if (x_100 == 0)
{
x_94 = x_92;
x_95 = x_100;
goto block_99;
}
else
{
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_box(0);
x_95 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_96; 
if (x_95 == 0)
{
lean_ctor_set_tag(x_94, 1);
x_96 = x_94;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_96 = x_98;
goto block_97;
}
block_97:
{
x_13 = x_58;
x_14 = x_59;
x_15 = x_60;
x_16 = x_62;
x_17 = x_70;
x_18 = x_63;
x_19 = x_64;
x_20 = x_91;
x_21 = x_66;
x_22 = x_65;
x_23 = x_67;
x_24 = x_96;
goto block_33;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_108; 
x_101 = lean_ctor_get(x_92, 0);
x_108 = !lean_is_exclusive(x_92);
if (x_108 == 0)
{
x_102 = x_92;
x_103 = x_108;
goto block_107;
}
else
{
lean_inc(x_101);
lean_dec(x_92);
x_102 = lean_box(0);
x_103 = x_108;
goto block_107;
}
block_107:
{
lean_object* x_104; 
if (x_103 == 0)
{
lean_ctor_set_tag(x_102, 0);
x_104 = x_102;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_101);
x_104 = x_106;
goto block_105;
}
block_105:
{
x_13 = x_58;
x_14 = x_59;
x_15 = x_60;
x_16 = x_62;
x_17 = x_70;
x_18 = x_63;
x_19 = x_64;
x_20 = x_91;
x_21 = x_66;
x_22 = x_65;
x_23 = x_67;
x_24 = x_104;
goto block_33;
}
}
}
}
}
block_130:
{
lean_object* x_122; double x_123; double x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_io_get_num_heartbeats();
x_123 = lean_float_of_nat(x_113);
x_124 = lean_float_of_nat(x_122);
x_125 = lean_box_float(x_123);
x_126 = lean_box_float(x_124);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_121);
lean_ctor_set(x_128, 1, x_127);
x_129 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_117, x_112, x_115, x_119, x_120, x_114, x_128, x_116, x_118, x_111, x_110);
lean_dec_ref(x_115);
return x_129;
}
block_144:
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_110 = x_131;
x_111 = x_132;
x_112 = x_134;
x_113 = x_133;
x_114 = x_135;
x_115 = x_136;
x_116 = x_138;
x_117 = x_137;
x_118 = x_139;
x_119 = x_140;
x_120 = x_141;
x_121 = x_143;
goto block_130;
}
block_158:
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_110 = x_145;
x_111 = x_146;
x_112 = x_148;
x_113 = x_147;
x_114 = x_149;
x_115 = x_150;
x_116 = x_152;
x_117 = x_151;
x_118 = x_153;
x_119 = x_154;
x_120 = x_155;
x_121 = x_157;
goto block_130;
}
block_173:
{
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec_ref(x_170);
x_131 = x_159;
x_132 = x_160;
x_133 = x_162;
x_134 = x_161;
x_135 = x_163;
x_136 = x_164;
x_137 = x_166;
x_138 = x_165;
x_139 = x_167;
x_140 = x_168;
x_141 = x_169;
x_142 = x_171;
goto block_144;
}
else
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec_ref(x_170);
x_145 = x_159;
x_146 = x_160;
x_147 = x_162;
x_148 = x_161;
x_149 = x_163;
x_150 = x_164;
x_151 = x_166;
x_152 = x_165;
x_153 = x_167;
x_154 = x_168;
x_155 = x_169;
x_156 = x_172;
goto block_158;
}
}
block_197:
{
lean_object* x_186; double x_187; double x_188; double x_189; double x_190; double x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_186 = lean_io_mono_nanos_now();
x_187 = lean_float_of_nat(x_178);
x_188 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_189 = lean_float_div(x_187, x_188);
x_190 = lean_float_of_nat(x_186);
x_191 = lean_float_div(x_190, x_188);
x_192 = lean_box_float(x_189);
x_193 = lean_box_float(x_191);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_185);
lean_ctor_set(x_195, 1, x_194);
x_196 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_181, x_176, x_179, x_183, x_184, x_177, x_195, x_180, x_182, x_175, x_174);
lean_dec_ref(x_179);
return x_196;
}
block_211:
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_174 = x_198;
x_175 = x_199;
x_176 = x_200;
x_177 = x_201;
x_178 = x_202;
x_179 = x_203;
x_180 = x_205;
x_181 = x_204;
x_182 = x_206;
x_183 = x_207;
x_184 = x_208;
x_185 = x_210;
goto block_197;
}
block_225:
{
lean_object* x_224; 
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_174 = x_212;
x_175 = x_213;
x_176 = x_214;
x_177 = x_215;
x_178 = x_216;
x_179 = x_217;
x_180 = x_219;
x_181 = x_218;
x_182 = x_220;
x_183 = x_221;
x_184 = x_222;
x_185 = x_224;
goto block_197;
}
block_240:
{
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec_ref(x_237);
x_198 = x_226;
x_199 = x_227;
x_200 = x_228;
x_201 = x_229;
x_202 = x_230;
x_203 = x_231;
x_204 = x_233;
x_205 = x_232;
x_206 = x_234;
x_207 = x_235;
x_208 = x_236;
x_209 = x_238;
goto block_211;
}
else
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
lean_dec_ref(x_237);
x_212 = x_226;
x_213 = x_227;
x_214 = x_228;
x_215 = x_229;
x_216 = x_230;
x_217 = x_231;
x_218 = x_233;
x_219 = x_232;
x_220 = x_234;
x_221 = x_235;
x_222 = x_236;
x_223 = x_239;
goto block_225;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_6);
x_17 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4(x_1, x_2, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_5);
return x_17;
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12_spec__13(x_1, x_2, x_3, x_4, x_5, x_6);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__4));
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
x_22 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_24; lean_object* x_25; 
x_24 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(x_5, x_6, x_24, x_24, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_1425; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_ctor_get(x_26, 0);
x_28 = lean_ctor_get(x_26, 1);
x_1425 = !lean_is_exclusive(x_26);
if (x_1425 == 0)
{
x_29 = x_26;
x_30 = x_1425;
goto block_1424;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = x_1425;
goto block_1424;
}
block_1424:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_91 = l_List_isEmpty___redArg(x_27);
if (x_91 == 0)
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_213; uint8_t x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_286; uint8_t x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_340; uint8_t x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_396; uint8_t x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_6);
x_115 = lean_ctor_get(x_9, 2);
x_116 = lean_ctor_get_uint8(x_115, sizeof(void*)*1);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_117 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(x_117, 0, x_1);
lean_closure_set(x_117, 1, x_2);
lean_closure_set(x_117, 2, x_3);
lean_closure_set(x_117, 3, x_4);
x_118 = 1;
if (x_116 == 0)
{
x_524 = x_7;
x_525 = x_8;
x_526 = x_9;
x_527 = x_10;
goto block_561;
}
else
{
lean_object* x_562; 
lean_inc(x_2);
x_562 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; uint8_t x_599; lean_object* x_600; lean_object* x_601; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; lean_object* x_616; lean_object* x_617; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; lean_object* x_625; lean_object* x_626; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_660; lean_object* x_661; lean_object* x_662; uint8_t x_663; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; uint8_t x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; lean_object* x_689; lean_object* x_690; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; uint8_t x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; uint8_t x_725; lean_object* x_726; uint8_t x_727; lean_object* x_728; lean_object* x_729; lean_object* x_734; lean_object* x_735; lean_object* x_736; uint8_t x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_753; lean_object* x_754; lean_object* x_755; uint8_t x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_762; lean_object* x_763; lean_object* x_764; uint8_t x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; uint8_t x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; uint8_t x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; uint8_t x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; uint8_t x_805; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; uint8_t x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_826; lean_object* x_827; lean_object* x_828; uint8_t x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_836; lean_object* x_837; lean_object* x_838; uint8_t x_839; lean_object* x_840; lean_object* x_841; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; uint8_t x_850; lean_object* x_851; lean_object* x_852; uint8_t x_853; lean_object* x_854; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; uint8_t x_864; lean_object* x_865; lean_object* x_866; uint8_t x_867; lean_object* x_868; lean_object* x_869; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; uint8_t x_879; lean_object* x_880; uint8_t x_881; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; uint8_t x_912; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; uint8_t x_939; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; uint8_t x_960; lean_object* x_961; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; uint8_t x_1042; lean_object* x_1043; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; uint8_t x_1061; lean_object* x_1062; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; uint8_t x_1070; lean_object* x_1071; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; uint8_t x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; uint8_t x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; uint8_t x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; uint8_t x_1108; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; uint8_t x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; lean_object* x_1135; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; uint8_t x_1144; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; uint8_t x_1154; lean_object* x_1155; lean_object* x_1156; uint8_t x_1157; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; uint8_t x_1168; lean_object* x_1169; lean_object* x_1170; uint8_t x_1171; lean_object* x_1172; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; uint8_t x_1182; lean_object* x_1183; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; uint8_t x_1198; lean_object* x_1199; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; uint8_t x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; uint8_t x_1219; lean_object* x_1220; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; uint8_t x_1228; lean_object* x_1229; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; uint8_t x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; uint8_t x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; uint8_t x_1264; lean_object* x_1265; lean_object* x_1266; uint8_t x_1267; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; uint8_t x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; uint8_t x_1293; lean_object* x_1294; lean_object* x_1295; uint8_t x_1296; lean_object* x_1297; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; uint8_t x_1308; lean_object* x_1309; lean_object* x_1310; uint8_t x_1311; lean_object* x_1329; lean_object* x_1330; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; uint8_t x_1339; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; uint8_t x_1349; lean_object* x_1350; uint8_t x_1410; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
lean_dec_ref(x_562);
lean_inc(x_28);
lean_inc(x_27);
x_564 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(x_564, 0, x_27);
lean_closure_set(x_564, 1, x_28);
x_565 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1410 = lean_unbox(x_563);
if (x_1410 == 0)
{
lean_object* x_1411; uint8_t x_1412; 
x_1411 = l_Lean_trace_profiler;
x_1412 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_115, x_1411);
if (x_1412 == 0)
{
lean_dec_ref(x_564);
lean_dec(x_563);
x_524 = x_7;
x_525 = x_8;
x_526 = x_9;
x_527 = x_10;
goto block_561;
}
else
{
lean_inc_ref(x_115);
lean_del_object(x_29);
goto block_1409;
}
}
else
{
lean_inc_ref(x_115);
lean_del_object(x_29);
goto block_1409;
}
block_578:
{
lean_object* x_569; double x_570; double x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; 
x_569 = lean_io_get_num_heartbeats();
x_570 = lean_float_of_nat(x_567);
x_571 = lean_float_of_nat(x_569);
x_572 = lean_box_float(x_570);
x_573 = lean_box_float(x_571);
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_572);
lean_ctor_set(x_574, 1, x_573);
x_575 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_575, 0, x_568);
lean_ctor_set(x_575, 1, x_574);
x_576 = lean_unbox(x_563);
lean_dec(x_563);
x_577 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_118, x_565, x_115, x_576, x_566, x_564, x_575, x_7, x_8, x_9, x_10);
lean_dec_ref(x_115);
return x_577;
}
block_583:
{
lean_object* x_582; 
x_582 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_582, 0, x_581);
x_566 = x_579;
x_567 = x_580;
x_568 = x_582;
goto block_578;
}
block_588:
{
lean_object* x_587; 
x_587 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_587, 0, x_586);
x_566 = x_584;
x_567 = x_585;
x_568 = x_587;
goto block_578;
}
block_594:
{
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; 
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
lean_dec_ref(x_591);
x_584 = x_589;
x_585 = x_590;
x_586 = x_592;
goto block_588;
}
else
{
lean_object* x_593; 
x_593 = lean_ctor_get(x_591, 0);
lean_inc(x_593);
lean_dec_ref(x_591);
x_579 = x_589;
x_580 = x_590;
x_581 = x_593;
goto block_583;
}
}
block_610:
{
lean_object* x_602; double x_603; double x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_602 = lean_io_get_num_heartbeats();
x_603 = lean_float_of_nat(x_595);
x_604 = lean_float_of_nat(x_602);
x_605 = lean_box_float(x_603);
x_606 = lean_box_float(x_604);
x_607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_607, 0, x_605);
lean_ctor_set(x_607, 1, x_606);
x_608 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_608, 0, x_601);
lean_ctor_set(x_608, 1, x_607);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_609 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_118, x_565, x_115, x_599, x_600, x_597, x_608, x_7, x_8, x_9, x_10);
x_589 = x_596;
x_590 = x_598;
x_591 = x_609;
goto block_594;
}
block_619:
{
lean_object* x_618; 
x_618 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_618, 0, x_617);
x_595 = x_611;
x_596 = x_612;
x_597 = x_613;
x_598 = x_614;
x_599 = x_615;
x_600 = x_616;
x_601 = x_618;
goto block_610;
}
block_628:
{
lean_object* x_627; 
x_627 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_627, 0, x_626);
x_595 = x_620;
x_596 = x_621;
x_597 = x_622;
x_598 = x_623;
x_599 = x_624;
x_600 = x_625;
x_601 = x_627;
goto block_610;
}
block_640:
{
lean_object* x_638; lean_object* x_639; 
x_638 = l_List_appendTR___redArg(x_635, x_633);
x_639 = l_List_appendTR___redArg(x_638, x_637);
x_620 = x_629;
x_621 = x_630;
x_622 = x_631;
x_623 = x_632;
x_624 = x_634;
x_625 = x_636;
x_626 = x_639;
goto block_628;
}
block_652:
{
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_650; 
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
lean_dec_ref(x_649);
x_629 = x_641;
x_630 = x_642;
x_631 = x_643;
x_632 = x_644;
x_633 = x_645;
x_634 = x_646;
x_635 = x_647;
x_636 = x_648;
x_637 = x_650;
goto block_640;
}
else
{
lean_object* x_651; 
lean_dec(x_647);
lean_dec(x_645);
x_651 = lean_ctor_get(x_649, 0);
lean_inc(x_651);
lean_dec_ref(x_649);
x_611 = x_641;
x_612 = x_642;
x_613 = x_643;
x_614 = x_644;
x_615 = x_646;
x_616 = x_648;
x_617 = x_651;
goto block_619;
}
}
block_666:
{
if (x_663 == 0)
{
lean_object* x_664; 
lean_dec_ref(x_658);
x_664 = l_Lean_Meta_SavedState_restore___redArg(x_654, x_8, x_10);
lean_dec_ref(x_654);
if (lean_obj_tag(x_664) == 0)
{
lean_dec_ref(x_664);
x_629 = x_653;
x_630 = x_655;
x_631 = x_656;
x_632 = x_657;
x_633 = x_659;
x_634 = x_660;
x_635 = x_661;
x_636 = x_662;
x_637 = x_28;
goto block_640;
}
else
{
lean_object* x_665; 
lean_dec(x_661);
lean_dec(x_659);
lean_dec(x_28);
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
lean_dec_ref(x_664);
x_611 = x_653;
x_612 = x_655;
x_613 = x_656;
x_614 = x_657;
x_615 = x_660;
x_616 = x_662;
x_617 = x_665;
goto block_619;
}
}
else
{
lean_dec_ref(x_654);
lean_dec(x_28);
x_641 = x_653;
x_642 = x_655;
x_643 = x_656;
x_644 = x_657;
x_645 = x_659;
x_646 = x_660;
x_647 = x_661;
x_648 = x_662;
x_649 = x_658;
goto block_652;
}
}
block_683:
{
lean_object* x_676; 
x_676 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
lean_dec_ref(x_676);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_28);
lean_inc(x_2);
x_678 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_674, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_678) == 0)
{
lean_dec(x_677);
lean_dec(x_28);
x_641 = x_667;
x_642 = x_668;
x_643 = x_669;
x_644 = x_670;
x_645 = x_671;
x_646 = x_672;
x_647 = x_673;
x_648 = x_675;
x_649 = x_678;
goto block_652;
}
else
{
lean_object* x_679; uint8_t x_680; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = l_Lean_Exception_isInterrupt(x_679);
if (x_680 == 0)
{
uint8_t x_681; 
x_681 = l_Lean_Exception_isRuntime(x_679);
x_653 = x_667;
x_654 = x_677;
x_655 = x_668;
x_656 = x_669;
x_657 = x_670;
x_658 = x_678;
x_659 = x_671;
x_660 = x_672;
x_661 = x_673;
x_662 = x_675;
x_663 = x_681;
goto block_666;
}
else
{
lean_dec(x_679);
x_653 = x_667;
x_654 = x_677;
x_655 = x_668;
x_656 = x_669;
x_657 = x_670;
x_658 = x_678;
x_659 = x_671;
x_660 = x_672;
x_661 = x_673;
x_662 = x_675;
x_663 = x_680;
goto block_666;
}
}
}
else
{
lean_object* x_682; 
lean_dec(x_674);
lean_dec(x_673);
lean_dec(x_671);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_682 = lean_ctor_get(x_676, 0);
lean_inc(x_682);
lean_dec_ref(x_676);
x_611 = x_667;
x_612 = x_668;
x_613 = x_669;
x_614 = x_670;
x_615 = x_672;
x_616 = x_675;
x_617 = x_682;
goto block_619;
}
}
block_693:
{
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
lean_dec_ref(x_690);
x_620 = x_684;
x_621 = x_685;
x_622 = x_686;
x_623 = x_687;
x_624 = x_688;
x_625 = x_689;
x_626 = x_691;
goto block_628;
}
else
{
lean_object* x_692; 
x_692 = lean_ctor_get(x_690, 0);
lean_inc(x_692);
lean_dec_ref(x_690);
x_611 = x_684;
x_612 = x_685;
x_613 = x_686;
x_614 = x_687;
x_615 = x_688;
x_616 = x_689;
x_617 = x_692;
goto block_619;
}
}
block_705:
{
lean_object* x_702; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_702 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_700, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_702) == 0)
{
lean_object* x_703; lean_object* x_704; 
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
lean_dec_ref(x_702);
x_704 = l_List_appendTR___redArg(x_699, x_703);
x_620 = x_694;
x_621 = x_695;
x_622 = x_696;
x_623 = x_697;
x_624 = x_698;
x_625 = x_701;
x_626 = x_704;
goto block_628;
}
else
{
lean_dec(x_699);
x_684 = x_694;
x_685 = x_695;
x_686 = x_696;
x_687 = x_697;
x_688 = x_698;
x_689 = x_701;
x_690 = x_702;
goto block_693;
}
}
block_719:
{
uint8_t x_716; 
x_716 = l_List_isEmpty___redArg(x_710);
lean_dec(x_710);
if (x_716 == 0)
{
if (x_715 == 0)
{
x_694 = x_706;
x_695 = x_707;
x_696 = x_708;
x_697 = x_709;
x_698 = x_711;
x_699 = x_713;
x_700 = x_712;
x_701 = x_714;
goto block_705;
}
else
{
lean_object* x_717; lean_object* x_718; 
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_717 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_718 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_717, x_7, x_8, x_9, x_10);
x_684 = x_706;
x_685 = x_707;
x_686 = x_708;
x_687 = x_709;
x_688 = x_711;
x_689 = x_714;
x_690 = x_718;
goto block_693;
}
}
else
{
x_694 = x_706;
x_695 = x_707;
x_696 = x_708;
x_697 = x_709;
x_698 = x_711;
x_699 = x_713;
x_700 = x_712;
x_701 = x_714;
goto block_705;
}
}
block_733:
{
uint8_t x_730; lean_object* x_731; 
x_730 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_726);
x_731 = l_List_appendTR___redArg(x_729, x_726);
if (x_730 == 0)
{
x_706 = x_720;
x_707 = x_721;
x_708 = x_722;
x_709 = x_723;
x_710 = x_724;
x_711 = x_725;
x_712 = x_731;
x_713 = x_726;
x_714 = x_728;
x_715 = x_727;
goto block_719;
}
else
{
uint8_t x_732; 
x_732 = l_List_isEmpty___redArg(x_726);
if (x_732 == 0)
{
x_667 = x_720;
x_668 = x_721;
x_669 = x_722;
x_670 = x_723;
x_671 = x_724;
x_672 = x_725;
x_673 = x_726;
x_674 = x_731;
x_675 = x_728;
goto block_683;
}
else
{
if (x_91 == 0)
{
x_706 = x_720;
x_707 = x_721;
x_708 = x_722;
x_709 = x_723;
x_710 = x_724;
x_711 = x_725;
x_712 = x_731;
x_713 = x_726;
x_714 = x_728;
x_715 = x_727;
goto block_719;
}
else
{
x_667 = x_720;
x_668 = x_721;
x_669 = x_722;
x_670 = x_723;
x_671 = x_724;
x_672 = x_725;
x_673 = x_726;
x_674 = x_731;
x_675 = x_728;
goto block_683;
}
}
}
}
block_752:
{
lean_object* x_741; double x_742; double x_743; double x_744; double x_745; double x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_741 = lean_io_mono_nanos_now();
x_742 = lean_float_of_nat(x_738);
x_743 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_744 = lean_float_div(x_742, x_743);
x_745 = lean_float_of_nat(x_741);
x_746 = lean_float_div(x_745, x_743);
x_747 = lean_box_float(x_744);
x_748 = lean_box_float(x_746);
x_749 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_749, 0, x_747);
lean_ctor_set(x_749, 1, x_748);
x_750 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_750, 0, x_740);
lean_ctor_set(x_750, 1, x_749);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_751 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_118, x_565, x_115, x_737, x_739, x_735, x_750, x_7, x_8, x_9, x_10);
x_589 = x_734;
x_590 = x_736;
x_591 = x_751;
goto block_594;
}
block_761:
{
lean_object* x_760; 
x_760 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_760, 0, x_759);
x_734 = x_753;
x_735 = x_754;
x_736 = x_755;
x_737 = x_756;
x_738 = x_757;
x_739 = x_758;
x_740 = x_760;
goto block_752;
}
block_770:
{
lean_object* x_769; 
x_769 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_769, 0, x_768);
x_734 = x_762;
x_735 = x_763;
x_736 = x_764;
x_737 = x_765;
x_738 = x_766;
x_739 = x_767;
x_740 = x_769;
goto block_752;
}
block_782:
{
lean_object* x_780; lean_object* x_781; 
x_780 = l_List_appendTR___redArg(x_777, x_774);
x_781 = l_List_appendTR___redArg(x_780, x_779);
x_762 = x_771;
x_763 = x_772;
x_764 = x_773;
x_765 = x_775;
x_766 = x_776;
x_767 = x_778;
x_768 = x_781;
goto block_770;
}
block_794:
{
if (lean_obj_tag(x_791) == 0)
{
lean_object* x_792; 
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
lean_dec_ref(x_791);
x_771 = x_783;
x_772 = x_784;
x_773 = x_785;
x_774 = x_786;
x_775 = x_787;
x_776 = x_788;
x_777 = x_789;
x_778 = x_790;
x_779 = x_792;
goto block_782;
}
else
{
lean_object* x_793; 
lean_dec(x_789);
lean_dec(x_786);
x_793 = lean_ctor_get(x_791, 0);
lean_inc(x_793);
lean_dec_ref(x_791);
x_753 = x_783;
x_754 = x_784;
x_755 = x_785;
x_756 = x_787;
x_757 = x_788;
x_758 = x_790;
x_759 = x_793;
goto block_761;
}
}
block_808:
{
if (x_805 == 0)
{
lean_object* x_806; 
lean_dec_ref(x_803);
x_806 = l_Lean_Meta_SavedState_restore___redArg(x_802, x_8, x_10);
lean_dec_ref(x_802);
if (lean_obj_tag(x_806) == 0)
{
lean_dec_ref(x_806);
x_771 = x_795;
x_772 = x_796;
x_773 = x_797;
x_774 = x_798;
x_775 = x_799;
x_776 = x_800;
x_777 = x_801;
x_778 = x_804;
x_779 = x_28;
goto block_782;
}
else
{
lean_object* x_807; 
lean_dec(x_801);
lean_dec(x_798);
lean_dec(x_28);
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
lean_dec_ref(x_806);
x_753 = x_795;
x_754 = x_796;
x_755 = x_797;
x_756 = x_799;
x_757 = x_800;
x_758 = x_804;
x_759 = x_807;
goto block_761;
}
}
else
{
lean_dec_ref(x_802);
lean_dec(x_28);
x_783 = x_795;
x_784 = x_796;
x_785 = x_797;
x_786 = x_798;
x_787 = x_799;
x_788 = x_800;
x_789 = x_801;
x_790 = x_804;
x_791 = x_803;
goto block_794;
}
}
block_825:
{
lean_object* x_818; 
x_818 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_818) == 0)
{
lean_object* x_819; lean_object* x_820; 
x_819 = lean_ctor_get(x_818, 0);
lean_inc(x_819);
lean_dec_ref(x_818);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_28);
lean_inc(x_2);
x_820 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_810, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_820) == 0)
{
lean_dec(x_819);
lean_dec(x_28);
x_783 = x_809;
x_784 = x_811;
x_785 = x_812;
x_786 = x_813;
x_787 = x_814;
x_788 = x_815;
x_789 = x_816;
x_790 = x_817;
x_791 = x_820;
goto block_794;
}
else
{
lean_object* x_821; uint8_t x_822; 
x_821 = lean_ctor_get(x_820, 0);
lean_inc(x_821);
x_822 = l_Lean_Exception_isInterrupt(x_821);
if (x_822 == 0)
{
uint8_t x_823; 
x_823 = l_Lean_Exception_isRuntime(x_821);
x_795 = x_809;
x_796 = x_811;
x_797 = x_812;
x_798 = x_813;
x_799 = x_814;
x_800 = x_815;
x_801 = x_816;
x_802 = x_819;
x_803 = x_820;
x_804 = x_817;
x_805 = x_823;
goto block_808;
}
else
{
lean_dec(x_821);
x_795 = x_809;
x_796 = x_811;
x_797 = x_812;
x_798 = x_813;
x_799 = x_814;
x_800 = x_815;
x_801 = x_816;
x_802 = x_819;
x_803 = x_820;
x_804 = x_817;
x_805 = x_822;
goto block_808;
}
}
}
else
{
lean_object* x_824; 
lean_dec(x_816);
lean_dec(x_813);
lean_dec(x_810);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_824 = lean_ctor_get(x_818, 0);
lean_inc(x_824);
lean_dec_ref(x_818);
x_753 = x_809;
x_754 = x_811;
x_755 = x_812;
x_756 = x_814;
x_757 = x_815;
x_758 = x_817;
x_759 = x_824;
goto block_761;
}
}
block_835:
{
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; 
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
lean_dec_ref(x_832);
x_762 = x_826;
x_763 = x_827;
x_764 = x_828;
x_765 = x_829;
x_766 = x_830;
x_767 = x_831;
x_768 = x_833;
goto block_770;
}
else
{
lean_object* x_834; 
x_834 = lean_ctor_get(x_832, 0);
lean_inc(x_834);
lean_dec_ref(x_832);
x_753 = x_826;
x_754 = x_827;
x_755 = x_828;
x_756 = x_829;
x_757 = x_830;
x_758 = x_831;
x_759 = x_834;
goto block_761;
}
}
block_844:
{
lean_object* x_842; lean_object* x_843; 
x_842 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_843 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_842, x_7, x_8, x_9, x_10);
x_826 = x_836;
x_827 = x_837;
x_828 = x_838;
x_829 = x_839;
x_830 = x_840;
x_831 = x_841;
x_832 = x_843;
goto block_835;
}
block_859:
{
uint8_t x_855; 
x_855 = l_List_isEmpty___redArg(x_849);
lean_dec(x_849);
if (x_855 == 0)
{
lean_dec(x_852);
lean_dec(x_845);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_836 = x_846;
x_837 = x_847;
x_838 = x_848;
x_839 = x_850;
x_840 = x_851;
x_841 = x_854;
goto block_844;
}
else
{
if (x_853 == 0)
{
lean_object* x_856; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_856 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_845, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_856) == 0)
{
lean_object* x_857; lean_object* x_858; 
x_857 = lean_ctor_get(x_856, 0);
lean_inc(x_857);
lean_dec_ref(x_856);
x_858 = l_List_appendTR___redArg(x_852, x_857);
x_762 = x_846;
x_763 = x_847;
x_764 = x_848;
x_765 = x_850;
x_766 = x_851;
x_767 = x_854;
x_768 = x_858;
goto block_770;
}
else
{
lean_dec(x_852);
x_826 = x_846;
x_827 = x_847;
x_828 = x_848;
x_829 = x_850;
x_830 = x_851;
x_831 = x_854;
x_832 = x_856;
goto block_835;
}
}
else
{
lean_dec(x_852);
lean_dec(x_845);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_836 = x_846;
x_837 = x_847;
x_838 = x_848;
x_839 = x_850;
x_840 = x_851;
x_841 = x_854;
goto block_844;
}
}
}
block_873:
{
uint8_t x_870; lean_object* x_871; 
x_870 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_866);
x_871 = l_List_appendTR___redArg(x_869, x_866);
if (x_870 == 0)
{
x_845 = x_871;
x_846 = x_860;
x_847 = x_861;
x_848 = x_862;
x_849 = x_863;
x_850 = x_864;
x_851 = x_865;
x_852 = x_866;
x_853 = x_867;
x_854 = x_868;
goto block_859;
}
else
{
uint8_t x_872; 
x_872 = l_List_isEmpty___redArg(x_866);
if (x_872 == 0)
{
x_809 = x_860;
x_810 = x_871;
x_811 = x_861;
x_812 = x_862;
x_813 = x_863;
x_814 = x_864;
x_815 = x_865;
x_816 = x_866;
x_817 = x_868;
goto block_825;
}
else
{
if (x_867 == 0)
{
x_845 = x_871;
x_846 = x_860;
x_847 = x_861;
x_848 = x_862;
x_849 = x_863;
x_850 = x_864;
x_851 = x_865;
x_852 = x_866;
x_853 = x_867;
x_854 = x_868;
goto block_859;
}
else
{
x_809 = x_860;
x_810 = x_871;
x_811 = x_861;
x_812 = x_862;
x_813 = x_863;
x_814 = x_864;
x_815 = x_865;
x_816 = x_866;
x_817 = x_868;
goto block_825;
}
}
}
}
block_898:
{
lean_object* x_882; 
x_882 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_882) == 0)
{
if (x_881 == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; 
x_883 = lean_ctor_get(x_882, 0);
lean_inc(x_883);
lean_dec_ref(x_882);
x_884 = lean_io_mono_nanos_now();
x_885 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_881, x_91, x_5, x_876, x_8);
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_886; lean_object* x_887; 
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
lean_dec_ref(x_885);
x_887 = l_List_reverse___redArg(x_886);
x_860 = x_874;
x_861 = x_875;
x_862 = x_877;
x_863 = x_878;
x_864 = x_879;
x_865 = x_884;
x_866 = x_880;
x_867 = x_881;
x_868 = x_883;
x_869 = x_887;
goto block_873;
}
else
{
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_888; 
x_888 = lean_ctor_get(x_885, 0);
lean_inc(x_888);
lean_dec_ref(x_885);
x_860 = x_874;
x_861 = x_875;
x_862 = x_877;
x_863 = x_878;
x_864 = x_879;
x_865 = x_884;
x_866 = x_880;
x_867 = x_881;
x_868 = x_883;
x_869 = x_888;
goto block_873;
}
else
{
lean_object* x_889; 
lean_dec(x_880);
lean_dec(x_878);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_889 = lean_ctor_get(x_885, 0);
lean_inc(x_889);
lean_dec_ref(x_885);
x_753 = x_874;
x_754 = x_875;
x_755 = x_877;
x_756 = x_879;
x_757 = x_884;
x_758 = x_883;
x_759 = x_889;
goto block_761;
}
}
}
else
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_890 = lean_ctor_get(x_882, 0);
lean_inc(x_890);
lean_dec_ref(x_882);
x_891 = lean_io_get_num_heartbeats();
x_892 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_881, x_91, x_5, x_876, x_8);
if (lean_obj_tag(x_892) == 0)
{
lean_object* x_893; lean_object* x_894; 
x_893 = lean_ctor_get(x_892, 0);
lean_inc(x_893);
lean_dec_ref(x_892);
x_894 = l_List_reverse___redArg(x_893);
x_720 = x_891;
x_721 = x_874;
x_722 = x_875;
x_723 = x_877;
x_724 = x_878;
x_725 = x_879;
x_726 = x_880;
x_727 = x_881;
x_728 = x_890;
x_729 = x_894;
goto block_733;
}
else
{
if (lean_obj_tag(x_892) == 0)
{
lean_object* x_895; 
x_895 = lean_ctor_get(x_892, 0);
lean_inc(x_895);
lean_dec_ref(x_892);
x_720 = x_891;
x_721 = x_874;
x_722 = x_875;
x_723 = x_877;
x_724 = x_878;
x_725 = x_879;
x_726 = x_880;
x_727 = x_881;
x_728 = x_890;
x_729 = x_895;
goto block_733;
}
else
{
lean_object* x_896; 
lean_dec(x_880);
lean_dec(x_878);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_896 = lean_ctor_get(x_892, 0);
lean_inc(x_896);
lean_dec_ref(x_892);
x_611 = x_891;
x_612 = x_874;
x_613 = x_875;
x_614 = x_877;
x_615 = x_879;
x_616 = x_890;
x_617 = x_896;
goto block_619;
}
}
}
}
else
{
lean_object* x_897; 
lean_dec(x_880);
lean_dec(x_878);
lean_dec(x_876);
lean_dec_ref(x_875);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_897 = lean_ctor_get(x_882, 0);
lean_inc(x_897);
lean_dec_ref(x_882);
x_579 = x_874;
x_580 = x_877;
x_581 = x_897;
goto block_583;
}
}
block_906:
{
lean_object* x_903; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_903 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_899, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; lean_object* x_905; 
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
lean_dec_ref(x_903);
x_905 = l_List_appendTR___redArg(x_902, x_904);
x_584 = x_900;
x_585 = x_901;
x_586 = x_905;
goto block_588;
}
else
{
lean_dec(x_902);
x_589 = x_900;
x_590 = x_901;
x_591 = x_903;
goto block_594;
}
}
block_916:
{
uint8_t x_913; 
x_913 = l_List_isEmpty___redArg(x_910);
lean_dec(x_910);
if (x_913 == 0)
{
if (x_912 == 0)
{
x_899 = x_907;
x_900 = x_908;
x_901 = x_909;
x_902 = x_911;
goto block_906;
}
else
{
lean_object* x_914; lean_object* x_915; 
lean_dec(x_911);
lean_dec(x_907);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_914 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_915 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_914, x_7, x_8, x_9, x_10);
x_589 = x_908;
x_590 = x_909;
x_591 = x_915;
goto block_594;
}
}
else
{
x_899 = x_907;
x_900 = x_908;
x_901 = x_909;
x_902 = x_911;
goto block_906;
}
}
block_924:
{
lean_object* x_922; lean_object* x_923; 
x_922 = l_List_appendTR___redArg(x_920, x_919);
x_923 = l_List_appendTR___redArg(x_922, x_921);
x_584 = x_917;
x_585 = x_918;
x_586 = x_923;
goto block_588;
}
block_932:
{
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; 
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
lean_dec_ref(x_929);
x_917 = x_925;
x_918 = x_926;
x_919 = x_927;
x_920 = x_928;
x_921 = x_930;
goto block_924;
}
else
{
lean_object* x_931; 
lean_dec(x_928);
lean_dec(x_927);
x_931 = lean_ctor_get(x_929, 0);
lean_inc(x_931);
lean_dec_ref(x_929);
x_579 = x_925;
x_580 = x_926;
x_581 = x_931;
goto block_583;
}
}
block_942:
{
if (x_939 == 0)
{
lean_object* x_940; 
lean_dec_ref(x_937);
x_940 = l_Lean_Meta_SavedState_restore___redArg(x_933, x_8, x_10);
lean_dec_ref(x_933);
if (lean_obj_tag(x_940) == 0)
{
lean_dec_ref(x_940);
x_917 = x_934;
x_918 = x_935;
x_919 = x_936;
x_920 = x_938;
x_921 = x_28;
goto block_924;
}
else
{
lean_object* x_941; 
lean_dec(x_938);
lean_dec(x_936);
lean_dec(x_28);
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
lean_dec_ref(x_940);
x_579 = x_934;
x_580 = x_935;
x_581 = x_941;
goto block_583;
}
}
else
{
lean_dec_ref(x_933);
lean_dec(x_28);
x_925 = x_934;
x_926 = x_935;
x_927 = x_936;
x_928 = x_938;
x_929 = x_937;
goto block_932;
}
}
block_955:
{
lean_object* x_948; 
x_948 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_948) == 0)
{
lean_object* x_949; lean_object* x_950; 
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
lean_dec_ref(x_948);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_28);
lean_inc(x_2);
x_950 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_943, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_950) == 0)
{
lean_dec(x_949);
lean_dec(x_28);
x_925 = x_944;
x_926 = x_945;
x_927 = x_946;
x_928 = x_947;
x_929 = x_950;
goto block_932;
}
else
{
lean_object* x_951; uint8_t x_952; 
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
x_952 = l_Lean_Exception_isInterrupt(x_951);
if (x_952 == 0)
{
uint8_t x_953; 
x_953 = l_Lean_Exception_isRuntime(x_951);
x_933 = x_949;
x_934 = x_944;
x_935 = x_945;
x_936 = x_946;
x_937 = x_950;
x_938 = x_947;
x_939 = x_953;
goto block_942;
}
else
{
lean_dec(x_951);
x_933 = x_949;
x_934 = x_944;
x_935 = x_945;
x_936 = x_946;
x_937 = x_950;
x_938 = x_947;
x_939 = x_952;
goto block_942;
}
}
}
else
{
lean_object* x_954; 
lean_dec(x_947);
lean_dec(x_946);
lean_dec(x_943);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_954 = lean_ctor_get(x_948, 0);
lean_inc(x_954);
lean_dec_ref(x_948);
x_579 = x_944;
x_580 = x_945;
x_581 = x_954;
goto block_583;
}
}
block_965:
{
uint8_t x_962; lean_object* x_963; 
x_962 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_959);
x_963 = l_List_appendTR___redArg(x_961, x_959);
if (x_962 == 0)
{
x_907 = x_963;
x_908 = x_956;
x_909 = x_957;
x_910 = x_958;
x_911 = x_959;
x_912 = x_960;
goto block_916;
}
else
{
uint8_t x_964; 
x_964 = l_List_isEmpty___redArg(x_959);
if (x_964 == 0)
{
x_943 = x_963;
x_944 = x_956;
x_945 = x_957;
x_946 = x_958;
x_947 = x_959;
goto block_955;
}
else
{
if (x_91 == 0)
{
x_907 = x_963;
x_908 = x_956;
x_909 = x_957;
x_910 = x_958;
x_911 = x_959;
x_912 = x_960;
goto block_916;
}
else
{
x_943 = x_963;
x_944 = x_956;
x_945 = x_957;
x_946 = x_958;
x_947 = x_959;
goto block_955;
}
}
}
}
block_981:
{
lean_object* x_969; double x_970; double x_971; double x_972; double x_973; double x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; uint8_t x_979; lean_object* x_980; 
x_969 = lean_io_mono_nanos_now();
x_970 = lean_float_of_nat(x_967);
x_971 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_972 = lean_float_div(x_970, x_971);
x_973 = lean_float_of_nat(x_969);
x_974 = lean_float_div(x_973, x_971);
x_975 = lean_box_float(x_972);
x_976 = lean_box_float(x_974);
x_977 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_977, 0, x_975);
lean_ctor_set(x_977, 1, x_976);
x_978 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_978, 0, x_968);
lean_ctor_set(x_978, 1, x_977);
x_979 = lean_unbox(x_563);
lean_dec(x_563);
x_980 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_118, x_565, x_115, x_979, x_966, x_564, x_978, x_7, x_8, x_9, x_10);
lean_dec_ref(x_115);
return x_980;
}
block_986:
{
lean_object* x_985; 
x_985 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_985, 0, x_984);
x_966 = x_982;
x_967 = x_983;
x_968 = x_985;
goto block_981;
}
block_994:
{
lean_object* x_992; lean_object* x_993; 
x_992 = l_List_appendTR___redArg(x_990, x_989);
x_993 = l_List_appendTR___redArg(x_992, x_991);
x_982 = x_987;
x_983 = x_988;
x_984 = x_993;
goto block_986;
}
block_999:
{
lean_object* x_998; 
x_998 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_998, 0, x_997);
x_966 = x_995;
x_967 = x_996;
x_968 = x_998;
goto block_981;
}
block_1007:
{
if (lean_obj_tag(x_1004) == 0)
{
lean_object* x_1005; 
x_1005 = lean_ctor_get(x_1004, 0);
lean_inc(x_1005);
lean_dec_ref(x_1004);
x_987 = x_1000;
x_988 = x_1001;
x_989 = x_1003;
x_990 = x_1002;
x_991 = x_1005;
goto block_994;
}
else
{
lean_object* x_1006; 
lean_dec(x_1003);
lean_dec(x_1002);
x_1006 = lean_ctor_get(x_1004, 0);
lean_inc(x_1006);
lean_dec_ref(x_1004);
x_995 = x_1000;
x_996 = x_1001;
x_997 = x_1006;
goto block_999;
}
}
block_1017:
{
if (x_1014 == 0)
{
lean_object* x_1015; 
lean_dec_ref(x_1010);
x_1015 = l_Lean_Meta_SavedState_restore___redArg(x_1013, x_8, x_10);
lean_dec_ref(x_1013);
if (lean_obj_tag(x_1015) == 0)
{
lean_dec_ref(x_1015);
x_987 = x_1008;
x_988 = x_1009;
x_989 = x_1012;
x_990 = x_1011;
x_991 = x_28;
goto block_994;
}
else
{
lean_object* x_1016; 
lean_dec(x_1012);
lean_dec(x_1011);
lean_dec(x_28);
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
lean_dec_ref(x_1015);
x_995 = x_1008;
x_996 = x_1009;
x_997 = x_1016;
goto block_999;
}
}
else
{
lean_dec_ref(x_1013);
lean_dec(x_28);
x_1000 = x_1008;
x_1001 = x_1009;
x_1002 = x_1011;
x_1003 = x_1012;
x_1004 = x_1010;
goto block_1007;
}
}
block_1030:
{
lean_object* x_1023; 
x_1023 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1023) == 0)
{
lean_object* x_1024; lean_object* x_1025; 
x_1024 = lean_ctor_get(x_1023, 0);
lean_inc(x_1024);
lean_dec_ref(x_1023);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_28);
lean_inc(x_2);
x_1025 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1022, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1025) == 0)
{
lean_dec(x_1024);
lean_dec(x_28);
x_1000 = x_1018;
x_1001 = x_1019;
x_1002 = x_1021;
x_1003 = x_1020;
x_1004 = x_1025;
goto block_1007;
}
else
{
lean_object* x_1026; uint8_t x_1027; 
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = l_Lean_Exception_isInterrupt(x_1026);
if (x_1027 == 0)
{
uint8_t x_1028; 
x_1028 = l_Lean_Exception_isRuntime(x_1026);
x_1008 = x_1018;
x_1009 = x_1019;
x_1010 = x_1025;
x_1011 = x_1021;
x_1012 = x_1020;
x_1013 = x_1024;
x_1014 = x_1028;
goto block_1017;
}
else
{
lean_dec(x_1026);
x_1008 = x_1018;
x_1009 = x_1019;
x_1010 = x_1025;
x_1011 = x_1021;
x_1012 = x_1020;
x_1013 = x_1024;
x_1014 = x_1027;
goto block_1017;
}
}
}
else
{
lean_object* x_1029; 
lean_dec(x_1022);
lean_dec(x_1021);
lean_dec(x_1020);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1029 = lean_ctor_get(x_1023, 0);
lean_inc(x_1029);
lean_dec_ref(x_1023);
x_995 = x_1018;
x_996 = x_1019;
x_997 = x_1029;
goto block_999;
}
}
block_1036:
{
if (lean_obj_tag(x_1033) == 0)
{
lean_object* x_1034; 
x_1034 = lean_ctor_get(x_1033, 0);
lean_inc(x_1034);
lean_dec_ref(x_1033);
x_982 = x_1031;
x_983 = x_1032;
x_984 = x_1034;
goto block_986;
}
else
{
lean_object* x_1035; 
x_1035 = lean_ctor_get(x_1033, 0);
lean_inc(x_1035);
lean_dec_ref(x_1033);
x_995 = x_1031;
x_996 = x_1032;
x_997 = x_1035;
goto block_999;
}
}
block_1055:
{
lean_object* x_1044; double x_1045; double x_1046; double x_1047; double x_1048; double x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
x_1044 = lean_io_mono_nanos_now();
x_1045 = lean_float_of_nat(x_1037);
x_1046 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_1047 = lean_float_div(x_1045, x_1046);
x_1048 = lean_float_of_nat(x_1044);
x_1049 = lean_float_div(x_1048, x_1046);
x_1050 = lean_box_float(x_1047);
x_1051 = lean_box_float(x_1049);
x_1052 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1052, 0, x_1050);
lean_ctor_set(x_1052, 1, x_1051);
x_1053 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1053, 0, x_1043);
lean_ctor_set(x_1053, 1, x_1052);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1054 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_118, x_565, x_115, x_1042, x_1041, x_1040, x_1053, x_7, x_8, x_9, x_10);
x_1031 = x_1038;
x_1032 = x_1039;
x_1033 = x_1054;
goto block_1036;
}
block_1064:
{
lean_object* x_1063; 
x_1063 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1063, 0, x_1062);
x_1037 = x_1056;
x_1038 = x_1057;
x_1039 = x_1058;
x_1040 = x_1060;
x_1041 = x_1059;
x_1042 = x_1061;
x_1043 = x_1063;
goto block_1055;
}
block_1073:
{
lean_object* x_1072; 
x_1072 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1072, 0, x_1071);
x_1037 = x_1065;
x_1038 = x_1066;
x_1039 = x_1067;
x_1040 = x_1069;
x_1041 = x_1068;
x_1042 = x_1070;
x_1043 = x_1072;
goto block_1055;
}
block_1085:
{
lean_object* x_1083; lean_object* x_1084; 
x_1083 = l_List_appendTR___redArg(x_1081, x_1080);
x_1084 = l_List_appendTR___redArg(x_1083, x_1082);
x_1065 = x_1074;
x_1066 = x_1075;
x_1067 = x_1076;
x_1068 = x_1078;
x_1069 = x_1077;
x_1070 = x_1079;
x_1071 = x_1084;
goto block_1073;
}
block_1097:
{
if (lean_obj_tag(x_1094) == 0)
{
lean_object* x_1095; 
x_1095 = lean_ctor_get(x_1094, 0);
lean_inc(x_1095);
lean_dec_ref(x_1094);
x_1074 = x_1086;
x_1075 = x_1087;
x_1076 = x_1088;
x_1077 = x_1090;
x_1078 = x_1089;
x_1079 = x_1091;
x_1080 = x_1093;
x_1081 = x_1092;
x_1082 = x_1095;
goto block_1085;
}
else
{
lean_object* x_1096; 
lean_dec(x_1093);
lean_dec(x_1092);
x_1096 = lean_ctor_get(x_1094, 0);
lean_inc(x_1096);
lean_dec_ref(x_1094);
x_1056 = x_1086;
x_1057 = x_1087;
x_1058 = x_1088;
x_1059 = x_1089;
x_1060 = x_1090;
x_1061 = x_1091;
x_1062 = x_1096;
goto block_1064;
}
}
block_1111:
{
if (x_1108 == 0)
{
lean_object* x_1109; 
lean_dec_ref(x_1098);
x_1109 = l_Lean_Meta_SavedState_restore___redArg(x_1105, x_8, x_10);
lean_dec_ref(x_1105);
if (lean_obj_tag(x_1109) == 0)
{
lean_dec_ref(x_1109);
x_1074 = x_1099;
x_1075 = x_1100;
x_1076 = x_1101;
x_1077 = x_1103;
x_1078 = x_1102;
x_1079 = x_1104;
x_1080 = x_1107;
x_1081 = x_1106;
x_1082 = x_28;
goto block_1085;
}
else
{
lean_object* x_1110; 
lean_dec(x_1107);
lean_dec(x_1106);
lean_dec(x_28);
x_1110 = lean_ctor_get(x_1109, 0);
lean_inc(x_1110);
lean_dec_ref(x_1109);
x_1056 = x_1099;
x_1057 = x_1100;
x_1058 = x_1101;
x_1059 = x_1102;
x_1060 = x_1103;
x_1061 = x_1104;
x_1062 = x_1110;
goto block_1064;
}
}
else
{
lean_dec_ref(x_1105);
lean_dec(x_28);
x_1086 = x_1099;
x_1087 = x_1100;
x_1088 = x_1101;
x_1089 = x_1102;
x_1090 = x_1103;
x_1091 = x_1104;
x_1092 = x_1106;
x_1093 = x_1107;
x_1094 = x_1098;
goto block_1097;
}
}
block_1128:
{
lean_object* x_1121; 
x_1121 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1121) == 0)
{
lean_object* x_1122; lean_object* x_1123; 
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
lean_dec_ref(x_1121);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_28);
lean_inc(x_2);
x_1123 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1118, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1123) == 0)
{
lean_dec(x_1122);
lean_dec(x_28);
x_1086 = x_1112;
x_1087 = x_1113;
x_1088 = x_1114;
x_1089 = x_1116;
x_1090 = x_1115;
x_1091 = x_1117;
x_1092 = x_1120;
x_1093 = x_1119;
x_1094 = x_1123;
goto block_1097;
}
else
{
lean_object* x_1124; uint8_t x_1125; 
x_1124 = lean_ctor_get(x_1123, 0);
lean_inc(x_1124);
x_1125 = l_Lean_Exception_isInterrupt(x_1124);
if (x_1125 == 0)
{
uint8_t x_1126; 
x_1126 = l_Lean_Exception_isRuntime(x_1124);
x_1098 = x_1123;
x_1099 = x_1112;
x_1100 = x_1113;
x_1101 = x_1114;
x_1102 = x_1116;
x_1103 = x_1115;
x_1104 = x_1117;
x_1105 = x_1122;
x_1106 = x_1120;
x_1107 = x_1119;
x_1108 = x_1126;
goto block_1111;
}
else
{
lean_dec(x_1124);
x_1098 = x_1123;
x_1099 = x_1112;
x_1100 = x_1113;
x_1101 = x_1114;
x_1102 = x_1116;
x_1103 = x_1115;
x_1104 = x_1117;
x_1105 = x_1122;
x_1106 = x_1120;
x_1107 = x_1119;
x_1108 = x_1125;
goto block_1111;
}
}
}
else
{
lean_object* x_1127; 
lean_dec(x_1120);
lean_dec(x_1119);
lean_dec(x_1118);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1127 = lean_ctor_get(x_1121, 0);
lean_inc(x_1127);
lean_dec_ref(x_1121);
x_1056 = x_1112;
x_1057 = x_1113;
x_1058 = x_1114;
x_1059 = x_1116;
x_1060 = x_1115;
x_1061 = x_1117;
x_1062 = x_1127;
goto block_1064;
}
}
block_1138:
{
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; 
x_1136 = lean_ctor_get(x_1135, 0);
lean_inc(x_1136);
lean_dec_ref(x_1135);
x_1065 = x_1129;
x_1066 = x_1130;
x_1067 = x_1131;
x_1068 = x_1133;
x_1069 = x_1132;
x_1070 = x_1134;
x_1071 = x_1136;
goto block_1073;
}
else
{
lean_object* x_1137; 
x_1137 = lean_ctor_get(x_1135, 0);
lean_inc(x_1137);
lean_dec_ref(x_1135);
x_1056 = x_1129;
x_1057 = x_1130;
x_1058 = x_1131;
x_1059 = x_1133;
x_1060 = x_1132;
x_1061 = x_1134;
x_1062 = x_1137;
goto block_1064;
}
}
block_1147:
{
lean_object* x_1145; lean_object* x_1146; 
x_1145 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_1146 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1145, x_7, x_8, x_9, x_10);
x_1129 = x_1139;
x_1130 = x_1140;
x_1131 = x_1141;
x_1132 = x_1143;
x_1133 = x_1142;
x_1134 = x_1144;
x_1135 = x_1146;
goto block_1138;
}
block_1162:
{
uint8_t x_1158; 
x_1158 = l_List_isEmpty___redArg(x_1156);
lean_dec(x_1156);
if (x_1158 == 0)
{
lean_dec(x_1155);
lean_dec(x_1153);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1139 = x_1148;
x_1140 = x_1149;
x_1141 = x_1150;
x_1142 = x_1152;
x_1143 = x_1151;
x_1144 = x_1154;
goto block_1147;
}
else
{
if (x_1157 == 0)
{
lean_object* x_1159; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1159 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1153, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1159) == 0)
{
lean_object* x_1160; lean_object* x_1161; 
x_1160 = lean_ctor_get(x_1159, 0);
lean_inc(x_1160);
lean_dec_ref(x_1159);
x_1161 = l_List_appendTR___redArg(x_1155, x_1160);
x_1065 = x_1148;
x_1066 = x_1149;
x_1067 = x_1150;
x_1068 = x_1152;
x_1069 = x_1151;
x_1070 = x_1154;
x_1071 = x_1161;
goto block_1073;
}
else
{
lean_dec(x_1155);
x_1129 = x_1148;
x_1130 = x_1149;
x_1131 = x_1150;
x_1132 = x_1151;
x_1133 = x_1152;
x_1134 = x_1154;
x_1135 = x_1159;
goto block_1138;
}
}
else
{
lean_dec(x_1155);
lean_dec(x_1153);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1139 = x_1148;
x_1140 = x_1149;
x_1141 = x_1150;
x_1142 = x_1152;
x_1143 = x_1151;
x_1144 = x_1154;
goto block_1147;
}
}
}
block_1176:
{
uint8_t x_1173; lean_object* x_1174; 
x_1173 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_1170);
x_1174 = l_List_appendTR___redArg(x_1172, x_1170);
if (x_1173 == 0)
{
x_1148 = x_1163;
x_1149 = x_1164;
x_1150 = x_1165;
x_1151 = x_1166;
x_1152 = x_1167;
x_1153 = x_1174;
x_1154 = x_1168;
x_1155 = x_1170;
x_1156 = x_1169;
x_1157 = x_1171;
goto block_1162;
}
else
{
uint8_t x_1175; 
x_1175 = l_List_isEmpty___redArg(x_1170);
if (x_1175 == 0)
{
x_1112 = x_1163;
x_1113 = x_1164;
x_1114 = x_1165;
x_1115 = x_1166;
x_1116 = x_1167;
x_1117 = x_1168;
x_1118 = x_1174;
x_1119 = x_1169;
x_1120 = x_1170;
goto block_1128;
}
else
{
if (x_1171 == 0)
{
x_1148 = x_1163;
x_1149 = x_1164;
x_1150 = x_1165;
x_1151 = x_1166;
x_1152 = x_1167;
x_1153 = x_1174;
x_1154 = x_1168;
x_1155 = x_1170;
x_1156 = x_1169;
x_1157 = x_1171;
goto block_1162;
}
else
{
x_1112 = x_1163;
x_1113 = x_1164;
x_1114 = x_1165;
x_1115 = x_1166;
x_1116 = x_1167;
x_1117 = x_1168;
x_1118 = x_1174;
x_1119 = x_1169;
x_1120 = x_1170;
goto block_1128;
}
}
}
}
block_1192:
{
lean_object* x_1184; double x_1185; double x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
x_1184 = lean_io_get_num_heartbeats();
x_1185 = lean_float_of_nat(x_1177);
x_1186 = lean_float_of_nat(x_1184);
x_1187 = lean_box_float(x_1185);
x_1188 = lean_box_float(x_1186);
x_1189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1189, 0, x_1187);
lean_ctor_set(x_1189, 1, x_1188);
x_1190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1190, 0, x_1183);
lean_ctor_set(x_1190, 1, x_1189);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1191 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_118, x_565, x_115, x_1182, x_1181, x_1180, x_1190, x_7, x_8, x_9, x_10);
x_1031 = x_1178;
x_1032 = x_1179;
x_1033 = x_1191;
goto block_1036;
}
block_1201:
{
lean_object* x_1200; 
x_1200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1200, 0, x_1199);
x_1177 = x_1193;
x_1178 = x_1194;
x_1179 = x_1195;
x_1180 = x_1197;
x_1181 = x_1196;
x_1182 = x_1198;
x_1183 = x_1200;
goto block_1192;
}
block_1213:
{
lean_object* x_1211; lean_object* x_1212; 
x_1211 = l_List_appendTR___redArg(x_1209, x_1208);
x_1212 = l_List_appendTR___redArg(x_1211, x_1210);
x_1193 = x_1202;
x_1194 = x_1203;
x_1195 = x_1204;
x_1196 = x_1206;
x_1197 = x_1205;
x_1198 = x_1207;
x_1199 = x_1212;
goto block_1201;
}
block_1222:
{
lean_object* x_1221; 
x_1221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1221, 0, x_1220);
x_1177 = x_1214;
x_1178 = x_1215;
x_1179 = x_1216;
x_1180 = x_1218;
x_1181 = x_1217;
x_1182 = x_1219;
x_1183 = x_1221;
goto block_1192;
}
block_1232:
{
if (lean_obj_tag(x_1229) == 0)
{
lean_object* x_1230; 
x_1230 = lean_ctor_get(x_1229, 0);
lean_inc(x_1230);
lean_dec_ref(x_1229);
x_1193 = x_1223;
x_1194 = x_1224;
x_1195 = x_1225;
x_1196 = x_1227;
x_1197 = x_1226;
x_1198 = x_1228;
x_1199 = x_1230;
goto block_1201;
}
else
{
lean_object* x_1231; 
x_1231 = lean_ctor_get(x_1229, 0);
lean_inc(x_1231);
lean_dec_ref(x_1229);
x_1214 = x_1223;
x_1215 = x_1224;
x_1216 = x_1225;
x_1217 = x_1227;
x_1218 = x_1226;
x_1219 = x_1228;
x_1220 = x_1231;
goto block_1222;
}
}
block_1244:
{
lean_object* x_1241; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1241 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1240, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1241) == 0)
{
lean_object* x_1242; lean_object* x_1243; 
x_1242 = lean_ctor_get(x_1241, 0);
lean_inc(x_1242);
lean_dec_ref(x_1241);
x_1243 = l_List_appendTR___redArg(x_1239, x_1242);
x_1193 = x_1233;
x_1194 = x_1234;
x_1195 = x_1235;
x_1196 = x_1237;
x_1197 = x_1236;
x_1198 = x_1238;
x_1199 = x_1243;
goto block_1201;
}
else
{
lean_dec(x_1239);
x_1223 = x_1233;
x_1224 = x_1234;
x_1225 = x_1235;
x_1226 = x_1236;
x_1227 = x_1237;
x_1228 = x_1238;
x_1229 = x_1241;
goto block_1232;
}
}
block_1256:
{
if (lean_obj_tag(x_1253) == 0)
{
lean_object* x_1254; 
x_1254 = lean_ctor_get(x_1253, 0);
lean_inc(x_1254);
lean_dec_ref(x_1253);
x_1202 = x_1245;
x_1203 = x_1246;
x_1204 = x_1247;
x_1205 = x_1249;
x_1206 = x_1248;
x_1207 = x_1250;
x_1208 = x_1252;
x_1209 = x_1251;
x_1210 = x_1254;
goto block_1213;
}
else
{
lean_object* x_1255; 
lean_dec(x_1252);
lean_dec(x_1251);
x_1255 = lean_ctor_get(x_1253, 0);
lean_inc(x_1255);
lean_dec_ref(x_1253);
x_1214 = x_1245;
x_1215 = x_1246;
x_1216 = x_1247;
x_1217 = x_1248;
x_1218 = x_1249;
x_1219 = x_1250;
x_1220 = x_1255;
goto block_1222;
}
}
block_1270:
{
if (x_1267 == 0)
{
lean_object* x_1268; 
lean_dec_ref(x_1261);
x_1268 = l_Lean_Meta_SavedState_restore___redArg(x_1260, x_8, x_10);
lean_dec_ref(x_1260);
if (lean_obj_tag(x_1268) == 0)
{
lean_dec_ref(x_1268);
x_1202 = x_1257;
x_1203 = x_1258;
x_1204 = x_1259;
x_1205 = x_1263;
x_1206 = x_1262;
x_1207 = x_1264;
x_1208 = x_1266;
x_1209 = x_1265;
x_1210 = x_28;
goto block_1213;
}
else
{
lean_object* x_1269; 
lean_dec(x_1266);
lean_dec(x_1265);
lean_dec(x_28);
x_1269 = lean_ctor_get(x_1268, 0);
lean_inc(x_1269);
lean_dec_ref(x_1268);
x_1214 = x_1257;
x_1215 = x_1258;
x_1216 = x_1259;
x_1217 = x_1262;
x_1218 = x_1263;
x_1219 = x_1264;
x_1220 = x_1269;
goto block_1222;
}
}
else
{
lean_dec_ref(x_1260);
lean_dec(x_28);
x_1245 = x_1257;
x_1246 = x_1258;
x_1247 = x_1259;
x_1248 = x_1262;
x_1249 = x_1263;
x_1250 = x_1264;
x_1251 = x_1265;
x_1252 = x_1266;
x_1253 = x_1261;
goto block_1256;
}
}
block_1287:
{
lean_object* x_1280; 
x_1280 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1280) == 0)
{
lean_object* x_1281; lean_object* x_1282; 
x_1281 = lean_ctor_get(x_1280, 0);
lean_inc(x_1281);
lean_dec_ref(x_1280);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_28);
lean_inc(x_2);
x_1282 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1279, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1282) == 0)
{
lean_dec(x_1281);
lean_dec(x_28);
x_1245 = x_1271;
x_1246 = x_1272;
x_1247 = x_1273;
x_1248 = x_1275;
x_1249 = x_1274;
x_1250 = x_1276;
x_1251 = x_1278;
x_1252 = x_1277;
x_1253 = x_1282;
goto block_1256;
}
else
{
lean_object* x_1283; uint8_t x_1284; 
x_1283 = lean_ctor_get(x_1282, 0);
lean_inc(x_1283);
x_1284 = l_Lean_Exception_isInterrupt(x_1283);
if (x_1284 == 0)
{
uint8_t x_1285; 
x_1285 = l_Lean_Exception_isRuntime(x_1283);
x_1257 = x_1271;
x_1258 = x_1272;
x_1259 = x_1273;
x_1260 = x_1281;
x_1261 = x_1282;
x_1262 = x_1275;
x_1263 = x_1274;
x_1264 = x_1276;
x_1265 = x_1278;
x_1266 = x_1277;
x_1267 = x_1285;
goto block_1270;
}
else
{
lean_dec(x_1283);
x_1257 = x_1271;
x_1258 = x_1272;
x_1259 = x_1273;
x_1260 = x_1281;
x_1261 = x_1282;
x_1262 = x_1275;
x_1263 = x_1274;
x_1264 = x_1276;
x_1265 = x_1278;
x_1266 = x_1277;
x_1267 = x_1284;
goto block_1270;
}
}
}
else
{
lean_object* x_1286; 
lean_dec(x_1279);
lean_dec(x_1278);
lean_dec(x_1277);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1286 = lean_ctor_get(x_1280, 0);
lean_inc(x_1286);
lean_dec_ref(x_1280);
x_1214 = x_1271;
x_1215 = x_1272;
x_1216 = x_1273;
x_1217 = x_1275;
x_1218 = x_1274;
x_1219 = x_1276;
x_1220 = x_1286;
goto block_1222;
}
}
block_1303:
{
uint8_t x_1298; lean_object* x_1299; 
x_1298 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_1295);
x_1299 = l_List_appendTR___redArg(x_1297, x_1295);
if (x_1298 == 0)
{
lean_dec(x_1294);
if (x_1296 == 0)
{
x_1233 = x_1288;
x_1234 = x_1289;
x_1235 = x_1290;
x_1236 = x_1292;
x_1237 = x_1291;
x_1238 = x_1293;
x_1239 = x_1295;
x_1240 = x_1299;
goto block_1244;
}
else
{
lean_object* x_1300; lean_object* x_1301; 
lean_dec(x_1299);
lean_dec(x_1295);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1300 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_1301 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1300, x_7, x_8, x_9, x_10);
x_1223 = x_1288;
x_1224 = x_1289;
x_1225 = x_1290;
x_1226 = x_1292;
x_1227 = x_1291;
x_1228 = x_1293;
x_1229 = x_1301;
goto block_1232;
}
}
else
{
uint8_t x_1302; 
x_1302 = l_List_isEmpty___redArg(x_1295);
if (x_1302 == 0)
{
x_1271 = x_1288;
x_1272 = x_1289;
x_1273 = x_1290;
x_1274 = x_1292;
x_1275 = x_1291;
x_1276 = x_1293;
x_1277 = x_1294;
x_1278 = x_1295;
x_1279 = x_1299;
goto block_1287;
}
else
{
if (x_1296 == 0)
{
lean_dec(x_1294);
x_1233 = x_1288;
x_1234 = x_1289;
x_1235 = x_1290;
x_1236 = x_1292;
x_1237 = x_1291;
x_1238 = x_1293;
x_1239 = x_1295;
x_1240 = x_1299;
goto block_1244;
}
else
{
x_1271 = x_1288;
x_1272 = x_1289;
x_1273 = x_1290;
x_1274 = x_1292;
x_1275 = x_1291;
x_1276 = x_1293;
x_1277 = x_1294;
x_1278 = x_1295;
x_1279 = x_1299;
goto block_1287;
}
}
}
}
block_1328:
{
lean_object* x_1312; 
x_1312 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_1312) == 0)
{
if (x_1311 == 0)
{
lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
x_1313 = lean_ctor_get(x_1312, 0);
lean_inc(x_1313);
lean_dec_ref(x_1312);
x_1314 = lean_io_mono_nanos_now();
x_1315 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_116, x_1311, x_5, x_1307, x_8);
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1316; lean_object* x_1317; 
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
lean_dec_ref(x_1315);
x_1317 = l_List_reverse___redArg(x_1316);
x_1163 = x_1314;
x_1164 = x_1304;
x_1165 = x_1305;
x_1166 = x_1306;
x_1167 = x_1313;
x_1168 = x_1308;
x_1169 = x_1310;
x_1170 = x_1309;
x_1171 = x_1311;
x_1172 = x_1317;
goto block_1176;
}
else
{
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1318; 
x_1318 = lean_ctor_get(x_1315, 0);
lean_inc(x_1318);
lean_dec_ref(x_1315);
x_1163 = x_1314;
x_1164 = x_1304;
x_1165 = x_1305;
x_1166 = x_1306;
x_1167 = x_1313;
x_1168 = x_1308;
x_1169 = x_1310;
x_1170 = x_1309;
x_1171 = x_1311;
x_1172 = x_1318;
goto block_1176;
}
else
{
lean_object* x_1319; 
lean_dec(x_1310);
lean_dec(x_1309);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1319 = lean_ctor_get(x_1315, 0);
lean_inc(x_1319);
lean_dec_ref(x_1315);
x_1056 = x_1314;
x_1057 = x_1304;
x_1058 = x_1305;
x_1059 = x_1313;
x_1060 = x_1306;
x_1061 = x_1308;
x_1062 = x_1319;
goto block_1064;
}
}
}
else
{
lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
x_1320 = lean_ctor_get(x_1312, 0);
lean_inc(x_1320);
lean_dec_ref(x_1312);
x_1321 = lean_io_get_num_heartbeats();
x_1322 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_116, x_1311, x_5, x_1307, x_8);
if (lean_obj_tag(x_1322) == 0)
{
lean_object* x_1323; lean_object* x_1324; 
x_1323 = lean_ctor_get(x_1322, 0);
lean_inc(x_1323);
lean_dec_ref(x_1322);
x_1324 = l_List_reverse___redArg(x_1323);
x_1288 = x_1321;
x_1289 = x_1304;
x_1290 = x_1305;
x_1291 = x_1320;
x_1292 = x_1306;
x_1293 = x_1308;
x_1294 = x_1310;
x_1295 = x_1309;
x_1296 = x_1311;
x_1297 = x_1324;
goto block_1303;
}
else
{
if (lean_obj_tag(x_1322) == 0)
{
lean_object* x_1325; 
x_1325 = lean_ctor_get(x_1322, 0);
lean_inc(x_1325);
lean_dec_ref(x_1322);
x_1288 = x_1321;
x_1289 = x_1304;
x_1290 = x_1305;
x_1291 = x_1320;
x_1292 = x_1306;
x_1293 = x_1308;
x_1294 = x_1310;
x_1295 = x_1309;
x_1296 = x_1311;
x_1297 = x_1325;
goto block_1303;
}
else
{
lean_object* x_1326; 
lean_dec(x_1310);
lean_dec(x_1309);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1326 = lean_ctor_get(x_1322, 0);
lean_inc(x_1326);
lean_dec_ref(x_1322);
x_1214 = x_1321;
x_1215 = x_1304;
x_1216 = x_1305;
x_1217 = x_1320;
x_1218 = x_1306;
x_1219 = x_1308;
x_1220 = x_1326;
goto block_1222;
}
}
}
}
else
{
lean_object* x_1327; 
lean_dec(x_1310);
lean_dec(x_1309);
lean_dec(x_1307);
lean_dec_ref(x_1306);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1327 = lean_ctor_get(x_1312, 0);
lean_inc(x_1327);
lean_dec_ref(x_1312);
x_995 = x_1304;
x_996 = x_1305;
x_997 = x_1327;
goto block_999;
}
}
block_1333:
{
lean_object* x_1331; lean_object* x_1332; 
x_1331 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_1332 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1331, x_7, x_8, x_9, x_10);
x_1031 = x_1329;
x_1032 = x_1330;
x_1033 = x_1332;
goto block_1036;
}
block_1344:
{
uint8_t x_1340; 
x_1340 = l_List_isEmpty___redArg(x_1337);
lean_dec(x_1337);
if (x_1340 == 0)
{
lean_dec(x_1338);
lean_dec(x_1336);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1329 = x_1334;
x_1330 = x_1335;
goto block_1333;
}
else
{
if (x_1339 == 0)
{
lean_object* x_1341; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1341 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1338, x_28, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1341) == 0)
{
lean_object* x_1342; lean_object* x_1343; 
x_1342 = lean_ctor_get(x_1341, 0);
lean_inc(x_1342);
lean_dec_ref(x_1341);
x_1343 = l_List_appendTR___redArg(x_1336, x_1342);
x_982 = x_1334;
x_983 = x_1335;
x_984 = x_1343;
goto block_986;
}
else
{
lean_dec(x_1336);
x_1031 = x_1334;
x_1032 = x_1335;
x_1033 = x_1341;
goto block_1036;
}
}
else
{
lean_dec(x_1338);
lean_dec(x_1336);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1329 = x_1334;
x_1330 = x_1335;
goto block_1333;
}
}
}
block_1354:
{
uint8_t x_1351; lean_object* x_1352; 
x_1351 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_1348);
x_1352 = l_List_appendTR___redArg(x_1350, x_1348);
if (x_1351 == 0)
{
x_1334 = x_1345;
x_1335 = x_1346;
x_1336 = x_1348;
x_1337 = x_1347;
x_1338 = x_1352;
x_1339 = x_1349;
goto block_1344;
}
else
{
uint8_t x_1353; 
x_1353 = l_List_isEmpty___redArg(x_1348);
if (x_1353 == 0)
{
x_1018 = x_1345;
x_1019 = x_1346;
x_1020 = x_1347;
x_1021 = x_1348;
x_1022 = x_1352;
goto block_1030;
}
else
{
if (x_1349 == 0)
{
x_1334 = x_1345;
x_1335 = x_1346;
x_1336 = x_1348;
x_1337 = x_1347;
x_1338 = x_1352;
x_1339 = x_1349;
goto block_1344;
}
else
{
x_1018 = x_1345;
x_1019 = x_1346;
x_1020 = x_1347;
x_1021 = x_1348;
x_1022 = x_1352;
goto block_1030;
}
}
}
}
block_1409:
{
lean_object* x_1355; 
x_1355 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_1355) == 0)
{
lean_object* x_1356; lean_object* x_1357; uint8_t x_1358; 
x_1356 = lean_ctor_get(x_1355, 0);
lean_inc(x_1356);
lean_dec_ref(x_1355);
x_1357 = l_Lean_trace_profiler_useHeartbeats;
x_1358 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_115, x_1357);
if (x_1358 == 0)
{
lean_object* x_1359; lean_object* x_1360; 
x_1359 = lean_io_mono_nanos_now();
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_1360 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_27, x_117, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1360) == 0)
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; 
x_1361 = lean_ctor_get(x_1360, 0);
lean_inc(x_1361);
lean_dec_ref(x_1360);
x_1362 = lean_ctor_get(x_1361, 0);
lean_inc(x_1362);
x_1363 = lean_ctor_get(x_1361, 1);
lean_inc(x_1363);
lean_dec(x_1361);
lean_inc(x_2);
x_1364 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_1364) == 0)
{
lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; uint8_t x_1369; 
x_1365 = lean_ctor_get(x_1364, 0);
lean_inc(x_1365);
lean_dec_ref(x_1364);
x_1366 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_1363, x_24);
lean_inc(x_1366);
lean_inc(x_1362);
x_1367 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(x_1367, 0, x_1362);
lean_closure_set(x_1367, 1, x_1366);
x_1368 = lean_box(0);
x_1369 = lean_unbox(x_1365);
if (x_1369 == 0)
{
lean_object* x_1370; uint8_t x_1371; 
x_1370 = l_Lean_trace_profiler;
x_1371 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_115, x_1370);
if (x_1371 == 0)
{
lean_object* x_1372; 
lean_dec_ref(x_1367);
lean_dec(x_1365);
x_1372 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_116, x_1358, x_5, x_1368, x_8);
if (lean_obj_tag(x_1372) == 0)
{
lean_object* x_1373; lean_object* x_1374; 
x_1373 = lean_ctor_get(x_1372, 0);
lean_inc(x_1373);
lean_dec_ref(x_1372);
x_1374 = l_List_reverse___redArg(x_1373);
x_1345 = x_1356;
x_1346 = x_1359;
x_1347 = x_1362;
x_1348 = x_1366;
x_1349 = x_1358;
x_1350 = x_1374;
goto block_1354;
}
else
{
if (lean_obj_tag(x_1372) == 0)
{
lean_object* x_1375; 
x_1375 = lean_ctor_get(x_1372, 0);
lean_inc(x_1375);
lean_dec_ref(x_1372);
x_1345 = x_1356;
x_1346 = x_1359;
x_1347 = x_1362;
x_1348 = x_1366;
x_1349 = x_1358;
x_1350 = x_1375;
goto block_1354;
}
else
{
lean_dec(x_1366);
lean_dec(x_1362);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1031 = x_1356;
x_1032 = x_1359;
x_1033 = x_1372;
goto block_1036;
}
}
}
else
{
uint8_t x_1376; 
x_1376 = lean_unbox(x_1365);
lean_dec(x_1365);
x_1304 = x_1356;
x_1305 = x_1359;
x_1306 = x_1367;
x_1307 = x_1368;
x_1308 = x_1376;
x_1309 = x_1366;
x_1310 = x_1362;
x_1311 = x_1358;
goto block_1328;
}
}
else
{
uint8_t x_1377; 
x_1377 = lean_unbox(x_1365);
lean_dec(x_1365);
x_1304 = x_1356;
x_1305 = x_1359;
x_1306 = x_1367;
x_1307 = x_1368;
x_1308 = x_1377;
x_1309 = x_1366;
x_1310 = x_1362;
x_1311 = x_1358;
goto block_1328;
}
}
else
{
lean_object* x_1378; 
lean_dec(x_1363);
lean_dec(x_1362);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1378 = lean_ctor_get(x_1364, 0);
lean_inc(x_1378);
lean_dec_ref(x_1364);
x_995 = x_1356;
x_996 = x_1359;
x_997 = x_1378;
goto block_999;
}
}
else
{
lean_object* x_1379; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1379 = lean_ctor_get(x_1360, 0);
lean_inc(x_1379);
lean_dec_ref(x_1360);
x_995 = x_1356;
x_996 = x_1359;
x_997 = x_1379;
goto block_999;
}
}
else
{
lean_object* x_1380; lean_object* x_1381; 
x_1380 = lean_io_get_num_heartbeats();
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_1381 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_27, x_117, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1381) == 0)
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; 
x_1382 = lean_ctor_get(x_1381, 0);
lean_inc(x_1382);
lean_dec_ref(x_1381);
x_1383 = lean_ctor_get(x_1382, 0);
lean_inc(x_1383);
x_1384 = lean_ctor_get(x_1382, 1);
lean_inc(x_1384);
lean_dec(x_1382);
lean_inc(x_2);
x_1385 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_1385) == 0)
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; uint8_t x_1390; 
x_1386 = lean_ctor_get(x_1385, 0);
lean_inc(x_1386);
lean_dec_ref(x_1385);
x_1387 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_1384, x_24);
lean_inc(x_1387);
lean_inc(x_1383);
x_1388 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(x_1388, 0, x_1383);
lean_closure_set(x_1388, 1, x_1387);
x_1389 = lean_box(0);
x_1390 = lean_unbox(x_1386);
if (x_1390 == 0)
{
lean_object* x_1391; uint8_t x_1392; 
x_1391 = l_Lean_trace_profiler;
x_1392 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_115, x_1391);
if (x_1392 == 0)
{
lean_object* x_1393; 
lean_dec_ref(x_1388);
lean_dec(x_1386);
x_1393 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_1358, x_91, x_5, x_1389, x_8);
if (lean_obj_tag(x_1393) == 0)
{
lean_object* x_1394; lean_object* x_1395; 
x_1394 = lean_ctor_get(x_1393, 0);
lean_inc(x_1394);
lean_dec_ref(x_1393);
x_1395 = l_List_reverse___redArg(x_1394);
x_956 = x_1356;
x_957 = x_1380;
x_958 = x_1383;
x_959 = x_1387;
x_960 = x_1358;
x_961 = x_1395;
goto block_965;
}
else
{
if (lean_obj_tag(x_1393) == 0)
{
lean_object* x_1396; 
x_1396 = lean_ctor_get(x_1393, 0);
lean_inc(x_1396);
lean_dec_ref(x_1393);
x_956 = x_1356;
x_957 = x_1380;
x_958 = x_1383;
x_959 = x_1387;
x_960 = x_1358;
x_961 = x_1396;
goto block_965;
}
else
{
lean_dec(x_1387);
lean_dec(x_1383);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_589 = x_1356;
x_590 = x_1380;
x_591 = x_1393;
goto block_594;
}
}
}
else
{
uint8_t x_1397; 
x_1397 = lean_unbox(x_1386);
lean_dec(x_1386);
x_874 = x_1356;
x_875 = x_1388;
x_876 = x_1389;
x_877 = x_1380;
x_878 = x_1383;
x_879 = x_1397;
x_880 = x_1387;
x_881 = x_1358;
goto block_898;
}
}
else
{
uint8_t x_1398; 
x_1398 = lean_unbox(x_1386);
lean_dec(x_1386);
x_874 = x_1356;
x_875 = x_1388;
x_876 = x_1389;
x_877 = x_1380;
x_878 = x_1383;
x_879 = x_1398;
x_880 = x_1387;
x_881 = x_1358;
goto block_898;
}
}
else
{
lean_object* x_1399; 
lean_dec(x_1384);
lean_dec(x_1383);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1399 = lean_ctor_get(x_1385, 0);
lean_inc(x_1399);
lean_dec_ref(x_1385);
x_579 = x_1356;
x_580 = x_1380;
x_581 = x_1399;
goto block_583;
}
}
else
{
lean_object* x_1400; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1400 = lean_ctor_get(x_1381, 0);
lean_inc(x_1400);
lean_dec_ref(x_1381);
x_579 = x_1356;
x_580 = x_1380;
x_581 = x_1400;
goto block_583;
}
}
}
else
{
lean_object* x_1401; lean_object* x_1402; uint8_t x_1403; uint8_t x_1408; 
lean_dec_ref(x_564);
lean_dec(x_563);
lean_dec_ref(x_117);
lean_dec_ref(x_115);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1401 = lean_ctor_get(x_1355, 0);
x_1408 = !lean_is_exclusive(x_1355);
if (x_1408 == 0)
{
x_1402 = x_1355;
x_1403 = x_1408;
goto block_1407;
}
else
{
lean_inc(x_1401);
lean_dec(x_1355);
x_1402 = lean_box(0);
x_1403 = x_1408;
goto block_1407;
}
block_1407:
{
lean_object* x_1404; 
if (x_1403 == 0)
{
x_1404 = x_1402;
goto block_1405;
}
else
{
lean_object* x_1406; 
x_1406 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1406, 0, x_1401);
x_1404 = x_1406;
goto block_1405;
}
block_1405:
{
return x_1404;
}
}
}
}
}
else
{
lean_object* x_1413; lean_object* x_1414; uint8_t x_1415; uint8_t x_1420; 
lean_dec_ref(x_117);
lean_del_object(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1413 = lean_ctor_get(x_562, 0);
x_1420 = !lean_is_exclusive(x_562);
if (x_1420 == 0)
{
x_1414 = x_562;
x_1415 = x_1420;
goto block_1419;
}
else
{
lean_inc(x_1413);
lean_dec(x_562);
x_1414 = lean_box(0);
x_1415 = x_1420;
goto block_1419;
}
block_1419:
{
lean_object* x_1416; 
if (x_1415 == 0)
{
x_1416 = x_1414;
goto block_1417;
}
else
{
lean_object* x_1418; 
x_1418 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1418, 0, x_1413);
x_1416 = x_1418;
goto block_1417;
}
block_1417:
{
return x_1416;
}
}
}
}
block_140:
{
lean_object* x_130; double x_131; double x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_io_get_num_heartbeats();
x_131 = lean_float_of_nat(x_119);
x_132 = lean_float_of_nat(x_130);
x_133 = lean_box_float(x_131);
x_134 = lean_box_float(x_132);
if (x_30 == 0)
{
lean_ctor_set(x_29, 1, x_134);
lean_ctor_set(x_29, 0, x_133);
x_135 = x_29;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_134);
x_135 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_129);
lean_ctor_set(x_136, 1, x_135);
x_137 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_118, x_127, x_125, x_121, x_120, x_123, x_136, x_126, x_124, x_128, x_122);
lean_dec_ref(x_125);
return x_137;
}
}
block_153:
{
lean_object* x_152; 
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_119 = x_141;
x_120 = x_143;
x_121 = x_142;
x_122 = x_144;
x_123 = x_145;
x_124 = x_146;
x_125 = x_147;
x_126 = x_148;
x_127 = x_149;
x_128 = x_150;
x_129 = x_152;
goto block_140;
}
block_169:
{
lean_object* x_167; lean_object* x_168; 
x_167 = l_List_appendTR___redArg(x_164, x_158);
x_168 = l_List_appendTR___redArg(x_167, x_166);
x_141 = x_154;
x_142 = x_156;
x_143 = x_155;
x_144 = x_157;
x_145 = x_159;
x_146 = x_160;
x_147 = x_161;
x_148 = x_162;
x_149 = x_163;
x_150 = x_165;
x_151 = x_168;
goto block_153;
}
block_182:
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_119 = x_170;
x_120 = x_172;
x_121 = x_171;
x_122 = x_173;
x_123 = x_174;
x_124 = x_175;
x_125 = x_176;
x_126 = x_177;
x_127 = x_178;
x_128 = x_179;
x_129 = x_181;
goto block_140;
}
block_196:
{
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
x_141 = x_183;
x_142 = x_185;
x_143 = x_184;
x_144 = x_186;
x_145 = x_187;
x_146 = x_188;
x_147 = x_189;
x_148 = x_190;
x_149 = x_191;
x_150 = x_192;
x_151 = x_194;
goto block_153;
}
else
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
lean_dec_ref(x_193);
x_170 = x_183;
x_171 = x_185;
x_172 = x_184;
x_173 = x_186;
x_174 = x_187;
x_175 = x_188;
x_176 = x_189;
x_177 = x_190;
x_178 = x_191;
x_179 = x_192;
x_180 = x_195;
goto block_182;
}
}
block_212:
{
lean_object* x_209; 
lean_inc(x_200);
lean_inc_ref(x_206);
lean_inc(x_201);
lean_inc_ref(x_204);
lean_inc(x_2);
x_209 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_202, x_28, x_204, x_201, x_206, x_200);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
x_211 = l_List_appendTR___redArg(x_205, x_210);
x_141 = x_197;
x_142 = x_198;
x_143 = x_199;
x_144 = x_200;
x_145 = x_207;
x_146 = x_201;
x_147 = x_203;
x_148 = x_204;
x_149 = x_208;
x_150 = x_206;
x_151 = x_211;
goto block_153;
}
else
{
lean_dec(x_205);
x_183 = x_197;
x_184 = x_199;
x_185 = x_198;
x_186 = x_200;
x_187 = x_207;
x_188 = x_201;
x_189 = x_203;
x_190 = x_204;
x_191 = x_208;
x_192 = x_206;
x_193 = x_209;
goto block_196;
}
}
block_230:
{
uint8_t x_227; 
x_227 = l_List_isEmpty___redArg(x_224);
lean_dec(x_224);
if (x_227 == 0)
{
if (x_214 == 0)
{
x_197 = x_213;
x_198 = x_215;
x_199 = x_216;
x_200 = x_217;
x_201 = x_218;
x_202 = x_219;
x_203 = x_220;
x_204 = x_221;
x_205 = x_222;
x_206 = x_223;
x_207 = x_225;
x_208 = x_226;
goto block_212;
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_222);
lean_dec(x_219);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_228 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_229 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_228, x_221, x_218, x_223, x_217);
x_183 = x_213;
x_184 = x_216;
x_185 = x_215;
x_186 = x_217;
x_187 = x_225;
x_188 = x_218;
x_189 = x_220;
x_190 = x_221;
x_191 = x_226;
x_192 = x_223;
x_193 = x_229;
goto block_196;
}
}
else
{
x_197 = x_213;
x_198 = x_215;
x_199 = x_216;
x_200 = x_217;
x_201 = x_218;
x_202 = x_219;
x_203 = x_220;
x_204 = x_221;
x_205 = x_222;
x_206 = x_223;
x_207 = x_225;
x_208 = x_226;
goto block_212;
}
}
block_246:
{
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_154 = x_231;
x_155 = x_233;
x_156 = x_232;
x_157 = x_235;
x_158 = x_234;
x_159 = x_236;
x_160 = x_237;
x_161 = x_238;
x_162 = x_239;
x_163 = x_241;
x_164 = x_240;
x_165 = x_242;
x_166 = x_244;
goto block_169;
}
else
{
lean_object* x_245; 
lean_dec(x_240);
lean_dec(x_234);
x_245 = lean_ctor_get(x_243, 0);
lean_inc(x_245);
lean_dec_ref(x_243);
x_170 = x_231;
x_171 = x_232;
x_172 = x_233;
x_173 = x_235;
x_174 = x_236;
x_175 = x_237;
x_176 = x_238;
x_177 = x_239;
x_178 = x_241;
x_179 = x_242;
x_180 = x_245;
goto block_182;
}
}
block_264:
{
if (x_261 == 0)
{
lean_object* x_262; 
lean_dec_ref(x_247);
x_262 = l_Lean_Meta_SavedState_restore___redArg(x_257, x_252, x_251);
lean_dec_ref(x_257);
if (lean_obj_tag(x_262) == 0)
{
lean_dec_ref(x_262);
x_154 = x_248;
x_155 = x_249;
x_156 = x_250;
x_157 = x_251;
x_158 = x_258;
x_159 = x_259;
x_160 = x_252;
x_161 = x_253;
x_162 = x_254;
x_163 = x_260;
x_164 = x_255;
x_165 = x_256;
x_166 = x_28;
goto block_169;
}
else
{
lean_object* x_263; 
lean_dec(x_258);
lean_dec(x_255);
lean_dec(x_28);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec_ref(x_262);
x_170 = x_248;
x_171 = x_250;
x_172 = x_249;
x_173 = x_251;
x_174 = x_259;
x_175 = x_252;
x_176 = x_253;
x_177 = x_254;
x_178 = x_260;
x_179 = x_256;
x_180 = x_263;
goto block_182;
}
}
else
{
lean_dec_ref(x_257);
lean_dec(x_28);
x_231 = x_248;
x_232 = x_250;
x_233 = x_249;
x_234 = x_258;
x_235 = x_251;
x_236 = x_259;
x_237 = x_252;
x_238 = x_253;
x_239 = x_254;
x_240 = x_255;
x_241 = x_260;
x_242 = x_256;
x_243 = x_247;
goto block_246;
}
}
block_285:
{
lean_object* x_278; 
x_278 = l_Lean_Meta_saveState___redArg(x_269, x_268);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec_ref(x_278);
lean_inc(x_268);
lean_inc_ref(x_274);
lean_inc(x_269);
lean_inc_ref(x_272);
lean_inc(x_28);
lean_inc(x_2);
x_280 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_270, x_28, x_272, x_269, x_274, x_268);
if (lean_obj_tag(x_280) == 0)
{
lean_dec(x_279);
lean_dec(x_28);
x_231 = x_265;
x_232 = x_266;
x_233 = x_267;
x_234 = x_275;
x_235 = x_268;
x_236 = x_276;
x_237 = x_269;
x_238 = x_271;
x_239 = x_272;
x_240 = x_273;
x_241 = x_277;
x_242 = x_274;
x_243 = x_280;
goto block_246;
}
else
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = l_Lean_Exception_isInterrupt(x_281);
if (x_282 == 0)
{
uint8_t x_283; 
x_283 = l_Lean_Exception_isRuntime(x_281);
x_247 = x_280;
x_248 = x_265;
x_249 = x_267;
x_250 = x_266;
x_251 = x_268;
x_252 = x_269;
x_253 = x_271;
x_254 = x_272;
x_255 = x_273;
x_256 = x_274;
x_257 = x_279;
x_258 = x_275;
x_259 = x_276;
x_260 = x_277;
x_261 = x_283;
goto block_264;
}
else
{
lean_dec(x_281);
x_247 = x_280;
x_248 = x_265;
x_249 = x_267;
x_250 = x_266;
x_251 = x_268;
x_252 = x_269;
x_253 = x_271;
x_254 = x_272;
x_255 = x_273;
x_256 = x_274;
x_257 = x_279;
x_258 = x_275;
x_259 = x_276;
x_260 = x_277;
x_261 = x_282;
goto block_264;
}
}
}
else
{
lean_object* x_284; 
lean_dec(x_275);
lean_dec(x_273);
lean_dec(x_270);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_284 = lean_ctor_get(x_278, 0);
lean_inc(x_284);
lean_dec_ref(x_278);
x_170 = x_265;
x_171 = x_266;
x_172 = x_267;
x_173 = x_268;
x_174 = x_276;
x_175 = x_269;
x_176 = x_271;
x_177 = x_272;
x_178 = x_277;
x_179 = x_274;
x_180 = x_284;
goto block_182;
}
}
block_303:
{
uint8_t x_300; lean_object* x_301; 
x_300 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_294);
x_301 = l_List_appendTR___redArg(x_299, x_294);
if (x_300 == 0)
{
x_213 = x_286;
x_214 = x_289;
x_215 = x_287;
x_216 = x_288;
x_217 = x_290;
x_218 = x_291;
x_219 = x_301;
x_220 = x_292;
x_221 = x_293;
x_222 = x_294;
x_223 = x_295;
x_224 = x_296;
x_225 = x_297;
x_226 = x_298;
goto block_230;
}
else
{
uint8_t x_302; 
x_302 = l_List_isEmpty___redArg(x_294);
if (x_302 == 0)
{
x_265 = x_286;
x_266 = x_287;
x_267 = x_288;
x_268 = x_290;
x_269 = x_291;
x_270 = x_301;
x_271 = x_292;
x_272 = x_293;
x_273 = x_294;
x_274 = x_295;
x_275 = x_296;
x_276 = x_297;
x_277 = x_298;
goto block_285;
}
else
{
if (x_91 == 0)
{
x_213 = x_286;
x_214 = x_289;
x_215 = x_287;
x_216 = x_288;
x_217 = x_290;
x_218 = x_291;
x_219 = x_301;
x_220 = x_292;
x_221 = x_293;
x_222 = x_294;
x_223 = x_295;
x_224 = x_296;
x_225 = x_297;
x_226 = x_298;
goto block_230;
}
else
{
x_265 = x_286;
x_266 = x_287;
x_267 = x_288;
x_268 = x_290;
x_269 = x_291;
x_270 = x_301;
x_271 = x_292;
x_272 = x_293;
x_273 = x_294;
x_274 = x_295;
x_275 = x_296;
x_276 = x_297;
x_277 = x_298;
goto block_285;
}
}
}
}
block_326:
{
lean_object* x_315; double x_316; double x_317; double x_318; double x_319; double x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_315 = lean_io_mono_nanos_now();
x_316 = lean_float_of_nat(x_313);
x_317 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_318 = lean_float_div(x_316, x_317);
x_319 = lean_float_of_nat(x_315);
x_320 = lean_float_div(x_319, x_317);
x_321 = lean_box_float(x_318);
x_322 = lean_box_float(x_320);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_314);
lean_ctor_set(x_324, 1, x_323);
x_325 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_118, x_311, x_309, x_305, x_304, x_307, x_324, x_310, x_308, x_312, x_306);
lean_dec_ref(x_309);
return x_325;
}
block_339:
{
lean_object* x_338; 
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_337);
x_304 = x_328;
x_305 = x_327;
x_306 = x_329;
x_307 = x_330;
x_308 = x_331;
x_309 = x_332;
x_310 = x_333;
x_311 = x_334;
x_312 = x_336;
x_313 = x_335;
x_314 = x_338;
goto block_326;
}
block_355:
{
lean_object* x_353; lean_object* x_354; 
x_353 = l_List_appendTR___redArg(x_349, x_343);
x_354 = l_List_appendTR___redArg(x_353, x_352);
x_327 = x_341;
x_328 = x_340;
x_329 = x_342;
x_330 = x_344;
x_331 = x_345;
x_332 = x_346;
x_333 = x_347;
x_334 = x_348;
x_335 = x_351;
x_336 = x_350;
x_337 = x_354;
goto block_339;
}
block_368:
{
lean_object* x_367; 
x_367 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_367, 0, x_366);
x_304 = x_357;
x_305 = x_356;
x_306 = x_358;
x_307 = x_359;
x_308 = x_360;
x_309 = x_361;
x_310 = x_362;
x_311 = x_363;
x_312 = x_365;
x_313 = x_364;
x_314 = x_367;
goto block_326;
}
block_382:
{
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
lean_dec_ref(x_379);
x_327 = x_370;
x_328 = x_369;
x_329 = x_371;
x_330 = x_372;
x_331 = x_373;
x_332 = x_374;
x_333 = x_375;
x_334 = x_376;
x_335 = x_378;
x_336 = x_377;
x_337 = x_380;
goto block_339;
}
else
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
lean_dec_ref(x_379);
x_356 = x_370;
x_357 = x_369;
x_358 = x_371;
x_359 = x_372;
x_360 = x_373;
x_361 = x_374;
x_362 = x_375;
x_363 = x_376;
x_364 = x_378;
x_365 = x_377;
x_366 = x_381;
goto block_368;
}
}
block_395:
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_394 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_393, x_389, x_387, x_392, x_385);
x_369 = x_384;
x_370 = x_383;
x_371 = x_385;
x_372 = x_386;
x_373 = x_387;
x_374 = x_388;
x_375 = x_389;
x_376 = x_390;
x_377 = x_392;
x_378 = x_391;
x_379 = x_394;
goto block_382;
}
block_414:
{
uint8_t x_410; 
x_410 = l_List_isEmpty___redArg(x_406);
lean_dec(x_406);
if (x_410 == 0)
{
lean_dec(x_404);
lean_dec(x_396);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_383 = x_397;
x_384 = x_398;
x_385 = x_400;
x_386 = x_407;
x_387 = x_401;
x_388 = x_402;
x_389 = x_403;
x_390 = x_408;
x_391 = x_409;
x_392 = x_405;
goto block_395;
}
else
{
if (x_399 == 0)
{
lean_object* x_411; 
lean_inc(x_400);
lean_inc_ref(x_405);
lean_inc(x_401);
lean_inc_ref(x_403);
lean_inc(x_2);
x_411 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_396, x_28, x_403, x_401, x_405, x_400);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
lean_dec_ref(x_411);
x_413 = l_List_appendTR___redArg(x_404, x_412);
x_327 = x_397;
x_328 = x_398;
x_329 = x_400;
x_330 = x_407;
x_331 = x_401;
x_332 = x_402;
x_333 = x_403;
x_334 = x_408;
x_335 = x_409;
x_336 = x_405;
x_337 = x_413;
goto block_339;
}
else
{
lean_dec(x_404);
x_369 = x_398;
x_370 = x_397;
x_371 = x_400;
x_372 = x_407;
x_373 = x_401;
x_374 = x_402;
x_375 = x_403;
x_376 = x_408;
x_377 = x_405;
x_378 = x_409;
x_379 = x_411;
goto block_382;
}
}
else
{
lean_dec(x_404);
lean_dec(x_396);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_383 = x_397;
x_384 = x_398;
x_385 = x_400;
x_386 = x_407;
x_387 = x_401;
x_388 = x_402;
x_389 = x_403;
x_390 = x_408;
x_391 = x_409;
x_392 = x_405;
goto block_395;
}
}
}
block_430:
{
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
lean_dec_ref(x_427);
x_340 = x_416;
x_341 = x_415;
x_342 = x_418;
x_343 = x_417;
x_344 = x_419;
x_345 = x_420;
x_346 = x_421;
x_347 = x_422;
x_348 = x_424;
x_349 = x_423;
x_350 = x_426;
x_351 = x_425;
x_352 = x_428;
goto block_355;
}
else
{
lean_object* x_429; 
lean_dec(x_423);
lean_dec(x_417);
x_429 = lean_ctor_get(x_427, 0);
lean_inc(x_429);
lean_dec_ref(x_427);
x_356 = x_415;
x_357 = x_416;
x_358 = x_418;
x_359 = x_419;
x_360 = x_420;
x_361 = x_421;
x_362 = x_422;
x_363 = x_424;
x_364 = x_425;
x_365 = x_426;
x_366 = x_429;
goto block_368;
}
}
block_448:
{
if (x_445 == 0)
{
lean_object* x_446; 
lean_dec_ref(x_438);
x_446 = l_Lean_Meta_SavedState_restore___redArg(x_442, x_434, x_433);
lean_dec_ref(x_442);
if (lean_obj_tag(x_446) == 0)
{
lean_dec_ref(x_446);
x_340 = x_431;
x_341 = x_432;
x_342 = x_433;
x_343 = x_440;
x_344 = x_441;
x_345 = x_434;
x_346 = x_435;
x_347 = x_436;
x_348 = x_443;
x_349 = x_437;
x_350 = x_439;
x_351 = x_444;
x_352 = x_28;
goto block_355;
}
else
{
lean_object* x_447; 
lean_dec(x_440);
lean_dec(x_437);
lean_dec(x_28);
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
lean_dec_ref(x_446);
x_356 = x_432;
x_357 = x_431;
x_358 = x_433;
x_359 = x_441;
x_360 = x_434;
x_361 = x_435;
x_362 = x_436;
x_363 = x_443;
x_364 = x_444;
x_365 = x_439;
x_366 = x_447;
goto block_368;
}
}
else
{
lean_dec_ref(x_442);
lean_dec(x_28);
x_415 = x_432;
x_416 = x_431;
x_417 = x_440;
x_418 = x_433;
x_419 = x_441;
x_420 = x_434;
x_421 = x_435;
x_422 = x_436;
x_423 = x_437;
x_424 = x_443;
x_425 = x_444;
x_426 = x_439;
x_427 = x_438;
goto block_430;
}
}
block_469:
{
lean_object* x_462; 
x_462 = l_Lean_Meta_saveState___redArg(x_453, x_452);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
lean_dec_ref(x_462);
lean_inc(x_452);
lean_inc_ref(x_457);
lean_inc(x_453);
lean_inc_ref(x_455);
lean_inc(x_28);
lean_inc(x_2);
x_464 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_449, x_28, x_455, x_453, x_457, x_452);
if (lean_obj_tag(x_464) == 0)
{
lean_dec(x_463);
lean_dec(x_28);
x_415 = x_450;
x_416 = x_451;
x_417 = x_458;
x_418 = x_452;
x_419 = x_459;
x_420 = x_453;
x_421 = x_454;
x_422 = x_455;
x_423 = x_456;
x_424 = x_460;
x_425 = x_461;
x_426 = x_457;
x_427 = x_464;
goto block_430;
}
else
{
lean_object* x_465; uint8_t x_466; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = l_Lean_Exception_isInterrupt(x_465);
if (x_466 == 0)
{
uint8_t x_467; 
x_467 = l_Lean_Exception_isRuntime(x_465);
x_431 = x_451;
x_432 = x_450;
x_433 = x_452;
x_434 = x_453;
x_435 = x_454;
x_436 = x_455;
x_437 = x_456;
x_438 = x_464;
x_439 = x_457;
x_440 = x_458;
x_441 = x_459;
x_442 = x_463;
x_443 = x_460;
x_444 = x_461;
x_445 = x_467;
goto block_448;
}
else
{
lean_dec(x_465);
x_431 = x_451;
x_432 = x_450;
x_433 = x_452;
x_434 = x_453;
x_435 = x_454;
x_436 = x_455;
x_437 = x_456;
x_438 = x_464;
x_439 = x_457;
x_440 = x_458;
x_441 = x_459;
x_442 = x_463;
x_443 = x_460;
x_444 = x_461;
x_445 = x_466;
goto block_448;
}
}
}
else
{
lean_object* x_468; 
lean_dec(x_458);
lean_dec(x_456);
lean_dec(x_449);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_468 = lean_ctor_get(x_462, 0);
lean_inc(x_468);
lean_dec_ref(x_462);
x_356 = x_450;
x_357 = x_451;
x_358 = x_452;
x_359 = x_459;
x_360 = x_453;
x_361 = x_454;
x_362 = x_455;
x_363 = x_460;
x_364 = x_461;
x_365 = x_457;
x_366 = x_468;
goto block_368;
}
}
block_487:
{
uint8_t x_484; lean_object* x_485; 
x_484 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_477);
x_485 = l_List_appendTR___redArg(x_483, x_477);
if (x_484 == 0)
{
x_396 = x_485;
x_397 = x_470;
x_398 = x_471;
x_399 = x_472;
x_400 = x_473;
x_401 = x_474;
x_402 = x_475;
x_403 = x_476;
x_404 = x_477;
x_405 = x_478;
x_406 = x_479;
x_407 = x_480;
x_408 = x_481;
x_409 = x_482;
goto block_414;
}
else
{
uint8_t x_486; 
x_486 = l_List_isEmpty___redArg(x_477);
if (x_486 == 0)
{
x_449 = x_485;
x_450 = x_470;
x_451 = x_471;
x_452 = x_473;
x_453 = x_474;
x_454 = x_475;
x_455 = x_476;
x_456 = x_477;
x_457 = x_478;
x_458 = x_479;
x_459 = x_480;
x_460 = x_481;
x_461 = x_482;
goto block_469;
}
else
{
if (x_472 == 0)
{
x_396 = x_485;
x_397 = x_470;
x_398 = x_471;
x_399 = x_472;
x_400 = x_473;
x_401 = x_474;
x_402 = x_475;
x_403 = x_476;
x_404 = x_477;
x_405 = x_478;
x_406 = x_479;
x_407 = x_480;
x_408 = x_481;
x_409 = x_482;
goto block_414;
}
else
{
x_449 = x_485;
x_450 = x_470;
x_451 = x_471;
x_452 = x_473;
x_453 = x_474;
x_454 = x_475;
x_455 = x_476;
x_456 = x_477;
x_457 = x_478;
x_458 = x_479;
x_459 = x_480;
x_460 = x_481;
x_461 = x_482;
goto block_469;
}
}
}
}
block_523:
{
lean_object* x_499; 
x_499 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_490);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; uint8_t x_502; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
lean_dec_ref(x_499);
x_501 = l_Lean_trace_profiler_useHeartbeats;
x_502 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_494, x_501);
if (x_502 == 0)
{
lean_object* x_503; lean_object* x_504; 
lean_del_object(x_29);
x_503 = lean_io_mono_nanos_now();
x_504 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_91, x_5, x_493, x_492);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
lean_dec_ref(x_504);
x_506 = l_List_reverse___redArg(x_505);
x_470 = x_488;
x_471 = x_500;
x_472 = x_502;
x_473 = x_490;
x_474 = x_492;
x_475 = x_494;
x_476 = x_495;
x_477 = x_496;
x_478 = x_498;
x_479 = x_489;
x_480 = x_491;
x_481 = x_497;
x_482 = x_503;
x_483 = x_506;
goto block_487;
}
else
{
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_507; 
x_507 = lean_ctor_get(x_504, 0);
lean_inc(x_507);
lean_dec_ref(x_504);
x_470 = x_488;
x_471 = x_500;
x_472 = x_502;
x_473 = x_490;
x_474 = x_492;
x_475 = x_494;
x_476 = x_495;
x_477 = x_496;
x_478 = x_498;
x_479 = x_489;
x_480 = x_491;
x_481 = x_497;
x_482 = x_503;
x_483 = x_507;
goto block_487;
}
else
{
lean_object* x_508; 
lean_dec(x_496);
lean_dec(x_489);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_508 = lean_ctor_get(x_504, 0);
lean_inc(x_508);
lean_dec_ref(x_504);
x_356 = x_488;
x_357 = x_500;
x_358 = x_490;
x_359 = x_491;
x_360 = x_492;
x_361 = x_494;
x_362 = x_495;
x_363 = x_497;
x_364 = x_503;
x_365 = x_498;
x_366 = x_508;
goto block_368;
}
}
}
else
{
lean_object* x_509; lean_object* x_510; 
x_509 = lean_io_get_num_heartbeats();
x_510 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_91, x_5, x_493, x_492);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
lean_dec_ref(x_510);
x_512 = l_List_reverse___redArg(x_511);
x_286 = x_509;
x_287 = x_488;
x_288 = x_500;
x_289 = x_502;
x_290 = x_490;
x_291 = x_492;
x_292 = x_494;
x_293 = x_495;
x_294 = x_496;
x_295 = x_498;
x_296 = x_489;
x_297 = x_491;
x_298 = x_497;
x_299 = x_512;
goto block_303;
}
else
{
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_513; 
x_513 = lean_ctor_get(x_510, 0);
lean_inc(x_513);
lean_dec_ref(x_510);
x_286 = x_509;
x_287 = x_488;
x_288 = x_500;
x_289 = x_502;
x_290 = x_490;
x_291 = x_492;
x_292 = x_494;
x_293 = x_495;
x_294 = x_496;
x_295 = x_498;
x_296 = x_489;
x_297 = x_491;
x_298 = x_497;
x_299 = x_513;
goto block_303;
}
else
{
lean_object* x_514; 
lean_dec(x_496);
lean_dec(x_489);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_514 = lean_ctor_get(x_510, 0);
lean_inc(x_514);
lean_dec_ref(x_510);
x_170 = x_509;
x_171 = x_488;
x_172 = x_500;
x_173 = x_490;
x_174 = x_491;
x_175 = x_492;
x_176 = x_494;
x_177 = x_495;
x_178 = x_497;
x_179 = x_498;
x_180 = x_514;
goto block_182;
}
}
}
}
else
{
lean_object* x_515; lean_object* x_516; uint8_t x_517; uint8_t x_522; 
lean_dec_ref(x_498);
lean_dec_ref(x_497);
lean_dec(x_496);
lean_dec_ref(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec(x_492);
lean_dec_ref(x_491);
lean_dec(x_490);
lean_dec(x_489);
lean_del_object(x_29);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_515 = lean_ctor_get(x_499, 0);
x_522 = !lean_is_exclusive(x_499);
if (x_522 == 0)
{
x_516 = x_499;
x_517 = x_522;
goto block_521;
}
else
{
lean_inc(x_515);
lean_dec(x_499);
x_516 = lean_box(0);
x_517 = x_522;
goto block_521;
}
block_521:
{
lean_object* x_518; 
if (x_517 == 0)
{
x_518 = x_516;
goto block_519;
}
else
{
lean_object* x_520; 
x_520 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_520, 0, x_515);
x_518 = x_520;
goto block_519;
}
block_519:
{
return x_518;
}
}
}
}
block_561:
{
lean_object* x_528; 
lean_inc(x_527);
lean_inc_ref(x_526);
lean_inc(x_525);
lean_inc_ref(x_524);
x_528 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_27, x_117, x_524, x_525, x_526, x_527);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; lean_object* x_534; lean_object* x_535; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
lean_dec_ref(x_528);
x_530 = lean_ctor_get(x_526, 2);
x_531 = lean_ctor_get(x_529, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_529, 1);
lean_inc(x_532);
lean_dec(x_529);
x_533 = lean_ctor_get_uint8(x_530, sizeof(void*)*1);
x_534 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_532, x_24);
x_535 = lean_box(0);
if (x_533 == 0)
{
lean_del_object(x_29);
x_103 = x_531;
x_104 = x_535;
x_105 = x_534;
x_106 = x_524;
x_107 = x_525;
x_108 = x_526;
x_109 = x_527;
goto block_114;
}
else
{
lean_object* x_536; 
lean_inc(x_2);
x_536 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_526);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
lean_dec_ref(x_536);
lean_inc(x_534);
lean_inc(x_531);
x_538 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(x_538, 0, x_531);
lean_closure_set(x_538, 1, x_534);
x_539 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_540 = lean_unbox(x_537);
if (x_540 == 0)
{
lean_object* x_541; uint8_t x_542; 
x_541 = l_Lean_trace_profiler;
x_542 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_530, x_541);
if (x_542 == 0)
{
lean_dec_ref(x_538);
lean_dec(x_537);
lean_del_object(x_29);
x_103 = x_531;
x_104 = x_535;
x_105 = x_534;
x_106 = x_524;
x_107 = x_525;
x_108 = x_526;
x_109 = x_527;
goto block_114;
}
else
{
uint8_t x_543; 
lean_inc_ref(x_530);
x_543 = lean_unbox(x_537);
lean_dec(x_537);
x_488 = x_543;
x_489 = x_531;
x_490 = x_527;
x_491 = x_538;
x_492 = x_525;
x_493 = x_535;
x_494 = x_530;
x_495 = x_524;
x_496 = x_534;
x_497 = x_539;
x_498 = x_526;
goto block_523;
}
}
else
{
uint8_t x_544; 
lean_inc_ref(x_530);
x_544 = lean_unbox(x_537);
lean_dec(x_537);
x_488 = x_544;
x_489 = x_531;
x_490 = x_527;
x_491 = x_538;
x_492 = x_525;
x_493 = x_535;
x_494 = x_530;
x_495 = x_524;
x_496 = x_534;
x_497 = x_539;
x_498 = x_526;
goto block_523;
}
}
else
{
lean_object* x_545; lean_object* x_546; uint8_t x_547; uint8_t x_552; 
lean_dec(x_534);
lean_dec(x_531);
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_525);
lean_dec_ref(x_524);
lean_del_object(x_29);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_545 = lean_ctor_get(x_536, 0);
x_552 = !lean_is_exclusive(x_536);
if (x_552 == 0)
{
x_546 = x_536;
x_547 = x_552;
goto block_551;
}
else
{
lean_inc(x_545);
lean_dec(x_536);
x_546 = lean_box(0);
x_547 = x_552;
goto block_551;
}
block_551:
{
lean_object* x_548; 
if (x_547 == 0)
{
x_548 = x_546;
goto block_549;
}
else
{
lean_object* x_550; 
x_550 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_550, 0, x_545);
x_548 = x_550;
goto block_549;
}
block_549:
{
return x_548;
}
}
}
}
}
else
{
lean_object* x_553; lean_object* x_554; uint8_t x_555; uint8_t x_560; 
lean_dec(x_527);
lean_dec_ref(x_526);
lean_dec(x_525);
lean_dec_ref(x_524);
lean_del_object(x_29);
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_553 = lean_ctor_get(x_528, 0);
x_560 = !lean_is_exclusive(x_528);
if (x_560 == 0)
{
x_554 = x_528;
x_555 = x_560;
goto block_559;
}
else
{
lean_inc(x_553);
lean_dec(x_528);
x_554 = lean_box(0);
x_555 = x_560;
goto block_559;
}
block_559:
{
lean_object* x_556; 
if (x_555 == 0)
{
x_556 = x_554;
goto block_557;
}
else
{
lean_object* x_558; 
x_558 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_558, 0, x_553);
x_556 = x_558;
goto block_557;
}
block_557:
{
return x_556;
}
}
}
}
}
else
{
lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; 
lean_del_object(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_5);
x_1421 = lean_ctor_get(x_1, 0);
lean_inc(x_1421);
x_1422 = lean_box(0);
x_1423 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1421, x_6, x_1422, x_7, x_8, x_9, x_10);
return x_1423;
}
block_47:
{
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec_ref(x_32);
x_38 = l_Lean_Meta_SavedState_restore___redArg(x_31, x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
lean_dec_ref(x_31);
if (lean_obj_tag(x_38) == 0)
{
lean_dec_ref(x_38);
x_12 = x_33;
x_13 = x_35;
x_14 = x_28;
goto block_18;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_28);
x_39 = lean_ctor_get(x_38, 0);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
x_40 = x_38;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_34);
lean_dec_ref(x_31);
lean_dec(x_28);
x_19 = x_33;
x_20 = x_35;
x_21 = x_32;
goto block_23;
}
}
block_69:
{
lean_object* x_55; 
x_55 = l_Lean_Meta_saveState___redArg(x_52, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_54);
lean_inc(x_52);
lean_inc(x_28);
x_57 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_50, x_28, x_48, x_52, x_51, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_28);
x_19 = x_49;
x_20 = x_53;
x_21 = x_57;
goto block_23;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = l_Lean_Exception_isInterrupt(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Exception_isRuntime(x_58);
x_31 = x_56;
x_32 = x_57;
x_33 = x_49;
x_34 = x_52;
x_35 = x_53;
x_36 = x_54;
x_37 = x_60;
goto block_47;
}
else
{
lean_dec(x_58);
x_31 = x_56;
x_32 = x_57;
x_33 = x_49;
x_34 = x_52;
x_35 = x_53;
x_36 = x_54;
x_37 = x_59;
goto block_47;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_61 = lean_ctor_get(x_55, 0);
x_68 = !lean_is_exclusive(x_55);
if (x_68 == 0)
{
x_62 = x_55;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_55);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
block_90:
{
uint8_t x_77; 
x_77 = l_List_isEmpty___redArg(x_71);
lean_dec(x_71);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_78 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_79 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_78, x_70, x_74, x_73, x_76);
lean_dec(x_76);
lean_dec_ref(x_73);
lean_dec(x_74);
lean_dec_ref(x_70);
return x_79;
}
else
{
lean_object* x_80; 
x_80 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_72, x_28, x_70, x_74, x_73, x_76);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_89; 
x_81 = lean_ctor_get(x_80, 0);
x_89 = !lean_is_exclusive(x_80);
if (x_89 == 0)
{
x_82 = x_80;
x_83 = x_89;
goto block_88;
}
else
{
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_box(0);
x_83 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_List_appendTR___redArg(x_75, x_81);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_84);
x_85 = x_82;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_84);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
else
{
lean_dec(x_75);
return x_80;
}
}
}
block_102:
{
uint8_t x_99; lean_object* x_100; 
x_99 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_97);
x_100 = l_List_appendTR___redArg(x_98, x_97);
if (x_99 == 0)
{
x_70 = x_92;
x_71 = x_93;
x_72 = x_100;
x_73 = x_94;
x_74 = x_95;
x_75 = x_97;
x_76 = x_96;
goto block_90;
}
else
{
uint8_t x_101; 
x_101 = l_List_isEmpty___redArg(x_97);
if (x_101 == 0)
{
x_48 = x_92;
x_49 = x_93;
x_50 = x_100;
x_51 = x_94;
x_52 = x_95;
x_53 = x_97;
x_54 = x_96;
goto block_69;
}
else
{
if (x_91 == 0)
{
x_70 = x_92;
x_71 = x_93;
x_72 = x_100;
x_73 = x_94;
x_74 = x_95;
x_75 = x_97;
x_76 = x_96;
goto block_90;
}
else
{
x_48 = x_92;
x_49 = x_93;
x_50 = x_100;
x_51 = x_94;
x_52 = x_95;
x_53 = x_97;
x_54 = x_96;
goto block_69;
}
}
}
}
block_114:
{
lean_object* x_110; 
x_110 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_91, x_5, x_104, x_107);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = l_List_reverse___redArg(x_111);
x_92 = x_106;
x_93 = x_103;
x_94 = x_108;
x_95 = x_107;
x_96 = x_109;
x_97 = x_105;
x_98 = x_112;
goto block_102;
}
else
{
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
lean_dec_ref(x_110);
x_92 = x_106;
x_93 = x_103;
x_94 = x_108;
x_95 = x_107;
x_96 = x_109;
x_97 = x_105;
x_98 = x_113;
goto block_102;
}
else
{
lean_dec(x_109);
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_28);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_110;
}
}
}
}
}
else
{
lean_object* x_1426; lean_object* x_1427; uint8_t x_1428; uint8_t x_1433; 
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
x_1426 = lean_ctor_get(x_25, 0);
x_1433 = !lean_is_exclusive(x_25);
if (x_1433 == 0)
{
x_1427 = x_25;
x_1428 = x_1433;
goto block_1432;
}
else
{
lean_inc(x_1426);
lean_dec(x_25);
x_1427 = lean_box(0);
x_1428 = x_1433;
goto block_1432;
}
block_1432:
{
lean_object* x_1429; 
if (x_1428 == 0)
{
x_1429 = x_1427;
goto block_1430;
}
else
{
lean_object* x_1431; 
x_1431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1431, 0, x_1426);
x_1429 = x_1431;
goto block_1430;
}
block_1430:
{
return x_1429;
}
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_List_appendTR___redArg(x_13, x_12);
x_16 = l_List_appendTR___redArg(x_15, x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
block_23:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_12 = x_19;
x_13 = x_20;
x_14 = x_22;
goto block_18;
}
else
{
lean_dec(x_20);
lean_dec(x_19);
return x_21;
}
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

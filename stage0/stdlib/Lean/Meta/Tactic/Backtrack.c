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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_53; double x_84; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec_ref(x_8);
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_dec(x_15);
x_37 = l_Lean_trace_profiler;
x_38 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_4, x_37);
if (x_38 == 0)
{
x_53 = x_38;
goto block_83;
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_Lean_trace_profiler_useHeartbeats;
x_91 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_4, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; double x_94; double x_95; double x_96; 
x_92 = l_Lean_trace_profiler_threshold;
x_93 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(x_4, x_92);
x_94 = lean_float_of_nat(x_93);
x_95 = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3);
x_96 = lean_float_div(x_94, x_95);
x_84 = x_96;
goto block_89;
}
else
{
lean_object* x_97; lean_object* x_98; double x_99; 
x_97 = l_Lean_trace_profiler_threshold;
x_98 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(x_4, x_97);
x_99 = lean_float_of_nat(x_98);
x_84 = x_99;
goto block_89;
}
}
block_34:
{
lean_object* x_24; 
x_24 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(x_6, x_18, x_16, x_17, x_19, x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec_ref(x_24);
x_25 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_14);
x_26 = lean_ctor_get(x_24, 0);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
x_27 = x_24;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
block_47:
{
double x_42; lean_object* x_43; 
x_42 = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0);
lean_inc_ref(x_3);
lean_inc(x_1);
x_43 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_3);
lean_ctor_set_float(x_43, sizeof(void*)*2, x_42);
lean_ctor_set_float(x_43, sizeof(void*)*2 + 8, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 16, x_2);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_3);
lean_dec(x_1);
x_16 = x_39;
x_17 = x_40;
x_18 = x_43;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_44; double x_45; double x_46; 
lean_dec_ref(x_43);
x_44 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_3);
x_45 = lean_unbox_float(x_35);
lean_dec(x_35);
lean_ctor_set_float(x_44, sizeof(void*)*2, x_45);
x_46 = lean_unbox_float(x_36);
lean_dec(x_36);
lean_ctor_set_float(x_44, sizeof(void*)*2 + 8, x_46);
lean_ctor_set_uint8(x_44, sizeof(void*)*2 + 16, x_2);
x_16 = x_39;
x_17 = x_40;
x_18 = x_44;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = lean_box(0);
goto block_34;
}
}
block_52:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_11, 5);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_14);
x_49 = lean_apply_6(x_7, x_14, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_48);
x_39 = x_48;
x_40 = x_50;
x_41 = lean_box(0);
goto block_47;
}
else
{
lean_object* x_51; 
lean_dec_ref(x_49);
x_51 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2);
lean_inc(x_48);
x_39 = x_48;
x_40 = x_51;
x_41 = lean_box(0);
goto block_47;
}
}
block_83:
{
if (x_5 == 0)
{
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_82; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_54 = lean_st_ref_take(x_12);
x_55 = lean_ctor_get(x_54, 4);
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = lean_ctor_get(x_54, 2);
x_59 = lean_ctor_get(x_54, 3);
x_60 = lean_ctor_get(x_54, 5);
x_61 = lean_ctor_get(x_54, 6);
x_62 = lean_ctor_get(x_54, 7);
x_63 = lean_ctor_get(x_54, 8);
x_82 = !lean_is_exclusive(x_54);
if (x_82 == 0)
{
x_64 = x_54;
x_65 = x_82;
goto block_81;
}
else
{
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_55);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_64 = lean_box(0);
x_65 = x_82;
goto block_81;
}
block_81:
{
uint64_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_80; 
x_66 = lean_ctor_get_uint64(x_55, sizeof(void*)*1);
x_67 = lean_ctor_get(x_55, 0);
x_80 = !lean_is_exclusive(x_55);
if (x_80 == 0)
{
x_68 = x_55;
x_69 = x_80;
goto block_79;
}
else
{
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_box(0);
x_69 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_70; lean_object* x_71; 
x_70 = l_Lean_PersistentArray_append___redArg(x_6, x_67);
lean_dec_ref(x_67);
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_70);
x_71 = x_68;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set_uint64(x_78, sizeof(void*)*1, x_66);
x_71 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_72; 
if (x_65 == 0)
{
lean_ctor_set(x_64, 4, x_71);
x_72 = x_64;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_76, 0, x_56);
lean_ctor_set(x_76, 1, x_57);
lean_ctor_set(x_76, 2, x_58);
lean_ctor_set(x_76, 3, x_59);
lean_ctor_set(x_76, 4, x_71);
lean_ctor_set(x_76, 5, x_60);
lean_ctor_set(x_76, 6, x_61);
lean_ctor_set(x_76, 7, x_62);
lean_ctor_set(x_76, 8, x_63);
x_72 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_st_ref_set(x_12, x_72);
lean_dec(x_12);
x_74 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(x_14);
return x_74;
}
}
}
}
}
else
{
goto block_52;
}
}
else
{
goto block_52;
}
}
block_89:
{
double x_85; double x_86; double x_87; uint8_t x_88; 
x_85 = lean_unbox_float(x_36);
x_86 = lean_unbox_float(x_35);
x_87 = lean_float_sub(x_85, x_86);
x_88 = lean_float_decLt(x_84, x_87);
x_53 = x_88;
goto block_83;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_250; uint8_t x_251; 
x_250 = lean_unsigned_to_nat(0u);
x_251 = lean_nat_dec_eq(x_5, x_250);
if (x_251 == 1)
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_252 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
x_253 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_252, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; uint8_t x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; uint8_t x_435; lean_object* x_436; uint8_t x_437; lean_object* x_438; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; uint8_t x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; uint8_t x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; uint8_t x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; uint8_t x_568; uint8_t x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; lean_object* x_594; lean_object* x_595; uint8_t x_596; uint8_t x_597; uint8_t x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; uint8_t x_650; lean_object* x_651; lean_object* x_652; uint8_t x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_671; lean_object* x_672; lean_object* x_673; uint8_t x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; uint8_t x_678; lean_object* x_679; lean_object* x_680; uint8_t x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; uint8_t x_703; lean_object* x_704; uint8_t x_705; uint8_t x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; uint8_t x_730; lean_object* x_731; lean_object* x_732; uint8_t x_733; uint8_t x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; uint8_t x_755; lean_object* x_756; uint8_t x_757; uint8_t x_758; lean_object* x_759; lean_object* x_760; uint8_t x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; uint8_t x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; lean_object* x_816; lean_object* x_817; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; uint8_t x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; uint8_t x_839; lean_object* x_840; lean_object* x_841; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; uint8_t x_859; lean_object* x_860; lean_object* x_861; uint8_t x_862; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; uint8_t x_911; lean_object* x_912; uint8_t x_913; lean_object* x_914; lean_object* x_915; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; lean_object* x_933; uint8_t x_934; lean_object* x_935; lean_object* x_936; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; uint8_t x_956; lean_object* x_957; uint8_t x_958; lean_object* x_959; lean_object* x_960; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; uint8_t x_977; lean_object* x_978; uint8_t x_979; lean_object* x_980; lean_object* x_981; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; uint8_t x_1001; uint8_t x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; uint8_t x_1052; uint8_t x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; uint8_t x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; uint8_t x_1102; lean_object* x_1103; lean_object* x_1104; uint8_t x_1105; uint8_t x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; uint8_t x_1159; lean_object* x_1160; lean_object* x_1161; uint8_t x_1162; lean_object* x_1163; lean_object* x_1164; uint8_t x_1165; lean_object* x_1166; lean_object* x_1167; uint8_t x_1168; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; uint8_t x_1199; lean_object* x_1200; lean_object* x_1201; uint8_t x_1202; lean_object* x_1203; uint8_t x_1204; uint8_t x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; uint8_t x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; uint8_t x_1261; uint8_t x_1262; lean_object* x_1263; lean_object* x_1264; uint8_t x_1265; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; uint8_t x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; uint8_t x_1304; lean_object* x_1305; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; uint8_t x_1356; lean_object* x_1357; lean_object* x_1358; uint8_t x_1359; lean_object* x_1360; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; uint8_t x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; uint8_t x_1412; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; uint8_t x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1553; lean_object* x_1564; 
x_254 = lean_ctor_get(x_1, 1);
x_255 = lean_ctor_get(x_1, 2);
x_256 = lean_ctor_get(x_1, 3);
x_257 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
x_368 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
x_479 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
x_1047 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
x_1094 = lean_unsigned_to_nat(1u);
x_1095 = lean_nat_sub(x_5, x_1094);
lean_dec(x_5);
lean_inc_ref(x_254);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_1564 = lean_apply_7(x_254, x_4, x_6, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1564) == 0)
{
lean_object* x_1565; 
x_1565 = lean_ctor_get(x_1564, 0);
lean_inc(x_1565);
lean_dec_ref(x_1564);
x_1493 = x_1565;
x_1494 = x_8;
x_1495 = x_9;
x_1496 = x_10;
x_1497 = x_11;
x_1498 = lean_box(0);
goto block_1552;
}
else
{
lean_object* x_1566; lean_object* x_1567; uint8_t x_1568; uint8_t x_1639; 
x_1566 = lean_ctor_get(x_1564, 0);
x_1639 = !lean_is_exclusive(x_1564);
if (x_1639 == 0)
{
x_1567 = x_1564;
x_1568 = x_1639;
goto block_1638;
}
else
{
lean_inc(x_1566);
lean_dec(x_1564);
x_1567 = lean_box(0);
x_1568 = x_1639;
goto block_1638;
}
block_1638:
{
lean_object* x_1569; lean_object* x_1570; uint8_t x_1571; uint8_t x_1572; lean_object* x_1573; lean_object* x_1574; uint8_t x_1611; uint8_t x_1636; 
lean_inc(x_1566);
x_1569 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(x_1569, 0, x_1566);
x_1636 = l_Lean_Exception_isInterrupt(x_1566);
if (x_1636 == 0)
{
uint8_t x_1637; 
lean_inc(x_1566);
x_1637 = l_Lean_Exception_isRuntime(x_1566);
x_1611 = x_1637;
goto block_1635;
}
else
{
x_1611 = x_1636;
goto block_1635;
}
block_1610:
{
lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; uint8_t x_1578; uint8_t x_1609; 
x_1575 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
x_1576 = lean_ctor_get(x_1575, 0);
x_1609 = !lean_is_exclusive(x_1575);
if (x_1609 == 0)
{
x_1577 = x_1575;
x_1578 = x_1609;
goto block_1608;
}
else
{
lean_inc(x_1576);
lean_dec(x_1575);
x_1577 = lean_box(0);
x_1578 = x_1609;
goto block_1608;
}
block_1608:
{
lean_object* x_1579; uint8_t x_1580; 
x_1579 = l_Lean_trace_profiler_useHeartbeats;
x_1580 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1574, x_1579);
if (x_1580 == 0)
{
lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; 
x_1581 = lean_io_mono_nanos_now();
x_1582 = lean_io_mono_nanos_now();
if (x_1578 == 0)
{
lean_ctor_set(x_1577, 0, x_1566);
x_1583 = x_1577;
goto block_1594;
}
else
{
lean_object* x_1595; 
x_1595 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1595, 0, x_1566);
x_1583 = x_1595;
goto block_1594;
}
block_1594:
{
double x_1584; double x_1585; double x_1586; double x_1587; double x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; 
x_1584 = lean_float_of_nat(x_1581);
x_1585 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_1586 = lean_float_div(x_1584, x_1585);
x_1587 = lean_float_of_nat(x_1582);
x_1588 = lean_float_div(x_1587, x_1585);
x_1589 = lean_box_float(x_1586);
x_1590 = lean_box_float(x_1588);
x_1591 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1591, 0, x_1589);
lean_ctor_set(x_1591, 1, x_1590);
x_1592 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1592, 0, x_1583);
lean_ctor_set(x_1592, 1, x_1591);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1593 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1571, x_1573, x_1574, x_1572, x_1576, x_1569, x_1592, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1574);
x_1553 = x_1593;
goto block_1563;
}
}
else
{
lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; 
x_1596 = lean_io_get_num_heartbeats();
x_1597 = lean_io_get_num_heartbeats();
if (x_1578 == 0)
{
lean_ctor_set(x_1577, 0, x_1566);
x_1598 = x_1577;
goto block_1606;
}
else
{
lean_object* x_1607; 
x_1607 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1607, 0, x_1566);
x_1598 = x_1607;
goto block_1606;
}
block_1606:
{
double x_1599; double x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; 
x_1599 = lean_float_of_nat(x_1596);
x_1600 = lean_float_of_nat(x_1597);
x_1601 = lean_box_float(x_1599);
x_1602 = lean_box_float(x_1600);
x_1603 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1603, 0, x_1601);
lean_ctor_set(x_1603, 1, x_1602);
x_1604 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1604, 0, x_1598);
lean_ctor_set(x_1604, 1, x_1603);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1605 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1571, x_1573, x_1574, x_1572, x_1576, x_1569, x_1604, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1574);
x_1553 = x_1605;
goto block_1563;
}
}
}
}
block_1635:
{
if (x_1611 == 0)
{
lean_object* x_1612; uint8_t x_1613; 
x_1612 = lean_ctor_get(x_10, 2);
x_1613 = lean_ctor_get_uint8(x_1612, sizeof(void*)*1);
if (x_1613 == 0)
{
lean_object* x_1614; 
lean_dec_ref(x_1569);
lean_dec(x_1095);
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
if (x_1568 == 0)
{
x_1614 = x_1567;
goto block_1615;
}
else
{
lean_object* x_1616; 
x_1616 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1616, 0, x_1566);
x_1614 = x_1616;
goto block_1615;
}
block_1615:
{
return x_1614;
}
}
else
{
lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; uint8_t x_1620; uint8_t x_1631; 
lean_del_object(x_1567);
lean_inc(x_2);
x_1617 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1618 = lean_ctor_get(x_1617, 0);
x_1631 = !lean_is_exclusive(x_1617);
if (x_1631 == 0)
{
x_1619 = x_1617;
x_1620 = x_1631;
goto block_1630;
}
else
{
lean_inc(x_1618);
lean_dec(x_1617);
x_1619 = lean_box(0);
x_1620 = x_1631;
goto block_1630;
}
block_1630:
{
lean_object* x_1621; uint8_t x_1622; 
x_1621 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1622 = lean_unbox(x_1618);
if (x_1622 == 0)
{
lean_object* x_1623; uint8_t x_1624; 
x_1623 = l_Lean_trace_profiler;
x_1624 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1612, x_1623);
if (x_1624 == 0)
{
lean_object* x_1625; 
lean_dec(x_1618);
lean_dec_ref(x_1569);
lean_dec(x_1095);
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
if (x_1620 == 0)
{
lean_ctor_set_tag(x_1619, 1);
lean_ctor_set(x_1619, 0, x_1566);
x_1625 = x_1619;
goto block_1626;
}
else
{
lean_object* x_1627; 
x_1627 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1627, 0, x_1566);
x_1625 = x_1627;
goto block_1626;
}
block_1626:
{
return x_1625;
}
}
else
{
uint8_t x_1628; 
lean_del_object(x_1619);
x_1628 = lean_unbox(x_1618);
lean_dec(x_1618);
lean_inc_ref(x_1612);
x_1570 = lean_box(0);
x_1571 = x_1613;
x_1572 = x_1628;
x_1573 = x_1621;
x_1574 = x_1612;
goto block_1610;
}
}
else
{
uint8_t x_1629; 
lean_del_object(x_1619);
x_1629 = lean_unbox(x_1618);
lean_dec(x_1618);
lean_inc_ref(x_1612);
x_1570 = lean_box(0);
x_1571 = x_1613;
x_1572 = x_1629;
x_1573 = x_1621;
x_1574 = x_1612;
goto block_1610;
}
}
}
}
else
{
lean_object* x_1632; 
lean_dec_ref(x_1569);
lean_dec(x_1095);
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
if (x_1568 == 0)
{
x_1632 = x_1567;
goto block_1633;
}
else
{
lean_object* x_1634; 
x_1634 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1634, 0, x_1566);
x_1632 = x_1634;
goto block_1633;
}
block_1633:
{
return x_1632;
}
}
}
}
}
block_285:
{
lean_object* x_274; double x_275; double x_276; double x_277; double x_278; double x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_274 = lean_io_mono_nanos_now();
x_275 = lean_float_of_nat(x_264);
x_276 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_277 = lean_float_div(x_275, x_276);
x_278 = lean_float_of_nat(x_274);
x_279 = lean_float_div(x_278, x_276);
x_280 = lean_box_float(x_277);
x_281 = lean_box_float(x_279);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_272);
lean_ctor_set(x_283, 1, x_282);
lean_inc(x_265);
lean_inc_ref(x_260);
lean_inc(x_259);
lean_inc_ref(x_262);
lean_inc_ref(x_271);
lean_inc(x_2);
x_284 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_267, x_271, x_258, x_270, x_266, x_257, x_283, x_262, x_259, x_260, x_265);
x_165 = x_258;
x_166 = x_259;
x_167 = x_267;
x_168 = x_268;
x_169 = x_260;
x_170 = x_261;
x_171 = x_269;
x_172 = x_262;
x_173 = x_263;
x_174 = x_271;
x_175 = x_265;
x_176 = x_284;
goto block_179;
}
block_310:
{
lean_object* x_302; double x_303; double x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_io_get_num_heartbeats();
x_303 = lean_float_of_nat(x_298);
x_304 = lean_float_of_nat(x_302);
x_305 = lean_box_float(x_303);
x_306 = lean_box_float(x_304);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_300);
lean_ctor_set(x_308, 1, x_307);
lean_inc(x_292);
lean_inc_ref(x_288);
lean_inc(x_287);
lean_inc_ref(x_290);
lean_inc_ref(x_299);
lean_inc(x_2);
x_309 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_294, x_299, x_286, x_297, x_293, x_257, x_308, x_290, x_287, x_288, x_292);
x_165 = x_286;
x_166 = x_287;
x_167 = x_294;
x_168 = x_295;
x_169 = x_288;
x_170 = x_289;
x_171 = x_296;
x_172 = x_290;
x_173 = x_291;
x_174 = x_299;
x_175 = x_292;
x_176 = x_309;
goto block_179;
}
block_367:
{
lean_object* x_328; 
x_328 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_320);
if (x_322 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
lean_dec_ref(x_328);
x_330 = lean_io_mono_nanos_now();
lean_inc(x_320);
lean_inc_ref(x_316);
lean_inc(x_313);
lean_inc_ref(x_318);
lean_inc(x_2);
x_331 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_321, x_315, x_312, x_318, x_313, x_316, x_320);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; uint8_t x_334; uint8_t x_339; 
x_332 = lean_ctor_get(x_331, 0);
x_339 = !lean_is_exclusive(x_331);
if (x_339 == 0)
{
x_333 = x_331;
x_334 = x_339;
goto block_338;
}
else
{
lean_inc(x_332);
lean_dec(x_331);
x_333 = lean_box(0);
x_334 = x_339;
goto block_338;
}
block_338:
{
lean_object* x_335; 
if (x_334 == 0)
{
lean_ctor_set_tag(x_333, 1);
x_335 = x_333;
goto block_336;
}
else
{
lean_object* x_337; 
x_337 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_337, 0, x_332);
x_335 = x_337;
goto block_336;
}
block_336:
{
x_258 = x_311;
x_259 = x_313;
x_260 = x_316;
x_261 = x_317;
x_262 = x_318;
x_263 = x_319;
x_264 = x_330;
x_265 = x_320;
x_266 = x_329;
x_267 = x_323;
x_268 = x_324;
x_269 = x_325;
x_270 = x_326;
x_271 = x_327;
x_272 = x_335;
x_273 = lean_box(0);
goto block_285;
}
}
}
else
{
lean_object* x_340; lean_object* x_341; uint8_t x_342; uint8_t x_347; 
x_340 = lean_ctor_get(x_331, 0);
x_347 = !lean_is_exclusive(x_331);
if (x_347 == 0)
{
x_341 = x_331;
x_342 = x_347;
goto block_346;
}
else
{
lean_inc(x_340);
lean_dec(x_331);
x_341 = lean_box(0);
x_342 = x_347;
goto block_346;
}
block_346:
{
lean_object* x_343; 
if (x_342 == 0)
{
lean_ctor_set_tag(x_341, 0);
x_343 = x_341;
goto block_344;
}
else
{
lean_object* x_345; 
x_345 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_345, 0, x_340);
x_343 = x_345;
goto block_344;
}
block_344:
{
x_258 = x_311;
x_259 = x_313;
x_260 = x_316;
x_261 = x_317;
x_262 = x_318;
x_263 = x_319;
x_264 = x_330;
x_265 = x_320;
x_266 = x_329;
x_267 = x_323;
x_268 = x_324;
x_269 = x_325;
x_270 = x_326;
x_271 = x_327;
x_272 = x_343;
x_273 = lean_box(0);
goto block_285;
}
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_328, 0);
lean_inc(x_348);
lean_dec_ref(x_328);
x_349 = lean_io_get_num_heartbeats();
lean_inc(x_320);
lean_inc_ref(x_316);
lean_inc(x_313);
lean_inc_ref(x_318);
lean_inc(x_2);
x_350 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_321, x_315, x_312, x_318, x_313, x_316, x_320);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; uint8_t x_353; uint8_t x_358; 
x_351 = lean_ctor_get(x_350, 0);
x_358 = !lean_is_exclusive(x_350);
if (x_358 == 0)
{
x_352 = x_350;
x_353 = x_358;
goto block_357;
}
else
{
lean_inc(x_351);
lean_dec(x_350);
x_352 = lean_box(0);
x_353 = x_358;
goto block_357;
}
block_357:
{
lean_object* x_354; 
if (x_353 == 0)
{
lean_ctor_set_tag(x_352, 1);
x_354 = x_352;
goto block_355;
}
else
{
lean_object* x_356; 
x_356 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_356, 0, x_351);
x_354 = x_356;
goto block_355;
}
block_355:
{
x_286 = x_311;
x_287 = x_313;
x_288 = x_316;
x_289 = x_317;
x_290 = x_318;
x_291 = x_319;
x_292 = x_320;
x_293 = x_348;
x_294 = x_323;
x_295 = x_324;
x_296 = x_325;
x_297 = x_326;
x_298 = x_349;
x_299 = x_327;
x_300 = x_354;
x_301 = lean_box(0);
goto block_310;
}
}
}
else
{
lean_object* x_359; lean_object* x_360; uint8_t x_361; uint8_t x_366; 
x_359 = lean_ctor_get(x_350, 0);
x_366 = !lean_is_exclusive(x_350);
if (x_366 == 0)
{
x_360 = x_350;
x_361 = x_366;
goto block_365;
}
else
{
lean_inc(x_359);
lean_dec(x_350);
x_360 = lean_box(0);
x_361 = x_366;
goto block_365;
}
block_365:
{
lean_object* x_362; 
if (x_361 == 0)
{
lean_ctor_set_tag(x_360, 0);
x_362 = x_360;
goto block_363;
}
else
{
lean_object* x_364; 
x_364 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_364, 0, x_359);
x_362 = x_364;
goto block_363;
}
block_363:
{
x_286 = x_311;
x_287 = x_313;
x_288 = x_316;
x_289 = x_317;
x_290 = x_318;
x_291 = x_319;
x_292 = x_320;
x_293 = x_348;
x_294 = x_323;
x_295 = x_324;
x_296 = x_325;
x_297 = x_326;
x_298 = x_349;
x_299 = x_327;
x_300 = x_362;
x_301 = lean_box(0);
goto block_310;
}
}
}
}
}
block_396:
{
lean_object* x_385; double x_386; double x_387; double x_388; double x_389; double x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_385 = lean_io_mono_nanos_now();
x_386 = lean_float_of_nat(x_379);
x_387 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_388 = lean_float_div(x_386, x_387);
x_389 = lean_float_of_nat(x_385);
x_390 = lean_float_div(x_389, x_387);
x_391 = lean_box_float(x_388);
x_392 = lean_box_float(x_390);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_383);
lean_ctor_set(x_394, 1, x_393);
lean_inc(x_377);
lean_inc_ref(x_372);
lean_inc(x_371);
lean_inc_ref(x_374);
lean_inc_ref(x_382);
lean_inc(x_2);
x_395 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_378, x_382, x_369, x_381, x_370, x_368, x_394, x_374, x_371, x_372, x_377);
x_235 = x_369;
x_236 = x_371;
x_237 = x_378;
x_238 = x_372;
x_239 = x_373;
x_240 = x_380;
x_241 = x_374;
x_242 = x_375;
x_243 = x_382;
x_244 = x_376;
x_245 = x_377;
x_246 = x_395;
goto block_249;
}
block_421:
{
lean_object* x_413; double x_414; double x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_413 = lean_io_get_num_heartbeats();
x_414 = lean_float_of_nat(x_406);
x_415 = lean_float_of_nat(x_413);
x_416 = lean_box_float(x_414);
x_417 = lean_box_float(x_415);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_411);
lean_ctor_set(x_419, 1, x_418);
lean_inc(x_405);
lean_inc_ref(x_400);
lean_inc(x_399);
lean_inc_ref(x_402);
lean_inc_ref(x_410);
lean_inc(x_2);
x_420 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_407, x_410, x_397, x_409, x_398, x_368, x_419, x_402, x_399, x_400, x_405);
x_235 = x_397;
x_236 = x_399;
x_237 = x_407;
x_238 = x_400;
x_239 = x_401;
x_240 = x_408;
x_241 = x_402;
x_242 = x_403;
x_243 = x_410;
x_244 = x_404;
x_245 = x_405;
x_246 = x_420;
goto block_249;
}
block_478:
{
lean_object* x_439; 
x_439 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_431);
if (x_434 == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
lean_dec_ref(x_439);
x_441 = lean_io_mono_nanos_now();
lean_inc(x_431);
lean_inc_ref(x_426);
lean_inc(x_424);
lean_inc_ref(x_428);
lean_inc(x_2);
x_442 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_422, x_425, x_432, x_428, x_424, x_426, x_431);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; uint8_t x_445; uint8_t x_450; 
x_443 = lean_ctor_get(x_442, 0);
x_450 = !lean_is_exclusive(x_442);
if (x_450 == 0)
{
x_444 = x_442;
x_445 = x_450;
goto block_449;
}
else
{
lean_inc(x_443);
lean_dec(x_442);
x_444 = lean_box(0);
x_445 = x_450;
goto block_449;
}
block_449:
{
lean_object* x_446; 
if (x_445 == 0)
{
lean_ctor_set_tag(x_444, 1);
x_446 = x_444;
goto block_447;
}
else
{
lean_object* x_448; 
x_448 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_448, 0, x_443);
x_446 = x_448;
goto block_447;
}
block_447:
{
x_369 = x_423;
x_370 = x_440;
x_371 = x_424;
x_372 = x_426;
x_373 = x_427;
x_374 = x_428;
x_375 = x_429;
x_376 = x_430;
x_377 = x_431;
x_378 = x_435;
x_379 = x_441;
x_380 = x_436;
x_381 = x_437;
x_382 = x_438;
x_383 = x_446;
x_384 = lean_box(0);
goto block_396;
}
}
}
else
{
lean_object* x_451; lean_object* x_452; uint8_t x_453; uint8_t x_458; 
x_451 = lean_ctor_get(x_442, 0);
x_458 = !lean_is_exclusive(x_442);
if (x_458 == 0)
{
x_452 = x_442;
x_453 = x_458;
goto block_457;
}
else
{
lean_inc(x_451);
lean_dec(x_442);
x_452 = lean_box(0);
x_453 = x_458;
goto block_457;
}
block_457:
{
lean_object* x_454; 
if (x_453 == 0)
{
lean_ctor_set_tag(x_452, 0);
x_454 = x_452;
goto block_455;
}
else
{
lean_object* x_456; 
x_456 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_456, 0, x_451);
x_454 = x_456;
goto block_455;
}
block_455:
{
x_369 = x_423;
x_370 = x_440;
x_371 = x_424;
x_372 = x_426;
x_373 = x_427;
x_374 = x_428;
x_375 = x_429;
x_376 = x_430;
x_377 = x_431;
x_378 = x_435;
x_379 = x_441;
x_380 = x_436;
x_381 = x_437;
x_382 = x_438;
x_383 = x_454;
x_384 = lean_box(0);
goto block_396;
}
}
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_439, 0);
lean_inc(x_459);
lean_dec_ref(x_439);
x_460 = lean_io_get_num_heartbeats();
lean_inc(x_431);
lean_inc_ref(x_426);
lean_inc(x_424);
lean_inc_ref(x_428);
lean_inc(x_2);
x_461 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_422, x_425, x_432, x_428, x_424, x_426, x_431);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; uint8_t x_464; uint8_t x_469; 
x_462 = lean_ctor_get(x_461, 0);
x_469 = !lean_is_exclusive(x_461);
if (x_469 == 0)
{
x_463 = x_461;
x_464 = x_469;
goto block_468;
}
else
{
lean_inc(x_462);
lean_dec(x_461);
x_463 = lean_box(0);
x_464 = x_469;
goto block_468;
}
block_468:
{
lean_object* x_465; 
if (x_464 == 0)
{
lean_ctor_set_tag(x_463, 1);
x_465 = x_463;
goto block_466;
}
else
{
lean_object* x_467; 
x_467 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_467, 0, x_462);
x_465 = x_467;
goto block_466;
}
block_466:
{
x_397 = x_423;
x_398 = x_459;
x_399 = x_424;
x_400 = x_426;
x_401 = x_427;
x_402 = x_428;
x_403 = x_429;
x_404 = x_430;
x_405 = x_431;
x_406 = x_460;
x_407 = x_435;
x_408 = x_436;
x_409 = x_437;
x_410 = x_438;
x_411 = x_465;
x_412 = lean_box(0);
goto block_421;
}
}
}
else
{
lean_object* x_470; lean_object* x_471; uint8_t x_472; uint8_t x_477; 
x_470 = lean_ctor_get(x_461, 0);
x_477 = !lean_is_exclusive(x_461);
if (x_477 == 0)
{
x_471 = x_461;
x_472 = x_477;
goto block_476;
}
else
{
lean_inc(x_470);
lean_dec(x_461);
x_471 = lean_box(0);
x_472 = x_477;
goto block_476;
}
block_476:
{
lean_object* x_473; 
if (x_472 == 0)
{
lean_ctor_set_tag(x_471, 0);
x_473 = x_471;
goto block_474;
}
else
{
lean_object* x_475; 
x_475 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_475, 0, x_470);
x_473 = x_475;
goto block_474;
}
block_474:
{
x_397 = x_423;
x_398 = x_459;
x_399 = x_424;
x_400 = x_426;
x_401 = x_427;
x_402 = x_428;
x_403 = x_429;
x_404 = x_430;
x_405 = x_431;
x_406 = x_460;
x_407 = x_435;
x_408 = x_436;
x_409 = x_437;
x_410 = x_438;
x_411 = x_473;
x_412 = lean_box(0);
goto block_421;
}
}
}
}
}
block_504:
{
lean_object* x_496; double x_497; double x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_496 = lean_io_get_num_heartbeats();
x_497 = lean_float_of_nat(x_484);
x_498 = lean_float_of_nat(x_496);
x_499 = lean_box_float(x_497);
x_500 = lean_box_float(x_498);
x_501 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_494);
lean_ctor_set(x_502, 1, x_501);
lean_inc(x_488);
lean_inc_ref(x_482);
lean_inc(x_481);
lean_inc_ref(x_485);
lean_inc_ref(x_493);
lean_inc(x_2);
x_503 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_490, x_493, x_480, x_491, x_489, x_479, x_502, x_485, x_481, x_482, x_488);
x_235 = x_480;
x_236 = x_481;
x_237 = x_490;
x_238 = x_482;
x_239 = x_483;
x_240 = x_492;
x_241 = x_485;
x_242 = x_486;
x_243 = x_493;
x_244 = x_487;
x_245 = x_488;
x_246 = x_503;
goto block_249;
}
block_532:
{
lean_object* x_521; double x_522; double x_523; double x_524; double x_525; double x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_521 = lean_io_mono_nanos_now();
x_522 = lean_float_of_nat(x_517);
x_523 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_524 = lean_float_div(x_522, x_523);
x_525 = lean_float_of_nat(x_521);
x_526 = lean_float_div(x_525, x_523);
x_527 = lean_box_float(x_524);
x_528 = lean_box_float(x_526);
x_529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_529, 0, x_527);
lean_ctor_set(x_529, 1, x_528);
x_530 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_530, 0, x_519);
lean_ctor_set(x_530, 1, x_529);
lean_inc(x_512);
lean_inc_ref(x_507);
lean_inc(x_506);
lean_inc_ref(x_509);
lean_inc_ref(x_518);
lean_inc(x_2);
x_531 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_514, x_518, x_505, x_515, x_513, x_479, x_530, x_509, x_506, x_507, x_512);
x_235 = x_505;
x_236 = x_506;
x_237 = x_514;
x_238 = x_507;
x_239 = x_508;
x_240 = x_516;
x_241 = x_509;
x_242 = x_510;
x_243 = x_518;
x_244 = x_511;
x_245 = x_512;
x_246 = x_531;
goto block_249;
}
block_557:
{
lean_object* x_549; double x_550; double x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_549 = lean_io_get_num_heartbeats();
x_550 = lean_float_of_nat(x_542);
x_551 = lean_float_of_nat(x_549);
x_552 = lean_box_float(x_550);
x_553 = lean_box_float(x_551);
x_554 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_554, 0, x_552);
lean_ctor_set(x_554, 1, x_553);
x_555 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_555, 0, x_547);
lean_ctor_set(x_555, 1, x_554);
lean_inc(x_541);
lean_inc_ref(x_535);
lean_inc(x_534);
lean_inc_ref(x_537);
lean_inc_ref(x_546);
lean_inc(x_2);
x_556 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_544, x_546, x_533, x_543, x_540, x_257, x_555, x_537, x_534, x_535, x_541);
x_235 = x_533;
x_236 = x_534;
x_237 = x_544;
x_238 = x_535;
x_239 = x_536;
x_240 = x_545;
x_241 = x_537;
x_242 = x_538;
x_243 = x_546;
x_244 = x_539;
x_245 = x_541;
x_246 = x_556;
goto block_249;
}
block_585:
{
lean_object* x_574; double x_575; double x_576; double x_577; double x_578; double x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_574 = lean_io_mono_nanos_now();
x_575 = lean_float_of_nat(x_559);
x_576 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_577 = lean_float_div(x_575, x_576);
x_578 = lean_float_of_nat(x_574);
x_579 = lean_float_div(x_578, x_576);
x_580 = lean_box_float(x_577);
x_581 = lean_box_float(x_579);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
x_583 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_583, 0, x_572);
lean_ctor_set(x_583, 1, x_582);
lean_inc(x_567);
lean_inc_ref(x_561);
lean_inc(x_560);
lean_inc_ref(x_563);
lean_inc_ref(x_571);
lean_inc(x_2);
x_584 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_569, x_571, x_558, x_568, x_566, x_257, x_583, x_563, x_560, x_561, x_567);
x_235 = x_558;
x_236 = x_560;
x_237 = x_569;
x_238 = x_561;
x_239 = x_562;
x_240 = x_570;
x_241 = x_563;
x_242 = x_564;
x_243 = x_571;
x_244 = x_565;
x_245 = x_567;
x_246 = x_584;
goto block_249;
}
block_642:
{
lean_object* x_603; 
x_603 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_595);
if (x_597 == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
lean_dec_ref(x_603);
x_605 = lean_io_mono_nanos_now();
lean_inc(x_595);
lean_inc_ref(x_589);
lean_inc(x_587);
lean_inc_ref(x_592);
lean_inc(x_2);
x_606 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_601, x_588, x_591, x_592, x_587, x_589, x_595);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; uint8_t x_609; uint8_t x_614; 
x_607 = lean_ctor_get(x_606, 0);
x_614 = !lean_is_exclusive(x_606);
if (x_614 == 0)
{
x_608 = x_606;
x_609 = x_614;
goto block_613;
}
else
{
lean_inc(x_607);
lean_dec(x_606);
x_608 = lean_box(0);
x_609 = x_614;
goto block_613;
}
block_613:
{
lean_object* x_610; 
if (x_609 == 0)
{
lean_ctor_set_tag(x_608, 1);
x_610 = x_608;
goto block_611;
}
else
{
lean_object* x_612; 
x_612 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_612, 0, x_607);
x_610 = x_612;
goto block_611;
}
block_611:
{
x_558 = x_586;
x_559 = x_605;
x_560 = x_587;
x_561 = x_589;
x_562 = x_590;
x_563 = x_592;
x_564 = x_593;
x_565 = x_594;
x_566 = x_604;
x_567 = x_595;
x_568 = x_596;
x_569 = x_598;
x_570 = x_600;
x_571 = x_602;
x_572 = x_610;
x_573 = lean_box(0);
goto block_585;
}
}
}
else
{
lean_object* x_615; lean_object* x_616; uint8_t x_617; uint8_t x_622; 
x_615 = lean_ctor_get(x_606, 0);
x_622 = !lean_is_exclusive(x_606);
if (x_622 == 0)
{
x_616 = x_606;
x_617 = x_622;
goto block_621;
}
else
{
lean_inc(x_615);
lean_dec(x_606);
x_616 = lean_box(0);
x_617 = x_622;
goto block_621;
}
block_621:
{
lean_object* x_618; 
if (x_617 == 0)
{
lean_ctor_set_tag(x_616, 0);
x_618 = x_616;
goto block_619;
}
else
{
lean_object* x_620; 
x_620 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_620, 0, x_615);
x_618 = x_620;
goto block_619;
}
block_619:
{
x_558 = x_586;
x_559 = x_605;
x_560 = x_587;
x_561 = x_589;
x_562 = x_590;
x_563 = x_592;
x_564 = x_593;
x_565 = x_594;
x_566 = x_604;
x_567 = x_595;
x_568 = x_596;
x_569 = x_598;
x_570 = x_600;
x_571 = x_602;
x_572 = x_618;
x_573 = lean_box(0);
goto block_585;
}
}
}
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_ctor_get(x_603, 0);
lean_inc(x_623);
lean_dec_ref(x_603);
x_624 = lean_io_get_num_heartbeats();
lean_inc(x_595);
lean_inc_ref(x_589);
lean_inc(x_587);
lean_inc_ref(x_592);
lean_inc(x_2);
x_625 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_601, x_588, x_591, x_592, x_587, x_589, x_595);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; uint8_t x_628; uint8_t x_633; 
x_626 = lean_ctor_get(x_625, 0);
x_633 = !lean_is_exclusive(x_625);
if (x_633 == 0)
{
x_627 = x_625;
x_628 = x_633;
goto block_632;
}
else
{
lean_inc(x_626);
lean_dec(x_625);
x_627 = lean_box(0);
x_628 = x_633;
goto block_632;
}
block_632:
{
lean_object* x_629; 
if (x_628 == 0)
{
lean_ctor_set_tag(x_627, 1);
x_629 = x_627;
goto block_630;
}
else
{
lean_object* x_631; 
x_631 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_631, 0, x_626);
x_629 = x_631;
goto block_630;
}
block_630:
{
x_533 = x_586;
x_534 = x_587;
x_535 = x_589;
x_536 = x_590;
x_537 = x_592;
x_538 = x_593;
x_539 = x_594;
x_540 = x_623;
x_541 = x_595;
x_542 = x_624;
x_543 = x_596;
x_544 = x_598;
x_545 = x_600;
x_546 = x_602;
x_547 = x_629;
x_548 = lean_box(0);
goto block_557;
}
}
}
else
{
lean_object* x_634; lean_object* x_635; uint8_t x_636; uint8_t x_641; 
x_634 = lean_ctor_get(x_625, 0);
x_641 = !lean_is_exclusive(x_625);
if (x_641 == 0)
{
x_635 = x_625;
x_636 = x_641;
goto block_640;
}
else
{
lean_inc(x_634);
lean_dec(x_625);
x_635 = lean_box(0);
x_636 = x_641;
goto block_640;
}
block_640:
{
lean_object* x_637; 
if (x_636 == 0)
{
lean_ctor_set_tag(x_635, 0);
x_637 = x_635;
goto block_638;
}
else
{
lean_object* x_639; 
x_639 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_639, 0, x_634);
x_637 = x_639;
goto block_638;
}
block_638:
{
x_533 = x_586;
x_534 = x_587;
x_535 = x_589;
x_536 = x_590;
x_537 = x_592;
x_538 = x_593;
x_539 = x_594;
x_540 = x_623;
x_541 = x_595;
x_542 = x_624;
x_543 = x_596;
x_544 = x_598;
x_545 = x_600;
x_546 = x_602;
x_547 = x_637;
x_548 = lean_box(0);
goto block_557;
}
}
}
}
}
block_670:
{
lean_object* x_659; double x_660; double x_661; double x_662; double x_663; double x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_659 = lean_io_mono_nanos_now();
x_660 = lean_float_of_nat(x_652);
x_661 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_662 = lean_float_div(x_660, x_661);
x_663 = lean_float_of_nat(x_659);
x_664 = lean_float_div(x_663, x_661);
x_665 = lean_box_float(x_662);
x_666 = lean_box_float(x_664);
x_667 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_667, 0, x_665);
lean_ctor_set(x_667, 1, x_666);
x_668 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_668, 0, x_657);
lean_ctor_set(x_668, 1, x_667);
lean_inc(x_651);
lean_inc_ref(x_647);
lean_inc(x_645);
lean_inc_ref(x_649);
lean_inc_ref(x_656);
lean_inc(x_2);
x_669 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_653, x_656, x_643, x_646, x_644, x_479, x_668, x_649, x_645, x_647, x_651);
x_165 = x_643;
x_166 = x_645;
x_167 = x_653;
x_168 = x_654;
x_169 = x_647;
x_170 = x_648;
x_171 = x_655;
x_172 = x_649;
x_173 = x_650;
x_174 = x_656;
x_175 = x_651;
x_176 = x_669;
goto block_179;
}
block_695:
{
lean_object* x_687; double x_688; double x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_687 = lean_io_get_num_heartbeats();
x_688 = lean_float_of_nat(x_680);
x_689 = lean_float_of_nat(x_687);
x_690 = lean_box_float(x_688);
x_691 = lean_box_float(x_689);
x_692 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_692, 0, x_690);
lean_ctor_set(x_692, 1, x_691);
x_693 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_693, 0, x_685);
lean_ctor_set(x_693, 1, x_692);
lean_inc(x_679);
lean_inc_ref(x_675);
lean_inc(x_673);
lean_inc_ref(x_677);
lean_inc_ref(x_684);
lean_inc(x_2);
x_694 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_681, x_684, x_671, x_674, x_672, x_479, x_693, x_677, x_673, x_675, x_679);
x_165 = x_671;
x_166 = x_673;
x_167 = x_681;
x_168 = x_682;
x_169 = x_675;
x_170 = x_676;
x_171 = x_683;
x_172 = x_677;
x_173 = x_678;
x_174 = x_684;
x_175 = x_679;
x_176 = x_694;
goto block_179;
}
block_723:
{
lean_object* x_712; double x_713; double x_714; double x_715; double x_716; double x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_712 = lean_io_mono_nanos_now();
x_713 = lean_float_of_nat(x_697);
x_714 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_715 = lean_float_div(x_713, x_714);
x_716 = lean_float_of_nat(x_712);
x_717 = lean_float_div(x_716, x_714);
x_718 = lean_box_float(x_715);
x_719 = lean_box_float(x_717);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_718);
lean_ctor_set(x_720, 1, x_719);
x_721 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_721, 0, x_710);
lean_ctor_set(x_721, 1, x_720);
lean_inc(x_704);
lean_inc_ref(x_700);
lean_inc(x_698);
lean_inc_ref(x_702);
lean_inc_ref(x_709);
lean_inc(x_2);
x_722 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_706, x_709, x_696, x_705, x_699, x_368, x_721, x_702, x_698, x_700, x_704);
x_165 = x_696;
x_166 = x_698;
x_167 = x_706;
x_168 = x_707;
x_169 = x_700;
x_170 = x_701;
x_171 = x_708;
x_172 = x_702;
x_173 = x_703;
x_174 = x_709;
x_175 = x_704;
x_176 = x_722;
goto block_179;
}
block_748:
{
lean_object* x_740; double x_741; double x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_740 = lean_io_get_num_heartbeats();
x_741 = lean_float_of_nat(x_732);
x_742 = lean_float_of_nat(x_740);
x_743 = lean_box_float(x_741);
x_744 = lean_box_float(x_742);
x_745 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_745, 0, x_743);
lean_ctor_set(x_745, 1, x_744);
x_746 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_746, 0, x_738);
lean_ctor_set(x_746, 1, x_745);
lean_inc(x_731);
lean_inc_ref(x_727);
lean_inc(x_725);
lean_inc_ref(x_729);
lean_inc_ref(x_737);
lean_inc(x_2);
x_747 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_734, x_737, x_724, x_733, x_726, x_368, x_746, x_729, x_725, x_727, x_731);
x_165 = x_724;
x_166 = x_725;
x_167 = x_734;
x_168 = x_735;
x_169 = x_727;
x_170 = x_728;
x_171 = x_736;
x_172 = x_729;
x_173 = x_730;
x_174 = x_737;
x_175 = x_731;
x_176 = x_747;
goto block_179;
}
block_805:
{
lean_object* x_766; 
x_766 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_756);
if (x_757 == 0)
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
lean_dec_ref(x_766);
x_768 = lean_io_mono_nanos_now();
lean_inc(x_756);
lean_inc_ref(x_752);
lean_inc(x_750);
lean_inc_ref(x_754);
lean_inc(x_2);
x_769 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_763, x_751, x_759, x_754, x_750, x_752, x_756);
if (lean_obj_tag(x_769) == 0)
{
lean_object* x_770; lean_object* x_771; uint8_t x_772; uint8_t x_777; 
x_770 = lean_ctor_get(x_769, 0);
x_777 = !lean_is_exclusive(x_769);
if (x_777 == 0)
{
x_771 = x_769;
x_772 = x_777;
goto block_776;
}
else
{
lean_inc(x_770);
lean_dec(x_769);
x_771 = lean_box(0);
x_772 = x_777;
goto block_776;
}
block_776:
{
lean_object* x_773; 
if (x_772 == 0)
{
lean_ctor_set_tag(x_771, 1);
x_773 = x_771;
goto block_774;
}
else
{
lean_object* x_775; 
x_775 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_775, 0, x_770);
x_773 = x_775;
goto block_774;
}
block_774:
{
x_696 = x_749;
x_697 = x_768;
x_698 = x_750;
x_699 = x_767;
x_700 = x_752;
x_701 = x_753;
x_702 = x_754;
x_703 = x_755;
x_704 = x_756;
x_705 = x_758;
x_706 = x_761;
x_707 = x_762;
x_708 = x_764;
x_709 = x_765;
x_710 = x_773;
x_711 = lean_box(0);
goto block_723;
}
}
}
else
{
lean_object* x_778; lean_object* x_779; uint8_t x_780; uint8_t x_785; 
x_778 = lean_ctor_get(x_769, 0);
x_785 = !lean_is_exclusive(x_769);
if (x_785 == 0)
{
x_779 = x_769;
x_780 = x_785;
goto block_784;
}
else
{
lean_inc(x_778);
lean_dec(x_769);
x_779 = lean_box(0);
x_780 = x_785;
goto block_784;
}
block_784:
{
lean_object* x_781; 
if (x_780 == 0)
{
lean_ctor_set_tag(x_779, 0);
x_781 = x_779;
goto block_782;
}
else
{
lean_object* x_783; 
x_783 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_783, 0, x_778);
x_781 = x_783;
goto block_782;
}
block_782:
{
x_696 = x_749;
x_697 = x_768;
x_698 = x_750;
x_699 = x_767;
x_700 = x_752;
x_701 = x_753;
x_702 = x_754;
x_703 = x_755;
x_704 = x_756;
x_705 = x_758;
x_706 = x_761;
x_707 = x_762;
x_708 = x_764;
x_709 = x_765;
x_710 = x_781;
x_711 = lean_box(0);
goto block_723;
}
}
}
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_786 = lean_ctor_get(x_766, 0);
lean_inc(x_786);
lean_dec_ref(x_766);
x_787 = lean_io_get_num_heartbeats();
lean_inc(x_756);
lean_inc_ref(x_752);
lean_inc(x_750);
lean_inc_ref(x_754);
lean_inc(x_2);
x_788 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_763, x_751, x_759, x_754, x_750, x_752, x_756);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; uint8_t x_791; uint8_t x_796; 
x_789 = lean_ctor_get(x_788, 0);
x_796 = !lean_is_exclusive(x_788);
if (x_796 == 0)
{
x_790 = x_788;
x_791 = x_796;
goto block_795;
}
else
{
lean_inc(x_789);
lean_dec(x_788);
x_790 = lean_box(0);
x_791 = x_796;
goto block_795;
}
block_795:
{
lean_object* x_792; 
if (x_791 == 0)
{
lean_ctor_set_tag(x_790, 1);
x_792 = x_790;
goto block_793;
}
else
{
lean_object* x_794; 
x_794 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_794, 0, x_789);
x_792 = x_794;
goto block_793;
}
block_793:
{
x_724 = x_749;
x_725 = x_750;
x_726 = x_786;
x_727 = x_752;
x_728 = x_753;
x_729 = x_754;
x_730 = x_755;
x_731 = x_756;
x_732 = x_787;
x_733 = x_758;
x_734 = x_761;
x_735 = x_762;
x_736 = x_764;
x_737 = x_765;
x_738 = x_792;
x_739 = lean_box(0);
goto block_748;
}
}
}
else
{
lean_object* x_797; lean_object* x_798; uint8_t x_799; uint8_t x_804; 
x_797 = lean_ctor_get(x_788, 0);
x_804 = !lean_is_exclusive(x_788);
if (x_804 == 0)
{
x_798 = x_788;
x_799 = x_804;
goto block_803;
}
else
{
lean_inc(x_797);
lean_dec(x_788);
x_798 = lean_box(0);
x_799 = x_804;
goto block_803;
}
block_803:
{
lean_object* x_800; 
if (x_799 == 0)
{
lean_ctor_set_tag(x_798, 0);
x_800 = x_798;
goto block_801;
}
else
{
lean_object* x_802; 
x_802 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_802, 0, x_797);
x_800 = x_802;
goto block_801;
}
block_801:
{
x_724 = x_749;
x_725 = x_750;
x_726 = x_786;
x_727 = x_752;
x_728 = x_753;
x_729 = x_754;
x_730 = x_755;
x_731 = x_756;
x_732 = x_787;
x_733 = x_758;
x_734 = x_761;
x_735 = x_762;
x_736 = x_764;
x_737 = x_765;
x_738 = x_800;
x_739 = lean_box(0);
goto block_748;
}
}
}
}
}
block_829:
{
lean_object* x_818; double x_819; double x_820; double x_821; double x_822; double x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_818 = lean_io_mono_nanos_now();
x_819 = lean_float_of_nat(x_814);
x_820 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_821 = lean_float_div(x_819, x_820);
x_822 = lean_float_of_nat(x_818);
x_823 = lean_float_div(x_822, x_820);
x_824 = lean_box_float(x_821);
x_825 = lean_box_float(x_823);
x_826 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_826, 0, x_824);
lean_ctor_set(x_826, 1, x_825);
x_827 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_827, 0, x_816);
lean_ctor_set(x_827, 1, x_826);
x_828 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_810, x_813, x_807, x_815, x_812, x_368, x_827, x_809, x_808, x_811, x_806);
lean_dec_ref(x_807);
return x_828;
}
block_850:
{
lean_object* x_842; double x_843; double x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_842 = lean_io_get_num_heartbeats();
x_843 = lean_float_of_nat(x_830);
x_844 = lean_float_of_nat(x_842);
x_845 = lean_box_float(x_843);
x_846 = lean_box_float(x_844);
x_847 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_847, 0, x_845);
lean_ctor_set(x_847, 1, x_846);
x_848 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_848, 0, x_840);
lean_ctor_set(x_848, 1, x_847);
x_849 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_835, x_838, x_832, x_839, x_837, x_368, x_848, x_834, x_833, x_836, x_831);
lean_dec_ref(x_832);
return x_849;
}
block_903:
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; uint8_t x_866; 
x_863 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_853);
x_864 = lean_ctor_get(x_863, 0);
lean_inc(x_864);
lean_dec_ref(x_863);
x_865 = l_Lean_trace_profiler_useHeartbeats;
x_866 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_855, x_865);
if (x_866 == 0)
{
lean_object* x_867; lean_object* x_868; 
x_867 = lean_io_mono_nanos_now();
lean_inc(x_853);
lean_inc_ref(x_861);
lean_inc(x_856);
lean_inc_ref(x_857);
lean_inc(x_2);
x_868 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_854, x_858, x_851, x_857, x_856, x_861, x_853);
if (lean_obj_tag(x_868) == 0)
{
lean_object* x_869; lean_object* x_870; uint8_t x_871; uint8_t x_876; 
x_869 = lean_ctor_get(x_868, 0);
x_876 = !lean_is_exclusive(x_868);
if (x_876 == 0)
{
x_870 = x_868;
x_871 = x_876;
goto block_875;
}
else
{
lean_inc(x_869);
lean_dec(x_868);
x_870 = lean_box(0);
x_871 = x_876;
goto block_875;
}
block_875:
{
lean_object* x_872; 
if (x_871 == 0)
{
lean_ctor_set_tag(x_870, 1);
x_872 = x_870;
goto block_873;
}
else
{
lean_object* x_874; 
x_874 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_874, 0, x_869);
x_872 = x_874;
goto block_873;
}
block_873:
{
x_806 = x_853;
x_807 = x_855;
x_808 = x_856;
x_809 = x_857;
x_810 = x_859;
x_811 = x_861;
x_812 = x_864;
x_813 = x_860;
x_814 = x_867;
x_815 = x_862;
x_816 = x_872;
x_817 = lean_box(0);
goto block_829;
}
}
}
else
{
lean_object* x_877; lean_object* x_878; uint8_t x_879; uint8_t x_884; 
x_877 = lean_ctor_get(x_868, 0);
x_884 = !lean_is_exclusive(x_868);
if (x_884 == 0)
{
x_878 = x_868;
x_879 = x_884;
goto block_883;
}
else
{
lean_inc(x_877);
lean_dec(x_868);
x_878 = lean_box(0);
x_879 = x_884;
goto block_883;
}
block_883:
{
lean_object* x_880; 
if (x_879 == 0)
{
lean_ctor_set_tag(x_878, 0);
x_880 = x_878;
goto block_881;
}
else
{
lean_object* x_882; 
x_882 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_882, 0, x_877);
x_880 = x_882;
goto block_881;
}
block_881:
{
x_806 = x_853;
x_807 = x_855;
x_808 = x_856;
x_809 = x_857;
x_810 = x_859;
x_811 = x_861;
x_812 = x_864;
x_813 = x_860;
x_814 = x_867;
x_815 = x_862;
x_816 = x_880;
x_817 = lean_box(0);
goto block_829;
}
}
}
}
else
{
lean_object* x_885; lean_object* x_886; 
x_885 = lean_io_get_num_heartbeats();
lean_inc(x_853);
lean_inc_ref(x_861);
lean_inc(x_856);
lean_inc_ref(x_857);
lean_inc(x_2);
x_886 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_854, x_858, x_851, x_857, x_856, x_861, x_853);
if (lean_obj_tag(x_886) == 0)
{
lean_object* x_887; lean_object* x_888; uint8_t x_889; uint8_t x_894; 
x_887 = lean_ctor_get(x_886, 0);
x_894 = !lean_is_exclusive(x_886);
if (x_894 == 0)
{
x_888 = x_886;
x_889 = x_894;
goto block_893;
}
else
{
lean_inc(x_887);
lean_dec(x_886);
x_888 = lean_box(0);
x_889 = x_894;
goto block_893;
}
block_893:
{
lean_object* x_890; 
if (x_889 == 0)
{
lean_ctor_set_tag(x_888, 1);
x_890 = x_888;
goto block_891;
}
else
{
lean_object* x_892; 
x_892 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_892, 0, x_887);
x_890 = x_892;
goto block_891;
}
block_891:
{
x_830 = x_885;
x_831 = x_853;
x_832 = x_855;
x_833 = x_856;
x_834 = x_857;
x_835 = x_859;
x_836 = x_861;
x_837 = x_864;
x_838 = x_860;
x_839 = x_862;
x_840 = x_890;
x_841 = lean_box(0);
goto block_850;
}
}
}
else
{
lean_object* x_895; lean_object* x_896; uint8_t x_897; uint8_t x_902; 
x_895 = lean_ctor_get(x_886, 0);
x_902 = !lean_is_exclusive(x_886);
if (x_902 == 0)
{
x_896 = x_886;
x_897 = x_902;
goto block_901;
}
else
{
lean_inc(x_895);
lean_dec(x_886);
x_896 = lean_box(0);
x_897 = x_902;
goto block_901;
}
block_901:
{
lean_object* x_898; 
if (x_897 == 0)
{
lean_ctor_set_tag(x_896, 0);
x_898 = x_896;
goto block_899;
}
else
{
lean_object* x_900; 
x_900 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_900, 0, x_895);
x_898 = x_900;
goto block_899;
}
block_899:
{
x_830 = x_885;
x_831 = x_853;
x_832 = x_855;
x_833 = x_856;
x_834 = x_857;
x_835 = x_859;
x_836 = x_861;
x_837 = x_864;
x_838 = x_860;
x_839 = x_862;
x_840 = x_898;
x_841 = lean_box(0);
goto block_850;
}
}
}
}
}
block_924:
{
lean_object* x_916; double x_917; double x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_916 = lean_io_get_num_heartbeats();
x_917 = lean_float_of_nat(x_908);
x_918 = lean_float_of_nat(x_916);
x_919 = lean_box_float(x_917);
x_920 = lean_box_float(x_918);
x_921 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_921, 0, x_919);
lean_ctor_set(x_921, 1, x_920);
x_922 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_922, 0, x_914);
lean_ctor_set(x_922, 1, x_921);
x_923 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_911, x_907, x_904, x_913, x_910, x_479, x_922, x_909, x_906, x_912, x_905);
lean_dec_ref(x_904);
return x_923;
}
block_948:
{
lean_object* x_937; double x_938; double x_939; double x_940; double x_941; double x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_937 = lean_io_mono_nanos_now();
x_938 = lean_float_of_nat(x_930);
x_939 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_940 = lean_float_div(x_938, x_939);
x_941 = lean_float_of_nat(x_937);
x_942 = lean_float_div(x_941, x_939);
x_943 = lean_box_float(x_940);
x_944 = lean_box_float(x_942);
x_945 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_945, 0, x_943);
lean_ctor_set(x_945, 1, x_944);
x_946 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_946, 0, x_935);
lean_ctor_set(x_946, 1, x_945);
x_947 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_932, x_928, x_925, x_934, x_931, x_479, x_946, x_929, x_927, x_933, x_926);
lean_dec_ref(x_925);
return x_947;
}
block_969:
{
lean_object* x_961; double x_962; double x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_961 = lean_io_get_num_heartbeats();
x_962 = lean_float_of_nat(x_949);
x_963 = lean_float_of_nat(x_961);
x_964 = lean_box_float(x_962);
x_965 = lean_box_float(x_963);
x_966 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_966, 0, x_964);
lean_ctor_set(x_966, 1, x_965);
x_967 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_967, 0, x_959);
lean_ctor_set(x_967, 1, x_966);
x_968 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_956, x_955, x_951, x_958, x_954, x_257, x_967, x_953, x_952, x_957, x_950);
lean_dec_ref(x_951);
return x_968;
}
block_993:
{
lean_object* x_982; double x_983; double x_984; double x_985; double x_986; double x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_982 = lean_io_mono_nanos_now();
x_983 = lean_float_of_nat(x_970);
x_984 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_985 = lean_float_div(x_983, x_984);
x_986 = lean_float_of_nat(x_982);
x_987 = lean_float_div(x_986, x_984);
x_988 = lean_box_float(x_985);
x_989 = lean_box_float(x_987);
x_990 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_990, 0, x_988);
lean_ctor_set(x_990, 1, x_989);
x_991 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_991, 0, x_980);
lean_ctor_set(x_991, 1, x_990);
x_992 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_977, x_976, x_972, x_979, x_975, x_257, x_991, x_974, x_973, x_978, x_971);
lean_dec_ref(x_972);
return x_992;
}
block_1046:
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; uint8_t x_1009; 
x_1006 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_995);
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
lean_dec_ref(x_1006);
x_1008 = l_Lean_trace_profiler_useHeartbeats;
x_1009 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_996, x_1008);
if (x_1009 == 0)
{
lean_object* x_1010; lean_object* x_1011; 
x_1010 = lean_io_mono_nanos_now();
lean_inc(x_995);
lean_inc_ref(x_1003);
lean_inc(x_997);
lean_inc_ref(x_998);
lean_inc(x_2);
x_1011 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1005, x_1000, x_1004, x_998, x_997, x_1003, x_995);
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; uint8_t x_1019; 
x_1012 = lean_ctor_get(x_1011, 0);
x_1019 = !lean_is_exclusive(x_1011);
if (x_1019 == 0)
{
x_1013 = x_1011;
x_1014 = x_1019;
goto block_1018;
}
else
{
lean_inc(x_1012);
lean_dec(x_1011);
x_1013 = lean_box(0);
x_1014 = x_1019;
goto block_1018;
}
block_1018:
{
lean_object* x_1015; 
if (x_1014 == 0)
{
lean_ctor_set_tag(x_1013, 1);
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
x_970 = x_1010;
x_971 = x_995;
x_972 = x_996;
x_973 = x_997;
x_974 = x_998;
x_975 = x_1007;
x_976 = x_999;
x_977 = x_1001;
x_978 = x_1003;
x_979 = x_1002;
x_980 = x_1015;
x_981 = lean_box(0);
goto block_993;
}
}
}
else
{
lean_object* x_1020; lean_object* x_1021; uint8_t x_1022; uint8_t x_1027; 
x_1020 = lean_ctor_get(x_1011, 0);
x_1027 = !lean_is_exclusive(x_1011);
if (x_1027 == 0)
{
x_1021 = x_1011;
x_1022 = x_1027;
goto block_1026;
}
else
{
lean_inc(x_1020);
lean_dec(x_1011);
x_1021 = lean_box(0);
x_1022 = x_1027;
goto block_1026;
}
block_1026:
{
lean_object* x_1023; 
if (x_1022 == 0)
{
lean_ctor_set_tag(x_1021, 0);
x_1023 = x_1021;
goto block_1024;
}
else
{
lean_object* x_1025; 
x_1025 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1025, 0, x_1020);
x_1023 = x_1025;
goto block_1024;
}
block_1024:
{
x_970 = x_1010;
x_971 = x_995;
x_972 = x_996;
x_973 = x_997;
x_974 = x_998;
x_975 = x_1007;
x_976 = x_999;
x_977 = x_1001;
x_978 = x_1003;
x_979 = x_1002;
x_980 = x_1023;
x_981 = lean_box(0);
goto block_993;
}
}
}
}
else
{
lean_object* x_1028; lean_object* x_1029; 
x_1028 = lean_io_get_num_heartbeats();
lean_inc(x_995);
lean_inc_ref(x_1003);
lean_inc(x_997);
lean_inc_ref(x_998);
lean_inc(x_2);
x_1029 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1005, x_1000, x_1004, x_998, x_997, x_1003, x_995);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; uint8_t x_1032; uint8_t x_1037; 
x_1030 = lean_ctor_get(x_1029, 0);
x_1037 = !lean_is_exclusive(x_1029);
if (x_1037 == 0)
{
x_1031 = x_1029;
x_1032 = x_1037;
goto block_1036;
}
else
{
lean_inc(x_1030);
lean_dec(x_1029);
x_1031 = lean_box(0);
x_1032 = x_1037;
goto block_1036;
}
block_1036:
{
lean_object* x_1033; 
if (x_1032 == 0)
{
lean_ctor_set_tag(x_1031, 1);
x_1033 = x_1031;
goto block_1034;
}
else
{
lean_object* x_1035; 
x_1035 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1035, 0, x_1030);
x_1033 = x_1035;
goto block_1034;
}
block_1034:
{
x_949 = x_1028;
x_950 = x_995;
x_951 = x_996;
x_952 = x_997;
x_953 = x_998;
x_954 = x_1007;
x_955 = x_999;
x_956 = x_1001;
x_957 = x_1003;
x_958 = x_1002;
x_959 = x_1033;
x_960 = lean_box(0);
goto block_969;
}
}
}
else
{
lean_object* x_1038; lean_object* x_1039; uint8_t x_1040; uint8_t x_1045; 
x_1038 = lean_ctor_get(x_1029, 0);
x_1045 = !lean_is_exclusive(x_1029);
if (x_1045 == 0)
{
x_1039 = x_1029;
x_1040 = x_1045;
goto block_1044;
}
else
{
lean_inc(x_1038);
lean_dec(x_1029);
x_1039 = lean_box(0);
x_1040 = x_1045;
goto block_1044;
}
block_1044:
{
lean_object* x_1041; 
if (x_1040 == 0)
{
lean_ctor_set_tag(x_1039, 0);
x_1041 = x_1039;
goto block_1042;
}
else
{
lean_object* x_1043; 
x_1043 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1043, 0, x_1038);
x_1041 = x_1043;
goto block_1042;
}
block_1042:
{
x_949 = x_1028;
x_950 = x_995;
x_951 = x_996;
x_952 = x_997;
x_953 = x_998;
x_954 = x_1007;
x_955 = x_999;
x_956 = x_1001;
x_957 = x_1003;
x_958 = x_1002;
x_959 = x_1041;
x_960 = lean_box(0);
goto block_969;
}
}
}
}
}
block_1093:
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; uint8_t x_1061; uint8_t x_1092; 
x_1058 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1057);
x_1059 = lean_ctor_get(x_1058, 0);
x_1092 = !lean_is_exclusive(x_1058);
if (x_1092 == 0)
{
x_1060 = x_1058;
x_1061 = x_1092;
goto block_1091;
}
else
{
lean_inc(x_1059);
lean_dec(x_1058);
x_1060 = lean_box(0);
x_1061 = x_1092;
goto block_1091;
}
block_1091:
{
lean_object* x_1062; uint8_t x_1063; 
x_1062 = l_Lean_trace_profiler_useHeartbeats;
x_1063 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1048, x_1062);
if (x_1063 == 0)
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1064 = lean_io_mono_nanos_now();
x_1065 = lean_io_mono_nanos_now();
if (x_1061 == 0)
{
lean_ctor_set_tag(x_1060, 1);
lean_ctor_set(x_1060, 0, x_1049);
x_1066 = x_1060;
goto block_1077;
}
else
{
lean_object* x_1078; 
x_1078 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1078, 0, x_1049);
x_1066 = x_1078;
goto block_1077;
}
block_1077:
{
double x_1067; double x_1068; double x_1069; double x_1070; double x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
x_1067 = lean_float_of_nat(x_1064);
x_1068 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_1069 = lean_float_div(x_1067, x_1068);
x_1070 = lean_float_of_nat(x_1065);
x_1071 = lean_float_div(x_1070, x_1068);
x_1072 = lean_box_float(x_1069);
x_1073 = lean_box_float(x_1071);
x_1074 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1074, 0, x_1072);
lean_ctor_set(x_1074, 1, x_1073);
x_1075 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1075, 0, x_1066);
lean_ctor_set(x_1075, 1, x_1074);
x_1076 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1053, x_1050, x_1048, x_1052, x_1059, x_1047, x_1075, x_1056, x_1051, x_1054, x_1057);
lean_dec_ref(x_1048);
return x_1076;
}
}
else
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1079 = lean_io_get_num_heartbeats();
x_1080 = lean_io_get_num_heartbeats();
if (x_1061 == 0)
{
lean_ctor_set_tag(x_1060, 1);
lean_ctor_set(x_1060, 0, x_1049);
x_1081 = x_1060;
goto block_1089;
}
else
{
lean_object* x_1090; 
x_1090 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1090, 0, x_1049);
x_1081 = x_1090;
goto block_1089;
}
block_1089:
{
double x_1082; double x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
x_1082 = lean_float_of_nat(x_1079);
x_1083 = lean_float_of_nat(x_1080);
x_1084 = lean_box_float(x_1082);
x_1085 = lean_box_float(x_1083);
x_1086 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1086, 0, x_1084);
lean_ctor_set(x_1086, 1, x_1085);
x_1087 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1087, 0, x_1081);
lean_ctor_set(x_1087, 1, x_1086);
x_1088 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1053, x_1050, x_1048, x_1052, x_1059, x_1047, x_1087, x_1056, x_1051, x_1054, x_1057);
lean_dec_ref(x_1048);
return x_1088;
}
}
}
}
block_1150:
{
lean_object* x_1111; 
x_1111 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1103);
if (x_1105 == 0)
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
x_1112 = lean_ctor_get(x_1111, 0);
lean_inc(x_1112);
lean_dec_ref(x_1111);
x_1113 = lean_io_mono_nanos_now();
lean_inc(x_1103);
lean_inc_ref(x_1099);
lean_inc(x_1097);
lean_inc_ref(x_1101);
lean_inc(x_2);
x_1114 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1095, x_1110, x_7, x_1101, x_1097, x_1099, x_1103);
if (lean_obj_tag(x_1114) == 0)
{
lean_object* x_1115; lean_object* x_1116; uint8_t x_1117; uint8_t x_1122; 
x_1115 = lean_ctor_get(x_1114, 0);
x_1122 = !lean_is_exclusive(x_1114);
if (x_1122 == 0)
{
x_1116 = x_1114;
x_1117 = x_1122;
goto block_1121;
}
else
{
lean_inc(x_1115);
lean_dec(x_1114);
x_1116 = lean_box(0);
x_1117 = x_1122;
goto block_1121;
}
block_1121:
{
lean_object* x_1118; 
if (x_1117 == 0)
{
lean_ctor_set_tag(x_1116, 1);
x_1118 = x_1116;
goto block_1119;
}
else
{
lean_object* x_1120; 
x_1120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1120, 0, x_1115);
x_1118 = x_1120;
goto block_1119;
}
block_1119:
{
x_643 = x_1096;
x_644 = x_1112;
x_645 = x_1097;
x_646 = x_1098;
x_647 = x_1099;
x_648 = x_1100;
x_649 = x_1101;
x_650 = x_1102;
x_651 = x_1103;
x_652 = x_1113;
x_653 = x_1106;
x_654 = x_1107;
x_655 = x_1108;
x_656 = x_1109;
x_657 = x_1118;
x_658 = lean_box(0);
goto block_670;
}
}
}
else
{
lean_object* x_1123; lean_object* x_1124; uint8_t x_1125; uint8_t x_1130; 
x_1123 = lean_ctor_get(x_1114, 0);
x_1130 = !lean_is_exclusive(x_1114);
if (x_1130 == 0)
{
x_1124 = x_1114;
x_1125 = x_1130;
goto block_1129;
}
else
{
lean_inc(x_1123);
lean_dec(x_1114);
x_1124 = lean_box(0);
x_1125 = x_1130;
goto block_1129;
}
block_1129:
{
lean_object* x_1126; 
if (x_1125 == 0)
{
lean_ctor_set_tag(x_1124, 0);
x_1126 = x_1124;
goto block_1127;
}
else
{
lean_object* x_1128; 
x_1128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1128, 0, x_1123);
x_1126 = x_1128;
goto block_1127;
}
block_1127:
{
x_643 = x_1096;
x_644 = x_1112;
x_645 = x_1097;
x_646 = x_1098;
x_647 = x_1099;
x_648 = x_1100;
x_649 = x_1101;
x_650 = x_1102;
x_651 = x_1103;
x_652 = x_1113;
x_653 = x_1106;
x_654 = x_1107;
x_655 = x_1108;
x_656 = x_1109;
x_657 = x_1126;
x_658 = lean_box(0);
goto block_670;
}
}
}
}
else
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; 
x_1131 = lean_ctor_get(x_1111, 0);
lean_inc(x_1131);
lean_dec_ref(x_1111);
x_1132 = lean_io_get_num_heartbeats();
lean_inc(x_1103);
lean_inc_ref(x_1099);
lean_inc(x_1097);
lean_inc_ref(x_1101);
lean_inc(x_2);
x_1133 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1095, x_1110, x_7, x_1101, x_1097, x_1099, x_1103);
if (lean_obj_tag(x_1133) == 0)
{
lean_object* x_1134; lean_object* x_1135; uint8_t x_1136; uint8_t x_1141; 
x_1134 = lean_ctor_get(x_1133, 0);
x_1141 = !lean_is_exclusive(x_1133);
if (x_1141 == 0)
{
x_1135 = x_1133;
x_1136 = x_1141;
goto block_1140;
}
else
{
lean_inc(x_1134);
lean_dec(x_1133);
x_1135 = lean_box(0);
x_1136 = x_1141;
goto block_1140;
}
block_1140:
{
lean_object* x_1137; 
if (x_1136 == 0)
{
lean_ctor_set_tag(x_1135, 1);
x_1137 = x_1135;
goto block_1138;
}
else
{
lean_object* x_1139; 
x_1139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1139, 0, x_1134);
x_1137 = x_1139;
goto block_1138;
}
block_1138:
{
x_671 = x_1096;
x_672 = x_1131;
x_673 = x_1097;
x_674 = x_1098;
x_675 = x_1099;
x_676 = x_1100;
x_677 = x_1101;
x_678 = x_1102;
x_679 = x_1103;
x_680 = x_1132;
x_681 = x_1106;
x_682 = x_1107;
x_683 = x_1108;
x_684 = x_1109;
x_685 = x_1137;
x_686 = lean_box(0);
goto block_695;
}
}
}
else
{
lean_object* x_1142; lean_object* x_1143; uint8_t x_1144; uint8_t x_1149; 
x_1142 = lean_ctor_get(x_1133, 0);
x_1149 = !lean_is_exclusive(x_1133);
if (x_1149 == 0)
{
x_1143 = x_1133;
x_1144 = x_1149;
goto block_1148;
}
else
{
lean_inc(x_1142);
lean_dec(x_1133);
x_1143 = lean_box(0);
x_1144 = x_1149;
goto block_1148;
}
block_1148:
{
lean_object* x_1145; 
if (x_1144 == 0)
{
lean_ctor_set_tag(x_1143, 0);
x_1145 = x_1143;
goto block_1146;
}
else
{
lean_object* x_1147; 
x_1147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1147, 0, x_1142);
x_1145 = x_1147;
goto block_1146;
}
block_1146:
{
x_671 = x_1096;
x_672 = x_1131;
x_673 = x_1097;
x_674 = x_1098;
x_675 = x_1099;
x_676 = x_1100;
x_677 = x_1101;
x_678 = x_1102;
x_679 = x_1103;
x_680 = x_1132;
x_681 = x_1106;
x_682 = x_1107;
x_683 = x_1108;
x_684 = x_1109;
x_685 = x_1145;
x_686 = lean_box(0);
goto block_695;
}
}
}
}
}
block_1192:
{
if (x_1168 == 0)
{
lean_object* x_1169; 
lean_dec_ref(x_1163);
lean_inc(x_1160);
lean_inc_ref(x_1156);
lean_inc(x_1152);
lean_inc_ref(x_1158);
lean_inc(x_1161);
x_1169 = lean_apply_6(x_1155, x_1161, x_1158, x_1152, x_1156, x_1160, lean_box(0));
if (lean_obj_tag(x_1169) == 0)
{
lean_object* x_1170; 
x_1170 = lean_ctor_get(x_1169, 0);
lean_inc(x_1170);
lean_dec_ref(x_1169);
if (lean_obj_tag(x_1170) == 0)
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; uint8_t x_1175; 
lean_inc(x_2);
x_1171 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1156);
x_1172 = lean_ctor_get(x_1171, 0);
lean_inc(x_1172);
lean_dec_ref(x_1171);
x_1173 = lean_nat_add(x_1095, x_1094);
lean_dec(x_1095);
x_1174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1174, 0, x_1161);
lean_ctor_set(x_1174, 1, x_7);
x_1175 = lean_unbox(x_1172);
if (x_1175 == 0)
{
lean_object* x_1176; uint8_t x_1177; 
x_1176 = l_Lean_trace_profiler;
x_1177 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1151, x_1176);
if (x_1177 == 0)
{
lean_object* x_1178; 
lean_dec(x_1172);
lean_inc(x_1160);
lean_inc_ref(x_1156);
lean_inc(x_1152);
lean_inc_ref(x_1158);
lean_inc(x_2);
x_1178 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1173, x_1154, x_1174, x_1158, x_1152, x_1156, x_1160);
x_165 = x_1151;
x_166 = x_1152;
x_167 = x_1165;
x_168 = x_1164;
x_169 = x_1156;
x_170 = x_1157;
x_171 = x_1166;
x_172 = x_1158;
x_173 = x_1159;
x_174 = x_1167;
x_175 = x_1160;
x_176 = x_1178;
goto block_179;
}
else
{
uint8_t x_1179; 
x_1179 = lean_unbox(x_1172);
lean_dec(x_1172);
x_749 = x_1151;
x_750 = x_1152;
x_751 = x_1154;
x_752 = x_1156;
x_753 = x_1157;
x_754 = x_1158;
x_755 = x_1159;
x_756 = x_1160;
x_757 = x_1162;
x_758 = x_1179;
x_759 = x_1174;
x_760 = lean_box(0);
x_761 = x_1165;
x_762 = x_1164;
x_763 = x_1173;
x_764 = x_1166;
x_765 = x_1167;
goto block_805;
}
}
else
{
uint8_t x_1180; 
x_1180 = lean_unbox(x_1172);
lean_dec(x_1172);
x_749 = x_1151;
x_750 = x_1152;
x_751 = x_1154;
x_752 = x_1156;
x_753 = x_1157;
x_754 = x_1158;
x_755 = x_1159;
x_756 = x_1160;
x_757 = x_1162;
x_758 = x_1180;
x_759 = x_1174;
x_760 = lean_box(0);
x_761 = x_1165;
x_762 = x_1164;
x_763 = x_1173;
x_764 = x_1166;
x_765 = x_1167;
goto block_805;
}
}
else
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; uint8_t x_1185; 
lean_dec(x_1161);
x_1181 = lean_ctor_get(x_1170, 0);
lean_inc(x_1181);
lean_dec_ref(x_1170);
lean_inc(x_2);
x_1182 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1156);
x_1183 = lean_ctor_get(x_1182, 0);
lean_inc(x_1183);
lean_dec_ref(x_1182);
x_1184 = l_List_appendTR___redArg(x_1181, x_1154);
x_1185 = lean_unbox(x_1183);
if (x_1185 == 0)
{
lean_object* x_1186; uint8_t x_1187; 
x_1186 = l_Lean_trace_profiler;
x_1187 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1151, x_1186);
if (x_1187 == 0)
{
lean_object* x_1188; 
lean_dec(x_1183);
lean_inc(x_1160);
lean_inc_ref(x_1156);
lean_inc(x_1152);
lean_inc_ref(x_1158);
lean_inc(x_2);
x_1188 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1095, x_1184, x_7, x_1158, x_1152, x_1156, x_1160);
x_165 = x_1151;
x_166 = x_1152;
x_167 = x_1165;
x_168 = x_1164;
x_169 = x_1156;
x_170 = x_1157;
x_171 = x_1166;
x_172 = x_1158;
x_173 = x_1159;
x_174 = x_1167;
x_175 = x_1160;
x_176 = x_1188;
goto block_179;
}
else
{
uint8_t x_1189; 
x_1189 = lean_unbox(x_1183);
lean_dec(x_1183);
x_1096 = x_1151;
x_1097 = x_1152;
x_1098 = x_1189;
x_1099 = x_1156;
x_1100 = x_1157;
x_1101 = x_1158;
x_1102 = x_1159;
x_1103 = x_1160;
x_1104 = lean_box(0);
x_1105 = x_1162;
x_1106 = x_1165;
x_1107 = x_1164;
x_1108 = x_1166;
x_1109 = x_1167;
x_1110 = x_1184;
goto block_1150;
}
}
else
{
uint8_t x_1190; 
x_1190 = lean_unbox(x_1183);
lean_dec(x_1183);
x_1096 = x_1151;
x_1097 = x_1152;
x_1098 = x_1190;
x_1099 = x_1156;
x_1100 = x_1157;
x_1101 = x_1158;
x_1102 = x_1159;
x_1103 = x_1160;
x_1104 = lean_box(0);
x_1105 = x_1162;
x_1106 = x_1165;
x_1107 = x_1164;
x_1108 = x_1166;
x_1109 = x_1167;
x_1110 = x_1184;
goto block_1150;
}
}
}
else
{
lean_object* x_1191; 
lean_dec(x_1161);
lean_dec(x_1154);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1191 = lean_ctor_get(x_1169, 0);
lean_inc(x_1191);
lean_dec_ref(x_1169);
x_150 = x_1151;
x_151 = x_1152;
x_152 = x_1164;
x_153 = x_1165;
x_154 = x_1166;
x_155 = x_1157;
x_156 = x_1156;
x_157 = x_1158;
x_158 = x_1167;
x_159 = x_1159;
x_160 = x_1160;
x_161 = x_1191;
x_162 = lean_box(0);
goto block_164;
}
}
else
{
lean_dec(x_1161);
lean_dec_ref(x_1155);
lean_dec(x_1154);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_150 = x_1151;
x_151 = x_1152;
x_152 = x_1164;
x_153 = x_1165;
x_154 = x_1166;
x_155 = x_1157;
x_156 = x_1156;
x_157 = x_1158;
x_158 = x_1167;
x_159 = x_1159;
x_160 = x_1160;
x_161 = x_1163;
x_162 = lean_box(0);
goto block_164;
}
}
block_1247:
{
lean_object* x_1208; 
x_1208 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1201);
if (x_1202 == 0)
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
x_1209 = lean_ctor_get(x_1208, 0);
lean_inc(x_1209);
lean_dec_ref(x_1208);
x_1210 = lean_io_mono_nanos_now();
lean_inc(x_1201);
lean_inc_ref(x_1196);
lean_inc(x_1195);
lean_inc_ref(x_1198);
lean_inc(x_2);
x_1211 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1095, x_1203, x_7, x_1198, x_1195, x_1196, x_1201);
if (lean_obj_tag(x_1211) == 0)
{
lean_object* x_1212; lean_object* x_1213; uint8_t x_1214; uint8_t x_1219; 
x_1212 = lean_ctor_get(x_1211, 0);
x_1219 = !lean_is_exclusive(x_1211);
if (x_1219 == 0)
{
x_1213 = x_1211;
x_1214 = x_1219;
goto block_1218;
}
else
{
lean_inc(x_1212);
lean_dec(x_1211);
x_1213 = lean_box(0);
x_1214 = x_1219;
goto block_1218;
}
block_1218:
{
lean_object* x_1215; 
if (x_1214 == 0)
{
lean_ctor_set_tag(x_1213, 1);
x_1215 = x_1213;
goto block_1216;
}
else
{
lean_object* x_1217; 
x_1217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1217, 0, x_1212);
x_1215 = x_1217;
goto block_1216;
}
block_1216:
{
x_505 = x_1193;
x_506 = x_1195;
x_507 = x_1196;
x_508 = x_1197;
x_509 = x_1198;
x_510 = x_1199;
x_511 = x_1200;
x_512 = x_1201;
x_513 = x_1209;
x_514 = x_1204;
x_515 = x_1205;
x_516 = x_1206;
x_517 = x_1210;
x_518 = x_1207;
x_519 = x_1215;
x_520 = lean_box(0);
goto block_532;
}
}
}
else
{
lean_object* x_1220; lean_object* x_1221; uint8_t x_1222; uint8_t x_1227; 
x_1220 = lean_ctor_get(x_1211, 0);
x_1227 = !lean_is_exclusive(x_1211);
if (x_1227 == 0)
{
x_1221 = x_1211;
x_1222 = x_1227;
goto block_1226;
}
else
{
lean_inc(x_1220);
lean_dec(x_1211);
x_1221 = lean_box(0);
x_1222 = x_1227;
goto block_1226;
}
block_1226:
{
lean_object* x_1223; 
if (x_1222 == 0)
{
lean_ctor_set_tag(x_1221, 0);
x_1223 = x_1221;
goto block_1224;
}
else
{
lean_object* x_1225; 
x_1225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1225, 0, x_1220);
x_1223 = x_1225;
goto block_1224;
}
block_1224:
{
x_505 = x_1193;
x_506 = x_1195;
x_507 = x_1196;
x_508 = x_1197;
x_509 = x_1198;
x_510 = x_1199;
x_511 = x_1200;
x_512 = x_1201;
x_513 = x_1209;
x_514 = x_1204;
x_515 = x_1205;
x_516 = x_1206;
x_517 = x_1210;
x_518 = x_1207;
x_519 = x_1223;
x_520 = lean_box(0);
goto block_532;
}
}
}
}
else
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; 
x_1228 = lean_ctor_get(x_1208, 0);
lean_inc(x_1228);
lean_dec_ref(x_1208);
x_1229 = lean_io_get_num_heartbeats();
lean_inc(x_1201);
lean_inc_ref(x_1196);
lean_inc(x_1195);
lean_inc_ref(x_1198);
lean_inc(x_2);
x_1230 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1095, x_1203, x_7, x_1198, x_1195, x_1196, x_1201);
if (lean_obj_tag(x_1230) == 0)
{
lean_object* x_1231; lean_object* x_1232; uint8_t x_1233; uint8_t x_1238; 
x_1231 = lean_ctor_get(x_1230, 0);
x_1238 = !lean_is_exclusive(x_1230);
if (x_1238 == 0)
{
x_1232 = x_1230;
x_1233 = x_1238;
goto block_1237;
}
else
{
lean_inc(x_1231);
lean_dec(x_1230);
x_1232 = lean_box(0);
x_1233 = x_1238;
goto block_1237;
}
block_1237:
{
lean_object* x_1234; 
if (x_1233 == 0)
{
lean_ctor_set_tag(x_1232, 1);
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
x_480 = x_1193;
x_481 = x_1195;
x_482 = x_1196;
x_483 = x_1197;
x_484 = x_1229;
x_485 = x_1198;
x_486 = x_1199;
x_487 = x_1200;
x_488 = x_1201;
x_489 = x_1228;
x_490 = x_1204;
x_491 = x_1205;
x_492 = x_1206;
x_493 = x_1207;
x_494 = x_1234;
x_495 = lean_box(0);
goto block_504;
}
}
}
else
{
lean_object* x_1239; lean_object* x_1240; uint8_t x_1241; uint8_t x_1246; 
x_1239 = lean_ctor_get(x_1230, 0);
x_1246 = !lean_is_exclusive(x_1230);
if (x_1246 == 0)
{
x_1240 = x_1230;
x_1241 = x_1246;
goto block_1245;
}
else
{
lean_inc(x_1239);
lean_dec(x_1230);
x_1240 = lean_box(0);
x_1241 = x_1246;
goto block_1245;
}
block_1245:
{
lean_object* x_1242; 
if (x_1241 == 0)
{
lean_ctor_set_tag(x_1240, 0);
x_1242 = x_1240;
goto block_1243;
}
else
{
lean_object* x_1244; 
x_1244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1244, 0, x_1239);
x_1242 = x_1244;
goto block_1243;
}
block_1243:
{
x_480 = x_1193;
x_481 = x_1195;
x_482 = x_1196;
x_483 = x_1197;
x_484 = x_1229;
x_485 = x_1198;
x_486 = x_1199;
x_487 = x_1200;
x_488 = x_1201;
x_489 = x_1228;
x_490 = x_1204;
x_491 = x_1205;
x_492 = x_1206;
x_493 = x_1207;
x_494 = x_1242;
x_495 = lean_box(0);
goto block_504;
}
}
}
}
}
block_1289:
{
if (x_1265 == 0)
{
lean_object* x_1266; 
lean_dec_ref(x_1255);
lean_inc(x_1258);
lean_inc_ref(x_1252);
lean_inc(x_1249);
lean_inc_ref(x_1254);
lean_inc(x_1259);
x_1266 = lean_apply_6(x_1251, x_1259, x_1254, x_1249, x_1252, x_1258, lean_box(0));
if (lean_obj_tag(x_1266) == 0)
{
lean_object* x_1267; 
x_1267 = lean_ctor_get(x_1266, 0);
lean_inc(x_1267);
lean_dec_ref(x_1266);
if (lean_obj_tag(x_1267) == 0)
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; uint8_t x_1272; 
lean_inc(x_2);
x_1268 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1252);
x_1269 = lean_ctor_get(x_1268, 0);
lean_inc(x_1269);
lean_dec_ref(x_1268);
x_1270 = lean_nat_add(x_1095, x_1094);
lean_dec(x_1095);
x_1271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1271, 0, x_1259);
lean_ctor_set(x_1271, 1, x_7);
x_1272 = lean_unbox(x_1269);
if (x_1272 == 0)
{
lean_object* x_1273; uint8_t x_1274; 
x_1273 = l_Lean_trace_profiler;
x_1274 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1248, x_1273);
if (x_1274 == 0)
{
lean_object* x_1275; 
lean_dec(x_1269);
lean_inc(x_1258);
lean_inc_ref(x_1252);
lean_inc(x_1249);
lean_inc_ref(x_1254);
lean_inc(x_2);
x_1275 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1270, x_1250, x_1271, x_1254, x_1249, x_1252, x_1258);
x_235 = x_1248;
x_236 = x_1249;
x_237 = x_1262;
x_238 = x_1252;
x_239 = x_1253;
x_240 = x_1263;
x_241 = x_1254;
x_242 = x_1256;
x_243 = x_1264;
x_244 = x_1257;
x_245 = x_1258;
x_246 = x_1275;
goto block_249;
}
else
{
uint8_t x_1276; 
x_1276 = lean_unbox(x_1269);
lean_dec(x_1269);
x_422 = x_1270;
x_423 = x_1248;
x_424 = x_1249;
x_425 = x_1250;
x_426 = x_1252;
x_427 = x_1253;
x_428 = x_1254;
x_429 = x_1256;
x_430 = x_1257;
x_431 = x_1258;
x_432 = x_1271;
x_433 = lean_box(0);
x_434 = x_1261;
x_435 = x_1262;
x_436 = x_1263;
x_437 = x_1276;
x_438 = x_1264;
goto block_478;
}
}
else
{
uint8_t x_1277; 
x_1277 = lean_unbox(x_1269);
lean_dec(x_1269);
x_422 = x_1270;
x_423 = x_1248;
x_424 = x_1249;
x_425 = x_1250;
x_426 = x_1252;
x_427 = x_1253;
x_428 = x_1254;
x_429 = x_1256;
x_430 = x_1257;
x_431 = x_1258;
x_432 = x_1271;
x_433 = lean_box(0);
x_434 = x_1261;
x_435 = x_1262;
x_436 = x_1263;
x_437 = x_1277;
x_438 = x_1264;
goto block_478;
}
}
else
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; uint8_t x_1282; 
lean_dec(x_1259);
x_1278 = lean_ctor_get(x_1267, 0);
lean_inc(x_1278);
lean_dec_ref(x_1267);
lean_inc(x_2);
x_1279 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1252);
x_1280 = lean_ctor_get(x_1279, 0);
lean_inc(x_1280);
lean_dec_ref(x_1279);
x_1281 = l_List_appendTR___redArg(x_1278, x_1250);
x_1282 = lean_unbox(x_1280);
if (x_1282 == 0)
{
lean_object* x_1283; uint8_t x_1284; 
x_1283 = l_Lean_trace_profiler;
x_1284 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1248, x_1283);
if (x_1284 == 0)
{
lean_object* x_1285; 
lean_dec(x_1280);
lean_inc(x_1258);
lean_inc_ref(x_1252);
lean_inc(x_1249);
lean_inc_ref(x_1254);
lean_inc(x_2);
x_1285 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1095, x_1281, x_7, x_1254, x_1249, x_1252, x_1258);
x_235 = x_1248;
x_236 = x_1249;
x_237 = x_1262;
x_238 = x_1252;
x_239 = x_1253;
x_240 = x_1263;
x_241 = x_1254;
x_242 = x_1256;
x_243 = x_1264;
x_244 = x_1257;
x_245 = x_1258;
x_246 = x_1285;
goto block_249;
}
else
{
uint8_t x_1286; 
x_1286 = lean_unbox(x_1280);
lean_dec(x_1280);
x_1193 = x_1248;
x_1194 = lean_box(0);
x_1195 = x_1249;
x_1196 = x_1252;
x_1197 = x_1253;
x_1198 = x_1254;
x_1199 = x_1256;
x_1200 = x_1257;
x_1201 = x_1258;
x_1202 = x_1261;
x_1203 = x_1281;
x_1204 = x_1262;
x_1205 = x_1286;
x_1206 = x_1263;
x_1207 = x_1264;
goto block_1247;
}
}
else
{
uint8_t x_1287; 
x_1287 = lean_unbox(x_1280);
lean_dec(x_1280);
x_1193 = x_1248;
x_1194 = lean_box(0);
x_1195 = x_1249;
x_1196 = x_1252;
x_1197 = x_1253;
x_1198 = x_1254;
x_1199 = x_1256;
x_1200 = x_1257;
x_1201 = x_1258;
x_1202 = x_1261;
x_1203 = x_1281;
x_1204 = x_1262;
x_1205 = x_1287;
x_1206 = x_1263;
x_1207 = x_1264;
goto block_1247;
}
}
}
else
{
lean_object* x_1288; 
lean_dec(x_1259);
lean_dec(x_1250);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1288 = lean_ctor_get(x_1266, 0);
lean_inc(x_1288);
lean_dec_ref(x_1266);
x_220 = x_1248;
x_221 = x_1249;
x_222 = x_1262;
x_223 = x_1263;
x_224 = x_1253;
x_225 = x_1252;
x_226 = x_1254;
x_227 = x_1264;
x_228 = x_1256;
x_229 = x_1257;
x_230 = x_1258;
x_231 = x_1288;
x_232 = lean_box(0);
goto block_234;
}
}
else
{
lean_dec(x_1259);
lean_dec_ref(x_1251);
lean_dec(x_1250);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_220 = x_1248;
x_221 = x_1249;
x_222 = x_1262;
x_223 = x_1263;
x_224 = x_1253;
x_225 = x_1252;
x_226 = x_1254;
x_227 = x_1264;
x_228 = x_1256;
x_229 = x_1257;
x_230 = x_1258;
x_231 = x_1255;
x_232 = lean_box(0);
goto block_234;
}
}
block_1350:
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; uint8_t x_1309; 
x_1306 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1300);
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
lean_dec_ref(x_1306);
x_1308 = l_Lean_trace_profiler_useHeartbeats;
x_1309 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1290, x_1308);
if (x_1309 == 0)
{
lean_object* x_1310; lean_object* x_1311; 
lean_dec_ref(x_1303);
x_1310 = lean_io_mono_nanos_now();
lean_inc(x_1300);
lean_inc_ref(x_1296);
lean_inc(x_1291);
lean_inc_ref(x_1298);
lean_inc(x_1301);
x_1311 = lean_apply_6(x_1292, x_1301, x_1298, x_1291, x_1296, x_1300, lean_box(0));
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
lean_inc_ref(x_3);
lean_inc(x_1300);
lean_inc_ref(x_1296);
lean_inc(x_1291);
lean_inc_ref(x_1298);
lean_inc(x_1301);
x_1314 = lean_apply_7(x_3, x_1301, x_1302, x_1298, x_1291, x_1296, x_1300, lean_box(0));
if (lean_obj_tag(x_1314) == 0)
{
lean_object* x_1315; 
lean_dec(x_1301);
lean_dec_ref(x_1295);
lean_dec(x_1294);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1315 = lean_ctor_get(x_1314, 0);
lean_inc(x_1315);
lean_dec_ref(x_1314);
x_205 = x_1290;
x_206 = x_1291;
x_207 = x_1304;
x_208 = x_1307;
x_209 = x_1297;
x_210 = x_1296;
x_211 = x_1298;
x_212 = x_1305;
x_213 = x_1299;
x_214 = x_1310;
x_215 = x_1300;
x_216 = x_1315;
x_217 = lean_box(0);
goto block_219;
}
else
{
lean_object* x_1316; uint8_t x_1317; 
x_1316 = lean_ctor_get(x_1314, 0);
lean_inc(x_1316);
lean_dec_ref(x_1314);
x_1317 = l_Lean_Exception_isInterrupt(x_1316);
if (x_1317 == 0)
{
uint8_t x_1318; 
lean_inc(x_1316);
x_1318 = l_Lean_Exception_isRuntime(x_1316);
x_1248 = x_1290;
x_1249 = x_1291;
x_1250 = x_1294;
x_1251 = x_1295;
x_1252 = x_1296;
x_1253 = x_1297;
x_1254 = x_1298;
x_1255 = x_1316;
x_1256 = x_1299;
x_1257 = x_1310;
x_1258 = x_1300;
x_1259 = x_1301;
x_1260 = lean_box(0);
x_1261 = x_1309;
x_1262 = x_1304;
x_1263 = x_1307;
x_1264 = x_1305;
x_1265 = x_1318;
goto block_1289;
}
else
{
x_1248 = x_1290;
x_1249 = x_1291;
x_1250 = x_1294;
x_1251 = x_1295;
x_1252 = x_1296;
x_1253 = x_1297;
x_1254 = x_1298;
x_1255 = x_1316;
x_1256 = x_1299;
x_1257 = x_1310;
x_1258 = x_1300;
x_1259 = x_1301;
x_1260 = lean_box(0);
x_1261 = x_1309;
x_1262 = x_1304;
x_1263 = x_1307;
x_1264 = x_1305;
x_1265 = x_1317;
goto block_1289;
}
}
}
else
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; uint8_t x_1323; 
lean_dec_ref(x_1302);
lean_dec_ref(x_1295);
lean_inc(x_2);
x_1319 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1296);
x_1320 = lean_ctor_get(x_1319, 0);
lean_inc(x_1320);
lean_dec_ref(x_1319);
x_1321 = lean_nat_add(x_1095, x_1094);
lean_dec(x_1095);
x_1322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1322, 0, x_1301);
lean_ctor_set(x_1322, 1, x_7);
x_1323 = lean_unbox(x_1320);
if (x_1323 == 0)
{
lean_object* x_1324; uint8_t x_1325; 
x_1324 = l_Lean_trace_profiler;
x_1325 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1290, x_1324);
if (x_1325 == 0)
{
lean_object* x_1326; 
lean_dec(x_1320);
lean_inc(x_1300);
lean_inc_ref(x_1296);
lean_inc(x_1291);
lean_inc_ref(x_1298);
lean_inc(x_2);
x_1326 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1321, x_1294, x_1322, x_1298, x_1291, x_1296, x_1300);
x_235 = x_1290;
x_236 = x_1291;
x_237 = x_1304;
x_238 = x_1296;
x_239 = x_1297;
x_240 = x_1307;
x_241 = x_1298;
x_242 = x_1299;
x_243 = x_1305;
x_244 = x_1310;
x_245 = x_1300;
x_246 = x_1326;
goto block_249;
}
else
{
uint8_t x_1327; 
x_1327 = lean_unbox(x_1320);
lean_dec(x_1320);
x_586 = x_1290;
x_587 = x_1291;
x_588 = x_1294;
x_589 = x_1296;
x_590 = x_1297;
x_591 = x_1322;
x_592 = x_1298;
x_593 = x_1299;
x_594 = x_1310;
x_595 = x_1300;
x_596 = x_1327;
x_597 = x_1309;
x_598 = x_1304;
x_599 = lean_box(0);
x_600 = x_1307;
x_601 = x_1321;
x_602 = x_1305;
goto block_642;
}
}
else
{
uint8_t x_1328; 
x_1328 = lean_unbox(x_1320);
lean_dec(x_1320);
x_586 = x_1290;
x_587 = x_1291;
x_588 = x_1294;
x_589 = x_1296;
x_590 = x_1297;
x_591 = x_1322;
x_592 = x_1298;
x_593 = x_1299;
x_594 = x_1310;
x_595 = x_1300;
x_596 = x_1328;
x_597 = x_1309;
x_598 = x_1304;
x_599 = lean_box(0);
x_600 = x_1307;
x_601 = x_1321;
x_602 = x_1305;
goto block_642;
}
}
}
else
{
lean_object* x_1329; 
lean_dec_ref(x_1302);
lean_dec(x_1301);
lean_dec_ref(x_1295);
lean_dec(x_1294);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1329 = lean_ctor_get(x_1311, 0);
lean_inc(x_1329);
lean_dec_ref(x_1311);
x_220 = x_1290;
x_221 = x_1291;
x_222 = x_1304;
x_223 = x_1307;
x_224 = x_1297;
x_225 = x_1296;
x_226 = x_1298;
x_227 = x_1305;
x_228 = x_1299;
x_229 = x_1310;
x_230 = x_1300;
x_231 = x_1329;
x_232 = lean_box(0);
goto block_234;
}
}
else
{
lean_object* x_1330; lean_object* x_1331; 
lean_dec_ref(x_1302);
x_1330 = lean_io_get_num_heartbeats();
lean_inc(x_1300);
lean_inc_ref(x_1296);
lean_inc(x_1291);
lean_inc_ref(x_1298);
lean_inc(x_1301);
x_1331 = lean_apply_6(x_1292, x_1301, x_1298, x_1291, x_1296, x_1300, lean_box(0));
if (lean_obj_tag(x_1331) == 0)
{
lean_object* x_1332; uint8_t x_1333; 
x_1332 = lean_ctor_get(x_1331, 0);
lean_inc(x_1332);
lean_dec_ref(x_1331);
x_1333 = lean_unbox(x_1332);
lean_dec(x_1332);
if (x_1333 == 0)
{
lean_object* x_1334; 
lean_inc_ref(x_3);
lean_inc(x_1300);
lean_inc_ref(x_1296);
lean_inc(x_1291);
lean_inc_ref(x_1298);
lean_inc(x_1301);
x_1334 = lean_apply_7(x_3, x_1301, x_1303, x_1298, x_1291, x_1296, x_1300, lean_box(0));
if (lean_obj_tag(x_1334) == 0)
{
lean_object* x_1335; 
lean_dec(x_1301);
lean_dec_ref(x_1295);
lean_dec(x_1294);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1335 = lean_ctor_get(x_1334, 0);
lean_inc(x_1335);
lean_dec_ref(x_1334);
x_135 = x_1290;
x_136 = x_1291;
x_137 = x_1330;
x_138 = x_1304;
x_139 = x_1307;
x_140 = x_1297;
x_141 = x_1296;
x_142 = x_1298;
x_143 = x_1305;
x_144 = x_1299;
x_145 = x_1300;
x_146 = x_1335;
x_147 = lean_box(0);
goto block_149;
}
else
{
lean_object* x_1336; uint8_t x_1337; 
x_1336 = lean_ctor_get(x_1334, 0);
lean_inc(x_1336);
lean_dec_ref(x_1334);
x_1337 = l_Lean_Exception_isInterrupt(x_1336);
if (x_1337 == 0)
{
uint8_t x_1338; 
lean_inc(x_1336);
x_1338 = l_Lean_Exception_isRuntime(x_1336);
x_1151 = x_1290;
x_1152 = x_1291;
x_1153 = lean_box(0);
x_1154 = x_1294;
x_1155 = x_1295;
x_1156 = x_1296;
x_1157 = x_1297;
x_1158 = x_1298;
x_1159 = x_1299;
x_1160 = x_1300;
x_1161 = x_1301;
x_1162 = x_1309;
x_1163 = x_1336;
x_1164 = x_1330;
x_1165 = x_1304;
x_1166 = x_1307;
x_1167 = x_1305;
x_1168 = x_1338;
goto block_1192;
}
else
{
x_1151 = x_1290;
x_1152 = x_1291;
x_1153 = lean_box(0);
x_1154 = x_1294;
x_1155 = x_1295;
x_1156 = x_1296;
x_1157 = x_1297;
x_1158 = x_1298;
x_1159 = x_1299;
x_1160 = x_1300;
x_1161 = x_1301;
x_1162 = x_1309;
x_1163 = x_1336;
x_1164 = x_1330;
x_1165 = x_1304;
x_1166 = x_1307;
x_1167 = x_1305;
x_1168 = x_1337;
goto block_1192;
}
}
}
else
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; uint8_t x_1343; 
lean_dec_ref(x_1303);
lean_dec_ref(x_1295);
lean_inc(x_2);
x_1339 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1296);
x_1340 = lean_ctor_get(x_1339, 0);
lean_inc(x_1340);
lean_dec_ref(x_1339);
x_1341 = lean_nat_add(x_1095, x_1094);
lean_dec(x_1095);
x_1342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1342, 0, x_1301);
lean_ctor_set(x_1342, 1, x_7);
x_1343 = lean_unbox(x_1340);
if (x_1343 == 0)
{
lean_object* x_1344; uint8_t x_1345; 
x_1344 = l_Lean_trace_profiler;
x_1345 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1290, x_1344);
if (x_1345 == 0)
{
lean_object* x_1346; 
lean_dec(x_1340);
lean_inc(x_1300);
lean_inc_ref(x_1296);
lean_inc(x_1291);
lean_inc_ref(x_1298);
lean_inc(x_2);
x_1346 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1341, x_1294, x_1342, x_1298, x_1291, x_1296, x_1300);
x_165 = x_1290;
x_166 = x_1291;
x_167 = x_1304;
x_168 = x_1330;
x_169 = x_1296;
x_170 = x_1297;
x_171 = x_1307;
x_172 = x_1298;
x_173 = x_1299;
x_174 = x_1305;
x_175 = x_1300;
x_176 = x_1346;
goto block_179;
}
else
{
uint8_t x_1347; 
x_1347 = lean_unbox(x_1340);
lean_dec(x_1340);
x_311 = x_1290;
x_312 = x_1342;
x_313 = x_1291;
x_314 = lean_box(0);
x_315 = x_1294;
x_316 = x_1296;
x_317 = x_1297;
x_318 = x_1298;
x_319 = x_1299;
x_320 = x_1300;
x_321 = x_1341;
x_322 = x_1309;
x_323 = x_1304;
x_324 = x_1330;
x_325 = x_1307;
x_326 = x_1347;
x_327 = x_1305;
goto block_367;
}
}
else
{
uint8_t x_1348; 
x_1348 = lean_unbox(x_1340);
lean_dec(x_1340);
x_311 = x_1290;
x_312 = x_1342;
x_313 = x_1291;
x_314 = lean_box(0);
x_315 = x_1294;
x_316 = x_1296;
x_317 = x_1297;
x_318 = x_1298;
x_319 = x_1299;
x_320 = x_1300;
x_321 = x_1341;
x_322 = x_1309;
x_323 = x_1304;
x_324 = x_1330;
x_325 = x_1307;
x_326 = x_1348;
x_327 = x_1305;
goto block_367;
}
}
}
else
{
lean_object* x_1349; 
lean_dec_ref(x_1303);
lean_dec(x_1301);
lean_dec_ref(x_1295);
lean_dec(x_1294);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1349 = lean_ctor_get(x_1331, 0);
lean_inc(x_1349);
lean_dec_ref(x_1331);
x_150 = x_1290;
x_151 = x_1291;
x_152 = x_1330;
x_153 = x_1304;
x_154 = x_1307;
x_155 = x_1297;
x_156 = x_1296;
x_157 = x_1298;
x_158 = x_1305;
x_159 = x_1299;
x_160 = x_1300;
x_161 = x_1349;
x_162 = lean_box(0);
goto block_164;
}
}
}
block_1401:
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; uint8_t x_1364; 
x_1361 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1352);
x_1362 = lean_ctor_get(x_1361, 0);
lean_inc(x_1362);
lean_dec_ref(x_1361);
x_1363 = l_Lean_trace_profiler_useHeartbeats;
x_1364 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1351, x_1363);
if (x_1364 == 0)
{
lean_object* x_1365; lean_object* x_1366; 
x_1365 = lean_io_mono_nanos_now();
lean_inc(x_1352);
lean_inc_ref(x_1358);
lean_inc(x_1354);
lean_inc_ref(x_1355);
lean_inc(x_2);
x_1366 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1095, x_1357, x_7, x_1355, x_1354, x_1358, x_1352);
if (lean_obj_tag(x_1366) == 0)
{
lean_object* x_1367; lean_object* x_1368; uint8_t x_1369; uint8_t x_1374; 
x_1367 = lean_ctor_get(x_1366, 0);
x_1374 = !lean_is_exclusive(x_1366);
if (x_1374 == 0)
{
x_1368 = x_1366;
x_1369 = x_1374;
goto block_1373;
}
else
{
lean_inc(x_1367);
lean_dec(x_1366);
x_1368 = lean_box(0);
x_1369 = x_1374;
goto block_1373;
}
block_1373:
{
lean_object* x_1370; 
if (x_1369 == 0)
{
lean_ctor_set_tag(x_1368, 1);
x_1370 = x_1368;
goto block_1371;
}
else
{
lean_object* x_1372; 
x_1372 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1372, 0, x_1367);
x_1370 = x_1372;
goto block_1371;
}
block_1371:
{
x_925 = x_1351;
x_926 = x_1352;
x_927 = x_1354;
x_928 = x_1353;
x_929 = x_1355;
x_930 = x_1365;
x_931 = x_1362;
x_932 = x_1356;
x_933 = x_1358;
x_934 = x_1359;
x_935 = x_1370;
x_936 = lean_box(0);
goto block_948;
}
}
}
else
{
lean_object* x_1375; lean_object* x_1376; uint8_t x_1377; uint8_t x_1382; 
x_1375 = lean_ctor_get(x_1366, 0);
x_1382 = !lean_is_exclusive(x_1366);
if (x_1382 == 0)
{
x_1376 = x_1366;
x_1377 = x_1382;
goto block_1381;
}
else
{
lean_inc(x_1375);
lean_dec(x_1366);
x_1376 = lean_box(0);
x_1377 = x_1382;
goto block_1381;
}
block_1381:
{
lean_object* x_1378; 
if (x_1377 == 0)
{
lean_ctor_set_tag(x_1376, 0);
x_1378 = x_1376;
goto block_1379;
}
else
{
lean_object* x_1380; 
x_1380 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1380, 0, x_1375);
x_1378 = x_1380;
goto block_1379;
}
block_1379:
{
x_925 = x_1351;
x_926 = x_1352;
x_927 = x_1354;
x_928 = x_1353;
x_929 = x_1355;
x_930 = x_1365;
x_931 = x_1362;
x_932 = x_1356;
x_933 = x_1358;
x_934 = x_1359;
x_935 = x_1378;
x_936 = lean_box(0);
goto block_948;
}
}
}
}
else
{
lean_object* x_1383; lean_object* x_1384; 
x_1383 = lean_io_get_num_heartbeats();
lean_inc(x_1352);
lean_inc_ref(x_1358);
lean_inc(x_1354);
lean_inc_ref(x_1355);
lean_inc(x_2);
x_1384 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1095, x_1357, x_7, x_1355, x_1354, x_1358, x_1352);
if (lean_obj_tag(x_1384) == 0)
{
lean_object* x_1385; lean_object* x_1386; uint8_t x_1387; uint8_t x_1392; 
x_1385 = lean_ctor_get(x_1384, 0);
x_1392 = !lean_is_exclusive(x_1384);
if (x_1392 == 0)
{
x_1386 = x_1384;
x_1387 = x_1392;
goto block_1391;
}
else
{
lean_inc(x_1385);
lean_dec(x_1384);
x_1386 = lean_box(0);
x_1387 = x_1392;
goto block_1391;
}
block_1391:
{
lean_object* x_1388; 
if (x_1387 == 0)
{
lean_ctor_set_tag(x_1386, 1);
x_1388 = x_1386;
goto block_1389;
}
else
{
lean_object* x_1390; 
x_1390 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1390, 0, x_1385);
x_1388 = x_1390;
goto block_1389;
}
block_1389:
{
x_904 = x_1351;
x_905 = x_1352;
x_906 = x_1354;
x_907 = x_1353;
x_908 = x_1383;
x_909 = x_1355;
x_910 = x_1362;
x_911 = x_1356;
x_912 = x_1358;
x_913 = x_1359;
x_914 = x_1388;
x_915 = lean_box(0);
goto block_924;
}
}
}
else
{
lean_object* x_1393; lean_object* x_1394; uint8_t x_1395; uint8_t x_1400; 
x_1393 = lean_ctor_get(x_1384, 0);
x_1400 = !lean_is_exclusive(x_1384);
if (x_1400 == 0)
{
x_1394 = x_1384;
x_1395 = x_1400;
goto block_1399;
}
else
{
lean_inc(x_1393);
lean_dec(x_1384);
x_1394 = lean_box(0);
x_1395 = x_1400;
goto block_1399;
}
block_1399:
{
lean_object* x_1396; 
if (x_1395 == 0)
{
lean_ctor_set_tag(x_1394, 0);
x_1396 = x_1394;
goto block_1397;
}
else
{
lean_object* x_1398; 
x_1398 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1398, 0, x_1393);
x_1396 = x_1398;
goto block_1397;
}
block_1397:
{
x_904 = x_1351;
x_905 = x_1352;
x_906 = x_1354;
x_907 = x_1353;
x_908 = x_1383;
x_909 = x_1355;
x_910 = x_1362;
x_911 = x_1356;
x_912 = x_1358;
x_913 = x_1359;
x_914 = x_1396;
x_915 = lean_box(0);
goto block_924;
}
}
}
}
}
block_1451:
{
if (x_1412 == 0)
{
lean_object* x_1413; 
lean_dec_ref(x_1409);
lean_inc(x_1404);
lean_inc_ref(x_1410);
lean_inc(x_1405);
lean_inc_ref(x_1406);
lean_inc(x_1402);
x_1413 = lean_apply_6(x_1411, x_1402, x_1406, x_1405, x_1410, x_1404, lean_box(0));
if (lean_obj_tag(x_1413) == 0)
{
lean_object* x_1414; 
x_1414 = lean_ctor_get(x_1413, 0);
lean_inc(x_1414);
lean_dec_ref(x_1413);
if (lean_obj_tag(x_1414) == 0)
{
lean_object* x_1415; uint8_t x_1416; lean_object* x_1417; lean_object* x_1418; 
x_1415 = lean_ctor_get(x_1410, 2);
x_1416 = lean_ctor_get_uint8(x_1415, sizeof(void*)*1);
x_1417 = lean_nat_add(x_1095, x_1094);
lean_dec(x_1095);
x_1418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1418, 0, x_1402);
lean_ctor_set(x_1418, 1, x_7);
if (x_1416 == 0)
{
x_5 = x_1417;
x_6 = x_1408;
x_7 = x_1418;
x_8 = x_1406;
x_9 = x_1405;
x_10 = x_1410;
x_11 = x_1404;
goto _start;
}
else
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; uint8_t x_1423; 
lean_inc(x_2);
x_1420 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1410);
x_1421 = lean_ctor_get(x_1420, 0);
lean_inc(x_1421);
lean_dec_ref(x_1420);
x_1422 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1423 = lean_unbox(x_1421);
if (x_1423 == 0)
{
lean_object* x_1424; uint8_t x_1425; 
x_1424 = l_Lean_trace_profiler;
x_1425 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1415, x_1424);
if (x_1425 == 0)
{
lean_dec(x_1421);
x_5 = x_1417;
x_6 = x_1408;
x_7 = x_1418;
x_8 = x_1406;
x_9 = x_1405;
x_10 = x_1410;
x_11 = x_1404;
goto _start;
}
else
{
uint8_t x_1427; 
lean_inc_ref(x_1415);
x_1427 = lean_unbox(x_1421);
lean_dec(x_1421);
x_851 = x_1418;
x_852 = lean_box(0);
x_853 = x_1404;
x_854 = x_1417;
x_855 = x_1415;
x_856 = x_1405;
x_857 = x_1406;
x_858 = x_1408;
x_859 = x_1407;
x_860 = x_1422;
x_861 = x_1410;
x_862 = x_1427;
goto block_903;
}
}
else
{
uint8_t x_1428; 
lean_inc_ref(x_1415);
x_1428 = lean_unbox(x_1421);
lean_dec(x_1421);
x_851 = x_1418;
x_852 = lean_box(0);
x_853 = x_1404;
x_854 = x_1417;
x_855 = x_1415;
x_856 = x_1405;
x_857 = x_1406;
x_858 = x_1408;
x_859 = x_1407;
x_860 = x_1422;
x_861 = x_1410;
x_862 = x_1428;
goto block_903;
}
}
}
else
{
lean_object* x_1429; lean_object* x_1430; uint8_t x_1431; lean_object* x_1432; 
lean_dec(x_1402);
x_1429 = lean_ctor_get(x_1410, 2);
x_1430 = lean_ctor_get(x_1414, 0);
lean_inc(x_1430);
lean_dec_ref(x_1414);
x_1431 = lean_ctor_get_uint8(x_1429, sizeof(void*)*1);
x_1432 = l_List_appendTR___redArg(x_1430, x_1408);
if (x_1431 == 0)
{
x_5 = x_1095;
x_6 = x_1432;
x_8 = x_1406;
x_9 = x_1405;
x_10 = x_1410;
x_11 = x_1404;
goto _start;
}
else
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; uint8_t x_1437; 
lean_inc(x_2);
x_1434 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1410);
x_1435 = lean_ctor_get(x_1434, 0);
lean_inc(x_1435);
lean_dec_ref(x_1434);
x_1436 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1437 = lean_unbox(x_1435);
if (x_1437 == 0)
{
lean_object* x_1438; uint8_t x_1439; 
x_1438 = l_Lean_trace_profiler;
x_1439 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1429, x_1438);
if (x_1439 == 0)
{
lean_dec(x_1435);
x_5 = x_1095;
x_6 = x_1432;
x_8 = x_1406;
x_9 = x_1405;
x_10 = x_1410;
x_11 = x_1404;
goto _start;
}
else
{
uint8_t x_1441; 
lean_inc_ref(x_1429);
x_1441 = lean_unbox(x_1435);
lean_dec(x_1435);
x_1351 = x_1429;
x_1352 = x_1404;
x_1353 = x_1436;
x_1354 = x_1405;
x_1355 = x_1406;
x_1356 = x_1407;
x_1357 = x_1432;
x_1358 = x_1410;
x_1359 = x_1441;
x_1360 = lean_box(0);
goto block_1401;
}
}
else
{
uint8_t x_1442; 
lean_inc_ref(x_1429);
x_1442 = lean_unbox(x_1435);
lean_dec(x_1435);
x_1351 = x_1429;
x_1352 = x_1404;
x_1353 = x_1436;
x_1354 = x_1405;
x_1355 = x_1406;
x_1356 = x_1407;
x_1357 = x_1432;
x_1358 = x_1410;
x_1359 = x_1442;
x_1360 = lean_box(0);
goto block_1401;
}
}
}
}
else
{
lean_object* x_1443; lean_object* x_1444; uint8_t x_1445; uint8_t x_1450; 
lean_dec_ref(x_1410);
lean_dec(x_1408);
lean_dec_ref(x_1406);
lean_dec(x_1405);
lean_dec(x_1404);
lean_dec(x_1402);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1443 = lean_ctor_get(x_1413, 0);
x_1450 = !lean_is_exclusive(x_1413);
if (x_1450 == 0)
{
x_1444 = x_1413;
x_1445 = x_1450;
goto block_1449;
}
else
{
lean_inc(x_1443);
lean_dec(x_1413);
x_1444 = lean_box(0);
x_1445 = x_1450;
goto block_1449;
}
block_1449:
{
lean_object* x_1446; 
if (x_1445 == 0)
{
x_1446 = x_1444;
goto block_1447;
}
else
{
lean_object* x_1448; 
x_1448 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1448, 0, x_1443);
x_1446 = x_1448;
goto block_1447;
}
block_1447:
{
return x_1446;
}
}
}
}
else
{
lean_dec_ref(x_1411);
lean_dec_ref(x_1410);
lean_dec(x_1408);
lean_dec_ref(x_1406);
lean_dec(x_1405);
lean_dec(x_1404);
lean_dec(x_1402);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1409;
}
}
block_1492:
{
lean_object* x_1463; 
lean_inc(x_1461);
lean_inc_ref(x_1460);
lean_inc(x_1459);
lean_inc_ref(x_1458);
lean_inc(x_1452);
x_1463 = lean_apply_6(x_1454, x_1452, x_1458, x_1459, x_1460, x_1461, lean_box(0));
if (lean_obj_tag(x_1463) == 0)
{
lean_object* x_1464; uint8_t x_1465; 
x_1464 = lean_ctor_get(x_1463, 0);
lean_inc(x_1464);
lean_dec_ref(x_1463);
x_1465 = lean_unbox(x_1464);
lean_dec(x_1464);
if (x_1465 == 0)
{
lean_object* x_1466; 
lean_inc_ref(x_3);
lean_inc(x_1461);
lean_inc_ref(x_1460);
lean_inc(x_1459);
lean_inc_ref(x_1458);
lean_inc(x_1452);
x_1466 = lean_apply_7(x_3, x_1452, x_1453, x_1458, x_1459, x_1460, x_1461, lean_box(0));
if (lean_obj_tag(x_1466) == 0)
{
lean_dec(x_1461);
lean_dec_ref(x_1460);
lean_dec(x_1459);
lean_dec_ref(x_1458);
lean_dec_ref(x_1457);
lean_dec(x_1455);
lean_dec(x_1452);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1466;
}
else
{
lean_object* x_1467; uint8_t x_1468; 
x_1467 = lean_ctor_get(x_1466, 0);
lean_inc(x_1467);
x_1468 = l_Lean_Exception_isInterrupt(x_1467);
if (x_1468 == 0)
{
uint8_t x_1469; 
x_1469 = l_Lean_Exception_isRuntime(x_1467);
x_1402 = x_1452;
x_1403 = lean_box(0);
x_1404 = x_1461;
x_1405 = x_1459;
x_1406 = x_1458;
x_1407 = x_1456;
x_1408 = x_1455;
x_1409 = x_1466;
x_1410 = x_1460;
x_1411 = x_1457;
x_1412 = x_1469;
goto block_1451;
}
else
{
lean_dec(x_1467);
x_1402 = x_1452;
x_1403 = lean_box(0);
x_1404 = x_1461;
x_1405 = x_1459;
x_1406 = x_1458;
x_1407 = x_1456;
x_1408 = x_1455;
x_1409 = x_1466;
x_1410 = x_1460;
x_1411 = x_1457;
x_1412 = x_1468;
goto block_1451;
}
}
}
else
{
lean_object* x_1470; uint8_t x_1471; lean_object* x_1472; lean_object* x_1473; 
lean_dec_ref(x_1457);
lean_dec_ref(x_1453);
x_1470 = lean_ctor_get(x_1460, 2);
x_1471 = lean_ctor_get_uint8(x_1470, sizeof(void*)*1);
x_1472 = lean_nat_add(x_1095, x_1094);
lean_dec(x_1095);
x_1473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1473, 0, x_1452);
lean_ctor_set(x_1473, 1, x_7);
if (x_1471 == 0)
{
x_5 = x_1472;
x_6 = x_1455;
x_7 = x_1473;
x_8 = x_1458;
x_9 = x_1459;
x_10 = x_1460;
x_11 = x_1461;
goto _start;
}
else
{
lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; uint8_t x_1478; 
lean_inc(x_2);
x_1475 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1460);
x_1476 = lean_ctor_get(x_1475, 0);
lean_inc(x_1476);
lean_dec_ref(x_1475);
x_1477 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1478 = lean_unbox(x_1476);
if (x_1478 == 0)
{
lean_object* x_1479; uint8_t x_1480; 
x_1479 = l_Lean_trace_profiler;
x_1480 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1470, x_1479);
if (x_1480 == 0)
{
lean_dec(x_1476);
x_5 = x_1472;
x_6 = x_1455;
x_7 = x_1473;
x_8 = x_1458;
x_9 = x_1459;
x_10 = x_1460;
x_11 = x_1461;
goto _start;
}
else
{
uint8_t x_1482; 
lean_inc_ref(x_1470);
x_1482 = lean_unbox(x_1476);
lean_dec(x_1476);
x_994 = lean_box(0);
x_995 = x_1461;
x_996 = x_1470;
x_997 = x_1459;
x_998 = x_1458;
x_999 = x_1477;
x_1000 = x_1455;
x_1001 = x_1456;
x_1002 = x_1482;
x_1003 = x_1460;
x_1004 = x_1473;
x_1005 = x_1472;
goto block_1046;
}
}
else
{
uint8_t x_1483; 
lean_inc_ref(x_1470);
x_1483 = lean_unbox(x_1476);
lean_dec(x_1476);
x_994 = lean_box(0);
x_995 = x_1461;
x_996 = x_1470;
x_997 = x_1459;
x_998 = x_1458;
x_999 = x_1477;
x_1000 = x_1455;
x_1001 = x_1456;
x_1002 = x_1483;
x_1003 = x_1460;
x_1004 = x_1473;
x_1005 = x_1472;
goto block_1046;
}
}
}
}
else
{
lean_object* x_1484; lean_object* x_1485; uint8_t x_1486; uint8_t x_1491; 
lean_dec(x_1461);
lean_dec_ref(x_1460);
lean_dec(x_1459);
lean_dec_ref(x_1458);
lean_dec_ref(x_1457);
lean_dec(x_1455);
lean_dec_ref(x_1453);
lean_dec(x_1452);
lean_dec(x_1095);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1484 = lean_ctor_get(x_1463, 0);
x_1491 = !lean_is_exclusive(x_1463);
if (x_1491 == 0)
{
x_1485 = x_1463;
x_1486 = x_1491;
goto block_1490;
}
else
{
lean_inc(x_1484);
lean_dec(x_1463);
x_1485 = lean_box(0);
x_1486 = x_1491;
goto block_1490;
}
block_1490:
{
lean_object* x_1487; 
if (x_1486 == 0)
{
x_1487 = x_1485;
goto block_1488;
}
else
{
lean_object* x_1489; 
x_1489 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1489, 0, x_1484);
x_1487 = x_1489;
goto block_1488;
}
block_1488:
{
return x_1487;
}
}
}
}
block_1552:
{
if (lean_obj_tag(x_1493) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_1499; uint8_t x_1500; lean_object* x_1501; 
lean_dec(x_1095);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1499 = lean_ctor_get(x_1496, 2);
lean_inc_ref(x_1499);
x_1500 = lean_ctor_get_uint8(x_1499, sizeof(void*)*1);
x_1501 = l_List_reverse___redArg(x_7);
if (x_1500 == 0)
{
lean_object* x_1502; 
lean_dec_ref(x_1499);
lean_dec(x_1497);
lean_dec_ref(x_1496);
lean_dec(x_1495);
lean_dec_ref(x_1494);
lean_dec(x_2);
x_1502 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1502, 0, x_1501);
return x_1502;
}
else
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; uint8_t x_1506; uint8_t x_1517; 
lean_inc(x_2);
x_1503 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1496);
x_1504 = lean_ctor_get(x_1503, 0);
x_1517 = !lean_is_exclusive(x_1503);
if (x_1517 == 0)
{
x_1505 = x_1503;
x_1506 = x_1517;
goto block_1516;
}
else
{
lean_inc(x_1504);
lean_dec(x_1503);
x_1505 = lean_box(0);
x_1506 = x_1517;
goto block_1516;
}
block_1516:
{
lean_object* x_1507; uint8_t x_1508; 
x_1507 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1508 = lean_unbox(x_1504);
if (x_1508 == 0)
{
lean_object* x_1509; uint8_t x_1510; 
x_1509 = l_Lean_trace_profiler;
x_1510 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1499, x_1509);
if (x_1510 == 0)
{
lean_object* x_1511; 
lean_dec(x_1504);
lean_dec_ref(x_1499);
lean_dec(x_1497);
lean_dec_ref(x_1496);
lean_dec(x_1495);
lean_dec_ref(x_1494);
lean_dec(x_2);
if (x_1506 == 0)
{
lean_ctor_set(x_1505, 0, x_1501);
x_1511 = x_1505;
goto block_1512;
}
else
{
lean_object* x_1513; 
x_1513 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1513, 0, x_1501);
x_1511 = x_1513;
goto block_1512;
}
block_1512:
{
return x_1511;
}
}
else
{
uint8_t x_1514; 
lean_del_object(x_1505);
x_1514 = lean_unbox(x_1504);
lean_dec(x_1504);
x_1048 = x_1499;
x_1049 = x_1501;
x_1050 = x_1507;
x_1051 = x_1495;
x_1052 = x_1514;
x_1053 = x_1500;
x_1054 = x_1496;
x_1055 = lean_box(0);
x_1056 = x_1494;
x_1057 = x_1497;
goto block_1093;
}
}
else
{
uint8_t x_1515; 
lean_del_object(x_1505);
x_1515 = lean_unbox(x_1504);
lean_dec(x_1504);
x_1048 = x_1499;
x_1049 = x_1501;
x_1050 = x_1507;
x_1051 = x_1495;
x_1052 = x_1515;
x_1053 = x_1500;
x_1054 = x_1496;
x_1055 = lean_box(0);
x_1056 = x_1494;
x_1057 = x_1497;
goto block_1093;
}
}
}
}
else
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; uint8_t x_1522; uint8_t x_1523; 
x_1518 = lean_ctor_get(x_6, 0);
lean_inc(x_1518);
x_1519 = lean_ctor_get(x_6, 1);
lean_inc(x_1519);
lean_dec_ref(x_6);
x_1520 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_1518, x_1495);
x_1521 = lean_ctor_get(x_1520, 0);
lean_inc(x_1521);
lean_dec_ref(x_1520);
x_1522 = 1;
x_1523 = lean_unbox(x_1521);
lean_dec(x_1521);
if (x_1523 == 0)
{
lean_object* x_1524; uint8_t x_1525; lean_object* x_1526; 
x_1524 = lean_ctor_get(x_1496, 2);
x_1525 = lean_ctor_get_uint8(x_1524, sizeof(void*)*1);
lean_inc(x_7);
lean_inc(x_1095);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc(x_1519);
x_1526 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed), 13, 7);
lean_closure_set(x_1526, 0, x_1519);
lean_closure_set(x_1526, 1, x_1);
lean_closure_set(x_1526, 2, x_2);
lean_closure_set(x_1526, 3, x_3);
lean_closure_set(x_1526, 4, x_4);
lean_closure_set(x_1526, 5, x_1095);
lean_closure_set(x_1526, 6, x_7);
if (x_1525 == 0)
{
lean_inc_ref(x_256);
lean_inc_ref(x_255);
x_1452 = x_1518;
x_1453 = x_1526;
x_1454 = x_255;
x_1455 = x_1519;
x_1456 = x_1522;
x_1457 = x_256;
x_1458 = x_1494;
x_1459 = x_1495;
x_1460 = x_1496;
x_1461 = x_1497;
x_1462 = lean_box(0);
goto block_1492;
}
else
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; uint8_t x_1531; 
lean_inc(x_2);
x_1527 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1496);
x_1528 = lean_ctor_get(x_1527, 0);
lean_inc(x_1528);
lean_dec_ref(x_1527);
lean_inc(x_1518);
x_1529 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(x_1529, 0, x_1518);
x_1530 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1531 = lean_unbox(x_1528);
if (x_1531 == 0)
{
lean_object* x_1532; uint8_t x_1533; 
x_1532 = l_Lean_trace_profiler;
x_1533 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1524, x_1532);
if (x_1533 == 0)
{
lean_dec_ref(x_1529);
lean_dec(x_1528);
lean_inc_ref(x_256);
lean_inc_ref(x_255);
x_1452 = x_1518;
x_1453 = x_1526;
x_1454 = x_255;
x_1455 = x_1519;
x_1456 = x_1522;
x_1457 = x_256;
x_1458 = x_1494;
x_1459 = x_1495;
x_1460 = x_1496;
x_1461 = x_1497;
x_1462 = lean_box(0);
goto block_1492;
}
else
{
uint8_t x_1534; 
lean_inc_ref(x_1524);
x_1534 = lean_unbox(x_1528);
lean_dec(x_1528);
lean_inc_ref(x_1526);
lean_inc_ref(x_256);
lean_inc_ref(x_255);
x_1290 = x_1524;
x_1291 = x_1495;
x_1292 = x_255;
x_1293 = lean_box(0);
x_1294 = x_1519;
x_1295 = x_256;
x_1296 = x_1496;
x_1297 = x_1529;
x_1298 = x_1494;
x_1299 = x_1534;
x_1300 = x_1497;
x_1301 = x_1518;
x_1302 = x_1526;
x_1303 = x_1526;
x_1304 = x_1522;
x_1305 = x_1530;
goto block_1350;
}
}
else
{
uint8_t x_1535; 
lean_inc_ref(x_1524);
x_1535 = lean_unbox(x_1528);
lean_dec(x_1528);
lean_inc_ref(x_1526);
lean_inc_ref(x_256);
lean_inc_ref(x_255);
x_1290 = x_1524;
x_1291 = x_1495;
x_1292 = x_255;
x_1293 = lean_box(0);
x_1294 = x_1519;
x_1295 = x_256;
x_1296 = x_1496;
x_1297 = x_1529;
x_1298 = x_1494;
x_1299 = x_1535;
x_1300 = x_1497;
x_1301 = x_1518;
x_1302 = x_1526;
x_1303 = x_1526;
x_1304 = x_1522;
x_1305 = x_1530;
goto block_1350;
}
}
}
else
{
lean_object* x_1536; uint8_t x_1537; lean_object* x_1538; 
x_1536 = lean_ctor_get(x_1496, 2);
x_1537 = lean_ctor_get_uint8(x_1536, sizeof(void*)*1);
x_1538 = lean_nat_add(x_1095, x_1094);
lean_dec(x_1095);
if (x_1537 == 0)
{
lean_dec(x_1518);
x_5 = x_1538;
x_6 = x_1519;
x_8 = x_1494;
x_9 = x_1495;
x_10 = x_1496;
x_11 = x_1497;
goto _start;
}
else
{
lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; uint8_t x_1544; 
lean_inc(x_2);
x_1540 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1496);
x_1541 = lean_ctor_get(x_1540, 0);
lean_inc(x_1541);
lean_dec_ref(x_1540);
x_1542 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(x_1542, 0, x_1518);
x_1543 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1544 = lean_unbox(x_1541);
if (x_1544 == 0)
{
lean_object* x_1545; uint8_t x_1546; 
x_1545 = l_Lean_trace_profiler;
x_1546 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1536, x_1545);
if (x_1546 == 0)
{
lean_dec_ref(x_1542);
lean_dec(x_1541);
x_5 = x_1538;
x_6 = x_1519;
x_8 = x_1494;
x_9 = x_1495;
x_10 = x_1496;
x_11 = x_1497;
goto _start;
}
else
{
uint8_t x_1548; 
lean_inc_ref(x_1536);
x_1548 = lean_unbox(x_1541);
lean_dec(x_1541);
x_60 = x_1538;
x_61 = x_1543;
x_62 = lean_box(0);
x_63 = x_1536;
x_64 = x_1495;
x_65 = x_1519;
x_66 = x_1522;
x_67 = x_1548;
x_68 = x_1496;
x_69 = x_1494;
x_70 = x_1542;
x_71 = x_1497;
goto block_112;
}
}
else
{
uint8_t x_1549; 
lean_inc_ref(x_1536);
x_1549 = lean_unbox(x_1541);
lean_dec(x_1541);
x_60 = x_1538;
x_61 = x_1543;
x_62 = lean_box(0);
x_63 = x_1536;
x_64 = x_1495;
x_65 = x_1519;
x_66 = x_1522;
x_67 = x_1549;
x_68 = x_1496;
x_69 = x_1494;
x_70 = x_1542;
x_71 = x_1497;
goto block_112;
}
}
}
}
}
else
{
lean_object* x_1550; 
lean_dec(x_6);
x_1550 = lean_ctor_get(x_1493, 0);
lean_inc(x_1550);
lean_dec_ref(x_1493);
x_5 = x_1095;
x_6 = x_1550;
x_8 = x_1494;
x_9 = x_1495;
x_10 = x_1496;
x_11 = x_1497;
goto _start;
}
}
block_1563:
{
if (lean_obj_tag(x_1553) == 0)
{
lean_object* x_1554; 
x_1554 = lean_ctor_get(x_1553, 0);
lean_inc(x_1554);
lean_dec_ref(x_1553);
x_1493 = x_1554;
x_1494 = x_8;
x_1495 = x_9;
x_1496 = x_10;
x_1497 = x_11;
x_1498 = lean_box(0);
goto block_1552;
}
else
{
lean_object* x_1555; lean_object* x_1556; uint8_t x_1557; uint8_t x_1562; 
lean_dec(x_1095);
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
x_1555 = lean_ctor_get(x_1553, 0);
x_1562 = !lean_is_exclusive(x_1553);
if (x_1562 == 0)
{
x_1556 = x_1553;
x_1557 = x_1562;
goto block_1561;
}
else
{
lean_inc(x_1555);
lean_dec(x_1553);
x_1556 = lean_box(0);
x_1557 = x_1562;
goto block_1561;
}
block_1561:
{
lean_object* x_1558; 
if (x_1557 == 0)
{
x_1558 = x_1556;
goto block_1559;
}
else
{
lean_object* x_1560; 
x_1560 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1560, 0, x_1555);
x_1558 = x_1560;
goto block_1559;
}
block_1559:
{
return x_1558;
}
}
}
}
}
block_34:
{
lean_object* x_26; double x_27; double x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_io_get_num_heartbeats();
x_27 = lean_float_of_nat(x_13);
x_28 = lean_float_of_nat(x_26);
x_29 = lean_box_float(x_27);
x_30 = lean_box_float(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_18, x_14, x_15, x_17, x_21, x_23, x_32, x_20, x_16, x_19, x_22);
lean_dec_ref(x_15);
return x_33;
}
block_59:
{
lean_object* x_48; double x_49; double x_50; double x_51; double x_52; double x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_io_mono_nanos_now();
x_49 = lean_float_of_nat(x_43);
x_50 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_51 = lean_float_div(x_49, x_50);
x_52 = lean_float_of_nat(x_48);
x_53 = lean_float_div(x_52, x_50);
x_54 = lean_box_float(x_51);
x_55 = lean_box_float(x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_39, x_35, x_36, x_38, x_42, x_45, x_57, x_41, x_37, x_40, x_44);
lean_dec_ref(x_36);
return x_58;
}
block_112:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l_Lean_trace_profiler_useHeartbeats;
x_75 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_63, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_io_mono_nanos_now();
lean_inc(x_71);
lean_inc_ref(x_68);
lean_inc(x_64);
lean_inc_ref(x_69);
lean_inc(x_2);
x_77 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_60, x_65, x_7, x_69, x_64, x_68, x_71);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
x_78 = lean_ctor_get(x_77, 0);
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
x_79 = x_77;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
lean_ctor_set_tag(x_79, 1);
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
x_35 = x_61;
x_36 = x_63;
x_37 = x_64;
x_38 = x_67;
x_39 = x_66;
x_40 = x_68;
x_41 = x_69;
x_42 = x_73;
x_43 = x_76;
x_44 = x_71;
x_45 = x_70;
x_46 = x_81;
x_47 = lean_box(0);
goto block_59;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_93; 
x_86 = lean_ctor_get(x_77, 0);
x_93 = !lean_is_exclusive(x_77);
if (x_93 == 0)
{
x_87 = x_77;
x_88 = x_93;
goto block_92;
}
else
{
lean_inc(x_86);
lean_dec(x_77);
x_87 = lean_box(0);
x_88 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_89; 
if (x_88 == 0)
{
lean_ctor_set_tag(x_87, 0);
x_89 = x_87;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_86);
x_89 = x_91;
goto block_90;
}
block_90:
{
x_35 = x_61;
x_36 = x_63;
x_37 = x_64;
x_38 = x_67;
x_39 = x_66;
x_40 = x_68;
x_41 = x_69;
x_42 = x_73;
x_43 = x_76;
x_44 = x_71;
x_45 = x_70;
x_46 = x_89;
x_47 = lean_box(0);
goto block_59;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_io_get_num_heartbeats();
lean_inc(x_71);
lean_inc_ref(x_68);
lean_inc(x_64);
lean_inc_ref(x_69);
lean_inc(x_2);
x_95 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_60, x_65, x_7, x_69, x_64, x_68, x_71);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_103; 
x_96 = lean_ctor_get(x_95, 0);
x_103 = !lean_is_exclusive(x_95);
if (x_103 == 0)
{
x_97 = x_95;
x_98 = x_103;
goto block_102;
}
else
{
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_box(0);
x_98 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_99; 
if (x_98 == 0)
{
lean_ctor_set_tag(x_97, 1);
x_99 = x_97;
goto block_100;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_96);
x_99 = x_101;
goto block_100;
}
block_100:
{
x_13 = x_94;
x_14 = x_61;
x_15 = x_63;
x_16 = x_64;
x_17 = x_67;
x_18 = x_66;
x_19 = x_68;
x_20 = x_69;
x_21 = x_73;
x_22 = x_71;
x_23 = x_70;
x_24 = x_99;
x_25 = lean_box(0);
goto block_34;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_111; 
x_104 = lean_ctor_get(x_95, 0);
x_111 = !lean_is_exclusive(x_95);
if (x_111 == 0)
{
x_105 = x_95;
x_106 = x_111;
goto block_110;
}
else
{
lean_inc(x_104);
lean_dec(x_95);
x_105 = lean_box(0);
x_106 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_107; 
if (x_106 == 0)
{
lean_ctor_set_tag(x_105, 0);
x_107 = x_105;
goto block_108;
}
else
{
lean_object* x_109; 
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_104);
x_107 = x_109;
goto block_108;
}
block_108:
{
x_13 = x_94;
x_14 = x_61;
x_15 = x_63;
x_16 = x_64;
x_17 = x_67;
x_18 = x_66;
x_19 = x_68;
x_20 = x_69;
x_21 = x_73;
x_22 = x_71;
x_23 = x_70;
x_24 = x_107;
x_25 = lean_box(0);
goto block_34;
}
}
}
}
}
block_134:
{
lean_object* x_126; double x_127; double x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_126 = lean_io_get_num_heartbeats();
x_127 = lean_float_of_nat(x_116);
x_128 = lean_float_of_nat(x_126);
x_129 = lean_box_float(x_127);
x_130 = lean_box_float(x_128);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_124);
lean_ctor_set(x_132, 1, x_131);
x_133 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_115, x_122, x_113, x_121, x_119, x_118, x_132, x_120, x_114, x_117, x_123);
lean_dec_ref(x_113);
return x_133;
}
block_149:
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_146);
x_113 = x_135;
x_114 = x_136;
x_115 = x_138;
x_116 = x_137;
x_117 = x_141;
x_118 = x_140;
x_119 = x_139;
x_120 = x_142;
x_121 = x_144;
x_122 = x_143;
x_123 = x_145;
x_124 = x_148;
x_125 = lean_box(0);
goto block_134;
}
block_164:
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_161);
x_113 = x_150;
x_114 = x_151;
x_115 = x_153;
x_116 = x_152;
x_117 = x_156;
x_118 = x_155;
x_119 = x_154;
x_120 = x_157;
x_121 = x_159;
x_122 = x_158;
x_123 = x_160;
x_124 = x_163;
x_125 = lean_box(0);
goto block_134;
}
block_179:
{
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec_ref(x_176);
x_135 = x_165;
x_136 = x_166;
x_137 = x_168;
x_138 = x_167;
x_139 = x_171;
x_140 = x_170;
x_141 = x_169;
x_142 = x_172;
x_143 = x_174;
x_144 = x_173;
x_145 = x_175;
x_146 = x_177;
x_147 = lean_box(0);
goto block_149;
}
else
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec_ref(x_176);
x_150 = x_165;
x_151 = x_166;
x_152 = x_168;
x_153 = x_167;
x_154 = x_171;
x_155 = x_170;
x_156 = x_169;
x_157 = x_172;
x_158 = x_174;
x_159 = x_173;
x_160 = x_175;
x_161 = x_178;
x_162 = lean_box(0);
goto block_164;
}
}
block_204:
{
lean_object* x_193; double x_194; double x_195; double x_196; double x_197; double x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_193 = lean_io_mono_nanos_now();
x_194 = lean_float_of_nat(x_189);
x_195 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_196 = lean_float_div(x_194, x_195);
x_197 = lean_float_of_nat(x_193);
x_198 = lean_float_div(x_197, x_195);
x_199 = lean_box_float(x_196);
x_200 = lean_box_float(x_198);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_191);
lean_ctor_set(x_202, 1, x_201);
x_203 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_182, x_188, x_180, x_187, x_185, x_184, x_202, x_186, x_181, x_183, x_190);
lean_dec_ref(x_180);
return x_203;
}
block_219:
{
lean_object* x_218; 
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_216);
x_180 = x_205;
x_181 = x_206;
x_182 = x_207;
x_183 = x_210;
x_184 = x_209;
x_185 = x_208;
x_186 = x_211;
x_187 = x_213;
x_188 = x_212;
x_189 = x_214;
x_190 = x_215;
x_191 = x_218;
x_192 = lean_box(0);
goto block_204;
}
block_234:
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_231);
x_180 = x_220;
x_181 = x_221;
x_182 = x_222;
x_183 = x_225;
x_184 = x_224;
x_185 = x_223;
x_186 = x_226;
x_187 = x_228;
x_188 = x_227;
x_189 = x_229;
x_190 = x_230;
x_191 = x_233;
x_192 = lean_box(0);
goto block_204;
}
block_249:
{
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_205 = x_235;
x_206 = x_236;
x_207 = x_237;
x_208 = x_240;
x_209 = x_239;
x_210 = x_238;
x_211 = x_241;
x_212 = x_243;
x_213 = x_242;
x_214 = x_244;
x_215 = x_245;
x_216 = x_247;
x_217 = lean_box(0);
goto block_219;
}
else
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
lean_dec_ref(x_246);
x_220 = x_235;
x_221 = x_236;
x_222 = x_237;
x_223 = x_240;
x_224 = x_239;
x_225 = x_238;
x_226 = x_241;
x_227 = x_243;
x_228 = x_242;
x_229 = x_244;
x_230 = x_245;
x_231 = x_248;
x_232 = lean_box(0);
goto block_234;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_25; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
x_9 = x_2;
x_10 = x_25;
goto block_24;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_11; uint8_t x_17; lean_object* x_18; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_7, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
x_11 = lean_box(0);
goto block_16;
}
else
{
x_17 = x_1;
x_18 = lean_box(0);
goto block_20;
}
block_16:
{
lean_object* x_12; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_3);
x_12 = x_9;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_3);
x_12 = x_15;
goto block_14;
}
block_14:
{
x_2 = x_8;
x_3 = x_12;
goto _start;
}
}
block_20:
{
if (x_17 == 0)
{
lean_del_object(x_9);
lean_dec(x_7);
x_2 = x_8;
goto _start;
}
else
{
x_11 = lean_box(0);
goto block_16;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_58; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_58 = !lean_is_exclusive(x_2);
if (x_58 == 0)
{
x_13 = x_2;
x_14 = x_58;
goto block_57;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_15; lean_object* x_16; lean_object* x_22; 
x_22 = l_Lean_Meta_saveState___redArg(x_5, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc_ref(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_11);
x_24 = lean_apply_6(x_1, x_11, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_11);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_15 = x_26;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_48; 
x_27 = lean_ctor_get(x_24, 0);
x_48 = !lean_is_exclusive(x_24);
if (x_48 == 0)
{
x_28 = x_24;
x_29 = x_48;
goto block_47;
}
else
{
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = x_48;
goto block_47;
}
block_47:
{
uint8_t x_30; uint8_t x_45; 
x_45 = l_Lean_Exception_isInterrupt(x_27);
if (x_45 == 0)
{
uint8_t x_46; 
lean_inc(x_27);
x_46 = l_Lean_Exception_isRuntime(x_27);
x_30 = x_46;
goto block_44;
}
else
{
x_30 = x_45;
goto block_44;
}
block_44:
{
if (x_30 == 0)
{
lean_object* x_31; 
lean_del_object(x_28);
lean_dec(x_27);
x_31 = l_Lean_Meta_SavedState_restore___redArg(x_23, x_5, x_7);
lean_dec(x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec_ref(x_31);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_11);
x_15 = x_32;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_31, 0);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
x_34 = x_31;
x_35 = x_40;
goto block_39;
}
else
{
lean_inc(x_33);
lean_dec(x_31);
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
lean_dec(x_23);
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
if (x_29 == 0)
{
x_41 = x_28;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_27);
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
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_49 = lean_ctor_get(x_22, 0);
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
x_50 = x_22;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_22);
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
block_21:
{
lean_object* x_17; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 0, x_15);
x_17 = x_13;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_3);
x_17 = x_20;
goto block_19;
}
block_19:
{
x_2 = x_12;
x_3 = x_17;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_24; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
x_10 = x_3;
x_11 = x_24;
goto block_23;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = x_24;
goto block_23;
}
block_23:
{
uint8_t x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_8, x_5);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
x_12 = x_1;
x_13 = lean_box(0);
goto block_19;
}
else
{
x_12 = x_2;
x_13 = lean_box(0);
goto block_19;
}
block_19:
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
lean_object* x_15; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_4);
x_15 = x_10;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_4);
x_15 = x_18;
goto block_17;
}
block_17:
{
x_3 = x_9;
x_4 = x_15;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_25; lean_object* x_26; 
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0));
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(x_5, x_6, x_25, x_25, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_1506; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 0);
x_29 = lean_ctor_get(x_27, 1);
x_1506 = !lean_is_exclusive(x_27);
if (x_1506 == 0)
{
x_30 = x_27;
x_31 = x_1506;
goto block_1505;
}
else
{
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = x_1506;
goto block_1505;
}
block_1505:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_95 = l_List_isEmpty___redArg(x_28);
if (x_95 == 0)
{
lean_object* x_121; uint8_t x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_274; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; lean_object* x_412; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; uint8_t x_467; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_6);
x_121 = lean_ctor_get(x_9, 2);
x_122 = lean_ctor_get_uint8(x_121, sizeof(void*)*1);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_123 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(x_123, 0, x_1);
lean_closure_set(x_123, 1, x_2);
lean_closure_set(x_123, 2, x_3);
lean_closure_set(x_123, 3, x_4);
x_124 = 1;
if (x_122 == 0)
{
x_549 = x_7;
x_550 = x_8;
x_551 = x_9;
x_552 = x_10;
x_553 = lean_box(0);
goto block_587;
}
else
{
lean_object* x_588; 
lean_inc(x_2);
x_588 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; uint8_t x_629; lean_object* x_630; lean_object* x_631; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; uint8_t x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; uint8_t x_668; lean_object* x_669; lean_object* x_670; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_680; lean_object* x_681; lean_object* x_682; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; lean_object* x_696; uint8_t x_697; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; uint8_t x_709; lean_object* x_710; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; uint8_t x_724; lean_object* x_725; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; uint8_t x_736; lean_object* x_737; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; uint8_t x_750; lean_object* x_751; uint8_t x_752; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; uint8_t x_763; lean_object* x_764; uint8_t x_765; lean_object* x_766; lean_object* x_767; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; uint8_t x_777; lean_object* x_778; lean_object* x_779; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; uint8_t x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; uint8_t x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; uint8_t x_819; lean_object* x_820; lean_object* x_821; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; uint8_t x_831; lean_object* x_832; lean_object* x_833; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; uint8_t x_845; lean_object* x_846; lean_object* x_847; uint8_t x_848; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; uint8_t x_860; lean_object* x_861; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; uint8_t x_875; lean_object* x_876; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; uint8_t x_884; lean_object* x_885; lean_object* x_886; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; uint8_t x_898; lean_object* x_899; uint8_t x_900; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; uint8_t x_913; uint8_t x_914; lean_object* x_915; lean_object* x_916; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; uint8_t x_928; uint8_t x_929; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; uint8_t x_962; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; uint8_t x_991; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; uint8_t x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; uint8_t x_1073; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1097; uint8_t x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1117; uint8_t x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1127; uint8_t x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1137; uint8_t x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1150; uint8_t x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1162; uint8_t x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; uint8_t x_1173; lean_object* x_1177; uint8_t x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1195; uint8_t x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1205; uint8_t x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1215; uint8_t x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; uint8_t x_1224; lean_object* x_1225; lean_object* x_1231; uint8_t x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; uint8_t x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; uint8_t x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; uint8_t x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; uint8_t x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; uint8_t x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; uint8_t x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1306; uint8_t x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; uint8_t x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1331; uint8_t x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; uint8_t x_1342; lean_object* x_1346; uint8_t x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; uint8_t x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; uint8_t x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; uint8_t x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; uint8_t x_1389; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; uint8_t x_1419; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; uint8_t x_1429; lean_object* x_1430; lean_object* x_1431; uint8_t x_1491; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
lean_dec_ref(x_588);
lean_inc(x_29);
lean_inc(x_28);
x_590 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(x_590, 0, x_28);
lean_closure_set(x_590, 1, x_29);
x_591 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1491 = lean_unbox(x_589);
if (x_1491 == 0)
{
lean_object* x_1492; uint8_t x_1493; 
x_1492 = l_Lean_trace_profiler;
x_1493 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_121, x_1492);
if (x_1493 == 0)
{
lean_dec_ref(x_590);
lean_dec(x_589);
x_549 = x_7;
x_550 = x_8;
x_551 = x_9;
x_552 = x_10;
x_553 = lean_box(0);
goto block_587;
}
else
{
lean_inc_ref(x_121);
lean_del_object(x_30);
goto block_1490;
}
}
else
{
lean_inc_ref(x_121);
lean_del_object(x_30);
goto block_1490;
}
block_605:
{
lean_object* x_596; double x_597; double x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; lean_object* x_604; 
x_596 = lean_io_get_num_heartbeats();
x_597 = lean_float_of_nat(x_592);
x_598 = lean_float_of_nat(x_596);
x_599 = lean_box_float(x_597);
x_600 = lean_box_float(x_598);
x_601 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_601, 0, x_599);
lean_ctor_set(x_601, 1, x_600);
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_594);
lean_ctor_set(x_602, 1, x_601);
x_603 = lean_unbox(x_589);
lean_dec(x_589);
x_604 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_124, x_591, x_121, x_603, x_593, x_590, x_602, x_7, x_8, x_9, x_10);
lean_dec_ref(x_121);
return x_604;
}
block_611:
{
lean_object* x_610; 
x_610 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_610, 0, x_608);
x_592 = x_606;
x_593 = x_607;
x_594 = x_610;
x_595 = lean_box(0);
goto block_605;
}
block_617:
{
lean_object* x_616; 
x_616 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_616, 0, x_614);
x_592 = x_612;
x_593 = x_613;
x_594 = x_616;
x_595 = lean_box(0);
goto block_605;
}
block_623:
{
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
lean_dec_ref(x_620);
x_612 = x_618;
x_613 = x_619;
x_614 = x_621;
x_615 = lean_box(0);
goto block_617;
}
else
{
lean_object* x_622; 
x_622 = lean_ctor_get(x_620, 0);
lean_inc(x_622);
lean_dec_ref(x_620);
x_606 = x_618;
x_607 = x_619;
x_608 = x_622;
x_609 = lean_box(0);
goto block_611;
}
}
block_640:
{
lean_object* x_632; double x_633; double x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_632 = lean_io_get_num_heartbeats();
x_633 = lean_float_of_nat(x_626);
x_634 = lean_float_of_nat(x_632);
x_635 = lean_box_float(x_633);
x_636 = lean_box_float(x_634);
x_637 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_630);
lean_ctor_set(x_638, 1, x_637);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_639 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_124, x_591, x_121, x_629, x_628, x_624, x_638, x_7, x_8, x_9, x_10);
x_618 = x_625;
x_619 = x_627;
x_620 = x_639;
goto block_623;
}
block_650:
{
lean_object* x_649; 
x_649 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_649, 0, x_647);
x_624 = x_641;
x_625 = x_642;
x_626 = x_643;
x_627 = x_644;
x_628 = x_646;
x_629 = x_645;
x_630 = x_649;
x_631 = lean_box(0);
goto block_640;
}
block_660:
{
lean_object* x_659; 
x_659 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_659, 0, x_657);
x_624 = x_651;
x_625 = x_652;
x_626 = x_653;
x_627 = x_654;
x_628 = x_656;
x_629 = x_655;
x_630 = x_659;
x_631 = lean_box(0);
goto block_640;
}
block_673:
{
lean_object* x_671; lean_object* x_672; 
x_671 = l_List_appendTR___redArg(x_662, x_666);
x_672 = l_List_appendTR___redArg(x_671, x_669);
x_651 = x_661;
x_652 = x_663;
x_653 = x_664;
x_654 = x_665;
x_655 = x_668;
x_656 = x_667;
x_657 = x_672;
x_658 = lean_box(0);
goto block_660;
}
block_685:
{
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; 
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
lean_dec_ref(x_682);
x_661 = x_674;
x_662 = x_675;
x_663 = x_676;
x_664 = x_677;
x_665 = x_679;
x_666 = x_678;
x_667 = x_681;
x_668 = x_680;
x_669 = x_683;
x_670 = lean_box(0);
goto block_673;
}
else
{
lean_object* x_684; 
lean_dec(x_678);
lean_dec(x_675);
x_684 = lean_ctor_get(x_682, 0);
lean_inc(x_684);
lean_dec_ref(x_682);
x_641 = x_674;
x_642 = x_676;
x_643 = x_677;
x_644 = x_679;
x_645 = x_680;
x_646 = x_681;
x_647 = x_684;
x_648 = lean_box(0);
goto block_650;
}
}
block_700:
{
if (x_697 == 0)
{
lean_object* x_698; 
lean_dec_ref(x_694);
x_698 = l_Lean_Meta_SavedState_restore___redArg(x_690, x_8, x_10);
lean_dec_ref(x_690);
if (lean_obj_tag(x_698) == 0)
{
lean_dec_ref(x_698);
x_661 = x_686;
x_662 = x_687;
x_663 = x_688;
x_664 = x_691;
x_665 = x_693;
x_666 = x_692;
x_667 = x_696;
x_668 = x_695;
x_669 = x_29;
x_670 = lean_box(0);
goto block_673;
}
else
{
lean_object* x_699; 
lean_dec(x_692);
lean_dec(x_687);
lean_dec(x_29);
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
lean_dec_ref(x_698);
x_641 = x_686;
x_642 = x_688;
x_643 = x_691;
x_644 = x_693;
x_645 = x_695;
x_646 = x_696;
x_647 = x_699;
x_648 = lean_box(0);
goto block_650;
}
}
else
{
lean_dec_ref(x_690);
lean_dec(x_29);
x_674 = x_686;
x_675 = x_687;
x_676 = x_688;
x_677 = x_691;
x_678 = x_692;
x_679 = x_693;
x_680 = x_695;
x_681 = x_696;
x_682 = x_694;
goto block_685;
}
}
block_718:
{
lean_object* x_711; 
x_711 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; 
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
lean_dec_ref(x_711);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_713 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_710, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_713) == 0)
{
lean_dec(x_712);
lean_dec(x_29);
x_674 = x_701;
x_675 = x_702;
x_676 = x_704;
x_677 = x_705;
x_678 = x_707;
x_679 = x_706;
x_680 = x_709;
x_681 = x_708;
x_682 = x_713;
goto block_685;
}
else
{
lean_object* x_714; uint8_t x_715; 
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
x_715 = l_Lean_Exception_isInterrupt(x_714);
if (x_715 == 0)
{
uint8_t x_716; 
x_716 = l_Lean_Exception_isRuntime(x_714);
x_686 = x_701;
x_687 = x_702;
x_688 = x_704;
x_689 = lean_box(0);
x_690 = x_712;
x_691 = x_705;
x_692 = x_707;
x_693 = x_706;
x_694 = x_713;
x_695 = x_709;
x_696 = x_708;
x_697 = x_716;
goto block_700;
}
else
{
lean_dec(x_714);
x_686 = x_701;
x_687 = x_702;
x_688 = x_704;
x_689 = lean_box(0);
x_690 = x_712;
x_691 = x_705;
x_692 = x_707;
x_693 = x_706;
x_694 = x_713;
x_695 = x_709;
x_696 = x_708;
x_697 = x_715;
goto block_700;
}
}
}
else
{
lean_object* x_717; 
lean_dec(x_710);
lean_dec(x_707);
lean_dec(x_702);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_717 = lean_ctor_get(x_711, 0);
lean_inc(x_717);
lean_dec_ref(x_711);
x_641 = x_701;
x_642 = x_704;
x_643 = x_705;
x_644 = x_706;
x_645 = x_709;
x_646 = x_708;
x_647 = x_717;
x_648 = lean_box(0);
goto block_650;
}
}
block_728:
{
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; 
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
lean_dec_ref(x_725);
x_651 = x_719;
x_652 = x_720;
x_653 = x_721;
x_654 = x_722;
x_655 = x_724;
x_656 = x_723;
x_657 = x_726;
x_658 = lean_box(0);
goto block_660;
}
else
{
lean_object* x_727; 
x_727 = lean_ctor_get(x_725, 0);
lean_inc(x_727);
lean_dec_ref(x_725);
x_641 = x_719;
x_642 = x_720;
x_643 = x_721;
x_644 = x_722;
x_645 = x_724;
x_646 = x_723;
x_647 = x_727;
x_648 = lean_box(0);
goto block_650;
}
}
block_741:
{
lean_object* x_738; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_738 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_737, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; lean_object* x_740; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
lean_dec_ref(x_738);
x_740 = l_List_appendTR___redArg(x_730, x_739);
x_651 = x_729;
x_652 = x_732;
x_653 = x_733;
x_654 = x_734;
x_655 = x_736;
x_656 = x_735;
x_657 = x_740;
x_658 = lean_box(0);
goto block_660;
}
else
{
lean_dec(x_730);
x_719 = x_729;
x_720 = x_732;
x_721 = x_733;
x_722 = x_734;
x_723 = x_735;
x_724 = x_736;
x_725 = x_738;
goto block_728;
}
}
block_756:
{
uint8_t x_753; 
x_753 = l_List_isEmpty___redArg(x_748);
lean_dec(x_748);
if (x_753 == 0)
{
if (x_752 == 0)
{
x_729 = x_742;
x_730 = x_743;
x_731 = lean_box(0);
x_732 = x_745;
x_733 = x_746;
x_734 = x_747;
x_735 = x_751;
x_736 = x_750;
x_737 = x_749;
goto block_741;
}
else
{
lean_object* x_754; lean_object* x_755; 
lean_dec(x_749);
lean_dec(x_743);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_754 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_755 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_754, x_7, x_8, x_9, x_10);
x_719 = x_742;
x_720 = x_745;
x_721 = x_746;
x_722 = x_747;
x_723 = x_751;
x_724 = x_750;
x_725 = x_755;
goto block_728;
}
}
else
{
x_729 = x_742;
x_730 = x_743;
x_731 = lean_box(0);
x_732 = x_745;
x_733 = x_746;
x_734 = x_747;
x_735 = x_751;
x_736 = x_750;
x_737 = x_749;
goto block_741;
}
}
block_771:
{
uint8_t x_768; lean_object* x_769; 
x_768 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_758);
x_769 = l_List_appendTR___redArg(x_766, x_758);
if (x_768 == 0)
{
x_742 = x_757;
x_743 = x_758;
x_744 = lean_box(0);
x_745 = x_759;
x_746 = x_760;
x_747 = x_762;
x_748 = x_761;
x_749 = x_769;
x_750 = x_763;
x_751 = x_764;
x_752 = x_765;
goto block_756;
}
else
{
uint8_t x_770; 
x_770 = l_List_isEmpty___redArg(x_758);
if (x_770 == 0)
{
x_701 = x_757;
x_702 = x_758;
x_703 = lean_box(0);
x_704 = x_759;
x_705 = x_760;
x_706 = x_762;
x_707 = x_761;
x_708 = x_764;
x_709 = x_763;
x_710 = x_769;
goto block_718;
}
else
{
if (x_95 == 0)
{
x_742 = x_757;
x_743 = x_758;
x_744 = lean_box(0);
x_745 = x_759;
x_746 = x_760;
x_747 = x_762;
x_748 = x_761;
x_749 = x_769;
x_750 = x_763;
x_751 = x_764;
x_752 = x_765;
goto block_756;
}
else
{
x_701 = x_757;
x_702 = x_758;
x_703 = lean_box(0);
x_704 = x_759;
x_705 = x_760;
x_706 = x_762;
x_707 = x_761;
x_708 = x_764;
x_709 = x_763;
x_710 = x_769;
goto block_718;
}
}
}
}
block_791:
{
lean_object* x_780; double x_781; double x_782; double x_783; double x_784; double x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_780 = lean_io_mono_nanos_now();
x_781 = lean_float_of_nat(x_773);
x_782 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_783 = lean_float_div(x_781, x_782);
x_784 = lean_float_of_nat(x_780);
x_785 = lean_float_div(x_784, x_782);
x_786 = lean_box_float(x_783);
x_787 = lean_box_float(x_785);
x_788 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
x_789 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_789, 0, x_778);
lean_ctor_set(x_789, 1, x_788);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_790 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_124, x_591, x_121, x_777, x_776, x_772, x_789, x_7, x_8, x_9, x_10);
x_618 = x_774;
x_619 = x_775;
x_620 = x_790;
goto block_623;
}
block_801:
{
lean_object* x_800; 
x_800 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_800, 0, x_798);
x_772 = x_792;
x_773 = x_793;
x_774 = x_794;
x_775 = x_795;
x_776 = x_797;
x_777 = x_796;
x_778 = x_800;
x_779 = lean_box(0);
goto block_791;
}
block_811:
{
lean_object* x_810; 
x_810 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_810, 0, x_808);
x_772 = x_802;
x_773 = x_803;
x_774 = x_804;
x_775 = x_805;
x_776 = x_807;
x_777 = x_806;
x_778 = x_810;
x_779 = lean_box(0);
goto block_791;
}
block_824:
{
lean_object* x_822; lean_object* x_823; 
x_822 = l_List_appendTR___redArg(x_813, x_817);
x_823 = l_List_appendTR___redArg(x_822, x_820);
x_802 = x_812;
x_803 = x_814;
x_804 = x_815;
x_805 = x_816;
x_806 = x_819;
x_807 = x_818;
x_808 = x_823;
x_809 = lean_box(0);
goto block_811;
}
block_836:
{
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; 
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
lean_dec_ref(x_833);
x_812 = x_825;
x_813 = x_826;
x_814 = x_827;
x_815 = x_828;
x_816 = x_830;
x_817 = x_829;
x_818 = x_832;
x_819 = x_831;
x_820 = x_834;
x_821 = lean_box(0);
goto block_824;
}
else
{
lean_object* x_835; 
lean_dec(x_829);
lean_dec(x_826);
x_835 = lean_ctor_get(x_833, 0);
lean_inc(x_835);
lean_dec_ref(x_833);
x_792 = x_825;
x_793 = x_827;
x_794 = x_828;
x_795 = x_830;
x_796 = x_831;
x_797 = x_832;
x_798 = x_835;
x_799 = lean_box(0);
goto block_801;
}
}
block_851:
{
if (x_848 == 0)
{
lean_object* x_849; 
lean_dec_ref(x_847);
x_849 = l_Lean_Meta_SavedState_restore___redArg(x_841, x_8, x_10);
lean_dec_ref(x_841);
if (lean_obj_tag(x_849) == 0)
{
lean_dec_ref(x_849);
x_812 = x_837;
x_813 = x_838;
x_814 = x_839;
x_815 = x_840;
x_816 = x_843;
x_817 = x_842;
x_818 = x_846;
x_819 = x_845;
x_820 = x_29;
x_821 = lean_box(0);
goto block_824;
}
else
{
lean_object* x_850; 
lean_dec(x_842);
lean_dec(x_838);
lean_dec(x_29);
x_850 = lean_ctor_get(x_849, 0);
lean_inc(x_850);
lean_dec_ref(x_849);
x_792 = x_837;
x_793 = x_839;
x_794 = x_840;
x_795 = x_843;
x_796 = x_845;
x_797 = x_846;
x_798 = x_850;
x_799 = lean_box(0);
goto block_801;
}
}
else
{
lean_dec_ref(x_841);
lean_dec(x_29);
x_825 = x_837;
x_826 = x_838;
x_827 = x_839;
x_828 = x_840;
x_829 = x_842;
x_830 = x_843;
x_831 = x_845;
x_832 = x_846;
x_833 = x_847;
goto block_836;
}
}
block_869:
{
lean_object* x_862; 
x_862 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_862) == 0)
{
lean_object* x_863; lean_object* x_864; 
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
lean_dec_ref(x_862);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_864 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_856, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_864) == 0)
{
lean_dec(x_863);
lean_dec(x_29);
x_825 = x_852;
x_826 = x_853;
x_827 = x_854;
x_828 = x_855;
x_829 = x_858;
x_830 = x_857;
x_831 = x_860;
x_832 = x_859;
x_833 = x_864;
goto block_836;
}
else
{
lean_object* x_865; uint8_t x_866; 
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
x_866 = l_Lean_Exception_isInterrupt(x_865);
if (x_866 == 0)
{
uint8_t x_867; 
x_867 = l_Lean_Exception_isRuntime(x_865);
x_837 = x_852;
x_838 = x_853;
x_839 = x_854;
x_840 = x_855;
x_841 = x_863;
x_842 = x_858;
x_843 = x_857;
x_844 = lean_box(0);
x_845 = x_860;
x_846 = x_859;
x_847 = x_864;
x_848 = x_867;
goto block_851;
}
else
{
lean_dec(x_865);
x_837 = x_852;
x_838 = x_853;
x_839 = x_854;
x_840 = x_855;
x_841 = x_863;
x_842 = x_858;
x_843 = x_857;
x_844 = lean_box(0);
x_845 = x_860;
x_846 = x_859;
x_847 = x_864;
x_848 = x_866;
goto block_851;
}
}
}
else
{
lean_object* x_868; 
lean_dec(x_858);
lean_dec(x_856);
lean_dec(x_853);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_868 = lean_ctor_get(x_862, 0);
lean_inc(x_868);
lean_dec_ref(x_862);
x_792 = x_852;
x_793 = x_854;
x_794 = x_855;
x_795 = x_857;
x_796 = x_860;
x_797 = x_859;
x_798 = x_868;
x_799 = lean_box(0);
goto block_801;
}
}
block_879:
{
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; 
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
lean_dec_ref(x_876);
x_802 = x_870;
x_803 = x_871;
x_804 = x_872;
x_805 = x_873;
x_806 = x_875;
x_807 = x_874;
x_808 = x_877;
x_809 = lean_box(0);
goto block_811;
}
else
{
lean_object* x_878; 
x_878 = lean_ctor_get(x_876, 0);
lean_inc(x_878);
lean_dec_ref(x_876);
x_792 = x_870;
x_793 = x_871;
x_794 = x_872;
x_795 = x_873;
x_796 = x_875;
x_797 = x_874;
x_798 = x_878;
x_799 = lean_box(0);
goto block_801;
}
}
block_889:
{
lean_object* x_887; lean_object* x_888; 
x_887 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_888 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_887, x_7, x_8, x_9, x_10);
x_870 = x_880;
x_871 = x_881;
x_872 = x_882;
x_873 = x_883;
x_874 = x_885;
x_875 = x_884;
x_876 = x_888;
goto block_879;
}
block_905:
{
uint8_t x_901; 
x_901 = l_List_isEmpty___redArg(x_896);
lean_dec(x_896);
if (x_901 == 0)
{
lean_dec(x_894);
lean_dec(x_891);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_880 = x_890;
x_881 = x_892;
x_882 = x_893;
x_883 = x_895;
x_884 = x_898;
x_885 = x_897;
x_886 = lean_box(0);
goto block_889;
}
else
{
if (x_900 == 0)
{
lean_object* x_902; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_902 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_894, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_903; lean_object* x_904; 
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
lean_dec_ref(x_902);
x_904 = l_List_appendTR___redArg(x_891, x_903);
x_802 = x_890;
x_803 = x_892;
x_804 = x_893;
x_805 = x_895;
x_806 = x_898;
x_807 = x_897;
x_808 = x_904;
x_809 = lean_box(0);
goto block_811;
}
else
{
lean_dec(x_891);
x_870 = x_890;
x_871 = x_892;
x_872 = x_893;
x_873 = x_895;
x_874 = x_897;
x_875 = x_898;
x_876 = x_902;
goto block_879;
}
}
else
{
lean_dec(x_894);
lean_dec(x_891);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_880 = x_890;
x_881 = x_892;
x_882 = x_893;
x_883 = x_895;
x_884 = x_898;
x_885 = x_897;
x_886 = lean_box(0);
goto block_889;
}
}
}
block_920:
{
uint8_t x_917; lean_object* x_918; 
x_917 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_907);
x_918 = l_List_appendTR___redArg(x_915, x_907);
if (x_917 == 0)
{
x_890 = x_906;
x_891 = x_907;
x_892 = x_908;
x_893 = x_909;
x_894 = x_918;
x_895 = x_911;
x_896 = x_910;
x_897 = x_912;
x_898 = x_913;
x_899 = lean_box(0);
x_900 = x_914;
goto block_905;
}
else
{
uint8_t x_919; 
x_919 = l_List_isEmpty___redArg(x_907);
if (x_919 == 0)
{
x_852 = x_906;
x_853 = x_907;
x_854 = x_908;
x_855 = x_909;
x_856 = x_918;
x_857 = x_911;
x_858 = x_910;
x_859 = x_912;
x_860 = x_913;
x_861 = lean_box(0);
goto block_869;
}
else
{
if (x_914 == 0)
{
x_890 = x_906;
x_891 = x_907;
x_892 = x_908;
x_893 = x_909;
x_894 = x_918;
x_895 = x_911;
x_896 = x_910;
x_897 = x_912;
x_898 = x_913;
x_899 = lean_box(0);
x_900 = x_914;
goto block_905;
}
else
{
x_852 = x_906;
x_853 = x_907;
x_854 = x_908;
x_855 = x_909;
x_856 = x_918;
x_857 = x_911;
x_858 = x_910;
x_859 = x_912;
x_860 = x_913;
x_861 = lean_box(0);
goto block_869;
}
}
}
}
block_946:
{
lean_object* x_930; 
x_930 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_930) == 0)
{
if (x_929 == 0)
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
lean_dec_ref(x_930);
x_932 = lean_io_mono_nanos_now();
x_933 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_929, x_95, x_5, x_925, x_8);
if (lean_obj_tag(x_933) == 0)
{
lean_object* x_934; lean_object* x_935; 
x_934 = lean_ctor_get(x_933, 0);
lean_inc(x_934);
lean_dec_ref(x_933);
x_935 = l_List_reverse___redArg(x_934);
x_906 = x_921;
x_907 = x_922;
x_908 = x_932;
x_909 = x_923;
x_910 = x_926;
x_911 = x_927;
x_912 = x_931;
x_913 = x_928;
x_914 = x_929;
x_915 = x_935;
x_916 = lean_box(0);
goto block_920;
}
else
{
if (lean_obj_tag(x_933) == 0)
{
lean_object* x_936; 
x_936 = lean_ctor_get(x_933, 0);
lean_inc(x_936);
lean_dec_ref(x_933);
x_906 = x_921;
x_907 = x_922;
x_908 = x_932;
x_909 = x_923;
x_910 = x_926;
x_911 = x_927;
x_912 = x_931;
x_913 = x_928;
x_914 = x_929;
x_915 = x_936;
x_916 = lean_box(0);
goto block_920;
}
else
{
lean_object* x_937; 
lean_dec(x_926);
lean_dec(x_922);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_937 = lean_ctor_get(x_933, 0);
lean_inc(x_937);
lean_dec_ref(x_933);
x_792 = x_921;
x_793 = x_932;
x_794 = x_923;
x_795 = x_927;
x_796 = x_928;
x_797 = x_931;
x_798 = x_937;
x_799 = lean_box(0);
goto block_801;
}
}
}
else
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_938 = lean_ctor_get(x_930, 0);
lean_inc(x_938);
lean_dec_ref(x_930);
x_939 = lean_io_get_num_heartbeats();
x_940 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_929, x_95, x_5, x_925, x_8);
if (lean_obj_tag(x_940) == 0)
{
lean_object* x_941; lean_object* x_942; 
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
lean_dec_ref(x_940);
x_942 = l_List_reverse___redArg(x_941);
x_757 = x_921;
x_758 = x_922;
x_759 = x_923;
x_760 = x_939;
x_761 = x_926;
x_762 = x_927;
x_763 = x_928;
x_764 = x_938;
x_765 = x_929;
x_766 = x_942;
x_767 = lean_box(0);
goto block_771;
}
else
{
if (lean_obj_tag(x_940) == 0)
{
lean_object* x_943; 
x_943 = lean_ctor_get(x_940, 0);
lean_inc(x_943);
lean_dec_ref(x_940);
x_757 = x_921;
x_758 = x_922;
x_759 = x_923;
x_760 = x_939;
x_761 = x_926;
x_762 = x_927;
x_763 = x_928;
x_764 = x_938;
x_765 = x_929;
x_766 = x_943;
x_767 = lean_box(0);
goto block_771;
}
else
{
lean_object* x_944; 
lean_dec(x_926);
lean_dec(x_922);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_944 = lean_ctor_get(x_940, 0);
lean_inc(x_944);
lean_dec_ref(x_940);
x_641 = x_921;
x_642 = x_923;
x_643 = x_939;
x_644 = x_927;
x_645 = x_928;
x_646 = x_938;
x_647 = x_944;
x_648 = lean_box(0);
goto block_650;
}
}
}
}
else
{
lean_object* x_945; 
lean_dec(x_926);
lean_dec(x_925);
lean_dec(x_922);
lean_dec_ref(x_921);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_945 = lean_ctor_get(x_930, 0);
lean_inc(x_945);
lean_dec_ref(x_930);
x_606 = x_923;
x_607 = x_927;
x_608 = x_945;
x_609 = lean_box(0);
goto block_611;
}
}
block_955:
{
lean_object* x_952; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_952 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_947, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_952) == 0)
{
lean_object* x_953; lean_object* x_954; 
x_953 = lean_ctor_get(x_952, 0);
lean_inc(x_953);
lean_dec_ref(x_952);
x_954 = l_List_appendTR___redArg(x_948, x_953);
x_612 = x_949;
x_613 = x_950;
x_614 = x_954;
x_615 = lean_box(0);
goto block_617;
}
else
{
lean_dec(x_948);
x_618 = x_949;
x_619 = x_950;
x_620 = x_952;
goto block_623;
}
}
block_966:
{
uint8_t x_963; 
x_963 = l_List_isEmpty___redArg(x_960);
lean_dec(x_960);
if (x_963 == 0)
{
if (x_962 == 0)
{
x_947 = x_956;
x_948 = x_957;
x_949 = x_958;
x_950 = x_959;
x_951 = lean_box(0);
goto block_955;
}
else
{
lean_object* x_964; lean_object* x_965; 
lean_dec(x_957);
lean_dec(x_956);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_964 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_965 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_964, x_7, x_8, x_9, x_10);
x_618 = x_958;
x_619 = x_959;
x_620 = x_965;
goto block_623;
}
}
else
{
x_947 = x_956;
x_948 = x_957;
x_949 = x_958;
x_950 = x_959;
x_951 = lean_box(0);
goto block_955;
}
}
block_975:
{
lean_object* x_973; lean_object* x_974; 
x_973 = l_List_appendTR___redArg(x_967, x_970);
x_974 = l_List_appendTR___redArg(x_973, x_971);
x_612 = x_968;
x_613 = x_969;
x_614 = x_974;
x_615 = lean_box(0);
goto block_617;
}
block_983:
{
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; 
x_981 = lean_ctor_get(x_980, 0);
lean_inc(x_981);
lean_dec_ref(x_980);
x_967 = x_976;
x_968 = x_977;
x_969 = x_979;
x_970 = x_978;
x_971 = x_981;
x_972 = lean_box(0);
goto block_975;
}
else
{
lean_object* x_982; 
lean_dec(x_978);
lean_dec(x_976);
x_982 = lean_ctor_get(x_980, 0);
lean_inc(x_982);
lean_dec_ref(x_980);
x_606 = x_977;
x_607 = x_979;
x_608 = x_982;
x_609 = lean_box(0);
goto block_611;
}
}
block_994:
{
if (x_991 == 0)
{
lean_object* x_992; 
lean_dec_ref(x_989);
x_992 = l_Lean_Meta_SavedState_restore___redArg(x_990, x_8, x_10);
lean_dec_ref(x_990);
if (lean_obj_tag(x_992) == 0)
{
lean_dec_ref(x_992);
x_967 = x_984;
x_968 = x_986;
x_969 = x_988;
x_970 = x_987;
x_971 = x_29;
x_972 = lean_box(0);
goto block_975;
}
else
{
lean_object* x_993; 
lean_dec(x_987);
lean_dec(x_984);
lean_dec(x_29);
x_993 = lean_ctor_get(x_992, 0);
lean_inc(x_993);
lean_dec_ref(x_992);
x_606 = x_986;
x_607 = x_988;
x_608 = x_993;
x_609 = lean_box(0);
goto block_611;
}
}
else
{
lean_dec_ref(x_990);
lean_dec(x_29);
x_976 = x_984;
x_977 = x_986;
x_978 = x_987;
x_979 = x_988;
x_980 = x_989;
goto block_983;
}
}
block_1008:
{
lean_object* x_1001; 
x_1001 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1001) == 0)
{
lean_object* x_1002; lean_object* x_1003; 
x_1002 = lean_ctor_get(x_1001, 0);
lean_inc(x_1002);
lean_dec_ref(x_1001);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_1003 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_995, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1003) == 0)
{
lean_dec(x_1002);
lean_dec(x_29);
x_976 = x_996;
x_977 = x_997;
x_978 = x_999;
x_979 = x_998;
x_980 = x_1003;
goto block_983;
}
else
{
lean_object* x_1004; uint8_t x_1005; 
x_1004 = lean_ctor_get(x_1003, 0);
lean_inc(x_1004);
x_1005 = l_Lean_Exception_isInterrupt(x_1004);
if (x_1005 == 0)
{
uint8_t x_1006; 
x_1006 = l_Lean_Exception_isRuntime(x_1004);
x_984 = x_996;
x_985 = lean_box(0);
x_986 = x_997;
x_987 = x_999;
x_988 = x_998;
x_989 = x_1003;
x_990 = x_1002;
x_991 = x_1006;
goto block_994;
}
else
{
lean_dec(x_1004);
x_984 = x_996;
x_985 = lean_box(0);
x_986 = x_997;
x_987 = x_999;
x_988 = x_998;
x_989 = x_1003;
x_990 = x_1002;
x_991 = x_1005;
goto block_994;
}
}
}
else
{
lean_object* x_1007; 
lean_dec(x_999);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1007 = lean_ctor_get(x_1001, 0);
lean_inc(x_1007);
lean_dec_ref(x_1001);
x_606 = x_997;
x_607 = x_998;
x_608 = x_1007;
x_609 = lean_box(0);
goto block_611;
}
}
block_1019:
{
uint8_t x_1016; lean_object* x_1017; 
x_1016 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_1009);
x_1017 = l_List_appendTR___redArg(x_1014, x_1009);
if (x_1016 == 0)
{
x_956 = x_1017;
x_957 = x_1009;
x_958 = x_1010;
x_959 = x_1012;
x_960 = x_1011;
x_961 = lean_box(0);
x_962 = x_1013;
goto block_966;
}
else
{
uint8_t x_1018; 
x_1018 = l_List_isEmpty___redArg(x_1009);
if (x_1018 == 0)
{
x_995 = x_1017;
x_996 = x_1009;
x_997 = x_1010;
x_998 = x_1012;
x_999 = x_1011;
x_1000 = lean_box(0);
goto block_1008;
}
else
{
if (x_95 == 0)
{
x_956 = x_1017;
x_957 = x_1009;
x_958 = x_1010;
x_959 = x_1012;
x_960 = x_1011;
x_961 = lean_box(0);
x_962 = x_1013;
goto block_966;
}
else
{
x_995 = x_1017;
x_996 = x_1009;
x_997 = x_1010;
x_998 = x_1012;
x_999 = x_1011;
x_1000 = lean_box(0);
goto block_1008;
}
}
}
}
block_1036:
{
lean_object* x_1024; double x_1025; double x_1026; double x_1027; double x_1028; double x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; uint8_t x_1034; lean_object* x_1035; 
x_1024 = lean_io_mono_nanos_now();
x_1025 = lean_float_of_nat(x_1020);
x_1026 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_1027 = lean_float_div(x_1025, x_1026);
x_1028 = lean_float_of_nat(x_1024);
x_1029 = lean_float_div(x_1028, x_1026);
x_1030 = lean_box_float(x_1027);
x_1031 = lean_box_float(x_1029);
x_1032 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1032, 0, x_1030);
lean_ctor_set(x_1032, 1, x_1031);
x_1033 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1033, 0, x_1022);
lean_ctor_set(x_1033, 1, x_1032);
x_1034 = lean_unbox(x_589);
lean_dec(x_589);
x_1035 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_124, x_591, x_121, x_1034, x_1021, x_590, x_1033, x_7, x_8, x_9, x_10);
lean_dec_ref(x_121);
return x_1035;
}
block_1042:
{
lean_object* x_1041; 
x_1041 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1041, 0, x_1039);
x_1020 = x_1037;
x_1021 = x_1038;
x_1022 = x_1041;
x_1023 = lean_box(0);
goto block_1036;
}
block_1051:
{
lean_object* x_1049; lean_object* x_1050; 
x_1049 = l_List_appendTR___redArg(x_1043, x_1045);
x_1050 = l_List_appendTR___redArg(x_1049, x_1047);
x_1037 = x_1044;
x_1038 = x_1046;
x_1039 = x_1050;
x_1040 = lean_box(0);
goto block_1042;
}
block_1057:
{
lean_object* x_1056; 
x_1056 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1056, 0, x_1054);
x_1020 = x_1052;
x_1021 = x_1053;
x_1022 = x_1056;
x_1023 = lean_box(0);
goto block_1036;
}
block_1065:
{
if (lean_obj_tag(x_1062) == 0)
{
lean_object* x_1063; 
x_1063 = lean_ctor_get(x_1062, 0);
lean_inc(x_1063);
lean_dec_ref(x_1062);
x_1043 = x_1058;
x_1044 = x_1059;
x_1045 = x_1060;
x_1046 = x_1061;
x_1047 = x_1063;
x_1048 = lean_box(0);
goto block_1051;
}
else
{
lean_object* x_1064; 
lean_dec(x_1060);
lean_dec(x_1058);
x_1064 = lean_ctor_get(x_1062, 0);
lean_inc(x_1064);
lean_dec_ref(x_1062);
x_1052 = x_1059;
x_1053 = x_1061;
x_1054 = x_1064;
x_1055 = lean_box(0);
goto block_1057;
}
}
block_1076:
{
if (x_1073 == 0)
{
lean_object* x_1074; 
lean_dec_ref(x_1070);
x_1074 = l_Lean_Meta_SavedState_restore___redArg(x_1067, x_8, x_10);
lean_dec_ref(x_1067);
if (lean_obj_tag(x_1074) == 0)
{
lean_dec_ref(x_1074);
x_1043 = x_1068;
x_1044 = x_1069;
x_1045 = x_1071;
x_1046 = x_1072;
x_1047 = x_29;
x_1048 = lean_box(0);
goto block_1051;
}
else
{
lean_object* x_1075; 
lean_dec(x_1071);
lean_dec(x_1068);
lean_dec(x_29);
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
lean_dec_ref(x_1074);
x_1052 = x_1069;
x_1053 = x_1072;
x_1054 = x_1075;
x_1055 = lean_box(0);
goto block_1057;
}
}
else
{
lean_dec_ref(x_1067);
lean_dec(x_29);
x_1058 = x_1068;
x_1059 = x_1069;
x_1060 = x_1071;
x_1061 = x_1072;
x_1062 = x_1070;
goto block_1065;
}
}
block_1090:
{
lean_object* x_1083; 
x_1083 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1083) == 0)
{
lean_object* x_1084; lean_object* x_1085; 
x_1084 = lean_ctor_get(x_1083, 0);
lean_inc(x_1084);
lean_dec_ref(x_1083);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_1085 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1079, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1085) == 0)
{
lean_dec(x_1084);
lean_dec(x_29);
x_1058 = x_1078;
x_1059 = x_1080;
x_1060 = x_1081;
x_1061 = x_1082;
x_1062 = x_1085;
goto block_1065;
}
else
{
lean_object* x_1086; uint8_t x_1087; 
x_1086 = lean_ctor_get(x_1085, 0);
lean_inc(x_1086);
x_1087 = l_Lean_Exception_isInterrupt(x_1086);
if (x_1087 == 0)
{
uint8_t x_1088; 
x_1088 = l_Lean_Exception_isRuntime(x_1086);
x_1066 = lean_box(0);
x_1067 = x_1084;
x_1068 = x_1078;
x_1069 = x_1080;
x_1070 = x_1085;
x_1071 = x_1081;
x_1072 = x_1082;
x_1073 = x_1088;
goto block_1076;
}
else
{
lean_dec(x_1086);
x_1066 = lean_box(0);
x_1067 = x_1084;
x_1068 = x_1078;
x_1069 = x_1080;
x_1070 = x_1085;
x_1071 = x_1081;
x_1072 = x_1082;
x_1073 = x_1087;
goto block_1076;
}
}
}
else
{
lean_object* x_1089; 
lean_dec(x_1081);
lean_dec(x_1079);
lean_dec(x_1078);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1089 = lean_ctor_get(x_1083, 0);
lean_inc(x_1089);
lean_dec_ref(x_1083);
x_1052 = x_1080;
x_1053 = x_1082;
x_1054 = x_1089;
x_1055 = lean_box(0);
goto block_1057;
}
}
block_1096:
{
if (lean_obj_tag(x_1093) == 0)
{
lean_object* x_1094; 
x_1094 = lean_ctor_get(x_1093, 0);
lean_inc(x_1094);
lean_dec_ref(x_1093);
x_1037 = x_1091;
x_1038 = x_1092;
x_1039 = x_1094;
x_1040 = lean_box(0);
goto block_1042;
}
else
{
lean_object* x_1095; 
x_1095 = lean_ctor_get(x_1093, 0);
lean_inc(x_1095);
lean_dec_ref(x_1093);
x_1052 = x_1091;
x_1053 = x_1092;
x_1054 = x_1095;
x_1055 = lean_box(0);
goto block_1057;
}
}
block_1116:
{
lean_object* x_1105; double x_1106; double x_1107; double x_1108; double x_1109; double x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
x_1105 = lean_io_mono_nanos_now();
x_1106 = lean_float_of_nat(x_1097);
x_1107 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_1108 = lean_float_div(x_1106, x_1107);
x_1109 = lean_float_of_nat(x_1105);
x_1110 = lean_float_div(x_1109, x_1107);
x_1111 = lean_box_float(x_1108);
x_1112 = lean_box_float(x_1110);
x_1113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1113, 0, x_1111);
lean_ctor_set(x_1113, 1, x_1112);
x_1114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1114, 0, x_1103);
lean_ctor_set(x_1114, 1, x_1113);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1115 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_124, x_591, x_121, x_1098, x_1102, x_1101, x_1114, x_7, x_8, x_9, x_10);
x_1091 = x_1099;
x_1092 = x_1100;
x_1093 = x_1115;
goto block_1096;
}
block_1126:
{
lean_object* x_1125; 
x_1125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1125, 0, x_1123);
x_1097 = x_1117;
x_1098 = x_1118;
x_1099 = x_1119;
x_1100 = x_1121;
x_1101 = x_1120;
x_1102 = x_1122;
x_1103 = x_1125;
x_1104 = lean_box(0);
goto block_1116;
}
block_1136:
{
lean_object* x_1135; 
x_1135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1135, 0, x_1133);
x_1097 = x_1127;
x_1098 = x_1128;
x_1099 = x_1129;
x_1100 = x_1131;
x_1101 = x_1130;
x_1102 = x_1132;
x_1103 = x_1135;
x_1104 = lean_box(0);
goto block_1116;
}
block_1149:
{
lean_object* x_1147; lean_object* x_1148; 
x_1147 = l_List_appendTR___redArg(x_1139, x_1141);
x_1148 = l_List_appendTR___redArg(x_1147, x_1145);
x_1127 = x_1137;
x_1128 = x_1138;
x_1129 = x_1140;
x_1130 = x_1143;
x_1131 = x_1142;
x_1132 = x_1144;
x_1133 = x_1148;
x_1134 = lean_box(0);
goto block_1136;
}
block_1161:
{
if (lean_obj_tag(x_1158) == 0)
{
lean_object* x_1159; 
x_1159 = lean_ctor_get(x_1158, 0);
lean_inc(x_1159);
lean_dec_ref(x_1158);
x_1137 = x_1150;
x_1138 = x_1151;
x_1139 = x_1152;
x_1140 = x_1153;
x_1141 = x_1154;
x_1142 = x_1156;
x_1143 = x_1155;
x_1144 = x_1157;
x_1145 = x_1159;
x_1146 = lean_box(0);
goto block_1149;
}
else
{
lean_object* x_1160; 
lean_dec(x_1154);
lean_dec(x_1152);
x_1160 = lean_ctor_get(x_1158, 0);
lean_inc(x_1160);
lean_dec_ref(x_1158);
x_1117 = x_1150;
x_1118 = x_1151;
x_1119 = x_1153;
x_1120 = x_1155;
x_1121 = x_1156;
x_1122 = x_1157;
x_1123 = x_1160;
x_1124 = lean_box(0);
goto block_1126;
}
}
block_1176:
{
if (x_1173 == 0)
{
lean_object* x_1174; 
lean_dec_ref(x_1164);
x_1174 = l_Lean_Meta_SavedState_restore___redArg(x_1166, x_8, x_10);
lean_dec_ref(x_1166);
if (lean_obj_tag(x_1174) == 0)
{
lean_dec_ref(x_1174);
x_1137 = x_1162;
x_1138 = x_1163;
x_1139 = x_1165;
x_1140 = x_1167;
x_1141 = x_1169;
x_1142 = x_1171;
x_1143 = x_1170;
x_1144 = x_1172;
x_1145 = x_29;
x_1146 = lean_box(0);
goto block_1149;
}
else
{
lean_object* x_1175; 
lean_dec(x_1169);
lean_dec(x_1165);
lean_dec(x_29);
x_1175 = lean_ctor_get(x_1174, 0);
lean_inc(x_1175);
lean_dec_ref(x_1174);
x_1117 = x_1162;
x_1118 = x_1163;
x_1119 = x_1167;
x_1120 = x_1170;
x_1121 = x_1171;
x_1122 = x_1172;
x_1123 = x_1175;
x_1124 = lean_box(0);
goto block_1126;
}
}
else
{
lean_dec_ref(x_1166);
lean_dec(x_29);
x_1150 = x_1162;
x_1151 = x_1163;
x_1152 = x_1165;
x_1153 = x_1167;
x_1154 = x_1169;
x_1155 = x_1170;
x_1156 = x_1171;
x_1157 = x_1172;
x_1158 = x_1164;
goto block_1161;
}
}
block_1194:
{
lean_object* x_1187; 
x_1187 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1187) == 0)
{
lean_object* x_1188; lean_object* x_1189; 
x_1188 = lean_ctor_get(x_1187, 0);
lean_inc(x_1188);
lean_dec_ref(x_1187);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_1189 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1184, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1189) == 0)
{
lean_dec(x_1188);
lean_dec(x_29);
x_1150 = x_1177;
x_1151 = x_1178;
x_1152 = x_1179;
x_1153 = x_1180;
x_1154 = x_1181;
x_1155 = x_1183;
x_1156 = x_1182;
x_1157 = x_1186;
x_1158 = x_1189;
goto block_1161;
}
else
{
lean_object* x_1190; uint8_t x_1191; 
x_1190 = lean_ctor_get(x_1189, 0);
lean_inc(x_1190);
x_1191 = l_Lean_Exception_isInterrupt(x_1190);
if (x_1191 == 0)
{
uint8_t x_1192; 
x_1192 = l_Lean_Exception_isRuntime(x_1190);
x_1162 = x_1177;
x_1163 = x_1178;
x_1164 = x_1189;
x_1165 = x_1179;
x_1166 = x_1188;
x_1167 = x_1180;
x_1168 = lean_box(0);
x_1169 = x_1181;
x_1170 = x_1183;
x_1171 = x_1182;
x_1172 = x_1186;
x_1173 = x_1192;
goto block_1176;
}
else
{
lean_dec(x_1190);
x_1162 = x_1177;
x_1163 = x_1178;
x_1164 = x_1189;
x_1165 = x_1179;
x_1166 = x_1188;
x_1167 = x_1180;
x_1168 = lean_box(0);
x_1169 = x_1181;
x_1170 = x_1183;
x_1171 = x_1182;
x_1172 = x_1186;
x_1173 = x_1191;
goto block_1176;
}
}
}
else
{
lean_object* x_1193; 
lean_dec(x_1184);
lean_dec(x_1181);
lean_dec(x_1179);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1193 = lean_ctor_get(x_1187, 0);
lean_inc(x_1193);
lean_dec_ref(x_1187);
x_1117 = x_1177;
x_1118 = x_1178;
x_1119 = x_1180;
x_1120 = x_1183;
x_1121 = x_1182;
x_1122 = x_1186;
x_1123 = x_1193;
x_1124 = lean_box(0);
goto block_1126;
}
}
block_1204:
{
if (lean_obj_tag(x_1201) == 0)
{
lean_object* x_1202; 
x_1202 = lean_ctor_get(x_1201, 0);
lean_inc(x_1202);
lean_dec_ref(x_1201);
x_1127 = x_1195;
x_1128 = x_1196;
x_1129 = x_1197;
x_1130 = x_1199;
x_1131 = x_1198;
x_1132 = x_1200;
x_1133 = x_1202;
x_1134 = lean_box(0);
goto block_1136;
}
else
{
lean_object* x_1203; 
x_1203 = lean_ctor_get(x_1201, 0);
lean_inc(x_1203);
lean_dec_ref(x_1201);
x_1117 = x_1195;
x_1118 = x_1196;
x_1119 = x_1197;
x_1120 = x_1199;
x_1121 = x_1198;
x_1122 = x_1200;
x_1123 = x_1203;
x_1124 = lean_box(0);
goto block_1126;
}
}
block_1214:
{
lean_object* x_1212; lean_object* x_1213; 
x_1212 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_1213 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1212, x_7, x_8, x_9, x_10);
x_1195 = x_1205;
x_1196 = x_1206;
x_1197 = x_1207;
x_1198 = x_1209;
x_1199 = x_1208;
x_1200 = x_1211;
x_1201 = x_1213;
goto block_1204;
}
block_1230:
{
uint8_t x_1226; 
x_1226 = l_List_isEmpty___redArg(x_1219);
lean_dec(x_1219);
if (x_1226 == 0)
{
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1205 = x_1215;
x_1206 = x_1216;
x_1207 = x_1218;
x_1208 = x_1222;
x_1209 = x_1221;
x_1210 = lean_box(0);
x_1211 = x_1225;
goto block_1214;
}
else
{
if (x_1224 == 0)
{
lean_object* x_1227; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1227 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1220, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1227) == 0)
{
lean_object* x_1228; lean_object* x_1229; 
x_1228 = lean_ctor_get(x_1227, 0);
lean_inc(x_1228);
lean_dec_ref(x_1227);
x_1229 = l_List_appendTR___redArg(x_1217, x_1228);
x_1127 = x_1215;
x_1128 = x_1216;
x_1129 = x_1218;
x_1130 = x_1222;
x_1131 = x_1221;
x_1132 = x_1225;
x_1133 = x_1229;
x_1134 = lean_box(0);
goto block_1136;
}
else
{
lean_dec(x_1217);
x_1195 = x_1215;
x_1196 = x_1216;
x_1197 = x_1218;
x_1198 = x_1221;
x_1199 = x_1222;
x_1200 = x_1225;
x_1201 = x_1227;
goto block_1204;
}
}
else
{
lean_dec(x_1220);
lean_dec(x_1217);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1205 = x_1215;
x_1206 = x_1216;
x_1207 = x_1218;
x_1208 = x_1222;
x_1209 = x_1221;
x_1210 = lean_box(0);
x_1211 = x_1225;
goto block_1214;
}
}
}
block_1245:
{
uint8_t x_1242; lean_object* x_1243; 
x_1242 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_1233);
x_1243 = l_List_appendTR___redArg(x_1240, x_1233);
if (x_1242 == 0)
{
x_1215 = x_1231;
x_1216 = x_1232;
x_1217 = x_1233;
x_1218 = x_1234;
x_1219 = x_1235;
x_1220 = x_1243;
x_1221 = x_1236;
x_1222 = x_1237;
x_1223 = lean_box(0);
x_1224 = x_1238;
x_1225 = x_1239;
goto block_1230;
}
else
{
uint8_t x_1244; 
x_1244 = l_List_isEmpty___redArg(x_1233);
if (x_1244 == 0)
{
x_1177 = x_1231;
x_1178 = x_1232;
x_1179 = x_1233;
x_1180 = x_1234;
x_1181 = x_1235;
x_1182 = x_1236;
x_1183 = x_1237;
x_1184 = x_1243;
x_1185 = lean_box(0);
x_1186 = x_1239;
goto block_1194;
}
else
{
if (x_1238 == 0)
{
x_1215 = x_1231;
x_1216 = x_1232;
x_1217 = x_1233;
x_1218 = x_1234;
x_1219 = x_1235;
x_1220 = x_1243;
x_1221 = x_1236;
x_1222 = x_1237;
x_1223 = lean_box(0);
x_1224 = x_1238;
x_1225 = x_1239;
goto block_1230;
}
else
{
x_1177 = x_1231;
x_1178 = x_1232;
x_1179 = x_1233;
x_1180 = x_1234;
x_1181 = x_1235;
x_1182 = x_1236;
x_1183 = x_1237;
x_1184 = x_1243;
x_1185 = lean_box(0);
x_1186 = x_1239;
goto block_1194;
}
}
}
}
block_1262:
{
lean_object* x_1254; double x_1255; double x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1254 = lean_io_get_num_heartbeats();
x_1255 = lean_float_of_nat(x_1247);
x_1256 = lean_float_of_nat(x_1254);
x_1257 = lean_box_float(x_1255);
x_1258 = lean_box_float(x_1256);
x_1259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1259, 0, x_1257);
lean_ctor_set(x_1259, 1, x_1258);
x_1260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1260, 0, x_1252);
lean_ctor_set(x_1260, 1, x_1259);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1261 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_124, x_591, x_121, x_1246, x_1251, x_1250, x_1260, x_7, x_8, x_9, x_10);
x_1091 = x_1248;
x_1092 = x_1249;
x_1093 = x_1261;
goto block_1096;
}
block_1272:
{
lean_object* x_1271; 
x_1271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1271, 0, x_1269);
x_1246 = x_1263;
x_1247 = x_1264;
x_1248 = x_1265;
x_1249 = x_1267;
x_1250 = x_1266;
x_1251 = x_1268;
x_1252 = x_1271;
x_1253 = lean_box(0);
goto block_1262;
}
block_1285:
{
lean_object* x_1283; lean_object* x_1284; 
x_1283 = l_List_appendTR___redArg(x_1274, x_1277);
x_1284 = l_List_appendTR___redArg(x_1283, x_1281);
x_1263 = x_1273;
x_1264 = x_1275;
x_1265 = x_1276;
x_1266 = x_1279;
x_1267 = x_1278;
x_1268 = x_1280;
x_1269 = x_1284;
x_1270 = lean_box(0);
goto block_1272;
}
block_1295:
{
lean_object* x_1294; 
x_1294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1294, 0, x_1292);
x_1246 = x_1286;
x_1247 = x_1287;
x_1248 = x_1288;
x_1249 = x_1290;
x_1250 = x_1289;
x_1251 = x_1291;
x_1252 = x_1294;
x_1253 = lean_box(0);
goto block_1262;
}
block_1305:
{
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; 
x_1303 = lean_ctor_get(x_1302, 0);
lean_inc(x_1303);
lean_dec_ref(x_1302);
x_1263 = x_1296;
x_1264 = x_1297;
x_1265 = x_1298;
x_1266 = x_1300;
x_1267 = x_1299;
x_1268 = x_1301;
x_1269 = x_1303;
x_1270 = lean_box(0);
goto block_1272;
}
else
{
lean_object* x_1304; 
x_1304 = lean_ctor_get(x_1302, 0);
lean_inc(x_1304);
lean_dec_ref(x_1302);
x_1286 = x_1296;
x_1287 = x_1297;
x_1288 = x_1298;
x_1289 = x_1300;
x_1290 = x_1299;
x_1291 = x_1301;
x_1292 = x_1304;
x_1293 = lean_box(0);
goto block_1295;
}
}
block_1318:
{
lean_object* x_1315; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1315 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1306, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1316; lean_object* x_1317; 
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
lean_dec_ref(x_1315);
x_1317 = l_List_appendTR___redArg(x_1308, x_1316);
x_1263 = x_1307;
x_1264 = x_1309;
x_1265 = x_1310;
x_1266 = x_1312;
x_1267 = x_1311;
x_1268 = x_1314;
x_1269 = x_1317;
x_1270 = lean_box(0);
goto block_1272;
}
else
{
lean_dec(x_1308);
x_1296 = x_1307;
x_1297 = x_1309;
x_1298 = x_1310;
x_1299 = x_1311;
x_1300 = x_1312;
x_1301 = x_1314;
x_1302 = x_1315;
goto block_1305;
}
}
block_1330:
{
if (lean_obj_tag(x_1327) == 0)
{
lean_object* x_1328; 
x_1328 = lean_ctor_get(x_1327, 0);
lean_inc(x_1328);
lean_dec_ref(x_1327);
x_1273 = x_1319;
x_1274 = x_1320;
x_1275 = x_1321;
x_1276 = x_1322;
x_1277 = x_1323;
x_1278 = x_1325;
x_1279 = x_1324;
x_1280 = x_1326;
x_1281 = x_1328;
x_1282 = lean_box(0);
goto block_1285;
}
else
{
lean_object* x_1329; 
lean_dec(x_1323);
lean_dec(x_1320);
x_1329 = lean_ctor_get(x_1327, 0);
lean_inc(x_1329);
lean_dec_ref(x_1327);
x_1286 = x_1319;
x_1287 = x_1321;
x_1288 = x_1322;
x_1289 = x_1324;
x_1290 = x_1325;
x_1291 = x_1326;
x_1292 = x_1329;
x_1293 = lean_box(0);
goto block_1295;
}
}
block_1345:
{
if (x_1342 == 0)
{
lean_object* x_1343; 
lean_dec_ref(x_1333);
x_1343 = l_Lean_Meta_SavedState_restore___redArg(x_1341, x_8, x_10);
lean_dec_ref(x_1341);
if (lean_obj_tag(x_1343) == 0)
{
lean_dec_ref(x_1343);
x_1273 = x_1332;
x_1274 = x_1334;
x_1275 = x_1335;
x_1276 = x_1336;
x_1277 = x_1337;
x_1278 = x_1339;
x_1279 = x_1338;
x_1280 = x_1340;
x_1281 = x_29;
x_1282 = lean_box(0);
goto block_1285;
}
else
{
lean_object* x_1344; 
lean_dec(x_1337);
lean_dec(x_1334);
lean_dec(x_29);
x_1344 = lean_ctor_get(x_1343, 0);
lean_inc(x_1344);
lean_dec_ref(x_1343);
x_1286 = x_1332;
x_1287 = x_1335;
x_1288 = x_1336;
x_1289 = x_1338;
x_1290 = x_1339;
x_1291 = x_1340;
x_1292 = x_1344;
x_1293 = lean_box(0);
goto block_1295;
}
}
else
{
lean_dec_ref(x_1341);
lean_dec(x_29);
x_1319 = x_1332;
x_1320 = x_1334;
x_1321 = x_1335;
x_1322 = x_1336;
x_1323 = x_1337;
x_1324 = x_1338;
x_1325 = x_1339;
x_1326 = x_1340;
x_1327 = x_1333;
goto block_1330;
}
}
block_1363:
{
lean_object* x_1356; 
x_1356 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1356) == 0)
{
lean_object* x_1357; lean_object* x_1358; 
x_1357 = lean_ctor_get(x_1356, 0);
lean_inc(x_1357);
lean_dec_ref(x_1356);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_1358 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1346, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1358) == 0)
{
lean_dec(x_1357);
lean_dec(x_29);
x_1319 = x_1347;
x_1320 = x_1348;
x_1321 = x_1349;
x_1322 = x_1350;
x_1323 = x_1351;
x_1324 = x_1353;
x_1325 = x_1352;
x_1326 = x_1355;
x_1327 = x_1358;
goto block_1330;
}
else
{
lean_object* x_1359; uint8_t x_1360; 
x_1359 = lean_ctor_get(x_1358, 0);
lean_inc(x_1359);
x_1360 = l_Lean_Exception_isInterrupt(x_1359);
if (x_1360 == 0)
{
uint8_t x_1361; 
x_1361 = l_Lean_Exception_isRuntime(x_1359);
x_1331 = lean_box(0);
x_1332 = x_1347;
x_1333 = x_1358;
x_1334 = x_1348;
x_1335 = x_1349;
x_1336 = x_1350;
x_1337 = x_1351;
x_1338 = x_1353;
x_1339 = x_1352;
x_1340 = x_1355;
x_1341 = x_1357;
x_1342 = x_1361;
goto block_1345;
}
else
{
lean_dec(x_1359);
x_1331 = lean_box(0);
x_1332 = x_1347;
x_1333 = x_1358;
x_1334 = x_1348;
x_1335 = x_1349;
x_1336 = x_1350;
x_1337 = x_1351;
x_1338 = x_1353;
x_1339 = x_1352;
x_1340 = x_1355;
x_1341 = x_1357;
x_1342 = x_1360;
goto block_1345;
}
}
}
else
{
lean_object* x_1362; 
lean_dec(x_1351);
lean_dec(x_1348);
lean_dec(x_1346);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1362 = lean_ctor_get(x_1356, 0);
lean_inc(x_1362);
lean_dec_ref(x_1356);
x_1286 = x_1347;
x_1287 = x_1349;
x_1288 = x_1350;
x_1289 = x_1353;
x_1290 = x_1352;
x_1291 = x_1355;
x_1292 = x_1362;
x_1293 = lean_box(0);
goto block_1295;
}
}
block_1380:
{
uint8_t x_1375; lean_object* x_1376; 
x_1375 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_1365);
x_1376 = l_List_appendTR___redArg(x_1373, x_1365);
if (x_1375 == 0)
{
lean_dec(x_1368);
if (x_1371 == 0)
{
x_1306 = x_1376;
x_1307 = x_1364;
x_1308 = x_1365;
x_1309 = x_1366;
x_1310 = x_1367;
x_1311 = x_1370;
x_1312 = x_1369;
x_1313 = lean_box(0);
x_1314 = x_1372;
goto block_1318;
}
else
{
lean_object* x_1377; lean_object* x_1378; 
lean_dec(x_1376);
lean_dec(x_1365);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1377 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_1378 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1377, x_7, x_8, x_9, x_10);
x_1296 = x_1364;
x_1297 = x_1366;
x_1298 = x_1367;
x_1299 = x_1370;
x_1300 = x_1369;
x_1301 = x_1372;
x_1302 = x_1378;
goto block_1305;
}
}
else
{
uint8_t x_1379; 
x_1379 = l_List_isEmpty___redArg(x_1365);
if (x_1379 == 0)
{
x_1346 = x_1376;
x_1347 = x_1364;
x_1348 = x_1365;
x_1349 = x_1366;
x_1350 = x_1367;
x_1351 = x_1368;
x_1352 = x_1370;
x_1353 = x_1369;
x_1354 = lean_box(0);
x_1355 = x_1372;
goto block_1363;
}
else
{
if (x_1371 == 0)
{
lean_dec(x_1368);
x_1306 = x_1376;
x_1307 = x_1364;
x_1308 = x_1365;
x_1309 = x_1366;
x_1310 = x_1367;
x_1311 = x_1370;
x_1312 = x_1369;
x_1313 = lean_box(0);
x_1314 = x_1372;
goto block_1318;
}
else
{
x_1346 = x_1376;
x_1347 = x_1364;
x_1348 = x_1365;
x_1349 = x_1366;
x_1350 = x_1367;
x_1351 = x_1368;
x_1352 = x_1370;
x_1353 = x_1369;
x_1354 = lean_box(0);
x_1355 = x_1372;
goto block_1363;
}
}
}
}
block_1406:
{
lean_object* x_1390; 
x_1390 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_1390) == 0)
{
if (x_1389 == 0)
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
x_1391 = lean_ctor_get(x_1390, 0);
lean_inc(x_1391);
lean_dec_ref(x_1390);
x_1392 = lean_io_mono_nanos_now();
x_1393 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_122, x_1389, x_5, x_1384, x_8);
if (lean_obj_tag(x_1393) == 0)
{
lean_object* x_1394; lean_object* x_1395; 
x_1394 = lean_ctor_get(x_1393, 0);
lean_inc(x_1394);
lean_dec_ref(x_1393);
x_1395 = l_List_reverse___redArg(x_1394);
x_1231 = x_1392;
x_1232 = x_1381;
x_1233 = x_1382;
x_1234 = x_1385;
x_1235 = x_1386;
x_1236 = x_1388;
x_1237 = x_1387;
x_1238 = x_1389;
x_1239 = x_1391;
x_1240 = x_1395;
x_1241 = lean_box(0);
goto block_1245;
}
else
{
if (lean_obj_tag(x_1393) == 0)
{
lean_object* x_1396; 
x_1396 = lean_ctor_get(x_1393, 0);
lean_inc(x_1396);
lean_dec_ref(x_1393);
x_1231 = x_1392;
x_1232 = x_1381;
x_1233 = x_1382;
x_1234 = x_1385;
x_1235 = x_1386;
x_1236 = x_1388;
x_1237 = x_1387;
x_1238 = x_1389;
x_1239 = x_1391;
x_1240 = x_1396;
x_1241 = lean_box(0);
goto block_1245;
}
else
{
lean_object* x_1397; 
lean_dec(x_1386);
lean_dec(x_1382);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1397 = lean_ctor_get(x_1393, 0);
lean_inc(x_1397);
lean_dec_ref(x_1393);
x_1117 = x_1392;
x_1118 = x_1381;
x_1119 = x_1385;
x_1120 = x_1387;
x_1121 = x_1388;
x_1122 = x_1391;
x_1123 = x_1397;
x_1124 = lean_box(0);
goto block_1126;
}
}
}
else
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
x_1398 = lean_ctor_get(x_1390, 0);
lean_inc(x_1398);
lean_dec_ref(x_1390);
x_1399 = lean_io_get_num_heartbeats();
x_1400 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_122, x_1389, x_5, x_1384, x_8);
if (lean_obj_tag(x_1400) == 0)
{
lean_object* x_1401; lean_object* x_1402; 
x_1401 = lean_ctor_get(x_1400, 0);
lean_inc(x_1401);
lean_dec_ref(x_1400);
x_1402 = l_List_reverse___redArg(x_1401);
x_1364 = x_1381;
x_1365 = x_1382;
x_1366 = x_1399;
x_1367 = x_1385;
x_1368 = x_1386;
x_1369 = x_1387;
x_1370 = x_1388;
x_1371 = x_1389;
x_1372 = x_1398;
x_1373 = x_1402;
x_1374 = lean_box(0);
goto block_1380;
}
else
{
if (lean_obj_tag(x_1400) == 0)
{
lean_object* x_1403; 
x_1403 = lean_ctor_get(x_1400, 0);
lean_inc(x_1403);
lean_dec_ref(x_1400);
x_1364 = x_1381;
x_1365 = x_1382;
x_1366 = x_1399;
x_1367 = x_1385;
x_1368 = x_1386;
x_1369 = x_1387;
x_1370 = x_1388;
x_1371 = x_1389;
x_1372 = x_1398;
x_1373 = x_1403;
x_1374 = lean_box(0);
goto block_1380;
}
else
{
lean_object* x_1404; 
lean_dec(x_1386);
lean_dec(x_1382);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1404 = lean_ctor_get(x_1400, 0);
lean_inc(x_1404);
lean_dec_ref(x_1400);
x_1286 = x_1381;
x_1287 = x_1399;
x_1288 = x_1385;
x_1289 = x_1387;
x_1290 = x_1388;
x_1291 = x_1398;
x_1292 = x_1404;
x_1293 = lean_box(0);
goto block_1295;
}
}
}
}
else
{
lean_object* x_1405; 
lean_dec_ref(x_1387);
lean_dec(x_1386);
lean_dec(x_1384);
lean_dec(x_1382);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1405 = lean_ctor_get(x_1390, 0);
lean_inc(x_1405);
lean_dec_ref(x_1390);
x_1052 = x_1385;
x_1053 = x_1388;
x_1054 = x_1405;
x_1055 = lean_box(0);
goto block_1057;
}
}
block_1412:
{
lean_object* x_1410; lean_object* x_1411; 
x_1410 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_1411 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1410, x_7, x_8, x_9, x_10);
x_1091 = x_1408;
x_1092 = x_1409;
x_1093 = x_1411;
goto block_1096;
}
block_1424:
{
uint8_t x_1420; 
x_1420 = l_List_isEmpty___redArg(x_1417);
lean_dec(x_1417);
if (x_1420 == 0)
{
lean_dec(x_1415);
lean_dec(x_1414);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1407 = lean_box(0);
x_1408 = x_1416;
x_1409 = x_1418;
goto block_1412;
}
else
{
if (x_1419 == 0)
{
lean_object* x_1421; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1421 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1415, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1421) == 0)
{
lean_object* x_1422; lean_object* x_1423; 
x_1422 = lean_ctor_get(x_1421, 0);
lean_inc(x_1422);
lean_dec_ref(x_1421);
x_1423 = l_List_appendTR___redArg(x_1414, x_1422);
x_1037 = x_1416;
x_1038 = x_1418;
x_1039 = x_1423;
x_1040 = lean_box(0);
goto block_1042;
}
else
{
lean_dec(x_1414);
x_1091 = x_1416;
x_1092 = x_1418;
x_1093 = x_1421;
goto block_1096;
}
}
else
{
lean_dec(x_1415);
lean_dec(x_1414);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1407 = lean_box(0);
x_1408 = x_1416;
x_1409 = x_1418;
goto block_1412;
}
}
}
block_1435:
{
uint8_t x_1432; lean_object* x_1433; 
x_1432 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_1425);
x_1433 = l_List_appendTR___redArg(x_1430, x_1425);
if (x_1432 == 0)
{
x_1413 = lean_box(0);
x_1414 = x_1425;
x_1415 = x_1433;
x_1416 = x_1426;
x_1417 = x_1427;
x_1418 = x_1428;
x_1419 = x_1429;
goto block_1424;
}
else
{
uint8_t x_1434; 
x_1434 = l_List_isEmpty___redArg(x_1425);
if (x_1434 == 0)
{
x_1077 = lean_box(0);
x_1078 = x_1425;
x_1079 = x_1433;
x_1080 = x_1426;
x_1081 = x_1427;
x_1082 = x_1428;
goto block_1090;
}
else
{
if (x_1429 == 0)
{
x_1413 = lean_box(0);
x_1414 = x_1425;
x_1415 = x_1433;
x_1416 = x_1426;
x_1417 = x_1427;
x_1418 = x_1428;
x_1419 = x_1429;
goto block_1424;
}
else
{
x_1077 = lean_box(0);
x_1078 = x_1425;
x_1079 = x_1433;
x_1080 = x_1426;
x_1081 = x_1427;
x_1082 = x_1428;
goto block_1090;
}
}
}
}
block_1490:
{
lean_object* x_1436; 
x_1436 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_1436) == 0)
{
lean_object* x_1437; lean_object* x_1438; uint8_t x_1439; 
x_1437 = lean_ctor_get(x_1436, 0);
lean_inc(x_1437);
lean_dec_ref(x_1436);
x_1438 = l_Lean_trace_profiler_useHeartbeats;
x_1439 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_121, x_1438);
if (x_1439 == 0)
{
lean_object* x_1440; lean_object* x_1441; 
x_1440 = lean_io_mono_nanos_now();
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_1441 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_28, x_123, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1441) == 0)
{
lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; 
x_1442 = lean_ctor_get(x_1441, 0);
lean_inc(x_1442);
lean_dec_ref(x_1441);
x_1443 = lean_ctor_get(x_1442, 0);
lean_inc(x_1443);
x_1444 = lean_ctor_get(x_1442, 1);
lean_inc(x_1444);
lean_dec(x_1442);
lean_inc(x_2);
x_1445 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_1445) == 0)
{
lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; uint8_t x_1450; 
x_1446 = lean_ctor_get(x_1445, 0);
lean_inc(x_1446);
lean_dec_ref(x_1445);
x_1447 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_1444, x_25);
lean_inc(x_1447);
lean_inc(x_1443);
x_1448 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(x_1448, 0, x_1443);
lean_closure_set(x_1448, 1, x_1447);
x_1449 = lean_box(0);
x_1450 = lean_unbox(x_1446);
if (x_1450 == 0)
{
lean_object* x_1451; uint8_t x_1452; 
x_1451 = l_Lean_trace_profiler;
x_1452 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_121, x_1451);
if (x_1452 == 0)
{
lean_object* x_1453; 
lean_dec_ref(x_1448);
lean_dec(x_1446);
x_1453 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_122, x_1439, x_5, x_1449, x_8);
if (lean_obj_tag(x_1453) == 0)
{
lean_object* x_1454; lean_object* x_1455; 
x_1454 = lean_ctor_get(x_1453, 0);
lean_inc(x_1454);
lean_dec_ref(x_1453);
x_1455 = l_List_reverse___redArg(x_1454);
x_1425 = x_1447;
x_1426 = x_1440;
x_1427 = x_1443;
x_1428 = x_1437;
x_1429 = x_1439;
x_1430 = x_1455;
x_1431 = lean_box(0);
goto block_1435;
}
else
{
if (lean_obj_tag(x_1453) == 0)
{
lean_object* x_1456; 
x_1456 = lean_ctor_get(x_1453, 0);
lean_inc(x_1456);
lean_dec_ref(x_1453);
x_1425 = x_1447;
x_1426 = x_1440;
x_1427 = x_1443;
x_1428 = x_1437;
x_1429 = x_1439;
x_1430 = x_1456;
x_1431 = lean_box(0);
goto block_1435;
}
else
{
lean_dec(x_1447);
lean_dec(x_1443);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1091 = x_1440;
x_1092 = x_1437;
x_1093 = x_1453;
goto block_1096;
}
}
}
else
{
uint8_t x_1457; 
x_1457 = lean_unbox(x_1446);
lean_dec(x_1446);
x_1381 = x_1457;
x_1382 = x_1447;
x_1383 = lean_box(0);
x_1384 = x_1449;
x_1385 = x_1440;
x_1386 = x_1443;
x_1387 = x_1448;
x_1388 = x_1437;
x_1389 = x_1439;
goto block_1406;
}
}
else
{
uint8_t x_1458; 
x_1458 = lean_unbox(x_1446);
lean_dec(x_1446);
x_1381 = x_1458;
x_1382 = x_1447;
x_1383 = lean_box(0);
x_1384 = x_1449;
x_1385 = x_1440;
x_1386 = x_1443;
x_1387 = x_1448;
x_1388 = x_1437;
x_1389 = x_1439;
goto block_1406;
}
}
else
{
lean_object* x_1459; 
lean_dec(x_1444);
lean_dec(x_1443);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1459 = lean_ctor_get(x_1445, 0);
lean_inc(x_1459);
lean_dec_ref(x_1445);
x_1052 = x_1440;
x_1053 = x_1437;
x_1054 = x_1459;
x_1055 = lean_box(0);
goto block_1057;
}
}
else
{
lean_object* x_1460; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1460 = lean_ctor_get(x_1441, 0);
lean_inc(x_1460);
lean_dec_ref(x_1441);
x_1052 = x_1440;
x_1053 = x_1437;
x_1054 = x_1460;
x_1055 = lean_box(0);
goto block_1057;
}
}
else
{
lean_object* x_1461; lean_object* x_1462; 
x_1461 = lean_io_get_num_heartbeats();
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_1462 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_28, x_123, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1462) == 0)
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; 
x_1463 = lean_ctor_get(x_1462, 0);
lean_inc(x_1463);
lean_dec_ref(x_1462);
x_1464 = lean_ctor_get(x_1463, 0);
lean_inc(x_1464);
x_1465 = lean_ctor_get(x_1463, 1);
lean_inc(x_1465);
lean_dec(x_1463);
lean_inc(x_2);
x_1466 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_1466) == 0)
{
lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; uint8_t x_1471; 
x_1467 = lean_ctor_get(x_1466, 0);
lean_inc(x_1467);
lean_dec_ref(x_1466);
x_1468 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_1465, x_25);
lean_inc(x_1468);
lean_inc(x_1464);
x_1469 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(x_1469, 0, x_1464);
lean_closure_set(x_1469, 1, x_1468);
x_1470 = lean_box(0);
x_1471 = lean_unbox(x_1467);
if (x_1471 == 0)
{
lean_object* x_1472; uint8_t x_1473; 
x_1472 = l_Lean_trace_profiler;
x_1473 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_121, x_1472);
if (x_1473 == 0)
{
lean_object* x_1474; 
lean_dec_ref(x_1469);
lean_dec(x_1467);
x_1474 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_1439, x_95, x_5, x_1470, x_8);
if (lean_obj_tag(x_1474) == 0)
{
lean_object* x_1475; lean_object* x_1476; 
x_1475 = lean_ctor_get(x_1474, 0);
lean_inc(x_1475);
lean_dec_ref(x_1474);
x_1476 = l_List_reverse___redArg(x_1475);
x_1009 = x_1468;
x_1010 = x_1461;
x_1011 = x_1464;
x_1012 = x_1437;
x_1013 = x_1439;
x_1014 = x_1476;
x_1015 = lean_box(0);
goto block_1019;
}
else
{
if (lean_obj_tag(x_1474) == 0)
{
lean_object* x_1477; 
x_1477 = lean_ctor_get(x_1474, 0);
lean_inc(x_1477);
lean_dec_ref(x_1474);
x_1009 = x_1468;
x_1010 = x_1461;
x_1011 = x_1464;
x_1012 = x_1437;
x_1013 = x_1439;
x_1014 = x_1477;
x_1015 = lean_box(0);
goto block_1019;
}
else
{
lean_dec(x_1468);
lean_dec(x_1464);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_618 = x_1461;
x_619 = x_1437;
x_620 = x_1474;
goto block_623;
}
}
}
else
{
uint8_t x_1478; 
x_1478 = lean_unbox(x_1467);
lean_dec(x_1467);
x_921 = x_1469;
x_922 = x_1468;
x_923 = x_1461;
x_924 = lean_box(0);
x_925 = x_1470;
x_926 = x_1464;
x_927 = x_1437;
x_928 = x_1478;
x_929 = x_1439;
goto block_946;
}
}
else
{
uint8_t x_1479; 
x_1479 = lean_unbox(x_1467);
lean_dec(x_1467);
x_921 = x_1469;
x_922 = x_1468;
x_923 = x_1461;
x_924 = lean_box(0);
x_925 = x_1470;
x_926 = x_1464;
x_927 = x_1437;
x_928 = x_1479;
x_929 = x_1439;
goto block_946;
}
}
else
{
lean_object* x_1480; 
lean_dec(x_1465);
lean_dec(x_1464);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1480 = lean_ctor_get(x_1466, 0);
lean_inc(x_1480);
lean_dec_ref(x_1466);
x_606 = x_1461;
x_607 = x_1437;
x_608 = x_1480;
x_609 = lean_box(0);
goto block_611;
}
}
else
{
lean_object* x_1481; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1481 = lean_ctor_get(x_1462, 0);
lean_inc(x_1481);
lean_dec_ref(x_1462);
x_606 = x_1461;
x_607 = x_1437;
x_608 = x_1481;
x_609 = lean_box(0);
goto block_611;
}
}
}
else
{
lean_object* x_1482; lean_object* x_1483; uint8_t x_1484; uint8_t x_1489; 
lean_dec_ref(x_590);
lean_dec(x_589);
lean_dec_ref(x_123);
lean_dec_ref(x_121);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1482 = lean_ctor_get(x_1436, 0);
x_1489 = !lean_is_exclusive(x_1436);
if (x_1489 == 0)
{
x_1483 = x_1436;
x_1484 = x_1489;
goto block_1488;
}
else
{
lean_inc(x_1482);
lean_dec(x_1436);
x_1483 = lean_box(0);
x_1484 = x_1489;
goto block_1488;
}
block_1488:
{
lean_object* x_1485; 
if (x_1484 == 0)
{
x_1485 = x_1483;
goto block_1486;
}
else
{
lean_object* x_1487; 
x_1487 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1487, 0, x_1482);
x_1485 = x_1487;
goto block_1486;
}
block_1486:
{
return x_1485;
}
}
}
}
}
else
{
lean_object* x_1494; lean_object* x_1495; uint8_t x_1496; uint8_t x_1501; 
lean_dec_ref(x_123);
lean_del_object(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1494 = lean_ctor_get(x_588, 0);
x_1501 = !lean_is_exclusive(x_588);
if (x_1501 == 0)
{
x_1495 = x_588;
x_1496 = x_1501;
goto block_1500;
}
else
{
lean_inc(x_1494);
lean_dec(x_588);
x_1495 = lean_box(0);
x_1496 = x_1501;
goto block_1500;
}
block_1500:
{
lean_object* x_1497; 
if (x_1496 == 0)
{
x_1497 = x_1495;
goto block_1498;
}
else
{
lean_object* x_1499; 
x_1499 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1499, 0, x_1494);
x_1497 = x_1499;
goto block_1498;
}
block_1498:
{
return x_1497;
}
}
}
}
block_147:
{
lean_object* x_137; double x_138; double x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_io_get_num_heartbeats();
x_138 = lean_float_of_nat(x_128);
x_139 = lean_float_of_nat(x_137);
x_140 = lean_box_float(x_138);
x_141 = lean_box_float(x_139);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_141);
lean_ctor_set(x_30, 0, x_140);
x_142 = x_30;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_141);
x_142 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_135);
lean_ctor_set(x_143, 1, x_142);
x_144 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_124, x_125, x_126, x_133, x_129, x_131, x_143, x_134, x_130, x_132, x_127);
lean_dec_ref(x_126);
return x_144;
}
}
block_161:
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_158);
x_125 = x_148;
x_126 = x_149;
x_127 = x_151;
x_128 = x_150;
x_129 = x_152;
x_130 = x_153;
x_131 = x_154;
x_132 = x_156;
x_133 = x_155;
x_134 = x_157;
x_135 = x_160;
x_136 = lean_box(0);
goto block_147;
}
block_178:
{
lean_object* x_176; lean_object* x_177; 
x_176 = l_List_appendTR___redArg(x_163, x_162);
x_177 = l_List_appendTR___redArg(x_176, x_174);
x_148 = x_164;
x_149 = x_165;
x_150 = x_167;
x_151 = x_166;
x_152 = x_168;
x_153 = x_169;
x_154 = x_170;
x_155 = x_172;
x_156 = x_171;
x_157 = x_173;
x_158 = x_177;
x_159 = lean_box(0);
goto block_161;
}
block_192:
{
lean_object* x_191; 
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_189);
x_125 = x_179;
x_126 = x_180;
x_127 = x_182;
x_128 = x_181;
x_129 = x_183;
x_130 = x_184;
x_131 = x_185;
x_132 = x_187;
x_133 = x_186;
x_134 = x_188;
x_135 = x_191;
x_136 = lean_box(0);
goto block_147;
}
block_206:
{
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
x_148 = x_193;
x_149 = x_194;
x_150 = x_196;
x_151 = x_195;
x_152 = x_197;
x_153 = x_198;
x_154 = x_199;
x_155 = x_201;
x_156 = x_200;
x_157 = x_202;
x_158 = x_204;
x_159 = lean_box(0);
goto block_161;
}
else
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
lean_dec_ref(x_203);
x_179 = x_193;
x_180 = x_194;
x_181 = x_196;
x_182 = x_195;
x_183 = x_197;
x_184 = x_198;
x_185 = x_199;
x_186 = x_201;
x_187 = x_200;
x_188 = x_202;
x_189 = x_205;
x_190 = lean_box(0);
goto block_192;
}
}
block_223:
{
lean_object* x_220; 
lean_inc(x_211);
lean_inc_ref(x_217);
lean_inc(x_215);
lean_inc_ref(x_212);
lean_inc(x_2);
x_220 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_210, x_29, x_212, x_215, x_217, x_211);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = l_List_appendTR___redArg(x_207, x_221);
x_148 = x_208;
x_149 = x_209;
x_150 = x_213;
x_151 = x_211;
x_152 = x_214;
x_153 = x_215;
x_154 = x_216;
x_155 = x_218;
x_156 = x_217;
x_157 = x_212;
x_158 = x_222;
x_159 = lean_box(0);
goto block_161;
}
else
{
lean_dec(x_207);
x_193 = x_208;
x_194 = x_209;
x_195 = x_211;
x_196 = x_213;
x_197 = x_214;
x_198 = x_215;
x_199 = x_216;
x_200 = x_217;
x_201 = x_218;
x_202 = x_212;
x_203 = x_220;
goto block_206;
}
}
block_242:
{
uint8_t x_239; 
x_239 = l_List_isEmpty___redArg(x_224);
lean_dec(x_224);
if (x_239 == 0)
{
if (x_231 == 0)
{
x_207 = x_225;
x_208 = x_226;
x_209 = x_227;
x_210 = x_228;
x_211 = x_229;
x_212 = x_230;
x_213 = x_232;
x_214 = x_233;
x_215 = x_234;
x_216 = x_235;
x_217 = x_237;
x_218 = x_236;
x_219 = lean_box(0);
goto block_223;
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_240 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_241 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_240, x_230, x_234, x_237, x_229);
x_193 = x_226;
x_194 = x_227;
x_195 = x_229;
x_196 = x_232;
x_197 = x_233;
x_198 = x_234;
x_199 = x_235;
x_200 = x_237;
x_201 = x_236;
x_202 = x_230;
x_203 = x_241;
goto block_206;
}
}
else
{
x_207 = x_225;
x_208 = x_226;
x_209 = x_227;
x_210 = x_228;
x_211 = x_229;
x_212 = x_230;
x_213 = x_232;
x_214 = x_233;
x_215 = x_234;
x_216 = x_235;
x_217 = x_237;
x_218 = x_236;
x_219 = lean_box(0);
goto block_223;
}
}
block_258:
{
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
x_162 = x_244;
x_163 = x_243;
x_164 = x_245;
x_165 = x_246;
x_166 = x_248;
x_167 = x_247;
x_168 = x_249;
x_169 = x_250;
x_170 = x_251;
x_171 = x_253;
x_172 = x_252;
x_173 = x_254;
x_174 = x_256;
x_175 = lean_box(0);
goto block_178;
}
else
{
lean_object* x_257; 
lean_dec(x_244);
lean_dec(x_243);
x_257 = lean_ctor_get(x_255, 0);
lean_inc(x_257);
lean_dec_ref(x_255);
x_179 = x_245;
x_180 = x_246;
x_181 = x_247;
x_182 = x_248;
x_183 = x_249;
x_184 = x_250;
x_185 = x_251;
x_186 = x_252;
x_187 = x_253;
x_188 = x_254;
x_189 = x_257;
x_190 = lean_box(0);
goto block_192;
}
}
block_277:
{
if (x_274 == 0)
{
lean_object* x_275; 
lean_dec_ref(x_261);
x_275 = l_Lean_Meta_SavedState_restore___redArg(x_265, x_270, x_264);
lean_dec_ref(x_265);
if (lean_obj_tag(x_275) == 0)
{
lean_dec_ref(x_275);
x_162 = x_259;
x_163 = x_260;
x_164 = x_262;
x_165 = x_263;
x_166 = x_264;
x_167 = x_268;
x_168 = x_269;
x_169 = x_270;
x_170 = x_271;
x_171 = x_272;
x_172 = x_273;
x_173 = x_266;
x_174 = x_29;
x_175 = lean_box(0);
goto block_178;
}
else
{
lean_object* x_276; 
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_29);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec_ref(x_275);
x_179 = x_262;
x_180 = x_263;
x_181 = x_268;
x_182 = x_264;
x_183 = x_269;
x_184 = x_270;
x_185 = x_271;
x_186 = x_273;
x_187 = x_272;
x_188 = x_266;
x_189 = x_276;
x_190 = lean_box(0);
goto block_192;
}
}
else
{
lean_dec_ref(x_265);
lean_dec(x_29);
x_243 = x_260;
x_244 = x_259;
x_245 = x_262;
x_246 = x_263;
x_247 = x_268;
x_248 = x_264;
x_249 = x_269;
x_250 = x_270;
x_251 = x_271;
x_252 = x_273;
x_253 = x_272;
x_254 = x_266;
x_255 = x_261;
goto block_258;
}
}
block_299:
{
lean_object* x_292; 
x_292 = l_Lean_Meta_saveState___redArg(x_287, x_282);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec_ref(x_292);
lean_inc(x_282);
lean_inc_ref(x_290);
lean_inc(x_287);
lean_inc_ref(x_284);
lean_inc(x_29);
lean_inc(x_2);
x_294 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_283, x_29, x_284, x_287, x_290, x_282);
if (lean_obj_tag(x_294) == 0)
{
lean_dec(x_293);
lean_dec(x_29);
x_243 = x_278;
x_244 = x_279;
x_245 = x_280;
x_246 = x_281;
x_247 = x_285;
x_248 = x_282;
x_249 = x_286;
x_250 = x_287;
x_251 = x_288;
x_252 = x_289;
x_253 = x_290;
x_254 = x_284;
x_255 = x_294;
goto block_258;
}
else
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = l_Lean_Exception_isInterrupt(x_295);
if (x_296 == 0)
{
uint8_t x_297; 
x_297 = l_Lean_Exception_isRuntime(x_295);
x_259 = x_279;
x_260 = x_278;
x_261 = x_294;
x_262 = x_280;
x_263 = x_281;
x_264 = x_282;
x_265 = x_293;
x_266 = x_284;
x_267 = lean_box(0);
x_268 = x_285;
x_269 = x_286;
x_270 = x_287;
x_271 = x_288;
x_272 = x_290;
x_273 = x_289;
x_274 = x_297;
goto block_277;
}
else
{
lean_dec(x_295);
x_259 = x_279;
x_260 = x_278;
x_261 = x_294;
x_262 = x_280;
x_263 = x_281;
x_264 = x_282;
x_265 = x_293;
x_266 = x_284;
x_267 = lean_box(0);
x_268 = x_285;
x_269 = x_286;
x_270 = x_287;
x_271 = x_288;
x_272 = x_290;
x_273 = x_289;
x_274 = x_296;
goto block_277;
}
}
}
else
{
lean_object* x_298; 
lean_dec(x_283);
lean_dec(x_279);
lean_dec(x_278);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_298 = lean_ctor_get(x_292, 0);
lean_inc(x_298);
lean_dec_ref(x_292);
x_179 = x_280;
x_180 = x_281;
x_181 = x_285;
x_182 = x_282;
x_183 = x_286;
x_184 = x_287;
x_185 = x_288;
x_186 = x_289;
x_187 = x_290;
x_188 = x_284;
x_189 = x_298;
x_190 = lean_box(0);
goto block_192;
}
}
block_318:
{
uint8_t x_315; lean_object* x_316; 
x_315 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_300);
x_316 = l_List_appendTR___redArg(x_313, x_300);
if (x_315 == 0)
{
x_224 = x_301;
x_225 = x_300;
x_226 = x_302;
x_227 = x_303;
x_228 = x_316;
x_229 = x_304;
x_230 = x_305;
x_231 = x_306;
x_232 = x_307;
x_233 = x_308;
x_234 = x_309;
x_235 = x_310;
x_236 = x_311;
x_237 = x_312;
x_238 = lean_box(0);
goto block_242;
}
else
{
uint8_t x_317; 
x_317 = l_List_isEmpty___redArg(x_300);
if (x_317 == 0)
{
x_278 = x_300;
x_279 = x_301;
x_280 = x_302;
x_281 = x_303;
x_282 = x_304;
x_283 = x_316;
x_284 = x_305;
x_285 = x_307;
x_286 = x_308;
x_287 = x_309;
x_288 = x_310;
x_289 = x_311;
x_290 = x_312;
x_291 = lean_box(0);
goto block_299;
}
else
{
if (x_95 == 0)
{
x_224 = x_301;
x_225 = x_300;
x_226 = x_302;
x_227 = x_303;
x_228 = x_316;
x_229 = x_304;
x_230 = x_305;
x_231 = x_306;
x_232 = x_307;
x_233 = x_308;
x_234 = x_309;
x_235 = x_310;
x_236 = x_311;
x_237 = x_312;
x_238 = lean_box(0);
goto block_242;
}
else
{
x_278 = x_300;
x_279 = x_301;
x_280 = x_302;
x_281 = x_303;
x_282 = x_304;
x_283 = x_316;
x_284 = x_305;
x_285 = x_307;
x_286 = x_308;
x_287 = x_309;
x_288 = x_310;
x_289 = x_311;
x_290 = x_312;
x_291 = lean_box(0);
goto block_299;
}
}
}
}
block_342:
{
lean_object* x_331; double x_332; double x_333; double x_334; double x_335; double x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_331 = lean_io_mono_nanos_now();
x_332 = lean_float_of_nat(x_321);
x_333 = lean_float_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0);
x_334 = lean_float_div(x_332, x_333);
x_335 = lean_float_of_nat(x_331);
x_336 = lean_float_div(x_335, x_333);
x_337 = lean_box_float(x_334);
x_338 = lean_box_float(x_336);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_329);
lean_ctor_set(x_340, 1, x_339);
x_341 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_124, x_319, x_320, x_327, x_323, x_325, x_340, x_328, x_324, x_326, x_322);
lean_dec_ref(x_320);
return x_341;
}
block_356:
{
lean_object* x_355; 
x_355 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_355, 0, x_353);
x_319 = x_343;
x_320 = x_345;
x_321 = x_344;
x_322 = x_346;
x_323 = x_347;
x_324 = x_348;
x_325 = x_349;
x_326 = x_351;
x_327 = x_350;
x_328 = x_352;
x_329 = x_355;
x_330 = lean_box(0);
goto block_342;
}
block_373:
{
lean_object* x_371; lean_object* x_372; 
x_371 = l_List_appendTR___redArg(x_358, x_357);
x_372 = l_List_appendTR___redArg(x_371, x_369);
x_343 = x_359;
x_344 = x_361;
x_345 = x_360;
x_346 = x_362;
x_347 = x_363;
x_348 = x_364;
x_349 = x_365;
x_350 = x_367;
x_351 = x_366;
x_352 = x_368;
x_353 = x_372;
x_354 = lean_box(0);
goto block_356;
}
block_387:
{
lean_object* x_386; 
x_386 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_386, 0, x_384);
x_319 = x_374;
x_320 = x_376;
x_321 = x_375;
x_322 = x_377;
x_323 = x_378;
x_324 = x_379;
x_325 = x_380;
x_326 = x_382;
x_327 = x_381;
x_328 = x_383;
x_329 = x_386;
x_330 = lean_box(0);
goto block_342;
}
block_401:
{
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec_ref(x_398);
x_343 = x_388;
x_344 = x_390;
x_345 = x_389;
x_346 = x_391;
x_347 = x_392;
x_348 = x_393;
x_349 = x_394;
x_350 = x_396;
x_351 = x_395;
x_352 = x_397;
x_353 = x_399;
x_354 = lean_box(0);
goto block_356;
}
else
{
lean_object* x_400; 
x_400 = lean_ctor_get(x_398, 0);
lean_inc(x_400);
lean_dec_ref(x_398);
x_374 = x_388;
x_375 = x_390;
x_376 = x_389;
x_377 = x_391;
x_378 = x_392;
x_379 = x_393;
x_380 = x_394;
x_381 = x_396;
x_382 = x_395;
x_383 = x_397;
x_384 = x_400;
x_385 = lean_box(0);
goto block_387;
}
}
block_415:
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_414 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_413, x_412, x_408, x_411, x_406);
x_388 = x_403;
x_389 = x_405;
x_390 = x_404;
x_391 = x_406;
x_392 = x_407;
x_393 = x_408;
x_394 = x_409;
x_395 = x_411;
x_396 = x_410;
x_397 = x_412;
x_398 = x_414;
goto block_401;
}
block_435:
{
uint8_t x_431; 
x_431 = l_List_isEmpty___redArg(x_418);
lean_dec(x_418);
if (x_431 == 0)
{
lean_dec(x_423);
lean_dec(x_417);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_402 = lean_box(0);
x_403 = x_419;
x_404 = x_420;
x_405 = x_421;
x_406 = x_422;
x_407 = x_426;
x_408 = x_427;
x_409 = x_428;
x_410 = x_429;
x_411 = x_430;
x_412 = x_424;
goto block_415;
}
else
{
if (x_425 == 0)
{
lean_object* x_432; 
lean_inc(x_422);
lean_inc_ref(x_430);
lean_inc(x_427);
lean_inc_ref(x_424);
lean_inc(x_2);
x_432 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_423, x_29, x_424, x_427, x_430, x_422);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
lean_dec_ref(x_432);
x_434 = l_List_appendTR___redArg(x_417, x_433);
x_343 = x_419;
x_344 = x_420;
x_345 = x_421;
x_346 = x_422;
x_347 = x_426;
x_348 = x_427;
x_349 = x_428;
x_350 = x_429;
x_351 = x_430;
x_352 = x_424;
x_353 = x_434;
x_354 = lean_box(0);
goto block_356;
}
else
{
lean_dec(x_417);
x_388 = x_419;
x_389 = x_421;
x_390 = x_420;
x_391 = x_422;
x_392 = x_426;
x_393 = x_427;
x_394 = x_428;
x_395 = x_430;
x_396 = x_429;
x_397 = x_424;
x_398 = x_432;
goto block_401;
}
}
else
{
lean_dec(x_423);
lean_dec(x_417);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_402 = lean_box(0);
x_403 = x_419;
x_404 = x_420;
x_405 = x_421;
x_406 = x_422;
x_407 = x_426;
x_408 = x_427;
x_409 = x_428;
x_410 = x_429;
x_411 = x_430;
x_412 = x_424;
goto block_415;
}
}
}
block_451:
{
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
lean_dec_ref(x_448);
x_357 = x_437;
x_358 = x_436;
x_359 = x_438;
x_360 = x_440;
x_361 = x_439;
x_362 = x_441;
x_363 = x_442;
x_364 = x_443;
x_365 = x_444;
x_366 = x_446;
x_367 = x_445;
x_368 = x_447;
x_369 = x_449;
x_370 = lean_box(0);
goto block_373;
}
else
{
lean_object* x_450; 
lean_dec(x_437);
lean_dec(x_436);
x_450 = lean_ctor_get(x_448, 0);
lean_inc(x_450);
lean_dec_ref(x_448);
x_374 = x_438;
x_375 = x_439;
x_376 = x_440;
x_377 = x_441;
x_378 = x_442;
x_379 = x_443;
x_380 = x_444;
x_381 = x_445;
x_382 = x_446;
x_383 = x_447;
x_384 = x_450;
x_385 = lean_box(0);
goto block_387;
}
}
block_470:
{
if (x_467 == 0)
{
lean_object* x_468; 
lean_dec_ref(x_454);
x_468 = l_Lean_Meta_SavedState_restore___redArg(x_459, x_463, x_458);
lean_dec_ref(x_459);
if (lean_obj_tag(x_468) == 0)
{
lean_dec_ref(x_468);
x_357 = x_452;
x_358 = x_453;
x_359 = x_455;
x_360 = x_456;
x_361 = x_457;
x_362 = x_458;
x_363 = x_462;
x_364 = x_463;
x_365 = x_464;
x_366 = x_465;
x_367 = x_466;
x_368 = x_460;
x_369 = x_29;
x_370 = lean_box(0);
goto block_373;
}
else
{
lean_object* x_469; 
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_29);
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
lean_dec_ref(x_468);
x_374 = x_455;
x_375 = x_457;
x_376 = x_456;
x_377 = x_458;
x_378 = x_462;
x_379 = x_463;
x_380 = x_464;
x_381 = x_466;
x_382 = x_465;
x_383 = x_460;
x_384 = x_469;
x_385 = lean_box(0);
goto block_387;
}
}
else
{
lean_dec_ref(x_459);
lean_dec(x_29);
x_436 = x_453;
x_437 = x_452;
x_438 = x_455;
x_439 = x_457;
x_440 = x_456;
x_441 = x_458;
x_442 = x_462;
x_443 = x_463;
x_444 = x_464;
x_445 = x_466;
x_446 = x_465;
x_447 = x_460;
x_448 = x_454;
goto block_451;
}
}
block_492:
{
lean_object* x_485; 
x_485 = l_Lean_Meta_saveState___redArg(x_481, x_477);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
lean_dec_ref(x_485);
lean_inc(x_477);
lean_inc_ref(x_484);
lean_inc(x_481);
lean_inc_ref(x_479);
lean_inc(x_29);
lean_inc(x_2);
x_487 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_478, x_29, x_479, x_481, x_484, x_477);
if (lean_obj_tag(x_487) == 0)
{
lean_dec(x_486);
lean_dec(x_29);
x_436 = x_472;
x_437 = x_473;
x_438 = x_474;
x_439 = x_475;
x_440 = x_476;
x_441 = x_477;
x_442 = x_480;
x_443 = x_481;
x_444 = x_482;
x_445 = x_483;
x_446 = x_484;
x_447 = x_479;
x_448 = x_487;
goto block_451;
}
else
{
lean_object* x_488; uint8_t x_489; 
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = l_Lean_Exception_isInterrupt(x_488);
if (x_489 == 0)
{
uint8_t x_490; 
x_490 = l_Lean_Exception_isRuntime(x_488);
x_452 = x_473;
x_453 = x_472;
x_454 = x_487;
x_455 = x_474;
x_456 = x_476;
x_457 = x_475;
x_458 = x_477;
x_459 = x_486;
x_460 = x_479;
x_461 = lean_box(0);
x_462 = x_480;
x_463 = x_481;
x_464 = x_482;
x_465 = x_484;
x_466 = x_483;
x_467 = x_490;
goto block_470;
}
else
{
lean_dec(x_488);
x_452 = x_473;
x_453 = x_472;
x_454 = x_487;
x_455 = x_474;
x_456 = x_476;
x_457 = x_475;
x_458 = x_477;
x_459 = x_486;
x_460 = x_479;
x_461 = lean_box(0);
x_462 = x_480;
x_463 = x_481;
x_464 = x_482;
x_465 = x_484;
x_466 = x_483;
x_467 = x_489;
goto block_470;
}
}
}
else
{
lean_object* x_491; 
lean_dec(x_478);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_491 = lean_ctor_get(x_485, 0);
lean_inc(x_491);
lean_dec_ref(x_485);
x_374 = x_474;
x_375 = x_475;
x_376 = x_476;
x_377 = x_477;
x_378 = x_480;
x_379 = x_481;
x_380 = x_482;
x_381 = x_483;
x_382 = x_484;
x_383 = x_479;
x_384 = x_491;
x_385 = lean_box(0);
goto block_387;
}
}
block_511:
{
uint8_t x_508; lean_object* x_509; 
x_508 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_493);
x_509 = l_List_appendTR___redArg(x_506, x_493);
if (x_508 == 0)
{
x_416 = lean_box(0);
x_417 = x_493;
x_418 = x_494;
x_419 = x_495;
x_420 = x_496;
x_421 = x_497;
x_422 = x_498;
x_423 = x_509;
x_424 = x_499;
x_425 = x_500;
x_426 = x_501;
x_427 = x_502;
x_428 = x_503;
x_429 = x_504;
x_430 = x_505;
goto block_435;
}
else
{
uint8_t x_510; 
x_510 = l_List_isEmpty___redArg(x_493);
if (x_510 == 0)
{
x_471 = lean_box(0);
x_472 = x_493;
x_473 = x_494;
x_474 = x_495;
x_475 = x_496;
x_476 = x_497;
x_477 = x_498;
x_478 = x_509;
x_479 = x_499;
x_480 = x_501;
x_481 = x_502;
x_482 = x_503;
x_483 = x_504;
x_484 = x_505;
goto block_492;
}
else
{
if (x_500 == 0)
{
x_416 = lean_box(0);
x_417 = x_493;
x_418 = x_494;
x_419 = x_495;
x_420 = x_496;
x_421 = x_497;
x_422 = x_498;
x_423 = x_509;
x_424 = x_499;
x_425 = x_500;
x_426 = x_501;
x_427 = x_502;
x_428 = x_503;
x_429 = x_504;
x_430 = x_505;
goto block_435;
}
else
{
x_471 = lean_box(0);
x_472 = x_493;
x_473 = x_494;
x_474 = x_495;
x_475 = x_496;
x_476 = x_497;
x_477 = x_498;
x_478 = x_509;
x_479 = x_499;
x_480 = x_501;
x_481 = x_502;
x_482 = x_503;
x_483 = x_504;
x_484 = x_505;
goto block_492;
}
}
}
}
block_548:
{
lean_object* x_524; 
x_524 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_517);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; uint8_t x_527; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
lean_dec_ref(x_524);
x_526 = l_Lean_trace_profiler_useHeartbeats;
x_527 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_516, x_526);
if (x_527 == 0)
{
lean_object* x_528; lean_object* x_529; 
lean_del_object(x_30);
x_528 = lean_io_mono_nanos_now();
x_529 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_95, x_5, x_515, x_518);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
lean_dec_ref(x_529);
x_531 = l_List_reverse___redArg(x_530);
x_493 = x_512;
x_494 = x_513;
x_495 = x_514;
x_496 = x_528;
x_497 = x_516;
x_498 = x_517;
x_499 = x_523;
x_500 = x_527;
x_501 = x_525;
x_502 = x_518;
x_503 = x_519;
x_504 = x_520;
x_505 = x_521;
x_506 = x_531;
x_507 = lean_box(0);
goto block_511;
}
else
{
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_532; 
x_532 = lean_ctor_get(x_529, 0);
lean_inc(x_532);
lean_dec_ref(x_529);
x_493 = x_512;
x_494 = x_513;
x_495 = x_514;
x_496 = x_528;
x_497 = x_516;
x_498 = x_517;
x_499 = x_523;
x_500 = x_527;
x_501 = x_525;
x_502 = x_518;
x_503 = x_519;
x_504 = x_520;
x_505 = x_521;
x_506 = x_532;
x_507 = lean_box(0);
goto block_511;
}
else
{
lean_object* x_533; 
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_533 = lean_ctor_get(x_529, 0);
lean_inc(x_533);
lean_dec_ref(x_529);
x_374 = x_514;
x_375 = x_528;
x_376 = x_516;
x_377 = x_517;
x_378 = x_525;
x_379 = x_518;
x_380 = x_519;
x_381 = x_520;
x_382 = x_521;
x_383 = x_523;
x_384 = x_533;
x_385 = lean_box(0);
goto block_387;
}
}
}
else
{
lean_object* x_534; lean_object* x_535; 
x_534 = lean_io_get_num_heartbeats();
x_535 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_95, x_5, x_515, x_518);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
lean_dec_ref(x_535);
x_537 = l_List_reverse___redArg(x_536);
x_300 = x_512;
x_301 = x_513;
x_302 = x_514;
x_303 = x_516;
x_304 = x_517;
x_305 = x_523;
x_306 = x_527;
x_307 = x_534;
x_308 = x_525;
x_309 = x_518;
x_310 = x_519;
x_311 = x_520;
x_312 = x_521;
x_313 = x_537;
x_314 = lean_box(0);
goto block_318;
}
else
{
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_538; 
x_538 = lean_ctor_get(x_535, 0);
lean_inc(x_538);
lean_dec_ref(x_535);
x_300 = x_512;
x_301 = x_513;
x_302 = x_514;
x_303 = x_516;
x_304 = x_517;
x_305 = x_523;
x_306 = x_527;
x_307 = x_534;
x_308 = x_525;
x_309 = x_518;
x_310 = x_519;
x_311 = x_520;
x_312 = x_521;
x_313 = x_538;
x_314 = lean_box(0);
goto block_318;
}
else
{
lean_object* x_539; 
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_539 = lean_ctor_get(x_535, 0);
lean_inc(x_539);
lean_dec_ref(x_535);
x_179 = x_514;
x_180 = x_516;
x_181 = x_534;
x_182 = x_517;
x_183 = x_525;
x_184 = x_518;
x_185 = x_519;
x_186 = x_520;
x_187 = x_521;
x_188 = x_523;
x_189 = x_539;
x_190 = lean_box(0);
goto block_192;
}
}
}
}
else
{
lean_object* x_540; lean_object* x_541; uint8_t x_542; uint8_t x_547; 
lean_dec_ref(x_523);
lean_dec_ref(x_521);
lean_dec_ref(x_519);
lean_dec(x_518);
lean_dec(x_517);
lean_dec_ref(x_516);
lean_dec(x_515);
lean_dec_ref(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_del_object(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_540 = lean_ctor_get(x_524, 0);
x_547 = !lean_is_exclusive(x_524);
if (x_547 == 0)
{
x_541 = x_524;
x_542 = x_547;
goto block_546;
}
else
{
lean_inc(x_540);
lean_dec(x_524);
x_541 = lean_box(0);
x_542 = x_547;
goto block_546;
}
block_546:
{
lean_object* x_543; 
if (x_542 == 0)
{
x_543 = x_541;
goto block_544;
}
else
{
lean_object* x_545; 
x_545 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_545, 0, x_540);
x_543 = x_545;
goto block_544;
}
block_544:
{
return x_543;
}
}
}
}
block_587:
{
lean_object* x_554; 
lean_inc(x_552);
lean_inc_ref(x_551);
lean_inc(x_550);
lean_inc_ref(x_549);
x_554 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_28, x_123, x_549, x_550, x_551, x_552);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; lean_object* x_560; lean_object* x_561; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
lean_dec_ref(x_554);
x_556 = lean_ctor_get(x_551, 2);
x_557 = lean_ctor_get(x_555, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_555, 1);
lean_inc(x_558);
lean_dec(x_555);
x_559 = lean_ctor_get_uint8(x_556, sizeof(void*)*1);
x_560 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_558, x_25);
x_561 = lean_box(0);
if (x_559 == 0)
{
lean_del_object(x_30);
x_108 = x_560;
x_109 = x_557;
x_110 = x_561;
x_111 = x_549;
x_112 = x_550;
x_113 = x_551;
x_114 = x_552;
x_115 = lean_box(0);
goto block_120;
}
else
{
lean_object* x_562; 
lean_inc(x_2);
x_562 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_551);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; uint8_t x_566; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
lean_dec_ref(x_562);
lean_inc(x_560);
lean_inc(x_557);
x_564 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(x_564, 0, x_557);
lean_closure_set(x_564, 1, x_560);
x_565 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_566 = lean_unbox(x_563);
if (x_566 == 0)
{
lean_object* x_567; uint8_t x_568; 
x_567 = l_Lean_trace_profiler;
x_568 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_556, x_567);
if (x_568 == 0)
{
lean_dec_ref(x_564);
lean_dec(x_563);
lean_del_object(x_30);
x_108 = x_560;
x_109 = x_557;
x_110 = x_561;
x_111 = x_549;
x_112 = x_550;
x_113 = x_551;
x_114 = x_552;
x_115 = lean_box(0);
goto block_120;
}
else
{
uint8_t x_569; 
lean_inc_ref(x_556);
x_569 = lean_unbox(x_563);
lean_dec(x_563);
x_512 = x_560;
x_513 = x_557;
x_514 = x_565;
x_515 = x_561;
x_516 = x_556;
x_517 = x_552;
x_518 = x_550;
x_519 = x_564;
x_520 = x_569;
x_521 = x_551;
x_522 = lean_box(0);
x_523 = x_549;
goto block_548;
}
}
else
{
uint8_t x_570; 
lean_inc_ref(x_556);
x_570 = lean_unbox(x_563);
lean_dec(x_563);
x_512 = x_560;
x_513 = x_557;
x_514 = x_565;
x_515 = x_561;
x_516 = x_556;
x_517 = x_552;
x_518 = x_550;
x_519 = x_564;
x_520 = x_570;
x_521 = x_551;
x_522 = lean_box(0);
x_523 = x_549;
goto block_548;
}
}
else
{
lean_object* x_571; lean_object* x_572; uint8_t x_573; uint8_t x_578; 
lean_dec(x_560);
lean_dec(x_557);
lean_dec(x_552);
lean_dec_ref(x_551);
lean_dec(x_550);
lean_dec_ref(x_549);
lean_del_object(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_571 = lean_ctor_get(x_562, 0);
x_578 = !lean_is_exclusive(x_562);
if (x_578 == 0)
{
x_572 = x_562;
x_573 = x_578;
goto block_577;
}
else
{
lean_inc(x_571);
lean_dec(x_562);
x_572 = lean_box(0);
x_573 = x_578;
goto block_577;
}
block_577:
{
lean_object* x_574; 
if (x_573 == 0)
{
x_574 = x_572;
goto block_575;
}
else
{
lean_object* x_576; 
x_576 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_576, 0, x_571);
x_574 = x_576;
goto block_575;
}
block_575:
{
return x_574;
}
}
}
}
}
else
{
lean_object* x_579; lean_object* x_580; uint8_t x_581; uint8_t x_586; 
lean_dec(x_552);
lean_dec_ref(x_551);
lean_dec(x_550);
lean_dec_ref(x_549);
lean_del_object(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_579 = lean_ctor_get(x_554, 0);
x_586 = !lean_is_exclusive(x_554);
if (x_586 == 0)
{
x_580 = x_554;
x_581 = x_586;
goto block_585;
}
else
{
lean_inc(x_579);
lean_dec(x_554);
x_580 = lean_box(0);
x_581 = x_586;
goto block_585;
}
block_585:
{
lean_object* x_582; 
if (x_581 == 0)
{
x_582 = x_580;
goto block_583;
}
else
{
lean_object* x_584; 
x_584 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_584, 0, x_579);
x_582 = x_584;
goto block_583;
}
block_583:
{
return x_582;
}
}
}
}
}
else
{
lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; 
lean_del_object(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_5);
x_1502 = lean_ctor_get(x_1, 0);
lean_inc(x_1502);
x_1503 = lean_box(0);
x_1504 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1502, x_6, x_1503, x_7, x_8, x_9, x_10);
return x_1504;
}
block_49:
{
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_38);
x_40 = l_Lean_Meta_SavedState_restore___redArg(x_34, x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_dec_ref(x_40);
x_12 = x_33;
x_13 = x_32;
x_14 = x_29;
x_15 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_29);
x_41 = lean_ctor_get(x_40, 0);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
x_42 = x_40;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_29);
x_20 = x_32;
x_21 = x_33;
x_22 = x_38;
goto block_24;
}
}
block_72:
{
lean_object* x_58; 
x_58 = l_Lean_Meta_saveState___redArg(x_52, x_53);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_29);
x_60 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_56, x_29, x_54, x_52, x_57, x_53);
if (lean_obj_tag(x_60) == 0)
{
lean_dec(x_59);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_29);
x_20 = x_51;
x_21 = x_50;
x_22 = x_60;
goto block_24;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = l_Lean_Exception_isInterrupt(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = l_Lean_Exception_isRuntime(x_61);
x_32 = x_51;
x_33 = x_50;
x_34 = x_59;
x_35 = x_52;
x_36 = x_53;
x_37 = lean_box(0);
x_38 = x_60;
x_39 = x_63;
goto block_49;
}
else
{
lean_dec(x_61);
x_32 = x_51;
x_33 = x_50;
x_34 = x_59;
x_35 = x_52;
x_36 = x_53;
x_37 = lean_box(0);
x_38 = x_60;
x_39 = x_62;
goto block_49;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec_ref(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_64 = lean_ctor_get(x_58, 0);
x_71 = !lean_is_exclusive(x_58);
if (x_71 == 0)
{
x_65 = x_58;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
block_94:
{
uint8_t x_81; 
x_81 = l_List_isEmpty___redArg(x_74);
lean_dec(x_74);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_79);
lean_dec(x_73);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_82 = lean_obj_once(&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2, &l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2_once, _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
x_83 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_82, x_77, x_75, x_80, x_76);
lean_dec(x_76);
lean_dec_ref(x_80);
lean_dec(x_75);
lean_dec_ref(x_77);
return x_83;
}
else
{
lean_object* x_84; 
x_84 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_79, x_29, x_77, x_75, x_80, x_76);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_93; 
x_85 = lean_ctor_get(x_84, 0);
x_93 = !lean_is_exclusive(x_84);
if (x_93 == 0)
{
x_86 = x_84;
x_87 = x_93;
goto block_92;
}
else
{
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_box(0);
x_87 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_List_appendTR___redArg(x_73, x_85);
if (x_87 == 0)
{
lean_ctor_set(x_86, 0, x_88);
x_89 = x_86;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_88);
x_89 = x_91;
goto block_90;
}
block_90:
{
return x_89;
}
}
}
else
{
lean_dec(x_73);
return x_84;
}
}
}
block_107:
{
uint8_t x_104; lean_object* x_105; 
x_104 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_97);
x_105 = l_List_appendTR___redArg(x_102, x_97);
if (x_104 == 0)
{
x_73 = x_97;
x_74 = x_96;
x_75 = x_98;
x_76 = x_99;
x_77 = x_100;
x_78 = lean_box(0);
x_79 = x_105;
x_80 = x_101;
goto block_94;
}
else
{
uint8_t x_106; 
x_106 = l_List_isEmpty___redArg(x_97);
if (x_106 == 0)
{
x_50 = x_96;
x_51 = x_97;
x_52 = x_98;
x_53 = x_99;
x_54 = x_100;
x_55 = lean_box(0);
x_56 = x_105;
x_57 = x_101;
goto block_72;
}
else
{
if (x_95 == 0)
{
x_73 = x_97;
x_74 = x_96;
x_75 = x_98;
x_76 = x_99;
x_77 = x_100;
x_78 = lean_box(0);
x_79 = x_105;
x_80 = x_101;
goto block_94;
}
else
{
x_50 = x_96;
x_51 = x_97;
x_52 = x_98;
x_53 = x_99;
x_54 = x_100;
x_55 = lean_box(0);
x_56 = x_105;
x_57 = x_101;
goto block_72;
}
}
}
}
block_120:
{
lean_object* x_116; 
x_116 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_95, x_5, x_110, x_112);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = l_List_reverse___redArg(x_117);
x_96 = x_109;
x_97 = x_108;
x_98 = x_112;
x_99 = x_114;
x_100 = x_111;
x_101 = x_113;
x_102 = x_118;
x_103 = lean_box(0);
goto block_107;
}
else
{
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec_ref(x_116);
x_96 = x_109;
x_97 = x_108;
x_98 = x_112;
x_99 = x_114;
x_100 = x_111;
x_101 = x_113;
x_102 = x_119;
x_103 = lean_box(0);
goto block_107;
}
else
{
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_116;
}
}
}
}
}
else
{
lean_object* x_1507; lean_object* x_1508; uint8_t x_1509; uint8_t x_1514; 
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
x_1507 = lean_ctor_get(x_26, 0);
x_1514 = !lean_is_exclusive(x_26);
if (x_1514 == 0)
{
x_1508 = x_26;
x_1509 = x_1514;
goto block_1513;
}
else
{
lean_inc(x_1507);
lean_dec(x_26);
x_1508 = lean_box(0);
x_1509 = x_1514;
goto block_1513;
}
block_1513:
{
lean_object* x_1510; 
if (x_1509 == 0)
{
x_1510 = x_1508;
goto block_1511;
}
else
{
lean_object* x_1512; 
x_1512 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1512, 0, x_1507);
x_1510 = x_1512;
goto block_1511;
}
block_1511:
{
return x_1510;
}
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_List_appendTR___redArg(x_13, x_12);
x_17 = l_List_appendTR___redArg(x_16, x_14);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
block_24:
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_12 = x_21;
x_13 = x_20;
x_14 = x_23;
x_15 = lean_box(0);
goto block_19;
}
else
{
lean_dec(x_21);
lean_dec(x_20);
return x_22;
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

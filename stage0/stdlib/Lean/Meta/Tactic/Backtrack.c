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
static lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0;
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
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__2;
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
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 42, .m_data = "⏭️ deemed acceptable, returning as subgoal"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__0_value;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 35, .m_data = "⏬ discharger generated new subgoals"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__0_value;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " success!"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__0_value;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1;
lean_object* l_Lean_exceptEmoji___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = " discarding already assigned goal "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__0_value;
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
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
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
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " working on: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__0_value;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
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
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__1_value;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2;
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
static double l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Backtrack exceeded the recursion limit"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__1_value;
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
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", new: "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__2_value;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3;
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "independent goals "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0_value;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2_value;
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = " working on them before "};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__4_value;
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
static lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__1_value;
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(x_11, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
uint8_t x_16; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_ppMVarId(x_19, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_1 = x_20;
x_2 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_2);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_26 = x_21;
} else {
 lean_dec_ref(x_21);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
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
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_box(0);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_box(0);
return x_5;
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
static lean_object* _init_l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0;
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0;
x_4 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__2;
lean_ctor_set(x_8, 0, x_11);
x_12 = lean_st_ref_set(x_1, x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
lean_dec(x_8);
x_15 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__2;
x_16 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint64(x_16, sizeof(void*)*1, x_14);
lean_ctor_set(x_6, 4, x_16);
x_17 = lean_st_ref_set(x_1, x_6);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_6, 4);
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
x_27 = lean_ctor_get(x_6, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_19);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_28 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_29 = x_19;
} else {
 lean_dec_ref(x_19);
 x_29 = lean_box(0);
}
x_30 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__2;
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 1, 8);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_28);
x_32 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_23);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_24);
lean_ctor_set(x_32, 6, x_25);
lean_ctor_set(x_32, 7, x_26);
lean_ctor_set(x_32, 8, x_27);
x_33 = lean_st_ref_set(x_1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_5);
return x_34;
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
uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_30; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_17 = x_9;
} else {
 lean_dec_ref(x_9);
 x_17 = lean_box(0);
}
x_30 = l_Lean_Exception_isInterrupt(x_16);
if (x_30 == 0)
{
uint8_t x_31; 
lean_inc(x_16);
x_31 = l_Lean_Exception_isRuntime(x_16);
x_18 = x_31;
goto block_29;
}
else
{
x_18 = x_30;
goto block_29;
}
block_29:
{
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
x_19 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_17)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_17;
}
lean_ctor_set(x_28, 0, x_16);
return x_28;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
return x_7;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
lean_dec(x_7);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1() {
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
x_7 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1() {
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
x_7 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1() {
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
x_7 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1() {
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
x_9 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1() {
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
x_10 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1;
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__0;
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
x_7 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__1;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1() {
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
x_10 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1() {
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(x_8, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_exceptEmoji___redArg(x_2);
x_13 = l_Lean_stringToMessageData(x_12);
x_14 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l_Lean_exceptEmoji___redArg(x_2);
x_19 = l_Lean_stringToMessageData(x_18);
x_20 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
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
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec(x_5);
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = lean_st_ref_get(x_8);
x_13 = lean_ctor_get(x_12, 4);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_replaceRef(x_3, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_15);
x_16 = l_Lean_PersistentArray_toArray___redArg(x_14);
lean_dec_ref(x_14);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4_spec__7(x_17, x_18, x_16);
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(x_20, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_st_ref_take(x_8);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_23);
x_30 = l_Lean_PersistentArray_push___redArg(x_1, x_29);
lean_ctor_set(x_26, 0, x_30);
x_31 = lean_st_ref_set(x_8, x_24);
x_32 = lean_box(0);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get_uint64(x_26, sizeof(void*)*1);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_23);
x_35 = l_Lean_PersistentArray_push___redArg(x_1, x_34);
x_36 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint64(x_36, sizeof(void*)*1, x_33);
lean_ctor_set(x_24, 4, x_36);
x_37 = lean_st_ref_set(x_8, x_24);
x_38 = lean_box(0);
lean_ctor_set(x_21, 0, x_38);
return x_21;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_39 = lean_ctor_get(x_24, 4);
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
x_42 = lean_ctor_get(x_24, 2);
x_43 = lean_ctor_get(x_24, 3);
x_44 = lean_ctor_get(x_24, 5);
x_45 = lean_ctor_get(x_24, 6);
x_46 = lean_ctor_get(x_24, 7);
x_47 = lean_ctor_get(x_24, 8);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_39);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_48 = lean_ctor_get_uint64(x_39, sizeof(void*)*1);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_49 = x_39;
} else {
 lean_dec_ref(x_39);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_23);
x_51 = l_Lean_PersistentArray_push___redArg(x_1, x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 1, 8);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint64(x_52, sizeof(void*)*1, x_48);
x_53 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_41);
lean_ctor_set(x_53, 2, x_42);
lean_ctor_set(x_53, 3, x_43);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_44);
lean_ctor_set(x_53, 6, x_45);
lean_ctor_set(x_53, 7, x_46);
lean_ctor_set(x_53, 8, x_47);
x_54 = lean_st_ref_set(x_8, x_53);
x_55 = lean_box(0);
lean_ctor_set(x_21, 0, x_55);
return x_21;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_56 = lean_ctor_get(x_21, 0);
lean_inc(x_56);
lean_dec(x_21);
x_57 = lean_st_ref_take(x_8);
x_58 = lean_ctor_get(x_57, 4);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_57, 3);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_57, 5);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_57, 6);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_57, 7);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_57, 8);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 lean_ctor_release(x_57, 5);
 lean_ctor_release(x_57, 6);
 lean_ctor_release(x_57, 7);
 lean_ctor_release(x_57, 8);
 x_67 = x_57;
} else {
 lean_dec_ref(x_57);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get_uint64(x_58, sizeof(void*)*1);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_69 = x_58;
} else {
 lean_dec_ref(x_58);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_56);
x_71 = l_Lean_PersistentArray_push___redArg(x_1, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_68);
if (lean_is_scalar(x_67)) {
 x_73 = lean_alloc_ctor(0, 9, 0);
} else {
 x_73 = x_67;
}
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_60);
lean_ctor_set(x_73, 2, x_61);
lean_ctor_set(x_73, 3, x_62);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_63);
lean_ctor_set(x_73, 6, x_64);
lean_ctor_set(x_73, 7, x_65);
lean_ctor_set(x_73, 8, x_66);
x_74 = lean_st_ref_set(x_8, x_73);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint64_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_77 = lean_ctor_get(x_7, 0);
x_78 = lean_ctor_get(x_7, 1);
x_79 = lean_ctor_get(x_7, 2);
x_80 = lean_ctor_get(x_7, 3);
x_81 = lean_ctor_get(x_7, 4);
x_82 = lean_ctor_get(x_7, 5);
x_83 = lean_ctor_get(x_7, 6);
x_84 = lean_ctor_get(x_7, 7);
x_85 = lean_ctor_get(x_7, 8);
x_86 = lean_ctor_get(x_7, 9);
x_87 = lean_ctor_get(x_7, 10);
x_88 = lean_ctor_get(x_7, 11);
x_89 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_90 = lean_ctor_get(x_7, 12);
x_91 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_92 = lean_ctor_get(x_7, 13);
lean_inc(x_92);
lean_inc(x_90);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_7);
x_93 = lean_st_ref_get(x_8);
x_94 = lean_ctor_get(x_93, 4);
lean_inc_ref(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc_ref(x_95);
lean_dec_ref(x_94);
x_96 = l_Lean_replaceRef(x_3, x_82);
lean_dec(x_82);
x_97 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_97, 0, x_77);
lean_ctor_set(x_97, 1, x_78);
lean_ctor_set(x_97, 2, x_79);
lean_ctor_set(x_97, 3, x_80);
lean_ctor_set(x_97, 4, x_81);
lean_ctor_set(x_97, 5, x_96);
lean_ctor_set(x_97, 6, x_83);
lean_ctor_set(x_97, 7, x_84);
lean_ctor_set(x_97, 8, x_85);
lean_ctor_set(x_97, 9, x_86);
lean_ctor_set(x_97, 10, x_87);
lean_ctor_set(x_97, 11, x_88);
lean_ctor_set(x_97, 12, x_90);
lean_ctor_set(x_97, 13, x_92);
lean_ctor_set_uint8(x_97, sizeof(void*)*14, x_89);
lean_ctor_set_uint8(x_97, sizeof(void*)*14 + 1, x_91);
x_98 = l_Lean_PersistentArray_toArray___redArg(x_95);
lean_dec_ref(x_95);
x_99 = lean_array_size(x_98);
x_100 = 0;
x_101 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4_spec__7(x_99, x_100, x_98);
x_102 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_102, 0, x_2);
lean_ctor_set(x_102, 1, x_4);
lean_ctor_set(x_102, 2, x_101);
x_103 = l_Lean_addMessageContextFull___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__6(x_102, x_5, x_6, x_97, x_8);
lean_dec_ref(x_97);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_st_ref_take(x_8);
x_107 = lean_ctor_get(x_106, 4);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_106, 0);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 2);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_106, 3);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_106, 5);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_106, 6);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_106, 7);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_106, 8);
lean_inc_ref(x_115);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 lean_ctor_release(x_106, 4);
 lean_ctor_release(x_106, 5);
 lean_ctor_release(x_106, 6);
 lean_ctor_release(x_106, 7);
 lean_ctor_release(x_106, 8);
 x_116 = x_106;
} else {
 lean_dec_ref(x_106);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get_uint64(x_107, sizeof(void*)*1);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_118 = x_107;
} else {
 lean_dec_ref(x_107);
 x_118 = lean_box(0);
}
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_3);
lean_ctor_set(x_119, 1, x_104);
x_120 = l_Lean_PersistentArray_push___redArg(x_1, x_119);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 1, 8);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set_uint64(x_121, sizeof(void*)*1, x_117);
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(0, 9, 0);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_108);
lean_ctor_set(x_122, 1, x_109);
lean_ctor_set(x_122, 2, x_110);
lean_ctor_set(x_122, 3, x_111);
lean_ctor_set(x_122, 4, x_121);
lean_ctor_set(x_122, 5, x_112);
lean_ctor_set(x_122, 6, x_113);
lean_ctor_set(x_122, 7, x_114);
lean_ctor_set(x_122, 8, x_115);
x_123 = lean_st_ref_set(x_8, x_122);
x_124 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_105;
}
lean_ctor_set(x_125, 0, x_124);
return x_125;
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
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3() {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_48; double x_81; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec_ref(x_8);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_dec(x_15);
x_32 = l_Lean_trace_profiler;
x_33 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_4, x_32);
if (x_33 == 0)
{
x_48 = x_33;
goto block_80;
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_trace_profiler_useHeartbeats;
x_88 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_4, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; double x_91; double x_92; double x_93; 
x_89 = l_Lean_trace_profiler_threshold;
x_90 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(x_4, x_89);
x_91 = lean_float_of_nat(x_90);
x_92 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3;
x_93 = lean_float_div(x_91, x_92);
x_81 = x_93;
goto block_86;
}
else
{
lean_object* x_94; lean_object* x_95; double x_96; 
x_94 = l_Lean_trace_profiler_threshold;
x_95 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__6(x_4, x_94);
x_96 = lean_float_of_nat(x_95);
x_81 = x_96;
goto block_86;
}
}
block_29:
{
lean_object* x_24; 
x_24 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__4(x_6, x_18, x_17, x_16, x_19, x_20, x_21, x_22);
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
uint8_t x_26; 
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
block_42:
{
double x_37; lean_object* x_38; 
x_37 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0;
lean_inc_ref(x_3);
lean_inc(x_1);
x_38 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set_float(x_38, sizeof(void*)*2, x_37);
lean_ctor_set_float(x_38, sizeof(void*)*2 + 8, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 16, x_2);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_3);
lean_dec(x_1);
x_16 = x_35;
x_17 = x_34;
x_18 = x_38;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = lean_box(0);
goto block_29;
}
else
{
lean_object* x_39; double x_40; double x_41; 
lean_dec_ref(x_38);
x_39 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_3);
x_40 = lean_unbox_float(x_30);
lean_dec(x_30);
lean_ctor_set_float(x_39, sizeof(void*)*2, x_40);
x_41 = lean_unbox_float(x_31);
lean_dec(x_31);
lean_ctor_set_float(x_39, sizeof(void*)*2 + 8, x_41);
lean_ctor_set_uint8(x_39, sizeof(void*)*2 + 16, x_2);
x_16 = x_35;
x_17 = x_34;
x_18 = x_39;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
x_23 = lean_box(0);
goto block_29;
}
}
block_47:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_11, 5);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_14);
x_44 = lean_apply_6(x_7, x_14, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_43);
x_34 = x_43;
x_35 = x_45;
x_36 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_46; 
lean_dec_ref(x_44);
x_46 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2;
lean_inc(x_43);
x_34 = x_43;
x_35 = x_46;
x_36 = lean_box(0);
goto block_42;
}
}
block_80:
{
if (x_5 == 0)
{
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_49 = lean_st_ref_take(x_12);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_49, 4);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = l_Lean_PersistentArray_append___redArg(x_6, x_53);
lean_dec_ref(x_53);
lean_ctor_set(x_51, 0, x_54);
x_55 = lean_st_ref_set(x_12, x_49);
lean_dec(x_12);
x_56 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(x_14);
return x_56;
}
else
{
uint64_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get_uint64(x_51, sizeof(void*)*1);
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec(x_51);
x_59 = l_Lean_PersistentArray_append___redArg(x_6, x_58);
lean_dec_ref(x_58);
x_60 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_57);
lean_ctor_set(x_49, 4, x_60);
x_61 = lean_st_ref_set(x_12, x_49);
lean_dec(x_12);
x_62 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(x_14);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_63 = lean_ctor_get(x_49, 4);
x_64 = lean_ctor_get(x_49, 0);
x_65 = lean_ctor_get(x_49, 1);
x_66 = lean_ctor_get(x_49, 2);
x_67 = lean_ctor_get(x_49, 3);
x_68 = lean_ctor_get(x_49, 5);
x_69 = lean_ctor_get(x_49, 6);
x_70 = lean_ctor_get(x_49, 7);
x_71 = lean_ctor_get(x_49, 8);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_63);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_49);
x_72 = lean_ctor_get_uint64(x_63, sizeof(void*)*1);
x_73 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_73);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_74 = x_63;
} else {
 lean_dec_ref(x_63);
 x_74 = lean_box(0);
}
x_75 = l_Lean_PersistentArray_append___redArg(x_6, x_73);
lean_dec_ref(x_73);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 1, 8);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set_uint64(x_76, sizeof(void*)*1, x_72);
x_77 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_65);
lean_ctor_set(x_77, 2, x_66);
lean_ctor_set(x_77, 3, x_67);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_77, 5, x_68);
lean_ctor_set(x_77, 6, x_69);
lean_ctor_set(x_77, 7, x_70);
lean_ctor_set(x_77, 8, x_71);
x_78 = lean_st_ref_set(x_12, x_77);
lean_dec(x_12);
x_79 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4_spec__5___redArg(x_14);
return x_79;
}
}
else
{
goto block_47;
}
}
else
{
goto block_47;
}
}
block_86:
{
double x_82; double x_83; double x_84; uint8_t x_85; 
x_82 = lean_unbox_float(x_31);
x_83 = lean_unbox_float(x_30);
x_84 = lean_float_sub(x_82, x_83);
x_85 = lean_float_decLt(x_81, x_84);
x_48 = x_85;
goto block_80;
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
static double _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2() {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_230; uint8_t x_231; 
x_230 = lean_unsigned_to_nat(0u);
x_231 = lean_nat_dec_eq(x_5, x_230);
if (x_231 == 1)
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_232 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2;
x_233 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_232, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; uint8_t x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_357; lean_object* x_358; uint8_t x_359; uint8_t x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; uint8_t x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_445; lean_object* x_446; uint8_t x_447; uint8_t x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_473; lean_object* x_474; uint8_t x_475; uint8_t x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_498; lean_object* x_499; uint8_t x_500; uint8_t x_501; uint8_t x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_526; lean_object* x_527; uint8_t x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; uint8_t x_532; uint8_t x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_563; uint8_t x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; uint8_t x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_591; uint8_t x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; uint8_t x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; lean_object* x_620; uint8_t x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; uint8_t x_629; lean_object* x_630; lean_object* x_631; lean_object* x_644; lean_object* x_645; lean_object* x_646; uint8_t x_647; lean_object* x_648; uint8_t x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; lean_object* x_658; lean_object* x_659; lean_object* x_669; lean_object* x_670; uint8_t x_671; lean_object* x_672; lean_object* x_673; uint8_t x_674; uint8_t x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; lean_object* x_706; uint8_t x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; lean_object* x_716; lean_object* x_717; lean_object* x_730; uint8_t x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; uint8_t x_739; lean_object* x_740; lean_object* x_741; lean_object* x_751; uint8_t x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; uint8_t x_761; lean_object* x_762; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; lean_object* x_792; uint8_t x_793; lean_object* x_794; lean_object* x_795; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; uint8_t x_812; lean_object* x_813; uint8_t x_814; lean_object* x_815; lean_object* x_816; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; uint8_t x_835; lean_object* x_836; lean_object* x_837; uint8_t x_838; lean_object* x_839; lean_object* x_840; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; uint8_t x_855; lean_object* x_856; lean_object* x_857; uint8_t x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; uint8_t x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; uint8_t x_884; lean_object* x_885; lean_object* x_907; lean_object* x_908; uint8_t x_909; lean_object* x_910; uint8_t x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; uint8_t x_975; uint8_t x_976; lean_object* x_977; lean_object* x_978; uint8_t x_979; uint8_t x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; uint8_t x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; uint8_t x_1025; lean_object* x_1050; lean_object* x_1051; uint8_t x_1052; lean_object* x_1053; uint8_t x_1054; lean_object* x_1055; uint8_t x_1056; lean_object* x_1057; uint8_t x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1085; uint8_t x_1086; lean_object* x_1087; lean_object* x_1088; uint8_t x_1089; uint8_t x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; uint8_t x_1102; lean_object* x_1127; lean_object* x_1128; uint8_t x_1129; uint8_t x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; uint8_t x_1194; lean_object* x_1195; uint8_t x_1196; lean_object* x_1197; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; uint8_t x_1227; lean_object* x_1228; uint8_t x_1229; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; uint8_t x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1362; lean_object* x_1368; 
x_234 = lean_ctor_get(x_1, 1);
x_235 = lean_ctor_get(x_1, 2);
x_236 = lean_ctor_get(x_1, 3);
x_237 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__3));
x_328 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__4));
x_419 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__5));
x_907 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__6));
x_971 = lean_unsigned_to_nat(1u);
x_972 = lean_nat_sub(x_5, x_971);
lean_dec(x_5);
lean_inc_ref(x_234);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_1368 = lean_apply_7(x_234, x_4, x_6, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_1368) == 0)
{
lean_object* x_1369; 
x_1369 = lean_ctor_get(x_1368, 0);
lean_inc(x_1369);
lean_dec_ref(x_1368);
x_1300 = x_1369;
x_1301 = x_8;
x_1302 = x_9;
x_1303 = x_10;
x_1304 = x_11;
x_1305 = lean_box(0);
goto block_1361;
}
else
{
lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; uint8_t x_1374; lean_object* x_1375; lean_object* x_1376; uint8_t x_1377; uint8_t x_1431; uint8_t x_1454; 
x_1370 = lean_ctor_get(x_1368, 0);
lean_inc(x_1370);
if (lean_is_exclusive(x_1368)) {
 lean_ctor_release(x_1368, 0);
 x_1371 = x_1368;
} else {
 lean_dec_ref(x_1368);
 x_1371 = lean_box(0);
}
lean_inc(x_1370);
x_1372 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___boxed), 7, 1);
lean_closure_set(x_1372, 0, x_1370);
x_1454 = l_Lean_Exception_isInterrupt(x_1370);
if (x_1454 == 0)
{
uint8_t x_1455; 
lean_inc(x_1370);
x_1455 = l_Lean_Exception_isRuntime(x_1370);
x_1431 = x_1455;
goto block_1453;
}
else
{
x_1431 = x_1454;
goto block_1453;
}
block_1430:
{
lean_object* x_1378; uint8_t x_1379; 
x_1378 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_11);
x_1379 = !lean_is_exclusive(x_1378);
if (x_1379 == 0)
{
lean_object* x_1380; lean_object* x_1381; uint8_t x_1382; 
x_1380 = lean_ctor_get(x_1378, 0);
x_1381 = l_Lean_trace_profiler_useHeartbeats;
x_1382 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1375, x_1381);
if (x_1382 == 0)
{
lean_object* x_1383; lean_object* x_1384; double x_1385; double x_1386; double x_1387; double x_1388; double x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; 
x_1383 = lean_io_mono_nanos_now();
x_1384 = lean_io_mono_nanos_now();
lean_ctor_set(x_1378, 0, x_1370);
x_1385 = lean_float_of_nat(x_1383);
x_1386 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_1387 = lean_float_div(x_1385, x_1386);
x_1388 = lean_float_of_nat(x_1384);
x_1389 = lean_float_div(x_1388, x_1386);
x_1390 = lean_box_float(x_1387);
x_1391 = lean_box_float(x_1389);
x_1392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1392, 0, x_1390);
lean_ctor_set(x_1392, 1, x_1391);
x_1393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1393, 0, x_1378);
lean_ctor_set(x_1393, 1, x_1392);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1394 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1377, x_1376, x_1375, x_1374, x_1380, x_1372, x_1393, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1375);
x_1362 = x_1394;
goto block_1367;
}
else
{
lean_object* x_1395; lean_object* x_1396; double x_1397; double x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1395 = lean_io_get_num_heartbeats();
x_1396 = lean_io_get_num_heartbeats();
lean_ctor_set(x_1378, 0, x_1370);
x_1397 = lean_float_of_nat(x_1395);
x_1398 = lean_float_of_nat(x_1396);
x_1399 = lean_box_float(x_1397);
x_1400 = lean_box_float(x_1398);
x_1401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1401, 0, x_1399);
lean_ctor_set(x_1401, 1, x_1400);
x_1402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1402, 0, x_1378);
lean_ctor_set(x_1402, 1, x_1401);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1403 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1377, x_1376, x_1375, x_1374, x_1380, x_1372, x_1402, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1375);
x_1362 = x_1403;
goto block_1367;
}
}
else
{
lean_object* x_1404; lean_object* x_1405; uint8_t x_1406; 
x_1404 = lean_ctor_get(x_1378, 0);
lean_inc(x_1404);
lean_dec(x_1378);
x_1405 = l_Lean_trace_profiler_useHeartbeats;
x_1406 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1375, x_1405);
if (x_1406 == 0)
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; double x_1410; double x_1411; double x_1412; double x_1413; double x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1407 = lean_io_mono_nanos_now();
x_1408 = lean_io_mono_nanos_now();
x_1409 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1409, 0, x_1370);
x_1410 = lean_float_of_nat(x_1407);
x_1411 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_1412 = lean_float_div(x_1410, x_1411);
x_1413 = lean_float_of_nat(x_1408);
x_1414 = lean_float_div(x_1413, x_1411);
x_1415 = lean_box_float(x_1412);
x_1416 = lean_box_float(x_1414);
x_1417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1417, 0, x_1415);
lean_ctor_set(x_1417, 1, x_1416);
x_1418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1418, 0, x_1409);
lean_ctor_set(x_1418, 1, x_1417);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1419 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1377, x_1376, x_1375, x_1374, x_1404, x_1372, x_1418, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1375);
x_1362 = x_1419;
goto block_1367;
}
else
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; double x_1423; double x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; 
x_1420 = lean_io_get_num_heartbeats();
x_1421 = lean_io_get_num_heartbeats();
x_1422 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1422, 0, x_1370);
x_1423 = lean_float_of_nat(x_1420);
x_1424 = lean_float_of_nat(x_1421);
x_1425 = lean_box_float(x_1423);
x_1426 = lean_box_float(x_1424);
x_1427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1427, 0, x_1425);
lean_ctor_set(x_1427, 1, x_1426);
x_1428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1428, 0, x_1422);
lean_ctor_set(x_1428, 1, x_1427);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_1429 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_1377, x_1376, x_1375, x_1374, x_1404, x_1372, x_1428, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1375);
x_1362 = x_1429;
goto block_1367;
}
}
}
block_1453:
{
if (x_1431 == 0)
{
lean_object* x_1432; uint8_t x_1433; 
x_1432 = lean_ctor_get(x_10, 2);
x_1433 = lean_ctor_get_uint8(x_1432, sizeof(void*)*1);
if (x_1433 == 0)
{
lean_object* x_1434; 
lean_dec_ref(x_1372);
lean_dec(x_972);
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
if (lean_is_scalar(x_1371)) {
 x_1434 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1434 = x_1371;
}
lean_ctor_set(x_1434, 0, x_1370);
return x_1434;
}
else
{
lean_object* x_1435; uint8_t x_1436; 
lean_dec(x_1371);
lean_inc(x_2);
x_1435 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_10);
x_1436 = !lean_is_exclusive(x_1435);
if (x_1436 == 0)
{
lean_object* x_1437; lean_object* x_1438; uint8_t x_1439; 
x_1437 = lean_ctor_get(x_1435, 0);
x_1438 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1439 = lean_unbox(x_1437);
if (x_1439 == 0)
{
lean_object* x_1440; uint8_t x_1441; 
x_1440 = l_Lean_trace_profiler;
x_1441 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1432, x_1440);
if (x_1441 == 0)
{
lean_dec(x_1437);
lean_dec_ref(x_1372);
lean_dec(x_972);
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
lean_ctor_set_tag(x_1435, 1);
lean_ctor_set(x_1435, 0, x_1370);
return x_1435;
}
else
{
uint8_t x_1442; 
lean_free_object(x_1435);
x_1442 = lean_unbox(x_1437);
lean_dec(x_1437);
lean_inc_ref(x_1432);
x_1373 = lean_box(0);
x_1374 = x_1442;
x_1375 = x_1432;
x_1376 = x_1438;
x_1377 = x_1433;
goto block_1430;
}
}
else
{
uint8_t x_1443; 
lean_free_object(x_1435);
x_1443 = lean_unbox(x_1437);
lean_dec(x_1437);
lean_inc_ref(x_1432);
x_1373 = lean_box(0);
x_1374 = x_1443;
x_1375 = x_1432;
x_1376 = x_1438;
x_1377 = x_1433;
goto block_1430;
}
}
else
{
lean_object* x_1444; lean_object* x_1445; uint8_t x_1446; 
x_1444 = lean_ctor_get(x_1435, 0);
lean_inc(x_1444);
lean_dec(x_1435);
x_1445 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1446 = lean_unbox(x_1444);
if (x_1446 == 0)
{
lean_object* x_1447; uint8_t x_1448; 
x_1447 = l_Lean_trace_profiler;
x_1448 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1432, x_1447);
if (x_1448 == 0)
{
lean_object* x_1449; 
lean_dec(x_1444);
lean_dec_ref(x_1372);
lean_dec(x_972);
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
x_1449 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1449, 0, x_1370);
return x_1449;
}
else
{
uint8_t x_1450; 
x_1450 = lean_unbox(x_1444);
lean_dec(x_1444);
lean_inc_ref(x_1432);
x_1373 = lean_box(0);
x_1374 = x_1450;
x_1375 = x_1432;
x_1376 = x_1445;
x_1377 = x_1433;
goto block_1430;
}
}
else
{
uint8_t x_1451; 
x_1451 = lean_unbox(x_1444);
lean_dec(x_1444);
lean_inc_ref(x_1432);
x_1373 = lean_box(0);
x_1374 = x_1451;
x_1375 = x_1432;
x_1376 = x_1445;
x_1377 = x_1433;
goto block_1430;
}
}
}
}
else
{
lean_object* x_1452; 
lean_dec_ref(x_1372);
lean_dec(x_972);
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
if (lean_is_scalar(x_1371)) {
 x_1452 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1452 = x_1371;
}
lean_ctor_set(x_1452, 0, x_1370);
return x_1452;
}
}
}
block_265:
{
lean_object* x_254; double x_255; double x_256; double x_257; double x_258; double x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_254 = lean_io_mono_nanos_now();
x_255 = lean_float_of_nat(x_238);
x_256 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_257 = lean_float_div(x_255, x_256);
x_258 = lean_float_of_nat(x_254);
x_259 = lean_float_div(x_258, x_256);
x_260 = lean_box_float(x_257);
x_261 = lean_box_float(x_259);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_252);
lean_ctor_set(x_263, 1, x_262);
lean_inc(x_248);
lean_inc_ref(x_247);
lean_inc(x_239);
lean_inc_ref(x_251);
lean_inc_ref(x_241);
lean_inc(x_2);
x_264 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_245, x_241, x_250, x_244, x_242, x_237, x_263, x_251, x_239, x_247, x_248);
x_145 = x_239;
x_146 = x_240;
x_147 = x_241;
x_148 = x_248;
x_149 = x_247;
x_150 = x_243;
x_151 = x_249;
x_152 = x_251;
x_153 = x_250;
x_154 = x_245;
x_155 = x_246;
x_156 = x_264;
goto block_159;
}
block_290:
{
lean_object* x_282; double x_283; double x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_282 = lean_io_get_num_heartbeats();
x_283 = lean_float_of_nat(x_272);
x_284 = lean_float_of_nat(x_282);
x_285 = lean_box_float(x_283);
x_286 = lean_box_float(x_284);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_280);
lean_ctor_set(x_288, 1, x_287);
lean_inc(x_276);
lean_inc_ref(x_275);
lean_inc(x_266);
lean_inc_ref(x_279);
lean_inc_ref(x_268);
lean_inc(x_2);
x_289 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_273, x_268, x_278, x_271, x_269, x_237, x_288, x_279, x_266, x_275, x_276);
x_145 = x_266;
x_146 = x_267;
x_147 = x_268;
x_148 = x_276;
x_149 = x_275;
x_150 = x_270;
x_151 = x_277;
x_152 = x_279;
x_153 = x_278;
x_154 = x_273;
x_155 = x_274;
x_156 = x_289;
goto block_159;
}
block_327:
{
lean_object* x_308; 
x_308 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_304);
if (x_292 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
lean_dec_ref(x_308);
x_310 = lean_io_mono_nanos_now();
lean_inc(x_304);
lean_inc_ref(x_303);
lean_inc(x_291);
lean_inc_ref(x_307);
lean_inc(x_2);
x_311 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_302, x_300, x_295, x_307, x_291, x_303, x_304);
if (lean_obj_tag(x_311) == 0)
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_311);
if (x_312 == 0)
{
lean_ctor_set_tag(x_311, 1);
x_238 = x_310;
x_239 = x_291;
x_240 = x_293;
x_241 = x_294;
x_242 = x_309;
x_243 = x_296;
x_244 = x_297;
x_245 = x_298;
x_246 = x_299;
x_247 = x_303;
x_248 = x_304;
x_249 = x_305;
x_250 = x_306;
x_251 = x_307;
x_252 = x_311;
x_253 = lean_box(0);
goto block_265;
}
else
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_311, 0);
lean_inc(x_313);
lean_dec(x_311);
x_314 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_314, 0, x_313);
x_238 = x_310;
x_239 = x_291;
x_240 = x_293;
x_241 = x_294;
x_242 = x_309;
x_243 = x_296;
x_244 = x_297;
x_245 = x_298;
x_246 = x_299;
x_247 = x_303;
x_248 = x_304;
x_249 = x_305;
x_250 = x_306;
x_251 = x_307;
x_252 = x_314;
x_253 = lean_box(0);
goto block_265;
}
}
else
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_311);
if (x_315 == 0)
{
lean_ctor_set_tag(x_311, 0);
x_238 = x_310;
x_239 = x_291;
x_240 = x_293;
x_241 = x_294;
x_242 = x_309;
x_243 = x_296;
x_244 = x_297;
x_245 = x_298;
x_246 = x_299;
x_247 = x_303;
x_248 = x_304;
x_249 = x_305;
x_250 = x_306;
x_251 = x_307;
x_252 = x_311;
x_253 = lean_box(0);
goto block_265;
}
else
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_311, 0);
lean_inc(x_316);
lean_dec(x_311);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
x_238 = x_310;
x_239 = x_291;
x_240 = x_293;
x_241 = x_294;
x_242 = x_309;
x_243 = x_296;
x_244 = x_297;
x_245 = x_298;
x_246 = x_299;
x_247 = x_303;
x_248 = x_304;
x_249 = x_305;
x_250 = x_306;
x_251 = x_307;
x_252 = x_317;
x_253 = lean_box(0);
goto block_265;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_308, 0);
lean_inc(x_318);
lean_dec_ref(x_308);
x_319 = lean_io_get_num_heartbeats();
lean_inc(x_304);
lean_inc_ref(x_303);
lean_inc(x_291);
lean_inc_ref(x_307);
lean_inc(x_2);
x_320 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_302, x_300, x_295, x_307, x_291, x_303, x_304);
if (lean_obj_tag(x_320) == 0)
{
uint8_t x_321; 
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
lean_ctor_set_tag(x_320, 1);
x_266 = x_291;
x_267 = x_293;
x_268 = x_294;
x_269 = x_318;
x_270 = x_296;
x_271 = x_297;
x_272 = x_319;
x_273 = x_298;
x_274 = x_299;
x_275 = x_303;
x_276 = x_304;
x_277 = x_305;
x_278 = x_306;
x_279 = x_307;
x_280 = x_320;
x_281 = lean_box(0);
goto block_290;
}
else
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_320, 0);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_322);
x_266 = x_291;
x_267 = x_293;
x_268 = x_294;
x_269 = x_318;
x_270 = x_296;
x_271 = x_297;
x_272 = x_319;
x_273 = x_298;
x_274 = x_299;
x_275 = x_303;
x_276 = x_304;
x_277 = x_305;
x_278 = x_306;
x_279 = x_307;
x_280 = x_323;
x_281 = lean_box(0);
goto block_290;
}
}
else
{
uint8_t x_324; 
x_324 = !lean_is_exclusive(x_320);
if (x_324 == 0)
{
lean_ctor_set_tag(x_320, 0);
x_266 = x_291;
x_267 = x_293;
x_268 = x_294;
x_269 = x_318;
x_270 = x_296;
x_271 = x_297;
x_272 = x_319;
x_273 = x_298;
x_274 = x_299;
x_275 = x_303;
x_276 = x_304;
x_277 = x_305;
x_278 = x_306;
x_279 = x_307;
x_280 = x_320;
x_281 = lean_box(0);
goto block_290;
}
else
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_320, 0);
lean_inc(x_325);
lean_dec(x_320);
x_326 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_266 = x_291;
x_267 = x_293;
x_268 = x_294;
x_269 = x_318;
x_270 = x_296;
x_271 = x_297;
x_272 = x_319;
x_273 = x_298;
x_274 = x_299;
x_275 = x_303;
x_276 = x_304;
x_277 = x_305;
x_278 = x_306;
x_279 = x_307;
x_280 = x_326;
x_281 = lean_box(0);
goto block_290;
}
}
}
}
block_356:
{
lean_object* x_345; double x_346; double x_347; double x_348; double x_349; double x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_345 = lean_io_mono_nanos_now();
x_346 = lean_float_of_nat(x_332);
x_347 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_348 = lean_float_div(x_346, x_347);
x_349 = lean_float_of_nat(x_345);
x_350 = lean_float_div(x_349, x_347);
x_351 = lean_box_float(x_348);
x_352 = lean_box_float(x_350);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_343);
lean_ctor_set(x_354, 1, x_353);
lean_inc(x_337);
lean_inc_ref(x_336);
lean_inc(x_329);
lean_inc_ref(x_341);
lean_inc_ref(x_330);
lean_inc(x_2);
x_355 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_333, x_330, x_340, x_335, x_342, x_328, x_354, x_341, x_329, x_336, x_337);
x_215 = x_329;
x_216 = x_330;
x_217 = x_337;
x_218 = x_336;
x_219 = x_338;
x_220 = x_331;
x_221 = x_339;
x_222 = x_341;
x_223 = x_340;
x_224 = x_333;
x_225 = x_334;
x_226 = x_355;
goto block_229;
}
block_381:
{
lean_object* x_373; double x_374; double x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_373 = lean_io_get_num_heartbeats();
x_374 = lean_float_of_nat(x_363);
x_375 = lean_float_of_nat(x_373);
x_376 = lean_box_float(x_374);
x_377 = lean_box_float(x_375);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_371);
lean_ctor_set(x_379, 1, x_378);
lean_inc(x_365);
lean_inc_ref(x_364);
lean_inc(x_357);
lean_inc_ref(x_369);
lean_inc_ref(x_358);
lean_inc(x_2);
x_380 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_360, x_358, x_368, x_362, x_370, x_328, x_379, x_369, x_357, x_364, x_365);
x_215 = x_357;
x_216 = x_358;
x_217 = x_365;
x_218 = x_364;
x_219 = x_366;
x_220 = x_359;
x_221 = x_367;
x_222 = x_369;
x_223 = x_368;
x_224 = x_360;
x_225 = x_361;
x_226 = x_380;
goto block_229;
}
block_418:
{
lean_object* x_399; 
x_399 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_393);
if (x_384 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
lean_dec_ref(x_399);
x_401 = lean_io_mono_nanos_now();
lean_inc(x_393);
lean_inc_ref(x_392);
lean_inc(x_383);
lean_inc_ref(x_398);
lean_inc(x_2);
x_402 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_386, x_391, x_395, x_398, x_383, x_392, x_393);
if (lean_obj_tag(x_402) == 0)
{
uint8_t x_403; 
x_403 = !lean_is_exclusive(x_402);
if (x_403 == 0)
{
lean_ctor_set_tag(x_402, 1);
x_329 = x_383;
x_330 = x_385;
x_331 = x_387;
x_332 = x_401;
x_333 = x_388;
x_334 = x_389;
x_335 = x_390;
x_336 = x_392;
x_337 = x_393;
x_338 = x_394;
x_339 = x_396;
x_340 = x_397;
x_341 = x_398;
x_342 = x_400;
x_343 = x_402;
x_344 = lean_box(0);
goto block_356;
}
else
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_402, 0);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_404);
x_329 = x_383;
x_330 = x_385;
x_331 = x_387;
x_332 = x_401;
x_333 = x_388;
x_334 = x_389;
x_335 = x_390;
x_336 = x_392;
x_337 = x_393;
x_338 = x_394;
x_339 = x_396;
x_340 = x_397;
x_341 = x_398;
x_342 = x_400;
x_343 = x_405;
x_344 = lean_box(0);
goto block_356;
}
}
else
{
uint8_t x_406; 
x_406 = !lean_is_exclusive(x_402);
if (x_406 == 0)
{
lean_ctor_set_tag(x_402, 0);
x_329 = x_383;
x_330 = x_385;
x_331 = x_387;
x_332 = x_401;
x_333 = x_388;
x_334 = x_389;
x_335 = x_390;
x_336 = x_392;
x_337 = x_393;
x_338 = x_394;
x_339 = x_396;
x_340 = x_397;
x_341 = x_398;
x_342 = x_400;
x_343 = x_402;
x_344 = lean_box(0);
goto block_356;
}
else
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_ctor_get(x_402, 0);
lean_inc(x_407);
lean_dec(x_402);
x_408 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_408, 0, x_407);
x_329 = x_383;
x_330 = x_385;
x_331 = x_387;
x_332 = x_401;
x_333 = x_388;
x_334 = x_389;
x_335 = x_390;
x_336 = x_392;
x_337 = x_393;
x_338 = x_394;
x_339 = x_396;
x_340 = x_397;
x_341 = x_398;
x_342 = x_400;
x_343 = x_408;
x_344 = lean_box(0);
goto block_356;
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_399, 0);
lean_inc(x_409);
lean_dec_ref(x_399);
x_410 = lean_io_get_num_heartbeats();
lean_inc(x_393);
lean_inc_ref(x_392);
lean_inc(x_383);
lean_inc_ref(x_398);
lean_inc(x_2);
x_411 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_386, x_391, x_395, x_398, x_383, x_392, x_393);
if (lean_obj_tag(x_411) == 0)
{
uint8_t x_412; 
x_412 = !lean_is_exclusive(x_411);
if (x_412 == 0)
{
lean_ctor_set_tag(x_411, 1);
x_357 = x_383;
x_358 = x_385;
x_359 = x_387;
x_360 = x_388;
x_361 = x_389;
x_362 = x_390;
x_363 = x_410;
x_364 = x_392;
x_365 = x_393;
x_366 = x_394;
x_367 = x_396;
x_368 = x_397;
x_369 = x_398;
x_370 = x_409;
x_371 = x_411;
x_372 = lean_box(0);
goto block_381;
}
else
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_411, 0);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_414, 0, x_413);
x_357 = x_383;
x_358 = x_385;
x_359 = x_387;
x_360 = x_388;
x_361 = x_389;
x_362 = x_390;
x_363 = x_410;
x_364 = x_392;
x_365 = x_393;
x_366 = x_394;
x_367 = x_396;
x_368 = x_397;
x_369 = x_398;
x_370 = x_409;
x_371 = x_414;
x_372 = lean_box(0);
goto block_381;
}
}
else
{
uint8_t x_415; 
x_415 = !lean_is_exclusive(x_411);
if (x_415 == 0)
{
lean_ctor_set_tag(x_411, 0);
x_357 = x_383;
x_358 = x_385;
x_359 = x_387;
x_360 = x_388;
x_361 = x_389;
x_362 = x_390;
x_363 = x_410;
x_364 = x_392;
x_365 = x_393;
x_366 = x_394;
x_367 = x_396;
x_368 = x_397;
x_369 = x_398;
x_370 = x_409;
x_371 = x_411;
x_372 = lean_box(0);
goto block_381;
}
else
{
lean_object* x_416; lean_object* x_417; 
x_416 = lean_ctor_get(x_411, 0);
lean_inc(x_416);
lean_dec(x_411);
x_417 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_417, 0, x_416);
x_357 = x_383;
x_358 = x_385;
x_359 = x_387;
x_360 = x_388;
x_361 = x_389;
x_362 = x_390;
x_363 = x_410;
x_364 = x_392;
x_365 = x_393;
x_366 = x_394;
x_367 = x_396;
x_368 = x_397;
x_369 = x_398;
x_370 = x_409;
x_371 = x_417;
x_372 = lean_box(0);
goto block_381;
}
}
}
}
block_444:
{
lean_object* x_436; double x_437; double x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_436 = lean_io_get_num_heartbeats();
x_437 = lean_float_of_nat(x_423);
x_438 = lean_float_of_nat(x_436);
x_439 = lean_box_float(x_437);
x_440 = lean_box_float(x_438);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_434);
lean_ctor_set(x_442, 1, x_441);
lean_inc(x_429);
lean_inc_ref(x_428);
lean_inc(x_420);
lean_inc_ref(x_433);
lean_inc_ref(x_421);
lean_inc(x_2);
x_443 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_424, x_421, x_432, x_427, x_425, x_419, x_442, x_433, x_420, x_428, x_429);
x_215 = x_420;
x_216 = x_421;
x_217 = x_429;
x_218 = x_428;
x_219 = x_430;
x_220 = x_422;
x_221 = x_431;
x_222 = x_433;
x_223 = x_432;
x_224 = x_424;
x_225 = x_426;
x_226 = x_443;
goto block_229;
}
block_472:
{
lean_object* x_461; double x_462; double x_463; double x_464; double x_465; double x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_461 = lean_io_mono_nanos_now();
x_462 = lean_float_of_nat(x_451);
x_463 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_464 = lean_float_div(x_462, x_463);
x_465 = lean_float_of_nat(x_461);
x_466 = lean_float_div(x_465, x_463);
x_467 = lean_box_float(x_464);
x_468 = lean_box_float(x_466);
x_469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
x_470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_470, 0, x_459);
lean_ctor_set(x_470, 1, x_469);
lean_inc(x_454);
lean_inc_ref(x_453);
lean_inc(x_445);
lean_inc_ref(x_458);
lean_inc_ref(x_446);
lean_inc(x_2);
x_471 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_448, x_446, x_457, x_452, x_449, x_419, x_470, x_458, x_445, x_453, x_454);
x_215 = x_445;
x_216 = x_446;
x_217 = x_454;
x_218 = x_453;
x_219 = x_455;
x_220 = x_447;
x_221 = x_456;
x_222 = x_458;
x_223 = x_457;
x_224 = x_448;
x_225 = x_450;
x_226 = x_471;
goto block_229;
}
block_497:
{
lean_object* x_489; double x_490; double x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_489 = lean_io_get_num_heartbeats();
x_490 = lean_float_of_nat(x_477);
x_491 = lean_float_of_nat(x_489);
x_492 = lean_box_float(x_490);
x_493 = lean_box_float(x_491);
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_487);
lean_ctor_set(x_495, 1, x_494);
lean_inc(x_481);
lean_inc_ref(x_480);
lean_inc(x_473);
lean_inc_ref(x_485);
lean_inc_ref(x_474);
lean_inc(x_2);
x_496 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_478, x_474, x_484, x_476, x_486, x_237, x_495, x_485, x_473, x_480, x_481);
x_215 = x_473;
x_216 = x_474;
x_217 = x_481;
x_218 = x_480;
x_219 = x_482;
x_220 = x_475;
x_221 = x_483;
x_222 = x_485;
x_223 = x_484;
x_224 = x_478;
x_225 = x_479;
x_226 = x_496;
goto block_229;
}
block_525:
{
lean_object* x_514; double x_515; double x_516; double x_517; double x_518; double x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_514 = lean_io_mono_nanos_now();
x_515 = lean_float_of_nat(x_508);
x_516 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_517 = lean_float_div(x_515, x_516);
x_518 = lean_float_of_nat(x_514);
x_519 = lean_float_div(x_518, x_516);
x_520 = lean_box_float(x_517);
x_521 = lean_box_float(x_519);
x_522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_522, 0, x_520);
lean_ctor_set(x_522, 1, x_521);
x_523 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_523, 0, x_512);
lean_ctor_set(x_523, 1, x_522);
lean_inc(x_505);
lean_inc_ref(x_504);
lean_inc(x_498);
lean_inc_ref(x_510);
lean_inc_ref(x_499);
lean_inc(x_2);
x_524 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_502, x_499, x_509, x_501, x_511, x_237, x_523, x_510, x_498, x_504, x_505);
x_215 = x_498;
x_216 = x_499;
x_217 = x_505;
x_218 = x_504;
x_219 = x_506;
x_220 = x_500;
x_221 = x_507;
x_222 = x_510;
x_223 = x_509;
x_224 = x_502;
x_225 = x_503;
x_226 = x_524;
goto block_229;
}
block_562:
{
lean_object* x_543; 
x_543 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_537);
if (x_528 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
lean_dec_ref(x_543);
x_545 = lean_io_mono_nanos_now();
lean_inc(x_537);
lean_inc_ref(x_536);
lean_inc(x_527);
lean_inc_ref(x_541);
lean_inc(x_2);
x_546 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_542, x_535, x_526, x_541, x_527, x_536, x_537);
if (lean_obj_tag(x_546) == 0)
{
uint8_t x_547; 
x_547 = !lean_is_exclusive(x_546);
if (x_547 == 0)
{
lean_ctor_set_tag(x_546, 1);
x_498 = x_527;
x_499 = x_529;
x_500 = x_530;
x_501 = x_532;
x_502 = x_533;
x_503 = x_534;
x_504 = x_536;
x_505 = x_537;
x_506 = x_538;
x_507 = x_539;
x_508 = x_545;
x_509 = x_540;
x_510 = x_541;
x_511 = x_544;
x_512 = x_546;
x_513 = lean_box(0);
goto block_525;
}
else
{
lean_object* x_548; lean_object* x_549; 
x_548 = lean_ctor_get(x_546, 0);
lean_inc(x_548);
lean_dec(x_546);
x_549 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_549, 0, x_548);
x_498 = x_527;
x_499 = x_529;
x_500 = x_530;
x_501 = x_532;
x_502 = x_533;
x_503 = x_534;
x_504 = x_536;
x_505 = x_537;
x_506 = x_538;
x_507 = x_539;
x_508 = x_545;
x_509 = x_540;
x_510 = x_541;
x_511 = x_544;
x_512 = x_549;
x_513 = lean_box(0);
goto block_525;
}
}
else
{
uint8_t x_550; 
x_550 = !lean_is_exclusive(x_546);
if (x_550 == 0)
{
lean_ctor_set_tag(x_546, 0);
x_498 = x_527;
x_499 = x_529;
x_500 = x_530;
x_501 = x_532;
x_502 = x_533;
x_503 = x_534;
x_504 = x_536;
x_505 = x_537;
x_506 = x_538;
x_507 = x_539;
x_508 = x_545;
x_509 = x_540;
x_510 = x_541;
x_511 = x_544;
x_512 = x_546;
x_513 = lean_box(0);
goto block_525;
}
else
{
lean_object* x_551; lean_object* x_552; 
x_551 = lean_ctor_get(x_546, 0);
lean_inc(x_551);
lean_dec(x_546);
x_552 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_552, 0, x_551);
x_498 = x_527;
x_499 = x_529;
x_500 = x_530;
x_501 = x_532;
x_502 = x_533;
x_503 = x_534;
x_504 = x_536;
x_505 = x_537;
x_506 = x_538;
x_507 = x_539;
x_508 = x_545;
x_509 = x_540;
x_510 = x_541;
x_511 = x_544;
x_512 = x_552;
x_513 = lean_box(0);
goto block_525;
}
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_543, 0);
lean_inc(x_553);
lean_dec_ref(x_543);
x_554 = lean_io_get_num_heartbeats();
lean_inc(x_537);
lean_inc_ref(x_536);
lean_inc(x_527);
lean_inc_ref(x_541);
lean_inc(x_2);
x_555 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_542, x_535, x_526, x_541, x_527, x_536, x_537);
if (lean_obj_tag(x_555) == 0)
{
uint8_t x_556; 
x_556 = !lean_is_exclusive(x_555);
if (x_556 == 0)
{
lean_ctor_set_tag(x_555, 1);
x_473 = x_527;
x_474 = x_529;
x_475 = x_530;
x_476 = x_532;
x_477 = x_554;
x_478 = x_533;
x_479 = x_534;
x_480 = x_536;
x_481 = x_537;
x_482 = x_538;
x_483 = x_539;
x_484 = x_540;
x_485 = x_541;
x_486 = x_553;
x_487 = x_555;
x_488 = lean_box(0);
goto block_497;
}
else
{
lean_object* x_557; lean_object* x_558; 
x_557 = lean_ctor_get(x_555, 0);
lean_inc(x_557);
lean_dec(x_555);
x_558 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_558, 0, x_557);
x_473 = x_527;
x_474 = x_529;
x_475 = x_530;
x_476 = x_532;
x_477 = x_554;
x_478 = x_533;
x_479 = x_534;
x_480 = x_536;
x_481 = x_537;
x_482 = x_538;
x_483 = x_539;
x_484 = x_540;
x_485 = x_541;
x_486 = x_553;
x_487 = x_558;
x_488 = lean_box(0);
goto block_497;
}
}
else
{
uint8_t x_559; 
x_559 = !lean_is_exclusive(x_555);
if (x_559 == 0)
{
lean_ctor_set_tag(x_555, 0);
x_473 = x_527;
x_474 = x_529;
x_475 = x_530;
x_476 = x_532;
x_477 = x_554;
x_478 = x_533;
x_479 = x_534;
x_480 = x_536;
x_481 = x_537;
x_482 = x_538;
x_483 = x_539;
x_484 = x_540;
x_485 = x_541;
x_486 = x_553;
x_487 = x_555;
x_488 = lean_box(0);
goto block_497;
}
else
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_ctor_get(x_555, 0);
lean_inc(x_560);
lean_dec(x_555);
x_561 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_561, 0, x_560);
x_473 = x_527;
x_474 = x_529;
x_475 = x_530;
x_476 = x_532;
x_477 = x_554;
x_478 = x_533;
x_479 = x_534;
x_480 = x_536;
x_481 = x_537;
x_482 = x_538;
x_483 = x_539;
x_484 = x_540;
x_485 = x_541;
x_486 = x_553;
x_487 = x_561;
x_488 = lean_box(0);
goto block_497;
}
}
}
}
block_590:
{
lean_object* x_579; double x_580; double x_581; double x_582; double x_583; double x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_579 = lean_io_mono_nanos_now();
x_580 = lean_float_of_nat(x_571);
x_581 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_582 = lean_float_div(x_580, x_581);
x_583 = lean_float_of_nat(x_579);
x_584 = lean_float_div(x_583, x_581);
x_585 = lean_box_float(x_582);
x_586 = lean_box_float(x_584);
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
x_588 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_588, 0, x_577);
lean_ctor_set(x_588, 1, x_587);
lean_inc(x_573);
lean_inc_ref(x_572);
lean_inc(x_563);
lean_inc_ref(x_576);
lean_inc_ref(x_566);
lean_inc(x_2);
x_589 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_568, x_566, x_575, x_564, x_570, x_419, x_588, x_576, x_563, x_572, x_573);
x_145 = x_563;
x_146 = x_565;
x_147 = x_566;
x_148 = x_573;
x_149 = x_572;
x_150 = x_567;
x_151 = x_574;
x_152 = x_576;
x_153 = x_575;
x_154 = x_568;
x_155 = x_569;
x_156 = x_589;
goto block_159;
}
block_615:
{
lean_object* x_607; double x_608; double x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_607 = lean_io_get_num_heartbeats();
x_608 = lean_float_of_nat(x_599);
x_609 = lean_float_of_nat(x_607);
x_610 = lean_box_float(x_608);
x_611 = lean_box_float(x_609);
x_612 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_612, 0, x_610);
lean_ctor_set(x_612, 1, x_611);
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_605);
lean_ctor_set(x_613, 1, x_612);
lean_inc(x_601);
lean_inc_ref(x_600);
lean_inc(x_591);
lean_inc_ref(x_604);
lean_inc_ref(x_594);
lean_inc(x_2);
x_614 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_596, x_594, x_603, x_592, x_598, x_419, x_613, x_604, x_591, x_600, x_601);
x_145 = x_591;
x_146 = x_593;
x_147 = x_594;
x_148 = x_601;
x_149 = x_600;
x_150 = x_595;
x_151 = x_602;
x_152 = x_604;
x_153 = x_603;
x_154 = x_596;
x_155 = x_597;
x_156 = x_614;
goto block_159;
}
block_643:
{
lean_object* x_632; double x_633; double x_634; double x_635; double x_636; double x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_632 = lean_io_mono_nanos_now();
x_633 = lean_float_of_nat(x_623);
x_634 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_635 = lean_float_div(x_633, x_634);
x_636 = lean_float_of_nat(x_632);
x_637 = lean_float_div(x_636, x_634);
x_638 = lean_box_float(x_635);
x_639 = lean_box_float(x_637);
x_640 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_630);
lean_ctor_set(x_641, 1, x_640);
lean_inc(x_625);
lean_inc_ref(x_624);
lean_inc(x_616);
lean_inc_ref(x_628);
lean_inc_ref(x_618);
lean_inc(x_2);
x_642 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_621, x_618, x_627, x_629, x_620, x_328, x_641, x_628, x_616, x_624, x_625);
x_145 = x_616;
x_146 = x_617;
x_147 = x_618;
x_148 = x_625;
x_149 = x_624;
x_150 = x_619;
x_151 = x_626;
x_152 = x_628;
x_153 = x_627;
x_154 = x_621;
x_155 = x_622;
x_156 = x_642;
goto block_159;
}
block_668:
{
lean_object* x_660; double x_661; double x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_660 = lean_io_get_num_heartbeats();
x_661 = lean_float_of_nat(x_651);
x_662 = lean_float_of_nat(x_660);
x_663 = lean_box_float(x_661);
x_664 = lean_box_float(x_662);
x_665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
x_666 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_666, 0, x_658);
lean_ctor_set(x_666, 1, x_665);
lean_inc(x_653);
lean_inc_ref(x_652);
lean_inc(x_644);
lean_inc_ref(x_656);
lean_inc_ref(x_646);
lean_inc(x_2);
x_667 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_649, x_646, x_655, x_657, x_648, x_328, x_666, x_656, x_644, x_652, x_653);
x_145 = x_644;
x_146 = x_645;
x_147 = x_646;
x_148 = x_653;
x_149 = x_652;
x_150 = x_647;
x_151 = x_654;
x_152 = x_656;
x_153 = x_655;
x_154 = x_649;
x_155 = x_650;
x_156 = x_667;
goto block_159;
}
block_705:
{
lean_object* x_686; 
x_686 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_681);
if (x_671 == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
lean_dec_ref(x_686);
x_688 = lean_io_mono_nanos_now();
lean_inc(x_681);
lean_inc_ref(x_680);
lean_inc(x_669);
lean_inc_ref(x_683);
lean_inc(x_2);
x_689 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_670, x_677, x_679, x_683, x_669, x_680, x_681);
if (lean_obj_tag(x_689) == 0)
{
uint8_t x_690; 
x_690 = !lean_is_exclusive(x_689);
if (x_690 == 0)
{
lean_ctor_set_tag(x_689, 1);
x_616 = x_669;
x_617 = x_672;
x_618 = x_673;
x_619 = x_674;
x_620 = x_687;
x_621 = x_675;
x_622 = x_676;
x_623 = x_688;
x_624 = x_680;
x_625 = x_681;
x_626 = x_682;
x_627 = x_684;
x_628 = x_683;
x_629 = x_685;
x_630 = x_689;
x_631 = lean_box(0);
goto block_643;
}
else
{
lean_object* x_691; lean_object* x_692; 
x_691 = lean_ctor_get(x_689, 0);
lean_inc(x_691);
lean_dec(x_689);
x_692 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_692, 0, x_691);
x_616 = x_669;
x_617 = x_672;
x_618 = x_673;
x_619 = x_674;
x_620 = x_687;
x_621 = x_675;
x_622 = x_676;
x_623 = x_688;
x_624 = x_680;
x_625 = x_681;
x_626 = x_682;
x_627 = x_684;
x_628 = x_683;
x_629 = x_685;
x_630 = x_692;
x_631 = lean_box(0);
goto block_643;
}
}
else
{
uint8_t x_693; 
x_693 = !lean_is_exclusive(x_689);
if (x_693 == 0)
{
lean_ctor_set_tag(x_689, 0);
x_616 = x_669;
x_617 = x_672;
x_618 = x_673;
x_619 = x_674;
x_620 = x_687;
x_621 = x_675;
x_622 = x_676;
x_623 = x_688;
x_624 = x_680;
x_625 = x_681;
x_626 = x_682;
x_627 = x_684;
x_628 = x_683;
x_629 = x_685;
x_630 = x_689;
x_631 = lean_box(0);
goto block_643;
}
else
{
lean_object* x_694; lean_object* x_695; 
x_694 = lean_ctor_get(x_689, 0);
lean_inc(x_694);
lean_dec(x_689);
x_695 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_695, 0, x_694);
x_616 = x_669;
x_617 = x_672;
x_618 = x_673;
x_619 = x_674;
x_620 = x_687;
x_621 = x_675;
x_622 = x_676;
x_623 = x_688;
x_624 = x_680;
x_625 = x_681;
x_626 = x_682;
x_627 = x_684;
x_628 = x_683;
x_629 = x_685;
x_630 = x_695;
x_631 = lean_box(0);
goto block_643;
}
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_696 = lean_ctor_get(x_686, 0);
lean_inc(x_696);
lean_dec_ref(x_686);
x_697 = lean_io_get_num_heartbeats();
lean_inc(x_681);
lean_inc_ref(x_680);
lean_inc(x_669);
lean_inc_ref(x_683);
lean_inc(x_2);
x_698 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_670, x_677, x_679, x_683, x_669, x_680, x_681);
if (lean_obj_tag(x_698) == 0)
{
uint8_t x_699; 
x_699 = !lean_is_exclusive(x_698);
if (x_699 == 0)
{
lean_ctor_set_tag(x_698, 1);
x_644 = x_669;
x_645 = x_672;
x_646 = x_673;
x_647 = x_674;
x_648 = x_696;
x_649 = x_675;
x_650 = x_676;
x_651 = x_697;
x_652 = x_680;
x_653 = x_681;
x_654 = x_682;
x_655 = x_684;
x_656 = x_683;
x_657 = x_685;
x_658 = x_698;
x_659 = lean_box(0);
goto block_668;
}
else
{
lean_object* x_700; lean_object* x_701; 
x_700 = lean_ctor_get(x_698, 0);
lean_inc(x_700);
lean_dec(x_698);
x_701 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_701, 0, x_700);
x_644 = x_669;
x_645 = x_672;
x_646 = x_673;
x_647 = x_674;
x_648 = x_696;
x_649 = x_675;
x_650 = x_676;
x_651 = x_697;
x_652 = x_680;
x_653 = x_681;
x_654 = x_682;
x_655 = x_684;
x_656 = x_683;
x_657 = x_685;
x_658 = x_701;
x_659 = lean_box(0);
goto block_668;
}
}
else
{
uint8_t x_702; 
x_702 = !lean_is_exclusive(x_698);
if (x_702 == 0)
{
lean_ctor_set_tag(x_698, 0);
x_644 = x_669;
x_645 = x_672;
x_646 = x_673;
x_647 = x_674;
x_648 = x_696;
x_649 = x_675;
x_650 = x_676;
x_651 = x_697;
x_652 = x_680;
x_653 = x_681;
x_654 = x_682;
x_655 = x_684;
x_656 = x_683;
x_657 = x_685;
x_658 = x_698;
x_659 = lean_box(0);
goto block_668;
}
else
{
lean_object* x_703; lean_object* x_704; 
x_703 = lean_ctor_get(x_698, 0);
lean_inc(x_703);
lean_dec(x_698);
x_704 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_704, 0, x_703);
x_644 = x_669;
x_645 = x_672;
x_646 = x_673;
x_647 = x_674;
x_648 = x_696;
x_649 = x_675;
x_650 = x_676;
x_651 = x_697;
x_652 = x_680;
x_653 = x_681;
x_654 = x_682;
x_655 = x_684;
x_656 = x_683;
x_657 = x_685;
x_658 = x_704;
x_659 = lean_box(0);
goto block_668;
}
}
}
}
block_729:
{
lean_object* x_718; double x_719; double x_720; double x_721; double x_722; double x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_718 = lean_io_mono_nanos_now();
x_719 = lean_float_of_nat(x_708);
x_720 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_721 = lean_float_div(x_719, x_720);
x_722 = lean_float_of_nat(x_718);
x_723 = lean_float_div(x_722, x_720);
x_724 = lean_box_float(x_721);
x_725 = lean_box_float(x_723);
x_726 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_726, 0, x_724);
lean_ctor_set(x_726, 1, x_725);
x_727 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_727, 0, x_716);
lean_ctor_set(x_727, 1, x_726);
x_728 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_715, x_713, x_711, x_707, x_712, x_328, x_727, x_706, x_709, x_710, x_714);
lean_dec_ref(x_711);
return x_728;
}
block_750:
{
lean_object* x_742; double x_743; double x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_742 = lean_io_get_num_heartbeats();
x_743 = lean_float_of_nat(x_735);
x_744 = lean_float_of_nat(x_742);
x_745 = lean_box_float(x_743);
x_746 = lean_box_float(x_744);
x_747 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_747, 0, x_745);
lean_ctor_set(x_747, 1, x_746);
x_748 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_748, 0, x_740);
lean_ctor_set(x_748, 1, x_747);
x_749 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_739, x_737, x_734, x_731, x_736, x_328, x_748, x_730, x_732, x_733, x_738);
lean_dec_ref(x_734);
return x_749;
}
block_783:
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; 
x_763 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_762);
x_764 = lean_ctor_get(x_763, 0);
lean_inc(x_764);
lean_dec_ref(x_763);
x_765 = l_Lean_trace_profiler_useHeartbeats;
x_766 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_757, x_765);
if (x_766 == 0)
{
lean_object* x_767; lean_object* x_768; 
x_767 = lean_io_mono_nanos_now();
lean_inc(x_762);
lean_inc_ref(x_756);
lean_inc(x_754);
lean_inc_ref(x_753);
lean_inc(x_2);
x_768 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_758, x_751, x_759, x_753, x_754, x_756, x_762);
if (lean_obj_tag(x_768) == 0)
{
uint8_t x_769; 
x_769 = !lean_is_exclusive(x_768);
if (x_769 == 0)
{
lean_ctor_set_tag(x_768, 1);
x_706 = x_753;
x_707 = x_752;
x_708 = x_767;
x_709 = x_754;
x_710 = x_756;
x_711 = x_757;
x_712 = x_764;
x_713 = x_760;
x_714 = x_762;
x_715 = x_761;
x_716 = x_768;
x_717 = lean_box(0);
goto block_729;
}
else
{
lean_object* x_770; lean_object* x_771; 
x_770 = lean_ctor_get(x_768, 0);
lean_inc(x_770);
lean_dec(x_768);
x_771 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_771, 0, x_770);
x_706 = x_753;
x_707 = x_752;
x_708 = x_767;
x_709 = x_754;
x_710 = x_756;
x_711 = x_757;
x_712 = x_764;
x_713 = x_760;
x_714 = x_762;
x_715 = x_761;
x_716 = x_771;
x_717 = lean_box(0);
goto block_729;
}
}
else
{
uint8_t x_772; 
x_772 = !lean_is_exclusive(x_768);
if (x_772 == 0)
{
lean_ctor_set_tag(x_768, 0);
x_706 = x_753;
x_707 = x_752;
x_708 = x_767;
x_709 = x_754;
x_710 = x_756;
x_711 = x_757;
x_712 = x_764;
x_713 = x_760;
x_714 = x_762;
x_715 = x_761;
x_716 = x_768;
x_717 = lean_box(0);
goto block_729;
}
else
{
lean_object* x_773; lean_object* x_774; 
x_773 = lean_ctor_get(x_768, 0);
lean_inc(x_773);
lean_dec(x_768);
x_774 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_774, 0, x_773);
x_706 = x_753;
x_707 = x_752;
x_708 = x_767;
x_709 = x_754;
x_710 = x_756;
x_711 = x_757;
x_712 = x_764;
x_713 = x_760;
x_714 = x_762;
x_715 = x_761;
x_716 = x_774;
x_717 = lean_box(0);
goto block_729;
}
}
}
else
{
lean_object* x_775; lean_object* x_776; 
x_775 = lean_io_get_num_heartbeats();
lean_inc(x_762);
lean_inc_ref(x_756);
lean_inc(x_754);
lean_inc_ref(x_753);
lean_inc(x_2);
x_776 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_758, x_751, x_759, x_753, x_754, x_756, x_762);
if (lean_obj_tag(x_776) == 0)
{
uint8_t x_777; 
x_777 = !lean_is_exclusive(x_776);
if (x_777 == 0)
{
lean_ctor_set_tag(x_776, 1);
x_730 = x_753;
x_731 = x_752;
x_732 = x_754;
x_733 = x_756;
x_734 = x_757;
x_735 = x_775;
x_736 = x_764;
x_737 = x_760;
x_738 = x_762;
x_739 = x_761;
x_740 = x_776;
x_741 = lean_box(0);
goto block_750;
}
else
{
lean_object* x_778; lean_object* x_779; 
x_778 = lean_ctor_get(x_776, 0);
lean_inc(x_778);
lean_dec(x_776);
x_779 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_779, 0, x_778);
x_730 = x_753;
x_731 = x_752;
x_732 = x_754;
x_733 = x_756;
x_734 = x_757;
x_735 = x_775;
x_736 = x_764;
x_737 = x_760;
x_738 = x_762;
x_739 = x_761;
x_740 = x_779;
x_741 = lean_box(0);
goto block_750;
}
}
else
{
uint8_t x_780; 
x_780 = !lean_is_exclusive(x_776);
if (x_780 == 0)
{
lean_ctor_set_tag(x_776, 0);
x_730 = x_753;
x_731 = x_752;
x_732 = x_754;
x_733 = x_756;
x_734 = x_757;
x_735 = x_775;
x_736 = x_764;
x_737 = x_760;
x_738 = x_762;
x_739 = x_761;
x_740 = x_776;
x_741 = lean_box(0);
goto block_750;
}
else
{
lean_object* x_781; lean_object* x_782; 
x_781 = lean_ctor_get(x_776, 0);
lean_inc(x_781);
lean_dec(x_776);
x_782 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_782, 0, x_781);
x_730 = x_753;
x_731 = x_752;
x_732 = x_754;
x_733 = x_756;
x_734 = x_757;
x_735 = x_775;
x_736 = x_764;
x_737 = x_760;
x_738 = x_762;
x_739 = x_761;
x_740 = x_782;
x_741 = lean_box(0);
goto block_750;
}
}
}
}
block_804:
{
lean_object* x_796; double x_797; double x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_796 = lean_io_get_num_heartbeats();
x_797 = lean_float_of_nat(x_790);
x_798 = lean_float_of_nat(x_796);
x_799 = lean_box_float(x_797);
x_800 = lean_box_float(x_798);
x_801 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
x_802 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_802, 0, x_794);
lean_ctor_set(x_802, 1, x_801);
x_803 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_793, x_785, x_788, x_791, x_784, x_419, x_802, x_786, x_787, x_789, x_792);
lean_dec_ref(x_788);
return x_803;
}
block_828:
{
lean_object* x_817; double x_818; double x_819; double x_820; double x_821; double x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_817 = lean_io_mono_nanos_now();
x_818 = lean_float_of_nat(x_808);
x_819 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_820 = lean_float_div(x_818, x_819);
x_821 = lean_float_of_nat(x_817);
x_822 = lean_float_div(x_821, x_819);
x_823 = lean_box_float(x_820);
x_824 = lean_box_float(x_822);
x_825 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_825, 0, x_823);
lean_ctor_set(x_825, 1, x_824);
x_826 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_826, 0, x_815);
lean_ctor_set(x_826, 1, x_825);
x_827 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_814, x_806, x_810, x_812, x_805, x_419, x_826, x_807, x_809, x_811, x_813);
lean_dec_ref(x_810);
return x_827;
}
block_849:
{
lean_object* x_841; double x_842; double x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_841 = lean_io_get_num_heartbeats();
x_842 = lean_float_of_nat(x_830);
x_843 = lean_float_of_nat(x_841);
x_844 = lean_box_float(x_842);
x_845 = lean_box_float(x_843);
x_846 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_846, 0, x_844);
lean_ctor_set(x_846, 1, x_845);
x_847 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_847, 0, x_839);
lean_ctor_set(x_847, 1, x_846);
x_848 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_838, x_834, x_836, x_835, x_833, x_237, x_847, x_829, x_831, x_832, x_837);
lean_dec_ref(x_836);
return x_848;
}
block_873:
{
lean_object* x_862; double x_863; double x_864; double x_865; double x_866; double x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_862 = lean_io_mono_nanos_now();
x_863 = lean_float_of_nat(x_859);
x_864 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_865 = lean_float_div(x_863, x_864);
x_866 = lean_float_of_nat(x_862);
x_867 = lean_float_div(x_866, x_864);
x_868 = lean_box_float(x_865);
x_869 = lean_box_float(x_867);
x_870 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_870, 1, x_869);
x_871 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_871, 0, x_860);
lean_ctor_set(x_871, 1, x_870);
x_872 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_858, x_854, x_856, x_855, x_853, x_237, x_871, x_850, x_851, x_852, x_857);
lean_dec_ref(x_856);
return x_872;
}
block_906:
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; uint8_t x_889; 
x_886 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_885);
x_887 = lean_ctor_get(x_886, 0);
lean_inc(x_887);
lean_dec_ref(x_886);
x_888 = l_Lean_trace_profiler_useHeartbeats;
x_889 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_881, x_888);
if (x_889 == 0)
{
lean_object* x_890; lean_object* x_891; 
x_890 = lean_io_mono_nanos_now();
lean_inc(x_885);
lean_inc_ref(x_877);
lean_inc(x_876);
lean_inc_ref(x_875);
lean_inc(x_2);
x_891 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_879, x_874, x_883, x_875, x_876, x_877, x_885);
if (lean_obj_tag(x_891) == 0)
{
uint8_t x_892; 
x_892 = !lean_is_exclusive(x_891);
if (x_892 == 0)
{
lean_ctor_set_tag(x_891, 1);
x_850 = x_875;
x_851 = x_876;
x_852 = x_877;
x_853 = x_887;
x_854 = x_878;
x_855 = x_880;
x_856 = x_881;
x_857 = x_885;
x_858 = x_884;
x_859 = x_890;
x_860 = x_891;
x_861 = lean_box(0);
goto block_873;
}
else
{
lean_object* x_893; lean_object* x_894; 
x_893 = lean_ctor_get(x_891, 0);
lean_inc(x_893);
lean_dec(x_891);
x_894 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_894, 0, x_893);
x_850 = x_875;
x_851 = x_876;
x_852 = x_877;
x_853 = x_887;
x_854 = x_878;
x_855 = x_880;
x_856 = x_881;
x_857 = x_885;
x_858 = x_884;
x_859 = x_890;
x_860 = x_894;
x_861 = lean_box(0);
goto block_873;
}
}
else
{
uint8_t x_895; 
x_895 = !lean_is_exclusive(x_891);
if (x_895 == 0)
{
lean_ctor_set_tag(x_891, 0);
x_850 = x_875;
x_851 = x_876;
x_852 = x_877;
x_853 = x_887;
x_854 = x_878;
x_855 = x_880;
x_856 = x_881;
x_857 = x_885;
x_858 = x_884;
x_859 = x_890;
x_860 = x_891;
x_861 = lean_box(0);
goto block_873;
}
else
{
lean_object* x_896; lean_object* x_897; 
x_896 = lean_ctor_get(x_891, 0);
lean_inc(x_896);
lean_dec(x_891);
x_897 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_897, 0, x_896);
x_850 = x_875;
x_851 = x_876;
x_852 = x_877;
x_853 = x_887;
x_854 = x_878;
x_855 = x_880;
x_856 = x_881;
x_857 = x_885;
x_858 = x_884;
x_859 = x_890;
x_860 = x_897;
x_861 = lean_box(0);
goto block_873;
}
}
}
else
{
lean_object* x_898; lean_object* x_899; 
x_898 = lean_io_get_num_heartbeats();
lean_inc(x_885);
lean_inc_ref(x_877);
lean_inc(x_876);
lean_inc_ref(x_875);
lean_inc(x_2);
x_899 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_879, x_874, x_883, x_875, x_876, x_877, x_885);
if (lean_obj_tag(x_899) == 0)
{
uint8_t x_900; 
x_900 = !lean_is_exclusive(x_899);
if (x_900 == 0)
{
lean_ctor_set_tag(x_899, 1);
x_829 = x_875;
x_830 = x_898;
x_831 = x_876;
x_832 = x_877;
x_833 = x_887;
x_834 = x_878;
x_835 = x_880;
x_836 = x_881;
x_837 = x_885;
x_838 = x_884;
x_839 = x_899;
x_840 = lean_box(0);
goto block_849;
}
else
{
lean_object* x_901; lean_object* x_902; 
x_901 = lean_ctor_get(x_899, 0);
lean_inc(x_901);
lean_dec(x_899);
x_902 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_902, 0, x_901);
x_829 = x_875;
x_830 = x_898;
x_831 = x_876;
x_832 = x_877;
x_833 = x_887;
x_834 = x_878;
x_835 = x_880;
x_836 = x_881;
x_837 = x_885;
x_838 = x_884;
x_839 = x_902;
x_840 = lean_box(0);
goto block_849;
}
}
else
{
uint8_t x_903; 
x_903 = !lean_is_exclusive(x_899);
if (x_903 == 0)
{
lean_ctor_set_tag(x_899, 0);
x_829 = x_875;
x_830 = x_898;
x_831 = x_876;
x_832 = x_877;
x_833 = x_887;
x_834 = x_878;
x_835 = x_880;
x_836 = x_881;
x_837 = x_885;
x_838 = x_884;
x_839 = x_899;
x_840 = lean_box(0);
goto block_849;
}
else
{
lean_object* x_904; lean_object* x_905; 
x_904 = lean_ctor_get(x_899, 0);
lean_inc(x_904);
lean_dec(x_899);
x_905 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_905, 0, x_904);
x_829 = x_875;
x_830 = x_898;
x_831 = x_876;
x_832 = x_877;
x_833 = x_887;
x_834 = x_878;
x_835 = x_880;
x_836 = x_881;
x_837 = x_885;
x_838 = x_884;
x_839 = x_905;
x_840 = lean_box(0);
goto block_849;
}
}
}
}
block_970:
{
lean_object* x_918; uint8_t x_919; 
x_918 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_912);
x_919 = !lean_is_exclusive(x_918);
if (x_919 == 0)
{
lean_object* x_920; lean_object* x_921; uint8_t x_922; 
x_920 = lean_ctor_get(x_918, 0);
x_921 = l_Lean_trace_profiler_useHeartbeats;
x_922 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_914, x_921);
if (x_922 == 0)
{
lean_object* x_923; lean_object* x_924; double x_925; double x_926; double x_927; double x_928; double x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_923 = lean_io_mono_nanos_now();
x_924 = lean_io_mono_nanos_now();
lean_ctor_set_tag(x_918, 1);
lean_ctor_set(x_918, 0, x_916);
x_925 = lean_float_of_nat(x_923);
x_926 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_927 = lean_float_div(x_925, x_926);
x_928 = lean_float_of_nat(x_924);
x_929 = lean_float_div(x_928, x_926);
x_930 = lean_box_float(x_927);
x_931 = lean_box_float(x_929);
x_932 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_932, 0, x_930);
lean_ctor_set(x_932, 1, x_931);
x_933 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_933, 0, x_918);
lean_ctor_set(x_933, 1, x_932);
x_934 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_909, x_908, x_914, x_911, x_920, x_907, x_933, x_915, x_910, x_913, x_912);
lean_dec_ref(x_914);
return x_934;
}
else
{
lean_object* x_935; lean_object* x_936; double x_937; double x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; 
x_935 = lean_io_get_num_heartbeats();
x_936 = lean_io_get_num_heartbeats();
lean_ctor_set_tag(x_918, 1);
lean_ctor_set(x_918, 0, x_916);
x_937 = lean_float_of_nat(x_935);
x_938 = lean_float_of_nat(x_936);
x_939 = lean_box_float(x_937);
x_940 = lean_box_float(x_938);
x_941 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_941, 0, x_939);
lean_ctor_set(x_941, 1, x_940);
x_942 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_942, 0, x_918);
lean_ctor_set(x_942, 1, x_941);
x_943 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_909, x_908, x_914, x_911, x_920, x_907, x_942, x_915, x_910, x_913, x_912);
lean_dec_ref(x_914);
return x_943;
}
}
else
{
lean_object* x_944; lean_object* x_945; uint8_t x_946; 
x_944 = lean_ctor_get(x_918, 0);
lean_inc(x_944);
lean_dec(x_918);
x_945 = l_Lean_trace_profiler_useHeartbeats;
x_946 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_914, x_945);
if (x_946 == 0)
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; double x_950; double x_951; double x_952; double x_953; double x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; 
x_947 = lean_io_mono_nanos_now();
x_948 = lean_io_mono_nanos_now();
x_949 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_949, 0, x_916);
x_950 = lean_float_of_nat(x_947);
x_951 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_952 = lean_float_div(x_950, x_951);
x_953 = lean_float_of_nat(x_948);
x_954 = lean_float_div(x_953, x_951);
x_955 = lean_box_float(x_952);
x_956 = lean_box_float(x_954);
x_957 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_957, 0, x_955);
lean_ctor_set(x_957, 1, x_956);
x_958 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_958, 0, x_949);
lean_ctor_set(x_958, 1, x_957);
x_959 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_909, x_908, x_914, x_911, x_944, x_907, x_958, x_915, x_910, x_913, x_912);
lean_dec_ref(x_914);
return x_959;
}
else
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; double x_963; double x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_960 = lean_io_get_num_heartbeats();
x_961 = lean_io_get_num_heartbeats();
x_962 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_962, 0, x_916);
x_963 = lean_float_of_nat(x_960);
x_964 = lean_float_of_nat(x_961);
x_965 = lean_box_float(x_963);
x_966 = lean_box_float(x_964);
x_967 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_967, 0, x_965);
lean_ctor_set(x_967, 1, x_966);
x_968 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_968, 0, x_962);
lean_ctor_set(x_968, 1, x_967);
x_969 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_909, x_908, x_914, x_911, x_944, x_907, x_968, x_915, x_910, x_913, x_912);
lean_dec_ref(x_914);
return x_969;
}
}
}
block_1007:
{
lean_object* x_988; 
x_988 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_984);
if (x_975 == 0)
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; 
x_989 = lean_ctor_get(x_988, 0);
lean_inc(x_989);
lean_dec_ref(x_988);
x_990 = lean_io_mono_nanos_now();
lean_inc(x_984);
lean_inc_ref(x_983);
lean_inc(x_974);
lean_inc_ref(x_987);
lean_inc(x_2);
x_991 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_972, x_973, x_7, x_987, x_974, x_983, x_984);
if (lean_obj_tag(x_991) == 0)
{
uint8_t x_992; 
x_992 = !lean_is_exclusive(x_991);
if (x_992 == 0)
{
lean_ctor_set_tag(x_991, 1);
x_563 = x_974;
x_564 = x_976;
x_565 = x_977;
x_566 = x_978;
x_567 = x_979;
x_568 = x_980;
x_569 = x_981;
x_570 = x_989;
x_571 = x_990;
x_572 = x_983;
x_573 = x_984;
x_574 = x_985;
x_575 = x_986;
x_576 = x_987;
x_577 = x_991;
x_578 = lean_box(0);
goto block_590;
}
else
{
lean_object* x_993; lean_object* x_994; 
x_993 = lean_ctor_get(x_991, 0);
lean_inc(x_993);
lean_dec(x_991);
x_994 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_994, 0, x_993);
x_563 = x_974;
x_564 = x_976;
x_565 = x_977;
x_566 = x_978;
x_567 = x_979;
x_568 = x_980;
x_569 = x_981;
x_570 = x_989;
x_571 = x_990;
x_572 = x_983;
x_573 = x_984;
x_574 = x_985;
x_575 = x_986;
x_576 = x_987;
x_577 = x_994;
x_578 = lean_box(0);
goto block_590;
}
}
else
{
uint8_t x_995; 
x_995 = !lean_is_exclusive(x_991);
if (x_995 == 0)
{
lean_ctor_set_tag(x_991, 0);
x_563 = x_974;
x_564 = x_976;
x_565 = x_977;
x_566 = x_978;
x_567 = x_979;
x_568 = x_980;
x_569 = x_981;
x_570 = x_989;
x_571 = x_990;
x_572 = x_983;
x_573 = x_984;
x_574 = x_985;
x_575 = x_986;
x_576 = x_987;
x_577 = x_991;
x_578 = lean_box(0);
goto block_590;
}
else
{
lean_object* x_996; lean_object* x_997; 
x_996 = lean_ctor_get(x_991, 0);
lean_inc(x_996);
lean_dec(x_991);
x_997 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_997, 0, x_996);
x_563 = x_974;
x_564 = x_976;
x_565 = x_977;
x_566 = x_978;
x_567 = x_979;
x_568 = x_980;
x_569 = x_981;
x_570 = x_989;
x_571 = x_990;
x_572 = x_983;
x_573 = x_984;
x_574 = x_985;
x_575 = x_986;
x_576 = x_987;
x_577 = x_997;
x_578 = lean_box(0);
goto block_590;
}
}
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_998 = lean_ctor_get(x_988, 0);
lean_inc(x_998);
lean_dec_ref(x_988);
x_999 = lean_io_get_num_heartbeats();
lean_inc(x_984);
lean_inc_ref(x_983);
lean_inc(x_974);
lean_inc_ref(x_987);
lean_inc(x_2);
x_1000 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_972, x_973, x_7, x_987, x_974, x_983, x_984);
if (lean_obj_tag(x_1000) == 0)
{
uint8_t x_1001; 
x_1001 = !lean_is_exclusive(x_1000);
if (x_1001 == 0)
{
lean_ctor_set_tag(x_1000, 1);
x_591 = x_974;
x_592 = x_976;
x_593 = x_977;
x_594 = x_978;
x_595 = x_979;
x_596 = x_980;
x_597 = x_981;
x_598 = x_998;
x_599 = x_999;
x_600 = x_983;
x_601 = x_984;
x_602 = x_985;
x_603 = x_986;
x_604 = x_987;
x_605 = x_1000;
x_606 = lean_box(0);
goto block_615;
}
else
{
lean_object* x_1002; lean_object* x_1003; 
x_1002 = lean_ctor_get(x_1000, 0);
lean_inc(x_1002);
lean_dec(x_1000);
x_1003 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1003, 0, x_1002);
x_591 = x_974;
x_592 = x_976;
x_593 = x_977;
x_594 = x_978;
x_595 = x_979;
x_596 = x_980;
x_597 = x_981;
x_598 = x_998;
x_599 = x_999;
x_600 = x_983;
x_601 = x_984;
x_602 = x_985;
x_603 = x_986;
x_604 = x_987;
x_605 = x_1003;
x_606 = lean_box(0);
goto block_615;
}
}
else
{
uint8_t x_1004; 
x_1004 = !lean_is_exclusive(x_1000);
if (x_1004 == 0)
{
lean_ctor_set_tag(x_1000, 0);
x_591 = x_974;
x_592 = x_976;
x_593 = x_977;
x_594 = x_978;
x_595 = x_979;
x_596 = x_980;
x_597 = x_981;
x_598 = x_998;
x_599 = x_999;
x_600 = x_983;
x_601 = x_984;
x_602 = x_985;
x_603 = x_986;
x_604 = x_987;
x_605 = x_1000;
x_606 = lean_box(0);
goto block_615;
}
else
{
lean_object* x_1005; lean_object* x_1006; 
x_1005 = lean_ctor_get(x_1000, 0);
lean_inc(x_1005);
lean_dec(x_1000);
x_1006 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1006, 0, x_1005);
x_591 = x_974;
x_592 = x_976;
x_593 = x_977;
x_594 = x_978;
x_595 = x_979;
x_596 = x_980;
x_597 = x_981;
x_598 = x_998;
x_599 = x_999;
x_600 = x_983;
x_601 = x_984;
x_602 = x_985;
x_603 = x_986;
x_604 = x_987;
x_605 = x_1006;
x_606 = lean_box(0);
goto block_615;
}
}
}
}
block_1049:
{
if (x_1025 == 0)
{
lean_object* x_1026; 
lean_dec_ref(x_1008);
lean_inc(x_1020);
lean_inc_ref(x_1019);
lean_inc(x_1009);
lean_inc_ref(x_1024);
lean_inc(x_1018);
x_1026 = lean_apply_6(x_1023, x_1018, x_1024, x_1009, x_1019, x_1020, lean_box(0));
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; 
x_1027 = lean_ctor_get(x_1026, 0);
lean_inc(x_1027);
lean_dec_ref(x_1026);
if (lean_obj_tag(x_1027) == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; uint8_t x_1032; 
lean_inc(x_2);
x_1028 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1019);
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
lean_dec_ref(x_1028);
x_1030 = lean_nat_add(x_972, x_971);
lean_dec(x_972);
x_1031 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1031, 0, x_1018);
lean_ctor_set(x_1031, 1, x_7);
x_1032 = lean_unbox(x_1029);
if (x_1032 == 0)
{
lean_object* x_1033; uint8_t x_1034; 
x_1033 = l_Lean_trace_profiler;
x_1034 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1022, x_1033);
if (x_1034 == 0)
{
lean_object* x_1035; 
lean_dec(x_1029);
lean_inc(x_1020);
lean_inc_ref(x_1019);
lean_inc(x_1009);
lean_inc_ref(x_1024);
lean_inc(x_2);
x_1035 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1030, x_1017, x_1031, x_1024, x_1009, x_1019, x_1020);
x_145 = x_1009;
x_146 = x_1011;
x_147 = x_1012;
x_148 = x_1020;
x_149 = x_1019;
x_150 = x_1014;
x_151 = x_1021;
x_152 = x_1024;
x_153 = x_1022;
x_154 = x_1015;
x_155 = x_1016;
x_156 = x_1035;
goto block_159;
}
else
{
uint8_t x_1036; 
x_1036 = lean_unbox(x_1029);
lean_dec(x_1029);
x_669 = x_1009;
x_670 = x_1030;
x_671 = x_1010;
x_672 = x_1011;
x_673 = x_1012;
x_674 = x_1014;
x_675 = x_1015;
x_676 = x_1016;
x_677 = x_1017;
x_678 = lean_box(0);
x_679 = x_1031;
x_680 = x_1019;
x_681 = x_1020;
x_682 = x_1021;
x_683 = x_1024;
x_684 = x_1022;
x_685 = x_1036;
goto block_705;
}
}
else
{
uint8_t x_1037; 
x_1037 = lean_unbox(x_1029);
lean_dec(x_1029);
x_669 = x_1009;
x_670 = x_1030;
x_671 = x_1010;
x_672 = x_1011;
x_673 = x_1012;
x_674 = x_1014;
x_675 = x_1015;
x_676 = x_1016;
x_677 = x_1017;
x_678 = lean_box(0);
x_679 = x_1031;
x_680 = x_1019;
x_681 = x_1020;
x_682 = x_1021;
x_683 = x_1024;
x_684 = x_1022;
x_685 = x_1037;
goto block_705;
}
}
else
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; uint8_t x_1042; 
lean_dec(x_1018);
x_1038 = lean_ctor_get(x_1027, 0);
lean_inc(x_1038);
lean_dec_ref(x_1027);
lean_inc(x_2);
x_1039 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1019);
x_1040 = lean_ctor_get(x_1039, 0);
lean_inc(x_1040);
lean_dec_ref(x_1039);
x_1041 = l_List_appendTR___redArg(x_1038, x_1017);
x_1042 = lean_unbox(x_1040);
if (x_1042 == 0)
{
lean_object* x_1043; uint8_t x_1044; 
x_1043 = l_Lean_trace_profiler;
x_1044 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1022, x_1043);
if (x_1044 == 0)
{
lean_object* x_1045; 
lean_dec(x_1040);
lean_inc(x_1020);
lean_inc_ref(x_1019);
lean_inc(x_1009);
lean_inc_ref(x_1024);
lean_inc(x_2);
x_1045 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_972, x_1041, x_7, x_1024, x_1009, x_1019, x_1020);
x_145 = x_1009;
x_146 = x_1011;
x_147 = x_1012;
x_148 = x_1020;
x_149 = x_1019;
x_150 = x_1014;
x_151 = x_1021;
x_152 = x_1024;
x_153 = x_1022;
x_154 = x_1015;
x_155 = x_1016;
x_156 = x_1045;
goto block_159;
}
else
{
uint8_t x_1046; 
x_1046 = lean_unbox(x_1040);
lean_dec(x_1040);
x_973 = x_1041;
x_974 = x_1009;
x_975 = x_1010;
x_976 = x_1046;
x_977 = x_1011;
x_978 = x_1012;
x_979 = x_1014;
x_980 = x_1015;
x_981 = x_1016;
x_982 = lean_box(0);
x_983 = x_1019;
x_984 = x_1020;
x_985 = x_1021;
x_986 = x_1022;
x_987 = x_1024;
goto block_1007;
}
}
else
{
uint8_t x_1047; 
x_1047 = lean_unbox(x_1040);
lean_dec(x_1040);
x_973 = x_1041;
x_974 = x_1009;
x_975 = x_1010;
x_976 = x_1047;
x_977 = x_1011;
x_978 = x_1012;
x_979 = x_1014;
x_980 = x_1015;
x_981 = x_1016;
x_982 = lean_box(0);
x_983 = x_1019;
x_984 = x_1020;
x_985 = x_1021;
x_986 = x_1022;
x_987 = x_1024;
goto block_1007;
}
}
}
else
{
lean_object* x_1048; 
lean_dec(x_1018);
lean_dec(x_1017);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1048 = lean_ctor_get(x_1026, 0);
lean_inc(x_1048);
lean_dec_ref(x_1026);
x_130 = x_1009;
x_131 = x_1011;
x_132 = x_1012;
x_133 = x_1019;
x_134 = x_1020;
x_135 = x_1014;
x_136 = x_1021;
x_137 = x_1022;
x_138 = x_1024;
x_139 = x_1015;
x_140 = x_1016;
x_141 = x_1048;
x_142 = lean_box(0);
goto block_144;
}
}
else
{
lean_dec_ref(x_1023);
lean_dec(x_1018);
lean_dec(x_1017);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_130 = x_1009;
x_131 = x_1011;
x_132 = x_1012;
x_133 = x_1019;
x_134 = x_1020;
x_135 = x_1014;
x_136 = x_1021;
x_137 = x_1022;
x_138 = x_1024;
x_139 = x_1015;
x_140 = x_1016;
x_141 = x_1008;
x_142 = lean_box(0);
goto block_144;
}
}
block_1084:
{
lean_object* x_1065; 
x_1065 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1060);
if (x_1052 == 0)
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
lean_dec_ref(x_1065);
x_1067 = lean_io_mono_nanos_now();
lean_inc(x_1060);
lean_inc_ref(x_1059);
lean_inc(x_1051);
lean_inc_ref(x_1064);
lean_inc(x_2);
x_1068 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_972, x_1055, x_7, x_1064, x_1051, x_1059, x_1060);
if (lean_obj_tag(x_1068) == 0)
{
uint8_t x_1069; 
x_1069 = !lean_is_exclusive(x_1068);
if (x_1069 == 0)
{
lean_ctor_set_tag(x_1068, 1);
x_445 = x_1051;
x_446 = x_1053;
x_447 = x_1054;
x_448 = x_1056;
x_449 = x_1066;
x_450 = x_1057;
x_451 = x_1067;
x_452 = x_1058;
x_453 = x_1059;
x_454 = x_1060;
x_455 = x_1061;
x_456 = x_1062;
x_457 = x_1063;
x_458 = x_1064;
x_459 = x_1068;
x_460 = lean_box(0);
goto block_472;
}
else
{
lean_object* x_1070; lean_object* x_1071; 
x_1070 = lean_ctor_get(x_1068, 0);
lean_inc(x_1070);
lean_dec(x_1068);
x_1071 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1071, 0, x_1070);
x_445 = x_1051;
x_446 = x_1053;
x_447 = x_1054;
x_448 = x_1056;
x_449 = x_1066;
x_450 = x_1057;
x_451 = x_1067;
x_452 = x_1058;
x_453 = x_1059;
x_454 = x_1060;
x_455 = x_1061;
x_456 = x_1062;
x_457 = x_1063;
x_458 = x_1064;
x_459 = x_1071;
x_460 = lean_box(0);
goto block_472;
}
}
else
{
uint8_t x_1072; 
x_1072 = !lean_is_exclusive(x_1068);
if (x_1072 == 0)
{
lean_ctor_set_tag(x_1068, 0);
x_445 = x_1051;
x_446 = x_1053;
x_447 = x_1054;
x_448 = x_1056;
x_449 = x_1066;
x_450 = x_1057;
x_451 = x_1067;
x_452 = x_1058;
x_453 = x_1059;
x_454 = x_1060;
x_455 = x_1061;
x_456 = x_1062;
x_457 = x_1063;
x_458 = x_1064;
x_459 = x_1068;
x_460 = lean_box(0);
goto block_472;
}
else
{
lean_object* x_1073; lean_object* x_1074; 
x_1073 = lean_ctor_get(x_1068, 0);
lean_inc(x_1073);
lean_dec(x_1068);
x_1074 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1074, 0, x_1073);
x_445 = x_1051;
x_446 = x_1053;
x_447 = x_1054;
x_448 = x_1056;
x_449 = x_1066;
x_450 = x_1057;
x_451 = x_1067;
x_452 = x_1058;
x_453 = x_1059;
x_454 = x_1060;
x_455 = x_1061;
x_456 = x_1062;
x_457 = x_1063;
x_458 = x_1064;
x_459 = x_1074;
x_460 = lean_box(0);
goto block_472;
}
}
}
else
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
x_1075 = lean_ctor_get(x_1065, 0);
lean_inc(x_1075);
lean_dec_ref(x_1065);
x_1076 = lean_io_get_num_heartbeats();
lean_inc(x_1060);
lean_inc_ref(x_1059);
lean_inc(x_1051);
lean_inc_ref(x_1064);
lean_inc(x_2);
x_1077 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_972, x_1055, x_7, x_1064, x_1051, x_1059, x_1060);
if (lean_obj_tag(x_1077) == 0)
{
uint8_t x_1078; 
x_1078 = !lean_is_exclusive(x_1077);
if (x_1078 == 0)
{
lean_ctor_set_tag(x_1077, 1);
x_420 = x_1051;
x_421 = x_1053;
x_422 = x_1054;
x_423 = x_1076;
x_424 = x_1056;
x_425 = x_1075;
x_426 = x_1057;
x_427 = x_1058;
x_428 = x_1059;
x_429 = x_1060;
x_430 = x_1061;
x_431 = x_1062;
x_432 = x_1063;
x_433 = x_1064;
x_434 = x_1077;
x_435 = lean_box(0);
goto block_444;
}
else
{
lean_object* x_1079; lean_object* x_1080; 
x_1079 = lean_ctor_get(x_1077, 0);
lean_inc(x_1079);
lean_dec(x_1077);
x_1080 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1080, 0, x_1079);
x_420 = x_1051;
x_421 = x_1053;
x_422 = x_1054;
x_423 = x_1076;
x_424 = x_1056;
x_425 = x_1075;
x_426 = x_1057;
x_427 = x_1058;
x_428 = x_1059;
x_429 = x_1060;
x_430 = x_1061;
x_431 = x_1062;
x_432 = x_1063;
x_433 = x_1064;
x_434 = x_1080;
x_435 = lean_box(0);
goto block_444;
}
}
else
{
uint8_t x_1081; 
x_1081 = !lean_is_exclusive(x_1077);
if (x_1081 == 0)
{
lean_ctor_set_tag(x_1077, 0);
x_420 = x_1051;
x_421 = x_1053;
x_422 = x_1054;
x_423 = x_1076;
x_424 = x_1056;
x_425 = x_1075;
x_426 = x_1057;
x_427 = x_1058;
x_428 = x_1059;
x_429 = x_1060;
x_430 = x_1061;
x_431 = x_1062;
x_432 = x_1063;
x_433 = x_1064;
x_434 = x_1077;
x_435 = lean_box(0);
goto block_444;
}
else
{
lean_object* x_1082; lean_object* x_1083; 
x_1082 = lean_ctor_get(x_1077, 0);
lean_inc(x_1082);
lean_dec(x_1077);
x_1083 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1083, 0, x_1082);
x_420 = x_1051;
x_421 = x_1053;
x_422 = x_1054;
x_423 = x_1076;
x_424 = x_1056;
x_425 = x_1075;
x_426 = x_1057;
x_427 = x_1058;
x_428 = x_1059;
x_429 = x_1060;
x_430 = x_1061;
x_431 = x_1062;
x_432 = x_1063;
x_433 = x_1064;
x_434 = x_1083;
x_435 = lean_box(0);
goto block_444;
}
}
}
}
block_1126:
{
if (x_1102 == 0)
{
lean_object* x_1103; 
lean_dec_ref(x_1094);
lean_inc(x_1096);
lean_inc_ref(x_1095);
lean_inc(x_1085);
lean_inc_ref(x_1101);
lean_inc(x_1093);
x_1103 = lean_apply_6(x_1100, x_1093, x_1101, x_1085, x_1095, x_1096, lean_box(0));
if (lean_obj_tag(x_1103) == 0)
{
lean_object* x_1104; 
x_1104 = lean_ctor_get(x_1103, 0);
lean_inc(x_1104);
lean_dec_ref(x_1103);
if (lean_obj_tag(x_1104) == 0)
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; uint8_t x_1109; 
lean_inc(x_2);
x_1105 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1095);
x_1106 = lean_ctor_get(x_1105, 0);
lean_inc(x_1106);
lean_dec_ref(x_1105);
x_1107 = lean_nat_add(x_972, x_971);
lean_dec(x_972);
x_1108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1108, 0, x_1093);
lean_ctor_set(x_1108, 1, x_7);
x_1109 = lean_unbox(x_1106);
if (x_1109 == 0)
{
lean_object* x_1110; uint8_t x_1111; 
x_1110 = l_Lean_trace_profiler;
x_1111 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1099, x_1110);
if (x_1111 == 0)
{
lean_object* x_1112; 
lean_dec(x_1106);
lean_inc(x_1096);
lean_inc_ref(x_1095);
lean_inc(x_1085);
lean_inc_ref(x_1101);
lean_inc(x_2);
x_1112 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1107, x_1092, x_1108, x_1101, x_1085, x_1095, x_1096);
x_215 = x_1085;
x_216 = x_1087;
x_217 = x_1096;
x_218 = x_1095;
x_219 = x_1097;
x_220 = x_1089;
x_221 = x_1098;
x_222 = x_1101;
x_223 = x_1099;
x_224 = x_1090;
x_225 = x_1091;
x_226 = x_1112;
goto block_229;
}
else
{
uint8_t x_1113; 
x_1113 = lean_unbox(x_1106);
lean_dec(x_1106);
x_382 = lean_box(0);
x_383 = x_1085;
x_384 = x_1086;
x_385 = x_1087;
x_386 = x_1107;
x_387 = x_1089;
x_388 = x_1090;
x_389 = x_1091;
x_390 = x_1113;
x_391 = x_1092;
x_392 = x_1095;
x_393 = x_1096;
x_394 = x_1097;
x_395 = x_1108;
x_396 = x_1098;
x_397 = x_1099;
x_398 = x_1101;
goto block_418;
}
}
else
{
uint8_t x_1114; 
x_1114 = lean_unbox(x_1106);
lean_dec(x_1106);
x_382 = lean_box(0);
x_383 = x_1085;
x_384 = x_1086;
x_385 = x_1087;
x_386 = x_1107;
x_387 = x_1089;
x_388 = x_1090;
x_389 = x_1091;
x_390 = x_1114;
x_391 = x_1092;
x_392 = x_1095;
x_393 = x_1096;
x_394 = x_1097;
x_395 = x_1108;
x_396 = x_1098;
x_397 = x_1099;
x_398 = x_1101;
goto block_418;
}
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; uint8_t x_1119; 
lean_dec(x_1093);
x_1115 = lean_ctor_get(x_1104, 0);
lean_inc(x_1115);
lean_dec_ref(x_1104);
lean_inc(x_2);
x_1116 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1095);
x_1117 = lean_ctor_get(x_1116, 0);
lean_inc(x_1117);
lean_dec_ref(x_1116);
x_1118 = l_List_appendTR___redArg(x_1115, x_1092);
x_1119 = lean_unbox(x_1117);
if (x_1119 == 0)
{
lean_object* x_1120; uint8_t x_1121; 
x_1120 = l_Lean_trace_profiler;
x_1121 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1099, x_1120);
if (x_1121 == 0)
{
lean_object* x_1122; 
lean_dec(x_1117);
lean_inc(x_1096);
lean_inc_ref(x_1095);
lean_inc(x_1085);
lean_inc_ref(x_1101);
lean_inc(x_2);
x_1122 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_972, x_1118, x_7, x_1101, x_1085, x_1095, x_1096);
x_215 = x_1085;
x_216 = x_1087;
x_217 = x_1096;
x_218 = x_1095;
x_219 = x_1097;
x_220 = x_1089;
x_221 = x_1098;
x_222 = x_1101;
x_223 = x_1099;
x_224 = x_1090;
x_225 = x_1091;
x_226 = x_1122;
goto block_229;
}
else
{
uint8_t x_1123; 
x_1123 = lean_unbox(x_1117);
lean_dec(x_1117);
x_1050 = lean_box(0);
x_1051 = x_1085;
x_1052 = x_1086;
x_1053 = x_1087;
x_1054 = x_1089;
x_1055 = x_1118;
x_1056 = x_1090;
x_1057 = x_1091;
x_1058 = x_1123;
x_1059 = x_1095;
x_1060 = x_1096;
x_1061 = x_1097;
x_1062 = x_1098;
x_1063 = x_1099;
x_1064 = x_1101;
goto block_1084;
}
}
else
{
uint8_t x_1124; 
x_1124 = lean_unbox(x_1117);
lean_dec(x_1117);
x_1050 = lean_box(0);
x_1051 = x_1085;
x_1052 = x_1086;
x_1053 = x_1087;
x_1054 = x_1089;
x_1055 = x_1118;
x_1056 = x_1090;
x_1057 = x_1091;
x_1058 = x_1124;
x_1059 = x_1095;
x_1060 = x_1096;
x_1061 = x_1097;
x_1062 = x_1098;
x_1063 = x_1099;
x_1064 = x_1101;
goto block_1084;
}
}
}
else
{
lean_object* x_1125; 
lean_dec(x_1093);
lean_dec(x_1092);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1125 = lean_ctor_get(x_1103, 0);
lean_inc(x_1125);
lean_dec_ref(x_1103);
x_200 = x_1085;
x_201 = x_1087;
x_202 = x_1095;
x_203 = x_1096;
x_204 = x_1097;
x_205 = x_1089;
x_206 = x_1098;
x_207 = x_1099;
x_208 = x_1101;
x_209 = x_1090;
x_210 = x_1091;
x_211 = x_1125;
x_212 = lean_box(0);
goto block_214;
}
}
else
{
lean_dec_ref(x_1100);
lean_dec(x_1093);
lean_dec(x_1092);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_200 = x_1085;
x_201 = x_1087;
x_202 = x_1095;
x_203 = x_1096;
x_204 = x_1097;
x_205 = x_1089;
x_206 = x_1098;
x_207 = x_1099;
x_208 = x_1101;
x_209 = x_1090;
x_210 = x_1091;
x_211 = x_1094;
x_212 = lean_box(0);
goto block_214;
}
}
block_1187:
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; uint8_t x_1146; 
x_1143 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1137);
x_1144 = lean_ctor_get(x_1143, 0);
lean_inc(x_1144);
lean_dec_ref(x_1143);
x_1145 = l_Lean_trace_profiler_useHeartbeats;
x_1146 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1142, x_1145);
if (x_1146 == 0)
{
lean_object* x_1147; lean_object* x_1148; 
lean_dec_ref(x_1135);
x_1147 = lean_io_mono_nanos_now();
lean_inc(x_1137);
lean_inc_ref(x_1136);
lean_inc(x_1127);
lean_inc_ref(x_1141);
lean_inc(x_1134);
x_1148 = lean_apply_6(x_1133, x_1134, x_1141, x_1127, x_1136, x_1137, lean_box(0));
if (lean_obj_tag(x_1148) == 0)
{
lean_object* x_1149; uint8_t x_1150; 
x_1149 = lean_ctor_get(x_1148, 0);
lean_inc(x_1149);
lean_dec_ref(x_1148);
x_1150 = lean_unbox(x_1149);
lean_dec(x_1149);
if (x_1150 == 0)
{
lean_object* x_1151; 
lean_inc_ref(x_3);
lean_inc(x_1137);
lean_inc_ref(x_1136);
lean_inc(x_1127);
lean_inc_ref(x_1141);
lean_inc(x_1134);
x_1151 = lean_apply_7(x_3, x_1134, x_1131, x_1141, x_1127, x_1136, x_1137, lean_box(0));
if (lean_obj_tag(x_1151) == 0)
{
lean_object* x_1152; 
lean_dec_ref(x_1140);
lean_dec(x_1134);
lean_dec(x_1132);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1152 = lean_ctor_get(x_1151, 0);
lean_inc(x_1152);
lean_dec_ref(x_1151);
x_185 = x_1127;
x_186 = x_1128;
x_187 = x_1136;
x_188 = x_1137;
x_189 = x_1147;
x_190 = x_1129;
x_191 = x_1139;
x_192 = x_1142;
x_193 = x_1141;
x_194 = x_1130;
x_195 = x_1144;
x_196 = x_1152;
x_197 = lean_box(0);
goto block_199;
}
else
{
lean_object* x_1153; uint8_t x_1154; 
x_1153 = lean_ctor_get(x_1151, 0);
lean_inc(x_1153);
lean_dec_ref(x_1151);
x_1154 = l_Lean_Exception_isInterrupt(x_1153);
if (x_1154 == 0)
{
uint8_t x_1155; 
lean_inc(x_1153);
x_1155 = l_Lean_Exception_isRuntime(x_1153);
x_1085 = x_1127;
x_1086 = x_1146;
x_1087 = x_1128;
x_1088 = lean_box(0);
x_1089 = x_1129;
x_1090 = x_1130;
x_1091 = x_1144;
x_1092 = x_1132;
x_1093 = x_1134;
x_1094 = x_1153;
x_1095 = x_1136;
x_1096 = x_1137;
x_1097 = x_1147;
x_1098 = x_1139;
x_1099 = x_1142;
x_1100 = x_1140;
x_1101 = x_1141;
x_1102 = x_1155;
goto block_1126;
}
else
{
x_1085 = x_1127;
x_1086 = x_1146;
x_1087 = x_1128;
x_1088 = lean_box(0);
x_1089 = x_1129;
x_1090 = x_1130;
x_1091 = x_1144;
x_1092 = x_1132;
x_1093 = x_1134;
x_1094 = x_1153;
x_1095 = x_1136;
x_1096 = x_1137;
x_1097 = x_1147;
x_1098 = x_1139;
x_1099 = x_1142;
x_1100 = x_1140;
x_1101 = x_1141;
x_1102 = x_1154;
goto block_1126;
}
}
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; uint8_t x_1160; 
lean_dec_ref(x_1140);
lean_dec_ref(x_1131);
lean_inc(x_2);
x_1156 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1136);
x_1157 = lean_ctor_get(x_1156, 0);
lean_inc(x_1157);
lean_dec_ref(x_1156);
x_1158 = lean_nat_add(x_972, x_971);
lean_dec(x_972);
x_1159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1159, 0, x_1134);
lean_ctor_set(x_1159, 1, x_7);
x_1160 = lean_unbox(x_1157);
if (x_1160 == 0)
{
lean_object* x_1161; uint8_t x_1162; 
x_1161 = l_Lean_trace_profiler;
x_1162 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1142, x_1161);
if (x_1162 == 0)
{
lean_object* x_1163; 
lean_dec(x_1157);
lean_inc(x_1137);
lean_inc_ref(x_1136);
lean_inc(x_1127);
lean_inc_ref(x_1141);
lean_inc(x_2);
x_1163 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1158, x_1132, x_1159, x_1141, x_1127, x_1136, x_1137);
x_215 = x_1127;
x_216 = x_1128;
x_217 = x_1137;
x_218 = x_1136;
x_219 = x_1147;
x_220 = x_1129;
x_221 = x_1139;
x_222 = x_1141;
x_223 = x_1142;
x_224 = x_1130;
x_225 = x_1144;
x_226 = x_1163;
goto block_229;
}
else
{
uint8_t x_1164; 
x_1164 = lean_unbox(x_1157);
lean_dec(x_1157);
x_526 = x_1159;
x_527 = x_1127;
x_528 = x_1146;
x_529 = x_1128;
x_530 = x_1129;
x_531 = lean_box(0);
x_532 = x_1164;
x_533 = x_1130;
x_534 = x_1144;
x_535 = x_1132;
x_536 = x_1136;
x_537 = x_1137;
x_538 = x_1147;
x_539 = x_1139;
x_540 = x_1142;
x_541 = x_1141;
x_542 = x_1158;
goto block_562;
}
}
else
{
uint8_t x_1165; 
x_1165 = lean_unbox(x_1157);
lean_dec(x_1157);
x_526 = x_1159;
x_527 = x_1127;
x_528 = x_1146;
x_529 = x_1128;
x_530 = x_1129;
x_531 = lean_box(0);
x_532 = x_1165;
x_533 = x_1130;
x_534 = x_1144;
x_535 = x_1132;
x_536 = x_1136;
x_537 = x_1137;
x_538 = x_1147;
x_539 = x_1139;
x_540 = x_1142;
x_541 = x_1141;
x_542 = x_1158;
goto block_562;
}
}
}
else
{
lean_object* x_1166; 
lean_dec_ref(x_1140);
lean_dec(x_1134);
lean_dec(x_1132);
lean_dec_ref(x_1131);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1166 = lean_ctor_get(x_1148, 0);
lean_inc(x_1166);
lean_dec_ref(x_1148);
x_200 = x_1127;
x_201 = x_1128;
x_202 = x_1136;
x_203 = x_1137;
x_204 = x_1147;
x_205 = x_1129;
x_206 = x_1139;
x_207 = x_1142;
x_208 = x_1141;
x_209 = x_1130;
x_210 = x_1144;
x_211 = x_1166;
x_212 = lean_box(0);
goto block_214;
}
}
else
{
lean_object* x_1167; lean_object* x_1168; 
lean_dec_ref(x_1131);
x_1167 = lean_io_get_num_heartbeats();
lean_inc(x_1137);
lean_inc_ref(x_1136);
lean_inc(x_1127);
lean_inc_ref(x_1141);
lean_inc(x_1134);
x_1168 = lean_apply_6(x_1133, x_1134, x_1141, x_1127, x_1136, x_1137, lean_box(0));
if (lean_obj_tag(x_1168) == 0)
{
lean_object* x_1169; uint8_t x_1170; 
x_1169 = lean_ctor_get(x_1168, 0);
lean_inc(x_1169);
lean_dec_ref(x_1168);
x_1170 = lean_unbox(x_1169);
lean_dec(x_1169);
if (x_1170 == 0)
{
lean_object* x_1171; 
lean_inc_ref(x_3);
lean_inc(x_1137);
lean_inc_ref(x_1136);
lean_inc(x_1127);
lean_inc_ref(x_1141);
lean_inc(x_1134);
x_1171 = lean_apply_7(x_3, x_1134, x_1135, x_1141, x_1127, x_1136, x_1137, lean_box(0));
if (lean_obj_tag(x_1171) == 0)
{
lean_object* x_1172; 
lean_dec_ref(x_1140);
lean_dec(x_1134);
lean_dec(x_1132);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1172 = lean_ctor_get(x_1171, 0);
lean_inc(x_1172);
lean_dec_ref(x_1171);
x_115 = x_1127;
x_116 = x_1167;
x_117 = x_1128;
x_118 = x_1136;
x_119 = x_1137;
x_120 = x_1129;
x_121 = x_1139;
x_122 = x_1142;
x_123 = x_1141;
x_124 = x_1130;
x_125 = x_1144;
x_126 = x_1172;
x_127 = lean_box(0);
goto block_129;
}
else
{
lean_object* x_1173; uint8_t x_1174; 
x_1173 = lean_ctor_get(x_1171, 0);
lean_inc(x_1173);
lean_dec_ref(x_1171);
x_1174 = l_Lean_Exception_isInterrupt(x_1173);
if (x_1174 == 0)
{
uint8_t x_1175; 
lean_inc(x_1173);
x_1175 = l_Lean_Exception_isRuntime(x_1173);
x_1008 = x_1173;
x_1009 = x_1127;
x_1010 = x_1146;
x_1011 = x_1167;
x_1012 = x_1128;
x_1013 = lean_box(0);
x_1014 = x_1129;
x_1015 = x_1130;
x_1016 = x_1144;
x_1017 = x_1132;
x_1018 = x_1134;
x_1019 = x_1136;
x_1020 = x_1137;
x_1021 = x_1139;
x_1022 = x_1142;
x_1023 = x_1140;
x_1024 = x_1141;
x_1025 = x_1175;
goto block_1049;
}
else
{
x_1008 = x_1173;
x_1009 = x_1127;
x_1010 = x_1146;
x_1011 = x_1167;
x_1012 = x_1128;
x_1013 = lean_box(0);
x_1014 = x_1129;
x_1015 = x_1130;
x_1016 = x_1144;
x_1017 = x_1132;
x_1018 = x_1134;
x_1019 = x_1136;
x_1020 = x_1137;
x_1021 = x_1139;
x_1022 = x_1142;
x_1023 = x_1140;
x_1024 = x_1141;
x_1025 = x_1174;
goto block_1049;
}
}
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; uint8_t x_1180; 
lean_dec_ref(x_1140);
lean_dec_ref(x_1135);
lean_inc(x_2);
x_1176 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1136);
x_1177 = lean_ctor_get(x_1176, 0);
lean_inc(x_1177);
lean_dec_ref(x_1176);
x_1178 = lean_nat_add(x_972, x_971);
lean_dec(x_972);
x_1179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1179, 0, x_1134);
lean_ctor_set(x_1179, 1, x_7);
x_1180 = lean_unbox(x_1177);
if (x_1180 == 0)
{
lean_object* x_1181; uint8_t x_1182; 
x_1181 = l_Lean_trace_profiler;
x_1182 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1142, x_1181);
if (x_1182 == 0)
{
lean_object* x_1183; 
lean_dec(x_1177);
lean_inc(x_1137);
lean_inc_ref(x_1136);
lean_inc(x_1127);
lean_inc_ref(x_1141);
lean_inc(x_2);
x_1183 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1178, x_1132, x_1179, x_1141, x_1127, x_1136, x_1137);
x_145 = x_1127;
x_146 = x_1167;
x_147 = x_1128;
x_148 = x_1137;
x_149 = x_1136;
x_150 = x_1129;
x_151 = x_1139;
x_152 = x_1141;
x_153 = x_1142;
x_154 = x_1130;
x_155 = x_1144;
x_156 = x_1183;
goto block_159;
}
else
{
uint8_t x_1184; 
x_1184 = lean_unbox(x_1177);
lean_dec(x_1177);
x_291 = x_1127;
x_292 = x_1146;
x_293 = x_1167;
x_294 = x_1128;
x_295 = x_1179;
x_296 = x_1129;
x_297 = x_1184;
x_298 = x_1130;
x_299 = x_1144;
x_300 = x_1132;
x_301 = lean_box(0);
x_302 = x_1178;
x_303 = x_1136;
x_304 = x_1137;
x_305 = x_1139;
x_306 = x_1142;
x_307 = x_1141;
goto block_327;
}
}
else
{
uint8_t x_1185; 
x_1185 = lean_unbox(x_1177);
lean_dec(x_1177);
x_291 = x_1127;
x_292 = x_1146;
x_293 = x_1167;
x_294 = x_1128;
x_295 = x_1179;
x_296 = x_1129;
x_297 = x_1185;
x_298 = x_1130;
x_299 = x_1144;
x_300 = x_1132;
x_301 = lean_box(0);
x_302 = x_1178;
x_303 = x_1136;
x_304 = x_1137;
x_305 = x_1139;
x_306 = x_1142;
x_307 = x_1141;
goto block_327;
}
}
}
else
{
lean_object* x_1186; 
lean_dec_ref(x_1140);
lean_dec_ref(x_1135);
lean_dec(x_1134);
lean_dec(x_1132);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1186 = lean_ctor_get(x_1168, 0);
lean_inc(x_1186);
lean_dec_ref(x_1168);
x_130 = x_1127;
x_131 = x_1167;
x_132 = x_1128;
x_133 = x_1136;
x_134 = x_1137;
x_135 = x_1129;
x_136 = x_1139;
x_137 = x_1142;
x_138 = x_1141;
x_139 = x_1130;
x_140 = x_1144;
x_141 = x_1186;
x_142 = lean_box(0);
goto block_144;
}
}
}
block_1218:
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; uint8_t x_1201; 
x_1198 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_1197);
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
lean_dec_ref(x_1198);
x_1200 = l_Lean_trace_profiler_useHeartbeats;
x_1201 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1190, x_1200);
if (x_1201 == 0)
{
lean_object* x_1202; lean_object* x_1203; 
x_1202 = lean_io_mono_nanos_now();
lean_inc(x_1197);
lean_inc_ref(x_1192);
lean_inc(x_1191);
lean_inc_ref(x_1189);
lean_inc(x_2);
x_1203 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_972, x_1193, x_7, x_1189, x_1191, x_1192, x_1197);
if (lean_obj_tag(x_1203) == 0)
{
uint8_t x_1204; 
x_1204 = !lean_is_exclusive(x_1203);
if (x_1204 == 0)
{
lean_ctor_set_tag(x_1203, 1);
x_805 = x_1199;
x_806 = x_1188;
x_807 = x_1189;
x_808 = x_1202;
x_809 = x_1191;
x_810 = x_1190;
x_811 = x_1192;
x_812 = x_1194;
x_813 = x_1197;
x_814 = x_1196;
x_815 = x_1203;
x_816 = lean_box(0);
goto block_828;
}
else
{
lean_object* x_1205; lean_object* x_1206; 
x_1205 = lean_ctor_get(x_1203, 0);
lean_inc(x_1205);
lean_dec(x_1203);
x_1206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1206, 0, x_1205);
x_805 = x_1199;
x_806 = x_1188;
x_807 = x_1189;
x_808 = x_1202;
x_809 = x_1191;
x_810 = x_1190;
x_811 = x_1192;
x_812 = x_1194;
x_813 = x_1197;
x_814 = x_1196;
x_815 = x_1206;
x_816 = lean_box(0);
goto block_828;
}
}
else
{
uint8_t x_1207; 
x_1207 = !lean_is_exclusive(x_1203);
if (x_1207 == 0)
{
lean_ctor_set_tag(x_1203, 0);
x_805 = x_1199;
x_806 = x_1188;
x_807 = x_1189;
x_808 = x_1202;
x_809 = x_1191;
x_810 = x_1190;
x_811 = x_1192;
x_812 = x_1194;
x_813 = x_1197;
x_814 = x_1196;
x_815 = x_1203;
x_816 = lean_box(0);
goto block_828;
}
else
{
lean_object* x_1208; lean_object* x_1209; 
x_1208 = lean_ctor_get(x_1203, 0);
lean_inc(x_1208);
lean_dec(x_1203);
x_1209 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1209, 0, x_1208);
x_805 = x_1199;
x_806 = x_1188;
x_807 = x_1189;
x_808 = x_1202;
x_809 = x_1191;
x_810 = x_1190;
x_811 = x_1192;
x_812 = x_1194;
x_813 = x_1197;
x_814 = x_1196;
x_815 = x_1209;
x_816 = lean_box(0);
goto block_828;
}
}
}
else
{
lean_object* x_1210; lean_object* x_1211; 
x_1210 = lean_io_get_num_heartbeats();
lean_inc(x_1197);
lean_inc_ref(x_1192);
lean_inc(x_1191);
lean_inc_ref(x_1189);
lean_inc(x_2);
x_1211 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_972, x_1193, x_7, x_1189, x_1191, x_1192, x_1197);
if (lean_obj_tag(x_1211) == 0)
{
uint8_t x_1212; 
x_1212 = !lean_is_exclusive(x_1211);
if (x_1212 == 0)
{
lean_ctor_set_tag(x_1211, 1);
x_784 = x_1199;
x_785 = x_1188;
x_786 = x_1189;
x_787 = x_1191;
x_788 = x_1190;
x_789 = x_1192;
x_790 = x_1210;
x_791 = x_1194;
x_792 = x_1197;
x_793 = x_1196;
x_794 = x_1211;
x_795 = lean_box(0);
goto block_804;
}
else
{
lean_object* x_1213; lean_object* x_1214; 
x_1213 = lean_ctor_get(x_1211, 0);
lean_inc(x_1213);
lean_dec(x_1211);
x_1214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1214, 0, x_1213);
x_784 = x_1199;
x_785 = x_1188;
x_786 = x_1189;
x_787 = x_1191;
x_788 = x_1190;
x_789 = x_1192;
x_790 = x_1210;
x_791 = x_1194;
x_792 = x_1197;
x_793 = x_1196;
x_794 = x_1214;
x_795 = lean_box(0);
goto block_804;
}
}
else
{
uint8_t x_1215; 
x_1215 = !lean_is_exclusive(x_1211);
if (x_1215 == 0)
{
lean_ctor_set_tag(x_1211, 0);
x_784 = x_1199;
x_785 = x_1188;
x_786 = x_1189;
x_787 = x_1191;
x_788 = x_1190;
x_789 = x_1192;
x_790 = x_1210;
x_791 = x_1194;
x_792 = x_1197;
x_793 = x_1196;
x_794 = x_1211;
x_795 = lean_box(0);
goto block_804;
}
else
{
lean_object* x_1216; lean_object* x_1217; 
x_1216 = lean_ctor_get(x_1211, 0);
lean_inc(x_1216);
lean_dec(x_1211);
x_1217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1217, 0, x_1216);
x_784 = x_1199;
x_785 = x_1188;
x_786 = x_1189;
x_787 = x_1191;
x_788 = x_1190;
x_789 = x_1192;
x_790 = x_1210;
x_791 = x_1194;
x_792 = x_1197;
x_793 = x_1196;
x_794 = x_1217;
x_795 = lean_box(0);
goto block_804;
}
}
}
}
block_1263:
{
if (x_1229 == 0)
{
lean_object* x_1230; 
lean_dec_ref(x_1219);
lean_inc(x_1228);
lean_inc_ref(x_1225);
lean_inc(x_1224);
lean_inc_ref(x_1223);
lean_inc(x_1222);
x_1230 = lean_apply_6(x_1226, x_1222, x_1223, x_1224, x_1225, x_1228, lean_box(0));
if (lean_obj_tag(x_1230) == 0)
{
lean_object* x_1231; 
x_1231 = lean_ctor_get(x_1230, 0);
lean_inc(x_1231);
lean_dec_ref(x_1230);
if (lean_obj_tag(x_1231) == 0)
{
lean_object* x_1232; uint8_t x_1233; lean_object* x_1234; lean_object* x_1235; 
x_1232 = lean_ctor_get(x_1225, 2);
x_1233 = lean_ctor_get_uint8(x_1232, sizeof(void*)*1);
x_1234 = lean_nat_add(x_972, x_971);
lean_dec(x_972);
x_1235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1235, 0, x_1222);
lean_ctor_set(x_1235, 1, x_7);
if (x_1233 == 0)
{
x_5 = x_1234;
x_6 = x_1220;
x_7 = x_1235;
x_8 = x_1223;
x_9 = x_1224;
x_10 = x_1225;
x_11 = x_1228;
goto _start;
}
else
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; uint8_t x_1240; 
lean_inc(x_2);
x_1237 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1225);
x_1238 = lean_ctor_get(x_1237, 0);
lean_inc(x_1238);
lean_dec_ref(x_1237);
x_1239 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1240 = lean_unbox(x_1238);
if (x_1240 == 0)
{
lean_object* x_1241; uint8_t x_1242; 
x_1241 = l_Lean_trace_profiler;
x_1242 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1232, x_1241);
if (x_1242 == 0)
{
lean_dec(x_1238);
x_5 = x_1234;
x_6 = x_1220;
x_7 = x_1235;
x_8 = x_1223;
x_9 = x_1224;
x_10 = x_1225;
x_11 = x_1228;
goto _start;
}
else
{
uint8_t x_1244; 
lean_inc_ref(x_1232);
x_1244 = lean_unbox(x_1238);
lean_dec(x_1238);
x_751 = x_1220;
x_752 = x_1244;
x_753 = x_1223;
x_754 = x_1224;
x_755 = lean_box(0);
x_756 = x_1225;
x_757 = x_1232;
x_758 = x_1234;
x_759 = x_1235;
x_760 = x_1239;
x_761 = x_1227;
x_762 = x_1228;
goto block_783;
}
}
else
{
uint8_t x_1245; 
lean_inc_ref(x_1232);
x_1245 = lean_unbox(x_1238);
lean_dec(x_1238);
x_751 = x_1220;
x_752 = x_1245;
x_753 = x_1223;
x_754 = x_1224;
x_755 = lean_box(0);
x_756 = x_1225;
x_757 = x_1232;
x_758 = x_1234;
x_759 = x_1235;
x_760 = x_1239;
x_761 = x_1227;
x_762 = x_1228;
goto block_783;
}
}
}
else
{
lean_object* x_1246; lean_object* x_1247; uint8_t x_1248; lean_object* x_1249; 
lean_dec(x_1222);
x_1246 = lean_ctor_get(x_1225, 2);
x_1247 = lean_ctor_get(x_1231, 0);
lean_inc(x_1247);
lean_dec_ref(x_1231);
x_1248 = lean_ctor_get_uint8(x_1246, sizeof(void*)*1);
x_1249 = l_List_appendTR___redArg(x_1247, x_1220);
if (x_1248 == 0)
{
x_5 = x_972;
x_6 = x_1249;
x_8 = x_1223;
x_9 = x_1224;
x_10 = x_1225;
x_11 = x_1228;
goto _start;
}
else
{
lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; uint8_t x_1254; 
lean_inc(x_2);
x_1251 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1225);
x_1252 = lean_ctor_get(x_1251, 0);
lean_inc(x_1252);
lean_dec_ref(x_1251);
x_1253 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1254 = lean_unbox(x_1252);
if (x_1254 == 0)
{
lean_object* x_1255; uint8_t x_1256; 
x_1255 = l_Lean_trace_profiler;
x_1256 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1246, x_1255);
if (x_1256 == 0)
{
lean_dec(x_1252);
x_5 = x_972;
x_6 = x_1249;
x_8 = x_1223;
x_9 = x_1224;
x_10 = x_1225;
x_11 = x_1228;
goto _start;
}
else
{
uint8_t x_1258; 
lean_inc_ref(x_1246);
x_1258 = lean_unbox(x_1252);
lean_dec(x_1252);
x_1188 = x_1253;
x_1189 = x_1223;
x_1190 = x_1246;
x_1191 = x_1224;
x_1192 = x_1225;
x_1193 = x_1249;
x_1194 = x_1258;
x_1195 = lean_box(0);
x_1196 = x_1227;
x_1197 = x_1228;
goto block_1218;
}
}
else
{
uint8_t x_1259; 
lean_inc_ref(x_1246);
x_1259 = lean_unbox(x_1252);
lean_dec(x_1252);
x_1188 = x_1253;
x_1189 = x_1223;
x_1190 = x_1246;
x_1191 = x_1224;
x_1192 = x_1225;
x_1193 = x_1249;
x_1194 = x_1259;
x_1195 = lean_box(0);
x_1196 = x_1227;
x_1197 = x_1228;
goto block_1218;
}
}
}
}
else
{
uint8_t x_1260; 
lean_dec(x_1228);
lean_dec_ref(x_1225);
lean_dec(x_1224);
lean_dec_ref(x_1223);
lean_dec(x_1222);
lean_dec(x_1220);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1260 = !lean_is_exclusive(x_1230);
if (x_1260 == 0)
{
return x_1230;
}
else
{
lean_object* x_1261; lean_object* x_1262; 
x_1261 = lean_ctor_get(x_1230, 0);
lean_inc(x_1261);
lean_dec(x_1230);
x_1262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1262, 0, x_1261);
return x_1262;
}
}
}
else
{
lean_dec(x_1228);
lean_dec_ref(x_1226);
lean_dec_ref(x_1225);
lean_dec(x_1224);
lean_dec_ref(x_1223);
lean_dec(x_1222);
lean_dec(x_1220);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1219;
}
}
block_1299:
{
lean_object* x_1275; 
lean_inc(x_1273);
lean_inc_ref(x_1272);
lean_inc(x_1271);
lean_inc_ref(x_1270);
lean_inc(x_1267);
x_1275 = lean_apply_6(x_1266, x_1267, x_1270, x_1271, x_1272, x_1273, lean_box(0));
if (lean_obj_tag(x_1275) == 0)
{
lean_object* x_1276; uint8_t x_1277; 
x_1276 = lean_ctor_get(x_1275, 0);
lean_inc(x_1276);
lean_dec_ref(x_1275);
x_1277 = lean_unbox(x_1276);
lean_dec(x_1276);
if (x_1277 == 0)
{
lean_object* x_1278; 
lean_inc_ref(x_3);
lean_inc(x_1273);
lean_inc_ref(x_1272);
lean_inc(x_1271);
lean_inc_ref(x_1270);
lean_inc(x_1267);
x_1278 = lean_apply_7(x_3, x_1267, x_1264, x_1270, x_1271, x_1272, x_1273, lean_box(0));
if (lean_obj_tag(x_1278) == 0)
{
lean_dec(x_1273);
lean_dec_ref(x_1272);
lean_dec(x_1271);
lean_dec_ref(x_1270);
lean_dec_ref(x_1268);
lean_dec(x_1267);
lean_dec(x_1265);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_1278;
}
else
{
lean_object* x_1279; uint8_t x_1280; 
x_1279 = lean_ctor_get(x_1278, 0);
lean_inc(x_1279);
x_1280 = l_Lean_Exception_isInterrupt(x_1279);
if (x_1280 == 0)
{
uint8_t x_1281; 
x_1281 = l_Lean_Exception_isRuntime(x_1279);
x_1219 = x_1278;
x_1220 = x_1265;
x_1221 = lean_box(0);
x_1222 = x_1267;
x_1223 = x_1270;
x_1224 = x_1271;
x_1225 = x_1272;
x_1226 = x_1268;
x_1227 = x_1269;
x_1228 = x_1273;
x_1229 = x_1281;
goto block_1263;
}
else
{
lean_dec(x_1279);
x_1219 = x_1278;
x_1220 = x_1265;
x_1221 = lean_box(0);
x_1222 = x_1267;
x_1223 = x_1270;
x_1224 = x_1271;
x_1225 = x_1272;
x_1226 = x_1268;
x_1227 = x_1269;
x_1228 = x_1273;
x_1229 = x_1280;
goto block_1263;
}
}
}
else
{
lean_object* x_1282; uint8_t x_1283; lean_object* x_1284; lean_object* x_1285; 
lean_dec_ref(x_1268);
lean_dec_ref(x_1264);
x_1282 = lean_ctor_get(x_1272, 2);
x_1283 = lean_ctor_get_uint8(x_1282, sizeof(void*)*1);
x_1284 = lean_nat_add(x_972, x_971);
lean_dec(x_972);
x_1285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1285, 0, x_1267);
lean_ctor_set(x_1285, 1, x_7);
if (x_1283 == 0)
{
x_5 = x_1284;
x_6 = x_1265;
x_7 = x_1285;
x_8 = x_1270;
x_9 = x_1271;
x_10 = x_1272;
x_11 = x_1273;
goto _start;
}
else
{
lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; uint8_t x_1290; 
lean_inc(x_2);
x_1287 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1272);
x_1288 = lean_ctor_get(x_1287, 0);
lean_inc(x_1288);
lean_dec_ref(x_1287);
x_1289 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1290 = lean_unbox(x_1288);
if (x_1290 == 0)
{
lean_object* x_1291; uint8_t x_1292; 
x_1291 = l_Lean_trace_profiler;
x_1292 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1282, x_1291);
if (x_1292 == 0)
{
lean_dec(x_1288);
x_5 = x_1284;
x_6 = x_1265;
x_7 = x_1285;
x_8 = x_1270;
x_9 = x_1271;
x_10 = x_1272;
x_11 = x_1273;
goto _start;
}
else
{
uint8_t x_1294; 
lean_inc_ref(x_1282);
x_1294 = lean_unbox(x_1288);
lean_dec(x_1288);
x_874 = x_1265;
x_875 = x_1270;
x_876 = x_1271;
x_877 = x_1272;
x_878 = x_1289;
x_879 = x_1284;
x_880 = x_1294;
x_881 = x_1282;
x_882 = lean_box(0);
x_883 = x_1285;
x_884 = x_1269;
x_885 = x_1273;
goto block_906;
}
}
else
{
uint8_t x_1295; 
lean_inc_ref(x_1282);
x_1295 = lean_unbox(x_1288);
lean_dec(x_1288);
x_874 = x_1265;
x_875 = x_1270;
x_876 = x_1271;
x_877 = x_1272;
x_878 = x_1289;
x_879 = x_1284;
x_880 = x_1295;
x_881 = x_1282;
x_882 = lean_box(0);
x_883 = x_1285;
x_884 = x_1269;
x_885 = x_1273;
goto block_906;
}
}
}
}
else
{
uint8_t x_1296; 
lean_dec(x_1273);
lean_dec_ref(x_1272);
lean_dec(x_1271);
lean_dec_ref(x_1270);
lean_dec_ref(x_1268);
lean_dec(x_1267);
lean_dec(x_1265);
lean_dec_ref(x_1264);
lean_dec(x_972);
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_1296 = !lean_is_exclusive(x_1275);
if (x_1296 == 0)
{
return x_1275;
}
else
{
lean_object* x_1297; lean_object* x_1298; 
x_1297 = lean_ctor_get(x_1275, 0);
lean_inc(x_1297);
lean_dec(x_1275);
x_1298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1298, 0, x_1297);
return x_1298;
}
}
}
block_1361:
{
if (lean_obj_tag(x_1300) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_1306; uint8_t x_1307; lean_object* x_1308; 
lean_dec(x_972);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1306 = lean_ctor_get(x_1303, 2);
lean_inc_ref(x_1306);
x_1307 = lean_ctor_get_uint8(x_1306, sizeof(void*)*1);
x_1308 = l_List_reverse___redArg(x_7);
if (x_1307 == 0)
{
lean_object* x_1309; 
lean_dec_ref(x_1306);
lean_dec(x_1304);
lean_dec_ref(x_1303);
lean_dec(x_1302);
lean_dec_ref(x_1301);
lean_dec(x_2);
x_1309 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1309, 0, x_1308);
return x_1309;
}
else
{
lean_object* x_1310; uint8_t x_1311; 
lean_inc(x_2);
x_1310 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1303);
x_1311 = !lean_is_exclusive(x_1310);
if (x_1311 == 0)
{
lean_object* x_1312; lean_object* x_1313; uint8_t x_1314; 
x_1312 = lean_ctor_get(x_1310, 0);
x_1313 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1314 = lean_unbox(x_1312);
if (x_1314 == 0)
{
lean_object* x_1315; uint8_t x_1316; 
x_1315 = l_Lean_trace_profiler;
x_1316 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1306, x_1315);
if (x_1316 == 0)
{
lean_dec(x_1312);
lean_dec_ref(x_1306);
lean_dec(x_1304);
lean_dec_ref(x_1303);
lean_dec(x_1302);
lean_dec_ref(x_1301);
lean_dec(x_2);
lean_ctor_set(x_1310, 0, x_1308);
return x_1310;
}
else
{
uint8_t x_1317; 
lean_free_object(x_1310);
x_1317 = lean_unbox(x_1312);
lean_dec(x_1312);
x_908 = x_1313;
x_909 = x_1307;
x_910 = x_1302;
x_911 = x_1317;
x_912 = x_1304;
x_913 = x_1303;
x_914 = x_1306;
x_915 = x_1301;
x_916 = x_1308;
x_917 = lean_box(0);
goto block_970;
}
}
else
{
uint8_t x_1318; 
lean_free_object(x_1310);
x_1318 = lean_unbox(x_1312);
lean_dec(x_1312);
x_908 = x_1313;
x_909 = x_1307;
x_910 = x_1302;
x_911 = x_1318;
x_912 = x_1304;
x_913 = x_1303;
x_914 = x_1306;
x_915 = x_1301;
x_916 = x_1308;
x_917 = lean_box(0);
goto block_970;
}
}
else
{
lean_object* x_1319; lean_object* x_1320; uint8_t x_1321; 
x_1319 = lean_ctor_get(x_1310, 0);
lean_inc(x_1319);
lean_dec(x_1310);
x_1320 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1321 = lean_unbox(x_1319);
if (x_1321 == 0)
{
lean_object* x_1322; uint8_t x_1323; 
x_1322 = l_Lean_trace_profiler;
x_1323 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1306, x_1322);
if (x_1323 == 0)
{
lean_object* x_1324; 
lean_dec(x_1319);
lean_dec_ref(x_1306);
lean_dec(x_1304);
lean_dec_ref(x_1303);
lean_dec(x_1302);
lean_dec_ref(x_1301);
lean_dec(x_2);
x_1324 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1324, 0, x_1308);
return x_1324;
}
else
{
uint8_t x_1325; 
x_1325 = lean_unbox(x_1319);
lean_dec(x_1319);
x_908 = x_1320;
x_909 = x_1307;
x_910 = x_1302;
x_911 = x_1325;
x_912 = x_1304;
x_913 = x_1303;
x_914 = x_1306;
x_915 = x_1301;
x_916 = x_1308;
x_917 = lean_box(0);
goto block_970;
}
}
else
{
uint8_t x_1326; 
x_1326 = lean_unbox(x_1319);
lean_dec(x_1319);
x_908 = x_1320;
x_909 = x_1307;
x_910 = x_1302;
x_911 = x_1326;
x_912 = x_1304;
x_913 = x_1303;
x_914 = x_1306;
x_915 = x_1301;
x_916 = x_1308;
x_917 = lean_box(0);
goto block_970;
}
}
}
}
else
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; uint8_t x_1331; uint8_t x_1332; 
x_1327 = lean_ctor_get(x_6, 0);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_6, 1);
lean_inc(x_1328);
lean_dec_ref(x_6);
x_1329 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_1327, x_1302);
x_1330 = lean_ctor_get(x_1329, 0);
lean_inc(x_1330);
lean_dec_ref(x_1329);
x_1331 = 1;
x_1332 = lean_unbox(x_1330);
lean_dec(x_1330);
if (x_1332 == 0)
{
lean_object* x_1333; uint8_t x_1334; lean_object* x_1335; 
x_1333 = lean_ctor_get(x_1303, 2);
x_1334 = lean_ctor_get_uint8(x_1333, sizeof(void*)*1);
lean_inc(x_7);
lean_inc(x_972);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc(x_1328);
x_1335 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__3___boxed), 13, 7);
lean_closure_set(x_1335, 0, x_1328);
lean_closure_set(x_1335, 1, x_1);
lean_closure_set(x_1335, 2, x_2);
lean_closure_set(x_1335, 3, x_3);
lean_closure_set(x_1335, 4, x_4);
lean_closure_set(x_1335, 5, x_972);
lean_closure_set(x_1335, 6, x_7);
if (x_1334 == 0)
{
lean_inc_ref(x_236);
lean_inc_ref(x_235);
x_1264 = x_1335;
x_1265 = x_1328;
x_1266 = x_235;
x_1267 = x_1327;
x_1268 = x_236;
x_1269 = x_1331;
x_1270 = x_1301;
x_1271 = x_1302;
x_1272 = x_1303;
x_1273 = x_1304;
x_1274 = lean_box(0);
goto block_1299;
}
else
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; uint8_t x_1340; 
lean_inc(x_2);
x_1336 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1303);
x_1337 = lean_ctor_get(x_1336, 0);
lean_inc(x_1337);
lean_dec_ref(x_1336);
lean_inc(x_1327);
x_1338 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___boxed), 7, 1);
lean_closure_set(x_1338, 0, x_1327);
x_1339 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1340 = lean_unbox(x_1337);
if (x_1340 == 0)
{
lean_object* x_1341; uint8_t x_1342; 
x_1341 = l_Lean_trace_profiler;
x_1342 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1333, x_1341);
if (x_1342 == 0)
{
lean_dec_ref(x_1338);
lean_dec(x_1337);
lean_inc_ref(x_236);
lean_inc_ref(x_235);
x_1264 = x_1335;
x_1265 = x_1328;
x_1266 = x_235;
x_1267 = x_1327;
x_1268 = x_236;
x_1269 = x_1331;
x_1270 = x_1301;
x_1271 = x_1302;
x_1272 = x_1303;
x_1273 = x_1304;
x_1274 = lean_box(0);
goto block_1299;
}
else
{
uint8_t x_1343; 
lean_inc_ref(x_1333);
x_1343 = lean_unbox(x_1337);
lean_dec(x_1337);
lean_inc_ref(x_236);
lean_inc_ref(x_235);
lean_inc_ref(x_1335);
x_1127 = x_1302;
x_1128 = x_1339;
x_1129 = x_1343;
x_1130 = x_1331;
x_1131 = x_1335;
x_1132 = x_1328;
x_1133 = x_235;
x_1134 = x_1327;
x_1135 = x_1335;
x_1136 = x_1303;
x_1137 = x_1304;
x_1138 = lean_box(0);
x_1139 = x_1338;
x_1140 = x_236;
x_1141 = x_1301;
x_1142 = x_1333;
goto block_1187;
}
}
else
{
uint8_t x_1344; 
lean_inc_ref(x_1333);
x_1344 = lean_unbox(x_1337);
lean_dec(x_1337);
lean_inc_ref(x_236);
lean_inc_ref(x_235);
lean_inc_ref(x_1335);
x_1127 = x_1302;
x_1128 = x_1339;
x_1129 = x_1344;
x_1130 = x_1331;
x_1131 = x_1335;
x_1132 = x_1328;
x_1133 = x_235;
x_1134 = x_1327;
x_1135 = x_1335;
x_1136 = x_1303;
x_1137 = x_1304;
x_1138 = lean_box(0);
x_1139 = x_1338;
x_1140 = x_236;
x_1141 = x_1301;
x_1142 = x_1333;
goto block_1187;
}
}
}
else
{
lean_object* x_1345; uint8_t x_1346; lean_object* x_1347; 
x_1345 = lean_ctor_get(x_1303, 2);
x_1346 = lean_ctor_get_uint8(x_1345, sizeof(void*)*1);
x_1347 = lean_nat_add(x_972, x_971);
lean_dec(x_972);
if (x_1346 == 0)
{
lean_dec(x_1327);
x_5 = x_1347;
x_6 = x_1328;
x_8 = x_1301;
x_9 = x_1302;
x_10 = x_1303;
x_11 = x_1304;
goto _start;
}
else
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; uint8_t x_1353; 
lean_inc(x_2);
x_1349 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_1303);
x_1350 = lean_ctor_get(x_1349, 0);
lean_inc(x_1350);
lean_dec_ref(x_1349);
x_1351 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___boxed), 7, 1);
lean_closure_set(x_1351, 0, x_1327);
x_1352 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1353 = lean_unbox(x_1350);
if (x_1353 == 0)
{
lean_object* x_1354; uint8_t x_1355; 
x_1354 = l_Lean_trace_profiler;
x_1355 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_1345, x_1354);
if (x_1355 == 0)
{
lean_dec_ref(x_1351);
lean_dec(x_1350);
x_5 = x_1347;
x_6 = x_1328;
x_8 = x_1301;
x_9 = x_1302;
x_10 = x_1303;
x_11 = x_1304;
goto _start;
}
else
{
uint8_t x_1357; 
lean_inc_ref(x_1345);
x_1357 = lean_unbox(x_1350);
lean_dec(x_1350);
x_60 = x_1328;
x_61 = x_1352;
x_62 = x_1302;
x_63 = lean_box(0);
x_64 = x_1304;
x_65 = x_1303;
x_66 = x_1357;
x_67 = x_1351;
x_68 = x_1347;
x_69 = x_1301;
x_70 = x_1331;
x_71 = x_1345;
goto block_92;
}
}
else
{
uint8_t x_1358; 
lean_inc_ref(x_1345);
x_1358 = lean_unbox(x_1350);
lean_dec(x_1350);
x_60 = x_1328;
x_61 = x_1352;
x_62 = x_1302;
x_63 = lean_box(0);
x_64 = x_1304;
x_65 = x_1303;
x_66 = x_1358;
x_67 = x_1351;
x_68 = x_1347;
x_69 = x_1301;
x_70 = x_1331;
x_71 = x_1345;
goto block_92;
}
}
}
}
}
else
{
lean_object* x_1359; 
lean_dec(x_6);
x_1359 = lean_ctor_get(x_1300, 0);
lean_inc(x_1359);
lean_dec_ref(x_1300);
x_5 = x_972;
x_6 = x_1359;
x_8 = x_1301;
x_9 = x_1302;
x_10 = x_1303;
x_11 = x_1304;
goto _start;
}
}
block_1367:
{
if (lean_obj_tag(x_1362) == 0)
{
lean_object* x_1363; 
x_1363 = lean_ctor_get(x_1362, 0);
lean_inc(x_1363);
lean_dec_ref(x_1362);
x_1300 = x_1363;
x_1301 = x_8;
x_1302 = x_9;
x_1303 = x_10;
x_1304 = x_11;
x_1305 = lean_box(0);
goto block_1361;
}
else
{
uint8_t x_1364; 
lean_dec(x_972);
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
x_1364 = !lean_is_exclusive(x_1362);
if (x_1364 == 0)
{
return x_1362;
}
else
{
lean_object* x_1365; lean_object* x_1366; 
x_1365 = lean_ctor_get(x_1362, 0);
lean_inc(x_1365);
lean_dec(x_1362);
x_1366 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1366, 0, x_1365);
return x_1366;
}
}
}
}
block_34:
{
lean_object* x_26; double x_27; double x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_io_get_num_heartbeats();
x_27 = lean_float_of_nat(x_20);
x_28 = lean_float_of_nat(x_26);
x_29 = lean_box_float(x_27);
x_30 = lean_box_float(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_22, x_13, x_23, x_18, x_15, x_19, x_32, x_21, x_14, x_17, x_16);
lean_dec_ref(x_23);
return x_33;
}
block_59:
{
lean_object* x_48; double x_49; double x_50; double x_51; double x_52; double x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_io_mono_nanos_now();
x_49 = lean_float_of_nat(x_36);
x_50 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
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
x_58 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_44, x_35, x_45, x_41, x_38, x_42, x_57, x_43, x_37, x_40, x_39);
lean_dec_ref(x_45);
return x_58;
}
block_92:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_64);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = l_Lean_trace_profiler_useHeartbeats;
x_75 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_71, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_io_mono_nanos_now();
lean_inc(x_64);
lean_inc_ref(x_65);
lean_inc(x_62);
lean_inc_ref(x_69);
lean_inc(x_2);
x_77 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_68, x_60, x_7, x_69, x_62, x_65, x_64);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_ctor_set_tag(x_77, 1);
x_35 = x_61;
x_36 = x_76;
x_37 = x_62;
x_38 = x_73;
x_39 = x_64;
x_40 = x_65;
x_41 = x_66;
x_42 = x_67;
x_43 = x_69;
x_44 = x_70;
x_45 = x_71;
x_46 = x_77;
x_47 = lean_box(0);
goto block_59;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_35 = x_61;
x_36 = x_76;
x_37 = x_62;
x_38 = x_73;
x_39 = x_64;
x_40 = x_65;
x_41 = x_66;
x_42 = x_67;
x_43 = x_69;
x_44 = x_70;
x_45 = x_71;
x_46 = x_80;
x_47 = lean_box(0);
goto block_59;
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_77);
if (x_81 == 0)
{
lean_ctor_set_tag(x_77, 0);
x_35 = x_61;
x_36 = x_76;
x_37 = x_62;
x_38 = x_73;
x_39 = x_64;
x_40 = x_65;
x_41 = x_66;
x_42 = x_67;
x_43 = x_69;
x_44 = x_70;
x_45 = x_71;
x_46 = x_77;
x_47 = lean_box(0);
goto block_59;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
lean_dec(x_77);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_35 = x_61;
x_36 = x_76;
x_37 = x_62;
x_38 = x_73;
x_39 = x_64;
x_40 = x_65;
x_41 = x_66;
x_42 = x_67;
x_43 = x_69;
x_44 = x_70;
x_45 = x_71;
x_46 = x_83;
x_47 = lean_box(0);
goto block_59;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_io_get_num_heartbeats();
lean_inc(x_64);
lean_inc_ref(x_65);
lean_inc(x_62);
lean_inc_ref(x_69);
lean_inc(x_2);
x_85 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_68, x_60, x_7, x_69, x_62, x_65, x_64);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_ctor_set_tag(x_85, 1);
x_13 = x_61;
x_14 = x_62;
x_15 = x_73;
x_16 = x_64;
x_17 = x_65;
x_18 = x_66;
x_19 = x_67;
x_20 = x_84;
x_21 = x_69;
x_22 = x_70;
x_23 = x_71;
x_24 = x_85;
x_25 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_13 = x_61;
x_14 = x_62;
x_15 = x_73;
x_16 = x_64;
x_17 = x_65;
x_18 = x_66;
x_19 = x_67;
x_20 = x_84;
x_21 = x_69;
x_22 = x_70;
x_23 = x_71;
x_24 = x_88;
x_25 = lean_box(0);
goto block_34;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
lean_ctor_set_tag(x_85, 0);
x_13 = x_61;
x_14 = x_62;
x_15 = x_73;
x_16 = x_64;
x_17 = x_65;
x_18 = x_66;
x_19 = x_67;
x_20 = x_84;
x_21 = x_69;
x_22 = x_70;
x_23 = x_71;
x_24 = x_85;
x_25 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_13 = x_61;
x_14 = x_62;
x_15 = x_73;
x_16 = x_64;
x_17 = x_65;
x_18 = x_66;
x_19 = x_67;
x_20 = x_84;
x_21 = x_69;
x_22 = x_70;
x_23 = x_71;
x_24 = x_91;
x_25 = lean_box(0);
goto block_34;
}
}
}
}
block_114:
{
lean_object* x_106; double x_107; double x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_io_get_num_heartbeats();
x_107 = lean_float_of_nat(x_94);
x_108 = lean_float_of_nat(x_106);
x_109 = lean_box_float(x_107);
x_110 = lean_box_float(x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_104);
lean_ctor_set(x_112, 1, x_111);
x_113 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_102, x_95, x_101, x_98, x_103, x_99, x_112, x_100, x_93, x_97, x_96);
lean_dec_ref(x_101);
return x_113;
}
block_129:
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_126);
x_93 = x_115;
x_94 = x_116;
x_95 = x_117;
x_96 = x_119;
x_97 = x_118;
x_98 = x_120;
x_99 = x_121;
x_100 = x_123;
x_101 = x_122;
x_102 = x_124;
x_103 = x_125;
x_104 = x_128;
x_105 = lean_box(0);
goto block_114;
}
block_144:
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_141);
x_93 = x_130;
x_94 = x_131;
x_95 = x_132;
x_96 = x_134;
x_97 = x_133;
x_98 = x_135;
x_99 = x_136;
x_100 = x_138;
x_101 = x_137;
x_102 = x_139;
x_103 = x_140;
x_104 = x_143;
x_105 = lean_box(0);
goto block_114;
}
block_159:
{
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
lean_dec_ref(x_156);
x_115 = x_145;
x_116 = x_146;
x_117 = x_147;
x_118 = x_149;
x_119 = x_148;
x_120 = x_150;
x_121 = x_151;
x_122 = x_153;
x_123 = x_152;
x_124 = x_154;
x_125 = x_155;
x_126 = x_157;
x_127 = lean_box(0);
goto block_129;
}
else
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
lean_dec_ref(x_156);
x_130 = x_145;
x_131 = x_146;
x_132 = x_147;
x_133 = x_149;
x_134 = x_148;
x_135 = x_150;
x_136 = x_151;
x_137 = x_153;
x_138 = x_152;
x_139 = x_154;
x_140 = x_155;
x_141 = x_158;
x_142 = lean_box(0);
goto block_144;
}
}
block_184:
{
lean_object* x_173; double x_174; double x_175; double x_176; double x_177; double x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_173 = lean_io_mono_nanos_now();
x_174 = lean_float_of_nat(x_164);
x_175 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_176 = lean_float_div(x_174, x_175);
x_177 = lean_float_of_nat(x_173);
x_178 = lean_float_div(x_177, x_175);
x_179 = lean_box_float(x_176);
x_180 = lean_box_float(x_178);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_171);
lean_ctor_set(x_182, 1, x_181);
x_183 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_169, x_161, x_168, x_165, x_170, x_166, x_182, x_167, x_160, x_163, x_162);
lean_dec_ref(x_168);
return x_183;
}
block_199:
{
lean_object* x_198; 
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_196);
x_160 = x_185;
x_161 = x_186;
x_162 = x_188;
x_163 = x_187;
x_164 = x_189;
x_165 = x_190;
x_166 = x_191;
x_167 = x_193;
x_168 = x_192;
x_169 = x_194;
x_170 = x_195;
x_171 = x_198;
x_172 = lean_box(0);
goto block_184;
}
block_214:
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_213, 0, x_211);
x_160 = x_200;
x_161 = x_201;
x_162 = x_203;
x_163 = x_202;
x_164 = x_204;
x_165 = x_205;
x_166 = x_206;
x_167 = x_208;
x_168 = x_207;
x_169 = x_209;
x_170 = x_210;
x_171 = x_213;
x_172 = lean_box(0);
goto block_184;
}
block_229:
{
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
x_185 = x_215;
x_186 = x_216;
x_187 = x_218;
x_188 = x_217;
x_189 = x_219;
x_190 = x_220;
x_191 = x_221;
x_192 = x_223;
x_193 = x_222;
x_194 = x_224;
x_195 = x_225;
x_196 = x_227;
x_197 = lean_box(0);
goto block_199;
}
else
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
lean_dec_ref(x_226);
x_200 = x_215;
x_201 = x_216;
x_202 = x_218;
x_203 = x_217;
x_204 = x_219;
x_205 = x_220;
x_206 = x_221;
x_207 = x_223;
x_208 = x_222;
x_209 = x_224;
x_210 = x_225;
x_211 = x_228;
x_212 = lean_box(0);
goto block_214;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofFormat(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofFormat(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3() {
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1;
x_15 = lean_box(0);
x_16 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_10, x_15);
x_17 = l_Lean_MessageData_ofList(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_13, x_15);
x_22 = l_Lean_MessageData_ofList(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1;
x_26 = lean_box(0);
x_27 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_10, x_26);
x_28 = l_Lean_MessageData_ofList(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_24, x_26);
x_33 = l_Lean_MessageData_ofList(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_9, 0);
lean_inc(x_40);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5() {
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1;
x_15 = lean_box(0);
x_16 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_10, x_15);
x_17 = l_Lean_MessageData_ofList(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5;
x_22 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_13, x_15);
x_23 = l_Lean_MessageData_ofList(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
x_27 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1;
x_28 = lean_box(0);
x_29 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_10, x_28);
x_30 = l_Lean_MessageData_ofList(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5;
x_35 = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__1(x_26, x_28);
x_36 = l_Lean_MessageData_ofList(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_11, 0);
lean_inc(x_41);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_9);
if (x_43 == 0)
{
return x_9;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_9, 0);
lean_inc(x_44);
lean_dec(x_9);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_14; lean_object* x_15; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_9 = x_2;
} else {
 lean_dec_ref(x_2);
 x_9 = lean_box(0);
}
x_18 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_7, x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
x_10 = lean_box(0);
goto block_13;
}
else
{
x_14 = x_1;
x_15 = lean_box(0);
goto block_17;
}
block_13:
{
lean_object* x_11; 
if (lean_is_scalar(x_9)) {
 x_11 = lean_alloc_ctor(1, 2, 0);
} else {
 x_11 = x_9;
}
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_3);
x_2 = x_8;
x_3 = x_11;
goto _start;
}
block_17:
{
if (x_14 == 0)
{
lean_dec(x_9);
lean_dec(x_7);
x_2 = x_8;
goto _start;
}
else
{
x_10 = lean_box(0);
goto block_13;
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
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_13 = x_2;
} else {
 lean_dec_ref(x_2);
 x_13 = lean_box(0);
}
x_19 = l_Lean_Meta_saveState___redArg(x_5, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc_ref(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_11);
x_21 = lean_apply_6(x_1, x_11, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_14 = x_23;
x_15 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_34; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_34 = l_Lean_Exception_isInterrupt(x_24);
if (x_34 == 0)
{
uint8_t x_35; 
lean_inc(x_24);
x_35 = l_Lean_Exception_isRuntime(x_24);
x_26 = x_35;
goto block_33;
}
else
{
x_26 = x_34;
goto block_33;
}
block_33:
{
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_dec(x_24);
x_27 = l_Lean_Meta_SavedState_restore___redArg(x_20, x_5, x_7);
lean_dec(x_20);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec_ref(x_27);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_11);
x_14 = x_28;
x_15 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
if (lean_is_scalar(x_25)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_25;
}
lean_ctor_set(x_32, 0, x_24);
return x_32;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_19, 0);
lean_inc(x_37);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
block_18:
{
lean_object* x_16; 
if (lean_is_scalar(x_13)) {
 x_16 = lean_alloc_ctor(1, 2, 0);
} else {
 x_16 = x_13;
}
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_3);
x_2 = x_12;
x_3 = x_16;
goto _start;
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0;
lean_inc(x_11);
x_13 = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(x_11, x_12);
x_14 = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(x_11, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0;
lean_inc(x_16);
x_18 = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__3___redArg(x_16, x_17);
x_19 = l_List_filterMapTR_go___at___00Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2_spec__4___redArg(x_16, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_10 = x_3;
} else {
 lean_dec_ref(x_3);
 x_10 = lean_box(0);
}
x_17 = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7___redArg(x_8, x_5);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
x_11 = x_1;
x_12 = lean_box(0);
goto block_16;
}
else
{
x_11 = x_2;
x_12 = lean_box(0);
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
lean_dec(x_10);
lean_dec(x_8);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_14; 
if (lean_is_scalar(x_10)) {
 x_14 = lean_alloc_ctor(1, 2, 0);
} else {
 x_14 = x_10;
}
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_9;
x_4 = x_14;
goto _start;
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2() {
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
x_25 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__0(x_5, x_6, x_25, x_25, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_81 = l_List_isEmpty___redArg(x_28);
if (x_81 == 0)
{
lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; lean_object* x_382; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_6);
x_107 = lean_ctor_get(x_9, 2);
x_108 = lean_ctor_get_uint8(x_107, sizeof(void*)*1);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_109 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__0___boxed), 10, 4);
lean_closure_set(x_109, 0, x_1);
lean_closure_set(x_109, 1, x_2);
lean_closure_set(x_109, 2, x_3);
lean_closure_set(x_109, 3, x_4);
x_110 = 1;
if (x_108 == 0)
{
x_528 = x_7;
x_529 = x_8;
x_530 = x_9;
x_531 = x_10;
x_532 = lean_box(0);
goto block_556;
}
else
{
lean_object* x_557; 
lean_inc(x_2);
x_557 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; lean_object* x_599; lean_object* x_600; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; lean_object* x_616; lean_object* x_617; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; uint8_t x_625; lean_object* x_626; lean_object* x_627; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_637; lean_object* x_638; lean_object* x_639; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; uint8_t x_650; lean_object* x_651; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; uint8_t x_664; lean_object* x_665; uint8_t x_666; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; uint8_t x_679; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; lean_object* x_694; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; uint8_t x_706; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; uint8_t x_720; uint8_t x_721; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; uint8_t x_733; uint8_t x_734; lean_object* x_735; lean_object* x_736; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; uint8_t x_746; lean_object* x_747; lean_object* x_748; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; lean_object* x_767; lean_object* x_768; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; uint8_t x_776; lean_object* x_777; lean_object* x_778; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; uint8_t x_788; lean_object* x_789; lean_object* x_790; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; uint8_t x_801; lean_object* x_802; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; uint8_t x_816; uint8_t x_817; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; uint8_t x_830; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; uint8_t x_844; lean_object* x_845; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; uint8_t x_855; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; uint8_t x_868; uint8_t x_869; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; uint8_t x_882; uint8_t x_883; lean_object* x_884; lean_object* x_885; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; uint8_t x_896; uint8_t x_897; lean_object* x_898; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; uint8_t x_931; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; uint8_t x_960; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; uint8_t x_982; lean_object* x_983; lean_object* x_984; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; uint8_t x_1042; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; uint8_t x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; uint8_t x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; uint8_t x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; uint8_t x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; uint8_t x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; uint8_t x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; uint8_t x_1142; uint8_t x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; uint8_t x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; uint8_t x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; uint8_t x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; uint8_t x_1193; lean_object* x_1194; uint8_t x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; uint8_t x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; uint8_t x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; uint8_t x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; uint8_t x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; uint8_t x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; uint8_t x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; uint8_t x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; uint8_t x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; uint8_t x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; uint8_t x_1311; uint8_t x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; uint8_t x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; uint8_t x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; uint8_t x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; uint8_t x_1358; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; uint8_t x_1387; lean_object* x_1388; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; uint8_t x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; uint8_t x_1455; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
lean_dec_ref(x_557);
lean_inc(x_29);
lean_inc(x_28);
x_559 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___boxed), 8, 2);
lean_closure_set(x_559, 0, x_28);
lean_closure_set(x_559, 1, x_29);
x_560 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_1455 = lean_unbox(x_558);
if (x_1455 == 0)
{
lean_object* x_1456; uint8_t x_1457; 
x_1456 = l_Lean_trace_profiler;
x_1457 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_107, x_1456);
if (x_1457 == 0)
{
lean_dec_ref(x_559);
lean_dec(x_558);
x_528 = x_7;
x_529 = x_8;
x_530 = x_9;
x_531 = x_10;
x_532 = lean_box(0);
goto block_556;
}
else
{
lean_inc_ref(x_107);
lean_dec(x_30);
goto block_1454;
}
}
else
{
lean_inc_ref(x_107);
lean_dec(x_30);
goto block_1454;
}
block_574:
{
lean_object* x_565; double x_566; double x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; lean_object* x_573; 
x_565 = lean_io_get_num_heartbeats();
x_566 = lean_float_of_nat(x_562);
x_567 = lean_float_of_nat(x_565);
x_568 = lean_box_float(x_566);
x_569 = lean_box_float(x_567);
x_570 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set(x_570, 1, x_569);
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_563);
lean_ctor_set(x_571, 1, x_570);
x_572 = lean_unbox(x_558);
lean_dec(x_558);
x_573 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_110, x_560, x_107, x_572, x_561, x_559, x_571, x_7, x_8, x_9, x_10);
lean_dec_ref(x_107);
return x_573;
}
block_580:
{
lean_object* x_579; 
x_579 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_579, 0, x_577);
x_561 = x_575;
x_562 = x_576;
x_563 = x_579;
x_564 = lean_box(0);
goto block_574;
}
block_586:
{
lean_object* x_585; 
x_585 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_585, 0, x_583);
x_561 = x_581;
x_562 = x_582;
x_563 = x_585;
x_564 = lean_box(0);
goto block_574;
}
block_592:
{
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
lean_dec_ref(x_589);
x_581 = x_587;
x_582 = x_588;
x_583 = x_590;
x_584 = lean_box(0);
goto block_586;
}
else
{
lean_object* x_591; 
x_591 = lean_ctor_get(x_589, 0);
lean_inc(x_591);
lean_dec_ref(x_589);
x_575 = x_587;
x_576 = x_588;
x_577 = x_591;
x_578 = lean_box(0);
goto block_580;
}
}
block_609:
{
lean_object* x_601; double x_602; double x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_601 = lean_io_get_num_heartbeats();
x_602 = lean_float_of_nat(x_593);
x_603 = lean_float_of_nat(x_601);
x_604 = lean_box_float(x_602);
x_605 = lean_box_float(x_603);
x_606 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_606, 0, x_604);
lean_ctor_set(x_606, 1, x_605);
x_607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_607, 0, x_599);
lean_ctor_set(x_607, 1, x_606);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_608 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_110, x_560, x_107, x_598, x_594, x_597, x_607, x_7, x_8, x_9, x_10);
x_587 = x_595;
x_588 = x_596;
x_589 = x_608;
goto block_592;
}
block_619:
{
lean_object* x_618; 
x_618 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_618, 0, x_616);
x_593 = x_610;
x_594 = x_611;
x_595 = x_612;
x_596 = x_613;
x_597 = x_614;
x_598 = x_615;
x_599 = x_618;
x_600 = lean_box(0);
goto block_609;
}
block_629:
{
lean_object* x_628; 
x_628 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_628, 0, x_626);
x_593 = x_620;
x_594 = x_621;
x_595 = x_622;
x_596 = x_623;
x_597 = x_624;
x_598 = x_625;
x_599 = x_628;
x_600 = lean_box(0);
goto block_609;
}
block_642:
{
lean_object* x_640; lean_object* x_641; 
x_640 = l_List_appendTR___redArg(x_634, x_635);
x_641 = l_List_appendTR___redArg(x_640, x_638);
x_620 = x_630;
x_621 = x_631;
x_622 = x_632;
x_623 = x_633;
x_624 = x_636;
x_625 = x_637;
x_626 = x_641;
x_627 = lean_box(0);
goto block_629;
}
block_654:
{
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
lean_dec_ref(x_651);
x_630 = x_643;
x_631 = x_644;
x_632 = x_645;
x_633 = x_646;
x_634 = x_647;
x_635 = x_648;
x_636 = x_649;
x_637 = x_650;
x_638 = x_652;
x_639 = lean_box(0);
goto block_642;
}
else
{
lean_object* x_653; 
lean_dec(x_648);
lean_dec(x_647);
x_653 = lean_ctor_get(x_651, 0);
lean_inc(x_653);
lean_dec_ref(x_651);
x_610 = x_643;
x_611 = x_644;
x_612 = x_645;
x_613 = x_646;
x_614 = x_649;
x_615 = x_650;
x_616 = x_653;
x_617 = lean_box(0);
goto block_619;
}
}
block_669:
{
if (x_666 == 0)
{
lean_object* x_667; 
lean_dec_ref(x_658);
x_667 = l_Lean_Meta_SavedState_restore___redArg(x_663, x_8, x_10);
lean_dec_ref(x_663);
if (lean_obj_tag(x_667) == 0)
{
lean_dec_ref(x_667);
x_630 = x_655;
x_631 = x_656;
x_632 = x_657;
x_633 = x_659;
x_634 = x_660;
x_635 = x_661;
x_636 = x_662;
x_637 = x_664;
x_638 = x_29;
x_639 = lean_box(0);
goto block_642;
}
else
{
lean_object* x_668; 
lean_dec(x_661);
lean_dec(x_660);
lean_dec(x_29);
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
lean_dec_ref(x_667);
x_610 = x_655;
x_611 = x_656;
x_612 = x_657;
x_613 = x_659;
x_614 = x_662;
x_615 = x_664;
x_616 = x_668;
x_617 = lean_box(0);
goto block_619;
}
}
else
{
lean_dec_ref(x_663);
lean_dec(x_29);
x_643 = x_655;
x_644 = x_656;
x_645 = x_657;
x_646 = x_659;
x_647 = x_660;
x_648 = x_661;
x_649 = x_662;
x_650 = x_664;
x_651 = x_658;
goto block_654;
}
}
block_687:
{
lean_object* x_680; 
x_680 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
lean_dec_ref(x_680);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_682 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_675, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_682) == 0)
{
lean_dec(x_681);
lean_dec(x_29);
x_643 = x_670;
x_644 = x_671;
x_645 = x_672;
x_646 = x_673;
x_647 = x_674;
x_648 = x_677;
x_649 = x_678;
x_650 = x_679;
x_651 = x_682;
goto block_654;
}
else
{
lean_object* x_683; uint8_t x_684; 
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = l_Lean_Exception_isInterrupt(x_683);
if (x_684 == 0)
{
uint8_t x_685; 
x_685 = l_Lean_Exception_isRuntime(x_683);
x_655 = x_670;
x_656 = x_671;
x_657 = x_672;
x_658 = x_682;
x_659 = x_673;
x_660 = x_674;
x_661 = x_677;
x_662 = x_678;
x_663 = x_681;
x_664 = x_679;
x_665 = lean_box(0);
x_666 = x_685;
goto block_669;
}
else
{
lean_dec(x_683);
x_655 = x_670;
x_656 = x_671;
x_657 = x_672;
x_658 = x_682;
x_659 = x_673;
x_660 = x_674;
x_661 = x_677;
x_662 = x_678;
x_663 = x_681;
x_664 = x_679;
x_665 = lean_box(0);
x_666 = x_684;
goto block_669;
}
}
}
else
{
lean_object* x_686; 
lean_dec(x_677);
lean_dec(x_675);
lean_dec(x_674);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_686 = lean_ctor_get(x_680, 0);
lean_inc(x_686);
lean_dec_ref(x_680);
x_610 = x_670;
x_611 = x_671;
x_612 = x_672;
x_613 = x_673;
x_614 = x_678;
x_615 = x_679;
x_616 = x_686;
x_617 = lean_box(0);
goto block_619;
}
}
block_697:
{
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; 
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
lean_dec_ref(x_694);
x_620 = x_688;
x_621 = x_689;
x_622 = x_690;
x_623 = x_691;
x_624 = x_692;
x_625 = x_693;
x_626 = x_695;
x_627 = lean_box(0);
goto block_629;
}
else
{
lean_object* x_696; 
x_696 = lean_ctor_get(x_694, 0);
lean_inc(x_696);
lean_dec_ref(x_694);
x_610 = x_688;
x_611 = x_689;
x_612 = x_690;
x_613 = x_691;
x_614 = x_692;
x_615 = x_693;
x_616 = x_696;
x_617 = lean_box(0);
goto block_619;
}
}
block_710:
{
lean_object* x_707; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_707 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_703, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; lean_object* x_709; 
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
lean_dec_ref(x_707);
x_709 = l_List_appendTR___redArg(x_702, x_708);
x_620 = x_698;
x_621 = x_699;
x_622 = x_700;
x_623 = x_701;
x_624 = x_705;
x_625 = x_706;
x_626 = x_709;
x_627 = lean_box(0);
goto block_629;
}
else
{
lean_dec(x_702);
x_688 = x_698;
x_689 = x_699;
x_690 = x_700;
x_691 = x_701;
x_692 = x_705;
x_693 = x_706;
x_694 = x_707;
goto block_697;
}
}
block_725:
{
uint8_t x_722; 
x_722 = l_List_isEmpty___redArg(x_718);
lean_dec(x_718);
if (x_722 == 0)
{
if (x_721 == 0)
{
x_698 = x_711;
x_699 = x_712;
x_700 = x_713;
x_701 = x_714;
x_702 = x_716;
x_703 = x_715;
x_704 = lean_box(0);
x_705 = x_719;
x_706 = x_720;
goto block_710;
}
else
{
lean_object* x_723; lean_object* x_724; 
lean_dec(x_716);
lean_dec(x_715);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_723 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2;
x_724 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_723, x_7, x_8, x_9, x_10);
x_688 = x_711;
x_689 = x_712;
x_690 = x_713;
x_691 = x_714;
x_692 = x_719;
x_693 = x_720;
x_694 = x_724;
goto block_697;
}
}
else
{
x_698 = x_711;
x_699 = x_712;
x_700 = x_713;
x_701 = x_714;
x_702 = x_716;
x_703 = x_715;
x_704 = lean_box(0);
x_705 = x_719;
x_706 = x_720;
goto block_710;
}
}
block_740:
{
uint8_t x_737; lean_object* x_738; 
x_737 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_730);
x_738 = l_List_appendTR___redArg(x_735, x_730);
if (x_737 == 0)
{
x_711 = x_726;
x_712 = x_727;
x_713 = x_728;
x_714 = x_729;
x_715 = x_738;
x_716 = x_730;
x_717 = lean_box(0);
x_718 = x_731;
x_719 = x_732;
x_720 = x_734;
x_721 = x_733;
goto block_725;
}
else
{
uint8_t x_739; 
x_739 = l_List_isEmpty___redArg(x_730);
if (x_739 == 0)
{
x_670 = x_726;
x_671 = x_727;
x_672 = x_728;
x_673 = x_729;
x_674 = x_730;
x_675 = x_738;
x_676 = lean_box(0);
x_677 = x_731;
x_678 = x_732;
x_679 = x_734;
goto block_687;
}
else
{
if (x_81 == 0)
{
x_711 = x_726;
x_712 = x_727;
x_713 = x_728;
x_714 = x_729;
x_715 = x_738;
x_716 = x_730;
x_717 = lean_box(0);
x_718 = x_731;
x_719 = x_732;
x_720 = x_734;
x_721 = x_733;
goto block_725;
}
else
{
x_670 = x_726;
x_671 = x_727;
x_672 = x_728;
x_673 = x_729;
x_674 = x_730;
x_675 = x_738;
x_676 = lean_box(0);
x_677 = x_731;
x_678 = x_732;
x_679 = x_734;
goto block_687;
}
}
}
}
block_760:
{
lean_object* x_749; double x_750; double x_751; double x_752; double x_753; double x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_749 = lean_io_mono_nanos_now();
x_750 = lean_float_of_nat(x_743);
x_751 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_752 = lean_float_div(x_750, x_751);
x_753 = lean_float_of_nat(x_749);
x_754 = lean_float_div(x_753, x_751);
x_755 = lean_box_float(x_752);
x_756 = lean_box_float(x_754);
x_757 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_756);
x_758 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_758, 0, x_747);
lean_ctor_set(x_758, 1, x_757);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_759 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_110, x_560, x_107, x_746, x_741, x_745, x_758, x_7, x_8, x_9, x_10);
x_587 = x_742;
x_588 = x_744;
x_589 = x_759;
goto block_592;
}
block_770:
{
lean_object* x_769; 
x_769 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_769, 0, x_767);
x_741 = x_761;
x_742 = x_762;
x_743 = x_763;
x_744 = x_764;
x_745 = x_765;
x_746 = x_766;
x_747 = x_769;
x_748 = lean_box(0);
goto block_760;
}
block_780:
{
lean_object* x_779; 
x_779 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_779, 0, x_777);
x_741 = x_771;
x_742 = x_772;
x_743 = x_773;
x_744 = x_774;
x_745 = x_775;
x_746 = x_776;
x_747 = x_779;
x_748 = lean_box(0);
goto block_760;
}
block_793:
{
lean_object* x_791; lean_object* x_792; 
x_791 = l_List_appendTR___redArg(x_785, x_786);
x_792 = l_List_appendTR___redArg(x_791, x_789);
x_771 = x_781;
x_772 = x_782;
x_773 = x_783;
x_774 = x_784;
x_775 = x_787;
x_776 = x_788;
x_777 = x_792;
x_778 = lean_box(0);
goto block_780;
}
block_805:
{
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; 
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
lean_dec_ref(x_802);
x_781 = x_794;
x_782 = x_795;
x_783 = x_796;
x_784 = x_797;
x_785 = x_798;
x_786 = x_799;
x_787 = x_800;
x_788 = x_801;
x_789 = x_803;
x_790 = lean_box(0);
goto block_793;
}
else
{
lean_object* x_804; 
lean_dec(x_799);
lean_dec(x_798);
x_804 = lean_ctor_get(x_802, 0);
lean_inc(x_804);
lean_dec_ref(x_802);
x_761 = x_794;
x_762 = x_795;
x_763 = x_796;
x_764 = x_797;
x_765 = x_800;
x_766 = x_801;
x_767 = x_804;
x_768 = lean_box(0);
goto block_770;
}
}
block_820:
{
if (x_817 == 0)
{
lean_object* x_818; 
lean_dec_ref(x_812);
x_818 = l_Lean_Meta_SavedState_restore___redArg(x_810, x_8, x_10);
lean_dec_ref(x_810);
if (lean_obj_tag(x_818) == 0)
{
lean_dec_ref(x_818);
x_781 = x_806;
x_782 = x_807;
x_783 = x_808;
x_784 = x_809;
x_785 = x_811;
x_786 = x_813;
x_787 = x_815;
x_788 = x_816;
x_789 = x_29;
x_790 = lean_box(0);
goto block_793;
}
else
{
lean_object* x_819; 
lean_dec(x_813);
lean_dec(x_811);
lean_dec(x_29);
x_819 = lean_ctor_get(x_818, 0);
lean_inc(x_819);
lean_dec_ref(x_818);
x_761 = x_806;
x_762 = x_807;
x_763 = x_808;
x_764 = x_809;
x_765 = x_815;
x_766 = x_816;
x_767 = x_819;
x_768 = lean_box(0);
goto block_770;
}
}
else
{
lean_dec_ref(x_810);
lean_dec(x_29);
x_794 = x_806;
x_795 = x_807;
x_796 = x_808;
x_797 = x_809;
x_798 = x_811;
x_799 = x_813;
x_800 = x_815;
x_801 = x_816;
x_802 = x_812;
goto block_805;
}
}
block_838:
{
lean_object* x_831; 
x_831 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_831) == 0)
{
lean_object* x_832; lean_object* x_833; 
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
lean_dec_ref(x_831);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_833 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_825, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_833) == 0)
{
lean_dec(x_832);
lean_dec(x_29);
x_794 = x_821;
x_795 = x_822;
x_796 = x_823;
x_797 = x_824;
x_798 = x_826;
x_799 = x_827;
x_800 = x_829;
x_801 = x_830;
x_802 = x_833;
goto block_805;
}
else
{
lean_object* x_834; uint8_t x_835; 
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
x_835 = l_Lean_Exception_isInterrupt(x_834);
if (x_835 == 0)
{
uint8_t x_836; 
x_836 = l_Lean_Exception_isRuntime(x_834);
x_806 = x_821;
x_807 = x_822;
x_808 = x_823;
x_809 = x_824;
x_810 = x_832;
x_811 = x_826;
x_812 = x_833;
x_813 = x_827;
x_814 = lean_box(0);
x_815 = x_829;
x_816 = x_830;
x_817 = x_836;
goto block_820;
}
else
{
lean_dec(x_834);
x_806 = x_821;
x_807 = x_822;
x_808 = x_823;
x_809 = x_824;
x_810 = x_832;
x_811 = x_826;
x_812 = x_833;
x_813 = x_827;
x_814 = lean_box(0);
x_815 = x_829;
x_816 = x_830;
x_817 = x_835;
goto block_820;
}
}
}
else
{
lean_object* x_837; 
lean_dec(x_827);
lean_dec(x_826);
lean_dec(x_825);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_837 = lean_ctor_get(x_831, 0);
lean_inc(x_837);
lean_dec_ref(x_831);
x_761 = x_821;
x_762 = x_822;
x_763 = x_823;
x_764 = x_824;
x_765 = x_829;
x_766 = x_830;
x_767 = x_837;
x_768 = lean_box(0);
goto block_770;
}
}
block_848:
{
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; 
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
lean_dec_ref(x_845);
x_771 = x_839;
x_772 = x_840;
x_773 = x_841;
x_774 = x_842;
x_775 = x_843;
x_776 = x_844;
x_777 = x_846;
x_778 = lean_box(0);
goto block_780;
}
else
{
lean_object* x_847; 
x_847 = lean_ctor_get(x_845, 0);
lean_inc(x_847);
lean_dec_ref(x_845);
x_761 = x_839;
x_762 = x_840;
x_763 = x_841;
x_764 = x_842;
x_765 = x_843;
x_766 = x_844;
x_767 = x_847;
x_768 = lean_box(0);
goto block_770;
}
}
block_858:
{
lean_object* x_856; lean_object* x_857; 
x_856 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2;
x_857 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_856, x_7, x_8, x_9, x_10);
x_839 = x_849;
x_840 = x_850;
x_841 = x_851;
x_842 = x_852;
x_843 = x_854;
x_844 = x_855;
x_845 = x_857;
goto block_848;
}
block_874:
{
uint8_t x_870; 
x_870 = l_List_isEmpty___redArg(x_866);
lean_dec(x_866);
if (x_870 == 0)
{
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_849 = x_859;
x_850 = x_860;
x_851 = x_861;
x_852 = x_862;
x_853 = lean_box(0);
x_854 = x_867;
x_855 = x_869;
goto block_858;
}
else
{
if (x_868 == 0)
{
lean_object* x_871; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_871 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_863, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_871) == 0)
{
lean_object* x_872; lean_object* x_873; 
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
lean_dec_ref(x_871);
x_873 = l_List_appendTR___redArg(x_864, x_872);
x_771 = x_859;
x_772 = x_860;
x_773 = x_861;
x_774 = x_862;
x_775 = x_867;
x_776 = x_869;
x_777 = x_873;
x_778 = lean_box(0);
goto block_780;
}
else
{
lean_dec(x_864);
x_839 = x_859;
x_840 = x_860;
x_841 = x_861;
x_842 = x_862;
x_843 = x_867;
x_844 = x_869;
x_845 = x_871;
goto block_848;
}
}
else
{
lean_dec(x_864);
lean_dec(x_863);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_849 = x_859;
x_850 = x_860;
x_851 = x_861;
x_852 = x_862;
x_853 = lean_box(0);
x_854 = x_867;
x_855 = x_869;
goto block_858;
}
}
}
block_889:
{
uint8_t x_886; lean_object* x_887; 
x_886 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_879);
x_887 = l_List_appendTR___redArg(x_884, x_879);
if (x_886 == 0)
{
x_859 = x_875;
x_860 = x_876;
x_861 = x_877;
x_862 = x_878;
x_863 = x_887;
x_864 = x_879;
x_865 = lean_box(0);
x_866 = x_880;
x_867 = x_881;
x_868 = x_882;
x_869 = x_883;
goto block_874;
}
else
{
uint8_t x_888; 
x_888 = l_List_isEmpty___redArg(x_879);
if (x_888 == 0)
{
x_821 = x_875;
x_822 = x_876;
x_823 = x_877;
x_824 = x_878;
x_825 = x_887;
x_826 = x_879;
x_827 = x_880;
x_828 = lean_box(0);
x_829 = x_881;
x_830 = x_883;
goto block_838;
}
else
{
if (x_882 == 0)
{
x_859 = x_875;
x_860 = x_876;
x_861 = x_877;
x_862 = x_878;
x_863 = x_887;
x_864 = x_879;
x_865 = lean_box(0);
x_866 = x_880;
x_867 = x_881;
x_868 = x_882;
x_869 = x_883;
goto block_874;
}
else
{
x_821 = x_875;
x_822 = x_876;
x_823 = x_877;
x_824 = x_878;
x_825 = x_887;
x_826 = x_879;
x_827 = x_880;
x_828 = lean_box(0);
x_829 = x_881;
x_830 = x_883;
goto block_838;
}
}
}
}
block_915:
{
lean_object* x_899; 
x_899 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_899) == 0)
{
if (x_897 == 0)
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; 
x_900 = lean_ctor_get(x_899, 0);
lean_inc(x_900);
lean_dec_ref(x_899);
x_901 = lean_io_mono_nanos_now();
x_902 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_897, x_81, x_5, x_898, x_8);
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_903; lean_object* x_904; 
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
lean_dec_ref(x_902);
x_904 = l_List_reverse___redArg(x_903);
x_875 = x_900;
x_876 = x_890;
x_877 = x_901;
x_878 = x_891;
x_879 = x_893;
x_880 = x_894;
x_881 = x_895;
x_882 = x_897;
x_883 = x_896;
x_884 = x_904;
x_885 = lean_box(0);
goto block_889;
}
else
{
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_905; 
x_905 = lean_ctor_get(x_902, 0);
lean_inc(x_905);
lean_dec_ref(x_902);
x_875 = x_900;
x_876 = x_890;
x_877 = x_901;
x_878 = x_891;
x_879 = x_893;
x_880 = x_894;
x_881 = x_895;
x_882 = x_897;
x_883 = x_896;
x_884 = x_905;
x_885 = lean_box(0);
goto block_889;
}
else
{
lean_object* x_906; 
lean_dec(x_894);
lean_dec(x_893);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_906 = lean_ctor_get(x_902, 0);
lean_inc(x_906);
lean_dec_ref(x_902);
x_761 = x_900;
x_762 = x_890;
x_763 = x_901;
x_764 = x_891;
x_765 = x_895;
x_766 = x_896;
x_767 = x_906;
x_768 = lean_box(0);
goto block_770;
}
}
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_907 = lean_ctor_get(x_899, 0);
lean_inc(x_907);
lean_dec_ref(x_899);
x_908 = lean_io_get_num_heartbeats();
x_909 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_897, x_81, x_5, x_898, x_8);
if (lean_obj_tag(x_909) == 0)
{
lean_object* x_910; lean_object* x_911; 
x_910 = lean_ctor_get(x_909, 0);
lean_inc(x_910);
lean_dec_ref(x_909);
x_911 = l_List_reverse___redArg(x_910);
x_726 = x_908;
x_727 = x_907;
x_728 = x_890;
x_729 = x_891;
x_730 = x_893;
x_731 = x_894;
x_732 = x_895;
x_733 = x_897;
x_734 = x_896;
x_735 = x_911;
x_736 = lean_box(0);
goto block_740;
}
else
{
if (lean_obj_tag(x_909) == 0)
{
lean_object* x_912; 
x_912 = lean_ctor_get(x_909, 0);
lean_inc(x_912);
lean_dec_ref(x_909);
x_726 = x_908;
x_727 = x_907;
x_728 = x_890;
x_729 = x_891;
x_730 = x_893;
x_731 = x_894;
x_732 = x_895;
x_733 = x_897;
x_734 = x_896;
x_735 = x_912;
x_736 = lean_box(0);
goto block_740;
}
else
{
lean_object* x_913; 
lean_dec(x_894);
lean_dec(x_893);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_913 = lean_ctor_get(x_909, 0);
lean_inc(x_913);
lean_dec_ref(x_909);
x_610 = x_908;
x_611 = x_907;
x_612 = x_890;
x_613 = x_891;
x_614 = x_895;
x_615 = x_896;
x_616 = x_913;
x_617 = lean_box(0);
goto block_619;
}
}
}
}
else
{
lean_object* x_914; 
lean_dec(x_898);
lean_dec_ref(x_895);
lean_dec(x_894);
lean_dec(x_893);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_914 = lean_ctor_get(x_899, 0);
lean_inc(x_914);
lean_dec_ref(x_899);
x_575 = x_890;
x_576 = x_891;
x_577 = x_914;
x_578 = lean_box(0);
goto block_580;
}
}
block_924:
{
lean_object* x_921; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_921 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_919, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_921) == 0)
{
lean_object* x_922; lean_object* x_923; 
x_922 = lean_ctor_get(x_921, 0);
lean_inc(x_922);
lean_dec_ref(x_921);
x_923 = l_List_appendTR___redArg(x_918, x_922);
x_581 = x_916;
x_582 = x_917;
x_583 = x_923;
x_584 = lean_box(0);
goto block_586;
}
else
{
lean_dec(x_918);
x_587 = x_916;
x_588 = x_917;
x_589 = x_921;
goto block_592;
}
}
block_935:
{
uint8_t x_932; 
x_932 = l_List_isEmpty___redArg(x_930);
lean_dec(x_930);
if (x_932 == 0)
{
if (x_931 == 0)
{
x_916 = x_925;
x_917 = x_926;
x_918 = x_927;
x_919 = x_928;
x_920 = lean_box(0);
goto block_924;
}
else
{
lean_object* x_933; lean_object* x_934; 
lean_dec(x_928);
lean_dec(x_927);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_933 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2;
x_934 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_933, x_7, x_8, x_9, x_10);
x_587 = x_925;
x_588 = x_926;
x_589 = x_934;
goto block_592;
}
}
else
{
x_916 = x_925;
x_917 = x_926;
x_918 = x_927;
x_919 = x_928;
x_920 = lean_box(0);
goto block_924;
}
}
block_944:
{
lean_object* x_942; lean_object* x_943; 
x_942 = l_List_appendTR___redArg(x_938, x_939);
x_943 = l_List_appendTR___redArg(x_942, x_940);
x_581 = x_936;
x_582 = x_937;
x_583 = x_943;
x_584 = lean_box(0);
goto block_586;
}
block_952:
{
if (lean_obj_tag(x_949) == 0)
{
lean_object* x_950; 
x_950 = lean_ctor_get(x_949, 0);
lean_inc(x_950);
lean_dec_ref(x_949);
x_936 = x_945;
x_937 = x_946;
x_938 = x_947;
x_939 = x_948;
x_940 = x_950;
x_941 = lean_box(0);
goto block_944;
}
else
{
lean_object* x_951; 
lean_dec(x_948);
lean_dec(x_947);
x_951 = lean_ctor_get(x_949, 0);
lean_inc(x_951);
lean_dec_ref(x_949);
x_575 = x_945;
x_576 = x_946;
x_577 = x_951;
x_578 = lean_box(0);
goto block_580;
}
}
block_963:
{
if (x_960 == 0)
{
lean_object* x_961; 
lean_dec_ref(x_958);
x_961 = l_Lean_Meta_SavedState_restore___redArg(x_954, x_8, x_10);
lean_dec_ref(x_954);
if (lean_obj_tag(x_961) == 0)
{
lean_dec_ref(x_961);
x_936 = x_953;
x_937 = x_955;
x_938 = x_957;
x_939 = x_959;
x_940 = x_29;
x_941 = lean_box(0);
goto block_944;
}
else
{
lean_object* x_962; 
lean_dec(x_959);
lean_dec(x_957);
lean_dec(x_29);
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
lean_dec_ref(x_961);
x_575 = x_953;
x_576 = x_955;
x_577 = x_962;
x_578 = lean_box(0);
goto block_580;
}
}
else
{
lean_dec_ref(x_954);
lean_dec(x_29);
x_945 = x_953;
x_946 = x_955;
x_947 = x_957;
x_948 = x_959;
x_949 = x_958;
goto block_952;
}
}
block_977:
{
lean_object* x_970; 
x_970 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; lean_object* x_972; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
lean_dec_ref(x_970);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_972 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_967, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_972) == 0)
{
lean_dec(x_971);
lean_dec(x_29);
x_945 = x_964;
x_946 = x_965;
x_947 = x_966;
x_948 = x_968;
x_949 = x_972;
goto block_952;
}
else
{
lean_object* x_973; uint8_t x_974; 
x_973 = lean_ctor_get(x_972, 0);
lean_inc(x_973);
x_974 = l_Lean_Exception_isInterrupt(x_973);
if (x_974 == 0)
{
uint8_t x_975; 
x_975 = l_Lean_Exception_isRuntime(x_973);
x_953 = x_964;
x_954 = x_971;
x_955 = x_965;
x_956 = lean_box(0);
x_957 = x_966;
x_958 = x_972;
x_959 = x_968;
x_960 = x_975;
goto block_963;
}
else
{
lean_dec(x_973);
x_953 = x_964;
x_954 = x_971;
x_955 = x_965;
x_956 = lean_box(0);
x_957 = x_966;
x_958 = x_972;
x_959 = x_968;
x_960 = x_974;
goto block_963;
}
}
}
else
{
lean_object* x_976; 
lean_dec(x_968);
lean_dec(x_967);
lean_dec(x_966);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_976 = lean_ctor_get(x_970, 0);
lean_inc(x_976);
lean_dec_ref(x_970);
x_575 = x_964;
x_576 = x_965;
x_577 = x_976;
x_578 = lean_box(0);
goto block_580;
}
}
block_988:
{
uint8_t x_985; lean_object* x_986; 
x_985 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_980);
x_986 = l_List_appendTR___redArg(x_983, x_980);
if (x_985 == 0)
{
x_925 = x_978;
x_926 = x_979;
x_927 = x_980;
x_928 = x_986;
x_929 = lean_box(0);
x_930 = x_981;
x_931 = x_982;
goto block_935;
}
else
{
uint8_t x_987; 
x_987 = l_List_isEmpty___redArg(x_980);
if (x_987 == 0)
{
x_964 = x_978;
x_965 = x_979;
x_966 = x_980;
x_967 = x_986;
x_968 = x_981;
x_969 = lean_box(0);
goto block_977;
}
else
{
if (x_81 == 0)
{
x_925 = x_978;
x_926 = x_979;
x_927 = x_980;
x_928 = x_986;
x_929 = lean_box(0);
x_930 = x_981;
x_931 = x_982;
goto block_935;
}
else
{
x_964 = x_978;
x_965 = x_979;
x_966 = x_980;
x_967 = x_986;
x_968 = x_981;
x_969 = lean_box(0);
goto block_977;
}
}
}
}
block_1005:
{
lean_object* x_993; double x_994; double x_995; double x_996; double x_997; double x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; lean_object* x_1004; 
x_993 = lean_io_mono_nanos_now();
x_994 = lean_float_of_nat(x_990);
x_995 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_996 = lean_float_div(x_994, x_995);
x_997 = lean_float_of_nat(x_993);
x_998 = lean_float_div(x_997, x_995);
x_999 = lean_box_float(x_996);
x_1000 = lean_box_float(x_998);
x_1001 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1001, 0, x_999);
lean_ctor_set(x_1001, 1, x_1000);
x_1002 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1002, 0, x_991);
lean_ctor_set(x_1002, 1, x_1001);
x_1003 = lean_unbox(x_558);
lean_dec(x_558);
x_1004 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_110, x_560, x_107, x_1003, x_989, x_559, x_1002, x_7, x_8, x_9, x_10);
lean_dec_ref(x_107);
return x_1004;
}
block_1011:
{
lean_object* x_1010; 
x_1010 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1010, 0, x_1008);
x_989 = x_1006;
x_990 = x_1007;
x_991 = x_1010;
x_992 = lean_box(0);
goto block_1005;
}
block_1020:
{
lean_object* x_1018; lean_object* x_1019; 
x_1018 = l_List_appendTR___redArg(x_1014, x_1015);
x_1019 = l_List_appendTR___redArg(x_1018, x_1016);
x_1006 = x_1012;
x_1007 = x_1013;
x_1008 = x_1019;
x_1009 = lean_box(0);
goto block_1011;
}
block_1026:
{
lean_object* x_1025; 
x_1025 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1025, 0, x_1023);
x_989 = x_1021;
x_990 = x_1022;
x_991 = x_1025;
x_992 = lean_box(0);
goto block_1005;
}
block_1034:
{
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; 
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
lean_dec_ref(x_1031);
x_1012 = x_1027;
x_1013 = x_1028;
x_1014 = x_1029;
x_1015 = x_1030;
x_1016 = x_1032;
x_1017 = lean_box(0);
goto block_1020;
}
else
{
lean_object* x_1033; 
lean_dec(x_1030);
lean_dec(x_1029);
x_1033 = lean_ctor_get(x_1031, 0);
lean_inc(x_1033);
lean_dec_ref(x_1031);
x_1021 = x_1027;
x_1022 = x_1028;
x_1023 = x_1033;
x_1024 = lean_box(0);
goto block_1026;
}
}
block_1045:
{
if (x_1042 == 0)
{
lean_object* x_1043; 
lean_dec_ref(x_1040);
x_1043 = l_Lean_Meta_SavedState_restore___redArg(x_1036, x_8, x_10);
lean_dec_ref(x_1036);
if (lean_obj_tag(x_1043) == 0)
{
lean_dec_ref(x_1043);
x_1012 = x_1035;
x_1013 = x_1037;
x_1014 = x_1038;
x_1015 = x_1041;
x_1016 = x_29;
x_1017 = lean_box(0);
goto block_1020;
}
else
{
lean_object* x_1044; 
lean_dec(x_1041);
lean_dec(x_1038);
lean_dec(x_29);
x_1044 = lean_ctor_get(x_1043, 0);
lean_inc(x_1044);
lean_dec_ref(x_1043);
x_1021 = x_1035;
x_1022 = x_1037;
x_1023 = x_1044;
x_1024 = lean_box(0);
goto block_1026;
}
}
else
{
lean_dec_ref(x_1036);
lean_dec(x_29);
x_1027 = x_1035;
x_1028 = x_1037;
x_1029 = x_1038;
x_1030 = x_1041;
x_1031 = x_1040;
goto block_1034;
}
}
block_1059:
{
lean_object* x_1052; 
x_1052 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1052) == 0)
{
lean_object* x_1053; lean_object* x_1054; 
x_1053 = lean_ctor_get(x_1052, 0);
lean_inc(x_1053);
lean_dec_ref(x_1052);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_1054 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1048, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1054) == 0)
{
lean_dec(x_1053);
lean_dec(x_29);
x_1027 = x_1046;
x_1028 = x_1049;
x_1029 = x_1050;
x_1030 = x_1051;
x_1031 = x_1054;
goto block_1034;
}
else
{
lean_object* x_1055; uint8_t x_1056; 
x_1055 = lean_ctor_get(x_1054, 0);
lean_inc(x_1055);
x_1056 = l_Lean_Exception_isInterrupt(x_1055);
if (x_1056 == 0)
{
uint8_t x_1057; 
x_1057 = l_Lean_Exception_isRuntime(x_1055);
x_1035 = x_1046;
x_1036 = x_1053;
x_1037 = x_1049;
x_1038 = x_1050;
x_1039 = lean_box(0);
x_1040 = x_1054;
x_1041 = x_1051;
x_1042 = x_1057;
goto block_1045;
}
else
{
lean_dec(x_1055);
x_1035 = x_1046;
x_1036 = x_1053;
x_1037 = x_1049;
x_1038 = x_1050;
x_1039 = lean_box(0);
x_1040 = x_1054;
x_1041 = x_1051;
x_1042 = x_1056;
goto block_1045;
}
}
}
else
{
lean_object* x_1058; 
lean_dec(x_1051);
lean_dec(x_1050);
lean_dec(x_1048);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1058 = lean_ctor_get(x_1052, 0);
lean_inc(x_1058);
lean_dec_ref(x_1052);
x_1021 = x_1046;
x_1022 = x_1049;
x_1023 = x_1058;
x_1024 = lean_box(0);
goto block_1026;
}
}
block_1065:
{
if (lean_obj_tag(x_1062) == 0)
{
lean_object* x_1063; 
x_1063 = lean_ctor_get(x_1062, 0);
lean_inc(x_1063);
lean_dec_ref(x_1062);
x_1006 = x_1060;
x_1007 = x_1061;
x_1008 = x_1063;
x_1009 = lean_box(0);
goto block_1011;
}
else
{
lean_object* x_1064; 
x_1064 = lean_ctor_get(x_1062, 0);
lean_inc(x_1064);
lean_dec_ref(x_1062);
x_1021 = x_1060;
x_1022 = x_1061;
x_1023 = x_1064;
x_1024 = lean_box(0);
goto block_1026;
}
}
block_1085:
{
lean_object* x_1074; double x_1075; double x_1076; double x_1077; double x_1078; double x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
x_1074 = lean_io_mono_nanos_now();
x_1075 = lean_float_of_nat(x_1071);
x_1076 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_1077 = lean_float_div(x_1075, x_1076);
x_1078 = lean_float_of_nat(x_1074);
x_1079 = lean_float_div(x_1078, x_1076);
x_1080 = lean_box_float(x_1077);
x_1081 = lean_box_float(x_1079);
x_1082 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1082, 0, x_1080);
lean_ctor_set(x_1082, 1, x_1081);
x_1083 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1083, 0, x_1072);
lean_ctor_set(x_1083, 1, x_1082);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1084 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_110, x_560, x_107, x_1066, x_1067, x_1070, x_1083, x_7, x_8, x_9, x_10);
x_1060 = x_1068;
x_1061 = x_1069;
x_1062 = x_1084;
goto block_1065;
}
block_1095:
{
lean_object* x_1094; 
x_1094 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1094, 0, x_1092);
x_1066 = x_1086;
x_1067 = x_1087;
x_1068 = x_1088;
x_1069 = x_1090;
x_1070 = x_1089;
x_1071 = x_1091;
x_1072 = x_1094;
x_1073 = lean_box(0);
goto block_1085;
}
block_1105:
{
lean_object* x_1104; 
x_1104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1104, 0, x_1102);
x_1066 = x_1096;
x_1067 = x_1097;
x_1068 = x_1098;
x_1069 = x_1100;
x_1070 = x_1099;
x_1071 = x_1101;
x_1072 = x_1104;
x_1073 = lean_box(0);
goto block_1085;
}
block_1118:
{
lean_object* x_1116; lean_object* x_1117; 
x_1116 = l_List_appendTR___redArg(x_1111, x_1113);
x_1117 = l_List_appendTR___redArg(x_1116, x_1114);
x_1096 = x_1106;
x_1097 = x_1107;
x_1098 = x_1108;
x_1099 = x_1110;
x_1100 = x_1109;
x_1101 = x_1112;
x_1102 = x_1117;
x_1103 = lean_box(0);
goto block_1105;
}
block_1130:
{
if (lean_obj_tag(x_1127) == 0)
{
lean_object* x_1128; 
x_1128 = lean_ctor_get(x_1127, 0);
lean_inc(x_1128);
lean_dec_ref(x_1127);
x_1106 = x_1119;
x_1107 = x_1120;
x_1108 = x_1121;
x_1109 = x_1123;
x_1110 = x_1122;
x_1111 = x_1124;
x_1112 = x_1125;
x_1113 = x_1126;
x_1114 = x_1128;
x_1115 = lean_box(0);
goto block_1118;
}
else
{
lean_object* x_1129; 
lean_dec(x_1126);
lean_dec(x_1124);
x_1129 = lean_ctor_get(x_1127, 0);
lean_inc(x_1129);
lean_dec_ref(x_1127);
x_1086 = x_1119;
x_1087 = x_1120;
x_1088 = x_1121;
x_1089 = x_1122;
x_1090 = x_1123;
x_1091 = x_1125;
x_1092 = x_1129;
x_1093 = lean_box(0);
goto block_1095;
}
}
block_1145:
{
if (x_1142 == 0)
{
lean_object* x_1143; 
lean_dec_ref(x_1134);
x_1143 = l_Lean_Meta_SavedState_restore___redArg(x_1138, x_8, x_10);
lean_dec_ref(x_1138);
if (lean_obj_tag(x_1143) == 0)
{
lean_dec_ref(x_1143);
x_1106 = x_1131;
x_1107 = x_1132;
x_1108 = x_1133;
x_1109 = x_1136;
x_1110 = x_1135;
x_1111 = x_1137;
x_1112 = x_1139;
x_1113 = x_1140;
x_1114 = x_29;
x_1115 = lean_box(0);
goto block_1118;
}
else
{
lean_object* x_1144; 
lean_dec(x_1140);
lean_dec(x_1137);
lean_dec(x_29);
x_1144 = lean_ctor_get(x_1143, 0);
lean_inc(x_1144);
lean_dec_ref(x_1143);
x_1086 = x_1131;
x_1087 = x_1132;
x_1088 = x_1133;
x_1089 = x_1135;
x_1090 = x_1136;
x_1091 = x_1139;
x_1092 = x_1144;
x_1093 = lean_box(0);
goto block_1095;
}
}
else
{
lean_dec_ref(x_1138);
lean_dec(x_29);
x_1119 = x_1131;
x_1120 = x_1132;
x_1121 = x_1133;
x_1122 = x_1135;
x_1123 = x_1136;
x_1124 = x_1137;
x_1125 = x_1139;
x_1126 = x_1140;
x_1127 = x_1134;
goto block_1130;
}
}
block_1163:
{
lean_object* x_1156; 
x_1156 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1156) == 0)
{
lean_object* x_1157; lean_object* x_1158; 
x_1157 = lean_ctor_get(x_1156, 0);
lean_inc(x_1157);
lean_dec_ref(x_1156);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_1158 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1149, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1158) == 0)
{
lean_dec(x_1157);
lean_dec(x_29);
x_1119 = x_1146;
x_1120 = x_1147;
x_1121 = x_1148;
x_1122 = x_1151;
x_1123 = x_1150;
x_1124 = x_1153;
x_1125 = x_1154;
x_1126 = x_1155;
x_1127 = x_1158;
goto block_1130;
}
else
{
lean_object* x_1159; uint8_t x_1160; 
x_1159 = lean_ctor_get(x_1158, 0);
lean_inc(x_1159);
x_1160 = l_Lean_Exception_isInterrupt(x_1159);
if (x_1160 == 0)
{
uint8_t x_1161; 
x_1161 = l_Lean_Exception_isRuntime(x_1159);
x_1131 = x_1146;
x_1132 = x_1147;
x_1133 = x_1148;
x_1134 = x_1158;
x_1135 = x_1151;
x_1136 = x_1150;
x_1137 = x_1153;
x_1138 = x_1157;
x_1139 = x_1154;
x_1140 = x_1155;
x_1141 = lean_box(0);
x_1142 = x_1161;
goto block_1145;
}
else
{
lean_dec(x_1159);
x_1131 = x_1146;
x_1132 = x_1147;
x_1133 = x_1148;
x_1134 = x_1158;
x_1135 = x_1151;
x_1136 = x_1150;
x_1137 = x_1153;
x_1138 = x_1157;
x_1139 = x_1154;
x_1140 = x_1155;
x_1141 = lean_box(0);
x_1142 = x_1160;
goto block_1145;
}
}
}
else
{
lean_object* x_1162; 
lean_dec(x_1155);
lean_dec(x_1153);
lean_dec(x_1149);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1162 = lean_ctor_get(x_1156, 0);
lean_inc(x_1162);
lean_dec_ref(x_1156);
x_1086 = x_1146;
x_1087 = x_1147;
x_1088 = x_1148;
x_1089 = x_1151;
x_1090 = x_1150;
x_1091 = x_1154;
x_1092 = x_1162;
x_1093 = lean_box(0);
goto block_1095;
}
}
block_1173:
{
if (lean_obj_tag(x_1170) == 0)
{
lean_object* x_1171; 
x_1171 = lean_ctor_get(x_1170, 0);
lean_inc(x_1171);
lean_dec_ref(x_1170);
x_1096 = x_1164;
x_1097 = x_1165;
x_1098 = x_1166;
x_1099 = x_1168;
x_1100 = x_1167;
x_1101 = x_1169;
x_1102 = x_1171;
x_1103 = lean_box(0);
goto block_1105;
}
else
{
lean_object* x_1172; 
x_1172 = lean_ctor_get(x_1170, 0);
lean_inc(x_1172);
lean_dec_ref(x_1170);
x_1086 = x_1164;
x_1087 = x_1165;
x_1088 = x_1166;
x_1089 = x_1168;
x_1090 = x_1167;
x_1091 = x_1169;
x_1092 = x_1172;
x_1093 = lean_box(0);
goto block_1095;
}
}
block_1183:
{
lean_object* x_1181; lean_object* x_1182; 
x_1181 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2;
x_1182 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1181, x_7, x_8, x_9, x_10);
x_1164 = x_1174;
x_1165 = x_1175;
x_1166 = x_1176;
x_1167 = x_1178;
x_1168 = x_1177;
x_1169 = x_1180;
x_1170 = x_1182;
goto block_1173;
}
block_1199:
{
uint8_t x_1195; 
x_1195 = l_List_isEmpty___redArg(x_1194);
lean_dec(x_1194);
if (x_1195 == 0)
{
lean_dec(x_1191);
lean_dec(x_1186);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1174 = x_1184;
x_1175 = x_1185;
x_1176 = x_1187;
x_1177 = x_1190;
x_1178 = x_1189;
x_1179 = lean_box(0);
x_1180 = x_1192;
goto block_1183;
}
else
{
if (x_1193 == 0)
{
lean_object* x_1196; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1196 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1186, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1196) == 0)
{
lean_object* x_1197; lean_object* x_1198; 
x_1197 = lean_ctor_get(x_1196, 0);
lean_inc(x_1197);
lean_dec_ref(x_1196);
x_1198 = l_List_appendTR___redArg(x_1191, x_1197);
x_1096 = x_1184;
x_1097 = x_1185;
x_1098 = x_1187;
x_1099 = x_1190;
x_1100 = x_1189;
x_1101 = x_1192;
x_1102 = x_1198;
x_1103 = lean_box(0);
goto block_1105;
}
else
{
lean_dec(x_1191);
x_1164 = x_1184;
x_1165 = x_1185;
x_1166 = x_1187;
x_1167 = x_1189;
x_1168 = x_1190;
x_1169 = x_1192;
x_1170 = x_1196;
goto block_1173;
}
}
else
{
lean_dec(x_1191);
lean_dec(x_1186);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1174 = x_1184;
x_1175 = x_1185;
x_1176 = x_1187;
x_1177 = x_1190;
x_1178 = x_1189;
x_1179 = lean_box(0);
x_1180 = x_1192;
goto block_1183;
}
}
}
block_1214:
{
uint8_t x_1211; lean_object* x_1212; 
x_1211 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_1205);
x_1212 = l_List_appendTR___redArg(x_1209, x_1205);
if (x_1211 == 0)
{
x_1184 = x_1200;
x_1185 = x_1201;
x_1186 = x_1212;
x_1187 = x_1202;
x_1188 = lean_box(0);
x_1189 = x_1203;
x_1190 = x_1204;
x_1191 = x_1205;
x_1192 = x_1206;
x_1193 = x_1207;
x_1194 = x_1208;
goto block_1199;
}
else
{
uint8_t x_1213; 
x_1213 = l_List_isEmpty___redArg(x_1205);
if (x_1213 == 0)
{
x_1146 = x_1200;
x_1147 = x_1201;
x_1148 = x_1202;
x_1149 = x_1212;
x_1150 = x_1203;
x_1151 = x_1204;
x_1152 = lean_box(0);
x_1153 = x_1205;
x_1154 = x_1206;
x_1155 = x_1208;
goto block_1163;
}
else
{
if (x_1207 == 0)
{
x_1184 = x_1200;
x_1185 = x_1201;
x_1186 = x_1212;
x_1187 = x_1202;
x_1188 = lean_box(0);
x_1189 = x_1203;
x_1190 = x_1204;
x_1191 = x_1205;
x_1192 = x_1206;
x_1193 = x_1207;
x_1194 = x_1208;
goto block_1199;
}
else
{
x_1146 = x_1200;
x_1147 = x_1201;
x_1148 = x_1202;
x_1149 = x_1212;
x_1150 = x_1203;
x_1151 = x_1204;
x_1152 = lean_box(0);
x_1153 = x_1205;
x_1154 = x_1206;
x_1155 = x_1208;
goto block_1163;
}
}
}
}
block_1231:
{
lean_object* x_1223; double x_1224; double x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; 
x_1223 = lean_io_get_num_heartbeats();
x_1224 = lean_float_of_nat(x_1220);
x_1225 = lean_float_of_nat(x_1223);
x_1226 = lean_box_float(x_1224);
x_1227 = lean_box_float(x_1225);
x_1228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1228, 0, x_1226);
lean_ctor_set(x_1228, 1, x_1227);
x_1229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1229, 0, x_1221);
lean_ctor_set(x_1229, 1, x_1228);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1230 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_110, x_560, x_107, x_1215, x_1216, x_1219, x_1229, x_7, x_8, x_9, x_10);
x_1060 = x_1217;
x_1061 = x_1218;
x_1062 = x_1230;
goto block_1065;
}
block_1241:
{
lean_object* x_1240; 
x_1240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1240, 0, x_1238);
x_1215 = x_1232;
x_1216 = x_1233;
x_1217 = x_1234;
x_1218 = x_1236;
x_1219 = x_1235;
x_1220 = x_1237;
x_1221 = x_1240;
x_1222 = lean_box(0);
goto block_1231;
}
block_1254:
{
lean_object* x_1252; lean_object* x_1253; 
x_1252 = l_List_appendTR___redArg(x_1247, x_1249);
x_1253 = l_List_appendTR___redArg(x_1252, x_1250);
x_1232 = x_1242;
x_1233 = x_1243;
x_1234 = x_1244;
x_1235 = x_1246;
x_1236 = x_1245;
x_1237 = x_1248;
x_1238 = x_1253;
x_1239 = lean_box(0);
goto block_1241;
}
block_1264:
{
lean_object* x_1263; 
x_1263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1263, 0, x_1261);
x_1215 = x_1255;
x_1216 = x_1256;
x_1217 = x_1257;
x_1218 = x_1259;
x_1219 = x_1258;
x_1220 = x_1260;
x_1221 = x_1263;
x_1222 = lean_box(0);
goto block_1231;
}
block_1274:
{
if (lean_obj_tag(x_1271) == 0)
{
lean_object* x_1272; 
x_1272 = lean_ctor_get(x_1271, 0);
lean_inc(x_1272);
lean_dec_ref(x_1271);
x_1232 = x_1265;
x_1233 = x_1266;
x_1234 = x_1267;
x_1235 = x_1269;
x_1236 = x_1268;
x_1237 = x_1270;
x_1238 = x_1272;
x_1239 = lean_box(0);
goto block_1241;
}
else
{
lean_object* x_1273; 
x_1273 = lean_ctor_get(x_1271, 0);
lean_inc(x_1273);
lean_dec_ref(x_1271);
x_1255 = x_1265;
x_1256 = x_1266;
x_1257 = x_1267;
x_1258 = x_1269;
x_1259 = x_1268;
x_1260 = x_1270;
x_1261 = x_1273;
x_1262 = lean_box(0);
goto block_1264;
}
}
block_1287:
{
lean_object* x_1284; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1284 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1282, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1284) == 0)
{
lean_object* x_1285; lean_object* x_1286; 
x_1285 = lean_ctor_get(x_1284, 0);
lean_inc(x_1285);
lean_dec_ref(x_1284);
x_1286 = l_List_appendTR___redArg(x_1281, x_1285);
x_1232 = x_1275;
x_1233 = x_1276;
x_1234 = x_1277;
x_1235 = x_1280;
x_1236 = x_1279;
x_1237 = x_1283;
x_1238 = x_1286;
x_1239 = lean_box(0);
goto block_1241;
}
else
{
lean_dec(x_1281);
x_1265 = x_1275;
x_1266 = x_1276;
x_1267 = x_1277;
x_1268 = x_1279;
x_1269 = x_1280;
x_1270 = x_1283;
x_1271 = x_1284;
goto block_1274;
}
}
block_1299:
{
if (lean_obj_tag(x_1296) == 0)
{
lean_object* x_1297; 
x_1297 = lean_ctor_get(x_1296, 0);
lean_inc(x_1297);
lean_dec_ref(x_1296);
x_1242 = x_1288;
x_1243 = x_1289;
x_1244 = x_1290;
x_1245 = x_1292;
x_1246 = x_1291;
x_1247 = x_1293;
x_1248 = x_1294;
x_1249 = x_1295;
x_1250 = x_1297;
x_1251 = lean_box(0);
goto block_1254;
}
else
{
lean_object* x_1298; 
lean_dec(x_1295);
lean_dec(x_1293);
x_1298 = lean_ctor_get(x_1296, 0);
lean_inc(x_1298);
lean_dec_ref(x_1296);
x_1255 = x_1288;
x_1256 = x_1289;
x_1257 = x_1290;
x_1258 = x_1291;
x_1259 = x_1292;
x_1260 = x_1294;
x_1261 = x_1298;
x_1262 = lean_box(0);
goto block_1264;
}
}
block_1314:
{
if (x_1311 == 0)
{
lean_object* x_1312; 
lean_dec_ref(x_1309);
x_1312 = l_Lean_Meta_SavedState_restore___redArg(x_1306, x_8, x_10);
lean_dec_ref(x_1306);
if (lean_obj_tag(x_1312) == 0)
{
lean_dec_ref(x_1312);
x_1242 = x_1300;
x_1243 = x_1301;
x_1244 = x_1302;
x_1245 = x_1304;
x_1246 = x_1303;
x_1247 = x_1305;
x_1248 = x_1308;
x_1249 = x_1310;
x_1250 = x_29;
x_1251 = lean_box(0);
goto block_1254;
}
else
{
lean_object* x_1313; 
lean_dec(x_1310);
lean_dec(x_1305);
lean_dec(x_29);
x_1313 = lean_ctor_get(x_1312, 0);
lean_inc(x_1313);
lean_dec_ref(x_1312);
x_1255 = x_1300;
x_1256 = x_1301;
x_1257 = x_1302;
x_1258 = x_1303;
x_1259 = x_1304;
x_1260 = x_1308;
x_1261 = x_1313;
x_1262 = lean_box(0);
goto block_1264;
}
}
else
{
lean_dec_ref(x_1306);
lean_dec(x_29);
x_1288 = x_1300;
x_1289 = x_1301;
x_1290 = x_1302;
x_1291 = x_1303;
x_1292 = x_1304;
x_1293 = x_1305;
x_1294 = x_1308;
x_1295 = x_1310;
x_1296 = x_1309;
goto block_1299;
}
}
block_1332:
{
lean_object* x_1325; 
x_1325 = l_Lean_Meta_saveState___redArg(x_8, x_10);
if (lean_obj_tag(x_1325) == 0)
{
lean_object* x_1326; lean_object* x_1327; 
x_1326 = lean_ctor_get(x_1325, 0);
lean_inc(x_1326);
lean_dec_ref(x_1325);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_29);
lean_inc(x_2);
x_1327 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1322, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1327) == 0)
{
lean_dec(x_1326);
lean_dec(x_29);
x_1288 = x_1315;
x_1289 = x_1316;
x_1290 = x_1317;
x_1291 = x_1320;
x_1292 = x_1319;
x_1293 = x_1321;
x_1294 = x_1323;
x_1295 = x_1324;
x_1296 = x_1327;
goto block_1299;
}
else
{
lean_object* x_1328; uint8_t x_1329; 
x_1328 = lean_ctor_get(x_1327, 0);
lean_inc(x_1328);
x_1329 = l_Lean_Exception_isInterrupt(x_1328);
if (x_1329 == 0)
{
uint8_t x_1330; 
x_1330 = l_Lean_Exception_isRuntime(x_1328);
x_1300 = x_1315;
x_1301 = x_1316;
x_1302 = x_1317;
x_1303 = x_1320;
x_1304 = x_1319;
x_1305 = x_1321;
x_1306 = x_1326;
x_1307 = lean_box(0);
x_1308 = x_1323;
x_1309 = x_1327;
x_1310 = x_1324;
x_1311 = x_1330;
goto block_1314;
}
else
{
lean_dec(x_1328);
x_1300 = x_1315;
x_1301 = x_1316;
x_1302 = x_1317;
x_1303 = x_1320;
x_1304 = x_1319;
x_1305 = x_1321;
x_1306 = x_1326;
x_1307 = lean_box(0);
x_1308 = x_1323;
x_1309 = x_1327;
x_1310 = x_1324;
x_1311 = x_1329;
goto block_1314;
}
}
}
else
{
lean_object* x_1331; 
lean_dec(x_1324);
lean_dec(x_1322);
lean_dec(x_1321);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1331 = lean_ctor_get(x_1325, 0);
lean_inc(x_1331);
lean_dec_ref(x_1325);
x_1255 = x_1315;
x_1256 = x_1316;
x_1257 = x_1317;
x_1258 = x_1320;
x_1259 = x_1319;
x_1260 = x_1323;
x_1261 = x_1331;
x_1262 = lean_box(0);
goto block_1264;
}
}
block_1349:
{
uint8_t x_1344; lean_object* x_1345; 
x_1344 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_1338);
x_1345 = l_List_appendTR___redArg(x_1342, x_1338);
if (x_1344 == 0)
{
lean_dec(x_1341);
if (x_1340 == 0)
{
x_1275 = x_1333;
x_1276 = x_1334;
x_1277 = x_1335;
x_1278 = lean_box(0);
x_1279 = x_1337;
x_1280 = x_1336;
x_1281 = x_1338;
x_1282 = x_1345;
x_1283 = x_1339;
goto block_1287;
}
else
{
lean_object* x_1346; lean_object* x_1347; 
lean_dec(x_1345);
lean_dec(x_1338);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1346 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2;
x_1347 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1346, x_7, x_8, x_9, x_10);
x_1265 = x_1333;
x_1266 = x_1334;
x_1267 = x_1335;
x_1268 = x_1337;
x_1269 = x_1336;
x_1270 = x_1339;
x_1271 = x_1347;
goto block_1274;
}
}
else
{
uint8_t x_1348; 
x_1348 = l_List_isEmpty___redArg(x_1338);
if (x_1348 == 0)
{
x_1315 = x_1333;
x_1316 = x_1334;
x_1317 = x_1335;
x_1318 = lean_box(0);
x_1319 = x_1337;
x_1320 = x_1336;
x_1321 = x_1338;
x_1322 = x_1345;
x_1323 = x_1339;
x_1324 = x_1341;
goto block_1332;
}
else
{
if (x_1340 == 0)
{
lean_dec(x_1341);
x_1275 = x_1333;
x_1276 = x_1334;
x_1277 = x_1335;
x_1278 = lean_box(0);
x_1279 = x_1337;
x_1280 = x_1336;
x_1281 = x_1338;
x_1282 = x_1345;
x_1283 = x_1339;
goto block_1287;
}
else
{
x_1315 = x_1333;
x_1316 = x_1334;
x_1317 = x_1335;
x_1318 = lean_box(0);
x_1319 = x_1337;
x_1320 = x_1336;
x_1321 = x_1338;
x_1322 = x_1345;
x_1323 = x_1339;
x_1324 = x_1341;
goto block_1332;
}
}
}
}
block_1375:
{
lean_object* x_1359; 
x_1359 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_1359) == 0)
{
if (x_1358 == 0)
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; 
x_1360 = lean_ctor_get(x_1359, 0);
lean_inc(x_1360);
lean_dec_ref(x_1359);
x_1361 = lean_io_mono_nanos_now();
x_1362 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_108, x_1358, x_5, x_1351, x_8);
if (lean_obj_tag(x_1362) == 0)
{
lean_object* x_1363; lean_object* x_1364; 
x_1363 = lean_ctor_get(x_1362, 0);
lean_inc(x_1363);
lean_dec_ref(x_1362);
x_1364 = l_List_reverse___redArg(x_1363);
x_1200 = x_1350;
x_1201 = x_1360;
x_1202 = x_1352;
x_1203 = x_1354;
x_1204 = x_1353;
x_1205 = x_1355;
x_1206 = x_1361;
x_1207 = x_1358;
x_1208 = x_1357;
x_1209 = x_1364;
x_1210 = lean_box(0);
goto block_1214;
}
else
{
if (lean_obj_tag(x_1362) == 0)
{
lean_object* x_1365; 
x_1365 = lean_ctor_get(x_1362, 0);
lean_inc(x_1365);
lean_dec_ref(x_1362);
x_1200 = x_1350;
x_1201 = x_1360;
x_1202 = x_1352;
x_1203 = x_1354;
x_1204 = x_1353;
x_1205 = x_1355;
x_1206 = x_1361;
x_1207 = x_1358;
x_1208 = x_1357;
x_1209 = x_1365;
x_1210 = lean_box(0);
goto block_1214;
}
else
{
lean_object* x_1366; 
lean_dec(x_1357);
lean_dec(x_1355);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1366 = lean_ctor_get(x_1362, 0);
lean_inc(x_1366);
lean_dec_ref(x_1362);
x_1086 = x_1350;
x_1087 = x_1360;
x_1088 = x_1352;
x_1089 = x_1353;
x_1090 = x_1354;
x_1091 = x_1361;
x_1092 = x_1366;
x_1093 = lean_box(0);
goto block_1095;
}
}
}
else
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
x_1367 = lean_ctor_get(x_1359, 0);
lean_inc(x_1367);
lean_dec_ref(x_1359);
x_1368 = lean_io_get_num_heartbeats();
x_1369 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_108, x_1358, x_5, x_1351, x_8);
if (lean_obj_tag(x_1369) == 0)
{
lean_object* x_1370; lean_object* x_1371; 
x_1370 = lean_ctor_get(x_1369, 0);
lean_inc(x_1370);
lean_dec_ref(x_1369);
x_1371 = l_List_reverse___redArg(x_1370);
x_1333 = x_1350;
x_1334 = x_1367;
x_1335 = x_1352;
x_1336 = x_1353;
x_1337 = x_1354;
x_1338 = x_1355;
x_1339 = x_1368;
x_1340 = x_1358;
x_1341 = x_1357;
x_1342 = x_1371;
x_1343 = lean_box(0);
goto block_1349;
}
else
{
if (lean_obj_tag(x_1369) == 0)
{
lean_object* x_1372; 
x_1372 = lean_ctor_get(x_1369, 0);
lean_inc(x_1372);
lean_dec_ref(x_1369);
x_1333 = x_1350;
x_1334 = x_1367;
x_1335 = x_1352;
x_1336 = x_1353;
x_1337 = x_1354;
x_1338 = x_1355;
x_1339 = x_1368;
x_1340 = x_1358;
x_1341 = x_1357;
x_1342 = x_1372;
x_1343 = lean_box(0);
goto block_1349;
}
else
{
lean_object* x_1373; 
lean_dec(x_1357);
lean_dec(x_1355);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1373 = lean_ctor_get(x_1369, 0);
lean_inc(x_1373);
lean_dec_ref(x_1369);
x_1255 = x_1350;
x_1256 = x_1367;
x_1257 = x_1352;
x_1258 = x_1353;
x_1259 = x_1354;
x_1260 = x_1368;
x_1261 = x_1373;
x_1262 = lean_box(0);
goto block_1264;
}
}
}
}
else
{
lean_object* x_1374; 
lean_dec(x_1357);
lean_dec(x_1355);
lean_dec_ref(x_1353);
lean_dec(x_1351);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1374 = lean_ctor_get(x_1359, 0);
lean_inc(x_1374);
lean_dec_ref(x_1359);
x_1021 = x_1352;
x_1022 = x_1354;
x_1023 = x_1374;
x_1024 = lean_box(0);
goto block_1026;
}
}
block_1381:
{
lean_object* x_1379; lean_object* x_1380; 
x_1379 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2;
x_1380 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_1379, x_7, x_8, x_9, x_10);
x_1060 = x_1376;
x_1061 = x_1378;
x_1062 = x_1380;
goto block_1065;
}
block_1393:
{
uint8_t x_1389; 
x_1389 = l_List_isEmpty___redArg(x_1388);
lean_dec(x_1388);
if (x_1389 == 0)
{
lean_dec(x_1386);
lean_dec(x_1384);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1376 = x_1383;
x_1377 = lean_box(0);
x_1378 = x_1385;
goto block_1381;
}
else
{
if (x_1387 == 0)
{
lean_object* x_1390; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_2);
x_1390 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_1384, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1390) == 0)
{
lean_object* x_1391; lean_object* x_1392; 
x_1391 = lean_ctor_get(x_1390, 0);
lean_inc(x_1391);
lean_dec_ref(x_1390);
x_1392 = l_List_appendTR___redArg(x_1386, x_1391);
x_1006 = x_1383;
x_1007 = x_1385;
x_1008 = x_1392;
x_1009 = lean_box(0);
goto block_1011;
}
else
{
lean_dec(x_1386);
x_1060 = x_1383;
x_1061 = x_1385;
x_1062 = x_1390;
goto block_1065;
}
}
else
{
lean_dec(x_1386);
lean_dec(x_1384);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1376 = x_1383;
x_1377 = lean_box(0);
x_1378 = x_1385;
goto block_1381;
}
}
}
block_1404:
{
uint8_t x_1401; lean_object* x_1402; 
x_1401 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_1396);
x_1402 = l_List_appendTR___redArg(x_1399, x_1396);
if (x_1401 == 0)
{
x_1382 = lean_box(0);
x_1383 = x_1394;
x_1384 = x_1402;
x_1385 = x_1395;
x_1386 = x_1396;
x_1387 = x_1397;
x_1388 = x_1398;
goto block_1393;
}
else
{
uint8_t x_1403; 
x_1403 = l_List_isEmpty___redArg(x_1396);
if (x_1403 == 0)
{
x_1046 = x_1394;
x_1047 = lean_box(0);
x_1048 = x_1402;
x_1049 = x_1395;
x_1050 = x_1396;
x_1051 = x_1398;
goto block_1059;
}
else
{
if (x_1397 == 0)
{
x_1382 = lean_box(0);
x_1383 = x_1394;
x_1384 = x_1402;
x_1385 = x_1395;
x_1386 = x_1396;
x_1387 = x_1397;
x_1388 = x_1398;
goto block_1393;
}
else
{
x_1046 = x_1394;
x_1047 = lean_box(0);
x_1048 = x_1402;
x_1049 = x_1395;
x_1050 = x_1396;
x_1051 = x_1398;
goto block_1059;
}
}
}
}
block_1454:
{
lean_object* x_1405; 
x_1405 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_10);
if (lean_obj_tag(x_1405) == 0)
{
lean_object* x_1406; lean_object* x_1407; uint8_t x_1408; 
x_1406 = lean_ctor_get(x_1405, 0);
lean_inc(x_1406);
lean_dec_ref(x_1405);
x_1407 = l_Lean_trace_profiler_useHeartbeats;
x_1408 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_107, x_1407);
if (x_1408 == 0)
{
lean_object* x_1409; lean_object* x_1410; 
x_1409 = lean_io_mono_nanos_now();
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_1410 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_28, x_109, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1410) == 0)
{
lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; 
x_1411 = lean_ctor_get(x_1410, 0);
lean_inc(x_1411);
lean_dec_ref(x_1410);
x_1412 = lean_ctor_get(x_1411, 0);
lean_inc(x_1412);
x_1413 = lean_ctor_get(x_1411, 1);
lean_inc(x_1413);
lean_dec(x_1411);
lean_inc(x_2);
x_1414 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_1414) == 0)
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; uint8_t x_1419; 
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
lean_dec_ref(x_1414);
x_1416 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_1413, x_25);
lean_inc(x_1416);
lean_inc(x_1412);
x_1417 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(x_1417, 0, x_1412);
lean_closure_set(x_1417, 1, x_1416);
x_1418 = lean_box(0);
x_1419 = lean_unbox(x_1415);
if (x_1419 == 0)
{
lean_object* x_1420; uint8_t x_1421; 
x_1420 = l_Lean_trace_profiler;
x_1421 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_107, x_1420);
if (x_1421 == 0)
{
lean_object* x_1422; 
lean_dec_ref(x_1417);
lean_dec(x_1415);
x_1422 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_108, x_1408, x_5, x_1418, x_8);
if (lean_obj_tag(x_1422) == 0)
{
lean_object* x_1423; lean_object* x_1424; 
x_1423 = lean_ctor_get(x_1422, 0);
lean_inc(x_1423);
lean_dec_ref(x_1422);
x_1424 = l_List_reverse___redArg(x_1423);
x_1394 = x_1406;
x_1395 = x_1409;
x_1396 = x_1416;
x_1397 = x_1408;
x_1398 = x_1412;
x_1399 = x_1424;
x_1400 = lean_box(0);
goto block_1404;
}
else
{
if (lean_obj_tag(x_1422) == 0)
{
lean_object* x_1425; 
x_1425 = lean_ctor_get(x_1422, 0);
lean_inc(x_1425);
lean_dec_ref(x_1422);
x_1394 = x_1406;
x_1395 = x_1409;
x_1396 = x_1416;
x_1397 = x_1408;
x_1398 = x_1412;
x_1399 = x_1425;
x_1400 = lean_box(0);
goto block_1404;
}
else
{
lean_dec(x_1416);
lean_dec(x_1412);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1060 = x_1406;
x_1061 = x_1409;
x_1062 = x_1422;
goto block_1065;
}
}
}
else
{
uint8_t x_1426; 
x_1426 = lean_unbox(x_1415);
lean_dec(x_1415);
x_1350 = x_1426;
x_1351 = x_1418;
x_1352 = x_1406;
x_1353 = x_1417;
x_1354 = x_1409;
x_1355 = x_1416;
x_1356 = lean_box(0);
x_1357 = x_1412;
x_1358 = x_1408;
goto block_1375;
}
}
else
{
uint8_t x_1427; 
x_1427 = lean_unbox(x_1415);
lean_dec(x_1415);
x_1350 = x_1427;
x_1351 = x_1418;
x_1352 = x_1406;
x_1353 = x_1417;
x_1354 = x_1409;
x_1355 = x_1416;
x_1356 = lean_box(0);
x_1357 = x_1412;
x_1358 = x_1408;
goto block_1375;
}
}
else
{
lean_object* x_1428; 
lean_dec(x_1413);
lean_dec(x_1412);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1428 = lean_ctor_get(x_1414, 0);
lean_inc(x_1428);
lean_dec_ref(x_1414);
x_1021 = x_1406;
x_1022 = x_1409;
x_1023 = x_1428;
x_1024 = lean_box(0);
goto block_1026;
}
}
else
{
lean_object* x_1429; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1429 = lean_ctor_get(x_1410, 0);
lean_inc(x_1429);
lean_dec_ref(x_1410);
x_1021 = x_1406;
x_1022 = x_1409;
x_1023 = x_1429;
x_1024 = lean_box(0);
goto block_1026;
}
}
else
{
lean_object* x_1430; lean_object* x_1431; 
x_1430 = lean_io_get_num_heartbeats();
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_1431 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_28, x_109, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1431) == 0)
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
x_1432 = lean_ctor_get(x_1431, 0);
lean_inc(x_1432);
lean_dec_ref(x_1431);
x_1433 = lean_ctor_get(x_1432, 0);
lean_inc(x_1433);
x_1434 = lean_ctor_get(x_1432, 1);
lean_inc(x_1434);
lean_dec(x_1432);
lean_inc(x_2);
x_1435 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_9);
if (lean_obj_tag(x_1435) == 0)
{
lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; uint8_t x_1440; 
x_1436 = lean_ctor_get(x_1435, 0);
lean_inc(x_1436);
lean_dec_ref(x_1435);
x_1437 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_1434, x_25);
lean_inc(x_1437);
lean_inc(x_1433);
x_1438 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(x_1438, 0, x_1433);
lean_closure_set(x_1438, 1, x_1437);
x_1439 = lean_box(0);
x_1440 = lean_unbox(x_1436);
if (x_1440 == 0)
{
lean_object* x_1441; uint8_t x_1442; 
x_1441 = l_Lean_trace_profiler;
x_1442 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_107, x_1441);
if (x_1442 == 0)
{
lean_object* x_1443; 
lean_dec_ref(x_1438);
lean_dec(x_1436);
x_1443 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__5___redArg(x_1408, x_81, x_5, x_1439, x_8);
if (lean_obj_tag(x_1443) == 0)
{
lean_object* x_1444; lean_object* x_1445; 
x_1444 = lean_ctor_get(x_1443, 0);
lean_inc(x_1444);
lean_dec_ref(x_1443);
x_1445 = l_List_reverse___redArg(x_1444);
x_978 = x_1406;
x_979 = x_1430;
x_980 = x_1437;
x_981 = x_1433;
x_982 = x_1408;
x_983 = x_1445;
x_984 = lean_box(0);
goto block_988;
}
else
{
if (lean_obj_tag(x_1443) == 0)
{
lean_object* x_1446; 
x_1446 = lean_ctor_get(x_1443, 0);
lean_inc(x_1446);
lean_dec_ref(x_1443);
x_978 = x_1406;
x_979 = x_1430;
x_980 = x_1437;
x_981 = x_1433;
x_982 = x_1408;
x_983 = x_1446;
x_984 = lean_box(0);
goto block_988;
}
else
{
lean_dec(x_1437);
lean_dec(x_1433);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_587 = x_1406;
x_588 = x_1430;
x_589 = x_1443;
goto block_592;
}
}
}
else
{
uint8_t x_1447; 
x_1447 = lean_unbox(x_1436);
lean_dec(x_1436);
x_890 = x_1406;
x_891 = x_1430;
x_892 = lean_box(0);
x_893 = x_1437;
x_894 = x_1433;
x_895 = x_1438;
x_896 = x_1447;
x_897 = x_1408;
x_898 = x_1439;
goto block_915;
}
}
else
{
uint8_t x_1448; 
x_1448 = lean_unbox(x_1436);
lean_dec(x_1436);
x_890 = x_1406;
x_891 = x_1430;
x_892 = lean_box(0);
x_893 = x_1437;
x_894 = x_1433;
x_895 = x_1438;
x_896 = x_1448;
x_897 = x_1408;
x_898 = x_1439;
goto block_915;
}
}
else
{
lean_object* x_1449; 
lean_dec(x_1434);
lean_dec(x_1433);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1449 = lean_ctor_get(x_1435, 0);
lean_inc(x_1449);
lean_dec_ref(x_1435);
x_575 = x_1406;
x_576 = x_1430;
x_577 = x_1449;
x_578 = lean_box(0);
goto block_580;
}
}
else
{
lean_object* x_1450; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_1450 = lean_ctor_get(x_1431, 0);
lean_inc(x_1450);
lean_dec_ref(x_1431);
x_575 = x_1406;
x_576 = x_1430;
x_577 = x_1450;
x_578 = lean_box(0);
goto block_580;
}
}
}
else
{
uint8_t x_1451; 
lean_dec_ref(x_559);
lean_dec(x_558);
lean_dec_ref(x_109);
lean_dec_ref(x_107);
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
x_1451 = !lean_is_exclusive(x_1405);
if (x_1451 == 0)
{
return x_1405;
}
else
{
lean_object* x_1452; lean_object* x_1453; 
x_1452 = lean_ctor_get(x_1405, 0);
lean_inc(x_1452);
lean_dec(x_1405);
x_1453 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1453, 0, x_1452);
return x_1453;
}
}
}
}
else
{
uint8_t x_1458; 
lean_dec_ref(x_109);
lean_dec(x_30);
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
x_1458 = !lean_is_exclusive(x_557);
if (x_1458 == 0)
{
return x_557;
}
else
{
lean_object* x_1459; lean_object* x_1460; 
x_1459 = lean_ctor_get(x_557, 0);
lean_inc(x_1459);
lean_dec(x_557);
x_1460 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1460, 0, x_1459);
return x_1460;
}
}
}
block_131:
{
lean_object* x_123; double x_124; double x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_123 = lean_io_get_num_heartbeats();
x_124 = lean_float_of_nat(x_113);
x_125 = lean_float_of_nat(x_123);
x_126 = lean_box_float(x_124);
x_127 = lean_box_float(x_125);
if (lean_is_scalar(x_30)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_30;
}
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_121);
lean_ctor_set(x_129, 1, x_128);
x_130 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_110, x_120, x_112, x_119, x_115, x_118, x_129, x_111, x_117, x_114, x_116);
lean_dec_ref(x_112);
return x_130;
}
block_145:
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_142);
x_111 = x_132;
x_112 = x_134;
x_113 = x_133;
x_114 = x_136;
x_115 = x_135;
x_116 = x_140;
x_117 = x_139;
x_118 = x_138;
x_119 = x_137;
x_120 = x_141;
x_121 = x_144;
x_122 = lean_box(0);
goto block_131;
}
block_162:
{
lean_object* x_160; lean_object* x_161; 
x_160 = l_List_appendTR___redArg(x_147, x_156);
x_161 = l_List_appendTR___redArg(x_160, x_158);
x_132 = x_146;
x_133 = x_149;
x_134 = x_148;
x_135 = x_151;
x_136 = x_150;
x_137 = x_155;
x_138 = x_154;
x_139 = x_153;
x_140 = x_152;
x_141 = x_157;
x_142 = x_161;
x_143 = lean_box(0);
goto block_145;
}
block_176:
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_173);
x_111 = x_163;
x_112 = x_165;
x_113 = x_164;
x_114 = x_167;
x_115 = x_166;
x_116 = x_171;
x_117 = x_170;
x_118 = x_169;
x_119 = x_168;
x_120 = x_172;
x_121 = x_175;
x_122 = lean_box(0);
goto block_131;
}
block_190:
{
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_132 = x_177;
x_133 = x_179;
x_134 = x_178;
x_135 = x_181;
x_136 = x_180;
x_137 = x_185;
x_138 = x_184;
x_139 = x_183;
x_140 = x_182;
x_141 = x_186;
x_142 = x_188;
x_143 = lean_box(0);
goto block_145;
}
else
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
lean_dec_ref(x_187);
x_163 = x_177;
x_164 = x_179;
x_165 = x_178;
x_166 = x_181;
x_167 = x_180;
x_168 = x_185;
x_169 = x_184;
x_170 = x_183;
x_171 = x_182;
x_172 = x_186;
x_173 = x_189;
x_174 = lean_box(0);
goto block_176;
}
}
block_207:
{
lean_object* x_204; 
lean_inc(x_195);
lean_inc_ref(x_194);
lean_inc(x_201);
lean_inc_ref(x_198);
lean_inc(x_2);
x_204 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_192, x_29, x_198, x_201, x_194, x_195);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = l_List_appendTR___redArg(x_191, x_205);
x_132 = x_198;
x_133 = x_193;
x_134 = x_199;
x_135 = x_200;
x_136 = x_194;
x_137 = x_196;
x_138 = x_197;
x_139 = x_201;
x_140 = x_195;
x_141 = x_203;
x_142 = x_206;
x_143 = lean_box(0);
goto block_145;
}
else
{
lean_dec(x_191);
x_177 = x_198;
x_178 = x_199;
x_179 = x_193;
x_180 = x_194;
x_181 = x_200;
x_182 = x_195;
x_183 = x_201;
x_184 = x_197;
x_185 = x_196;
x_186 = x_203;
x_187 = x_204;
goto block_190;
}
}
block_226:
{
uint8_t x_223; 
x_223 = l_List_isEmpty___redArg(x_221);
lean_dec(x_221);
if (x_223 == 0)
{
if (x_208 == 0)
{
x_191 = x_209;
x_192 = x_210;
x_193 = x_211;
x_194 = x_212;
x_195 = x_213;
x_196 = x_214;
x_197 = x_215;
x_198 = x_216;
x_199 = x_217;
x_200 = x_218;
x_201 = x_219;
x_202 = lean_box(0);
x_203 = x_222;
goto block_207;
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_224 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2;
x_225 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_224, x_216, x_219, x_212, x_213);
x_177 = x_216;
x_178 = x_217;
x_179 = x_211;
x_180 = x_212;
x_181 = x_218;
x_182 = x_213;
x_183 = x_219;
x_184 = x_215;
x_185 = x_214;
x_186 = x_222;
x_187 = x_225;
goto block_190;
}
}
else
{
x_191 = x_209;
x_192 = x_210;
x_193 = x_211;
x_194 = x_212;
x_195 = x_213;
x_196 = x_214;
x_197 = x_215;
x_198 = x_216;
x_199 = x_217;
x_200 = x_218;
x_201 = x_219;
x_202 = lean_box(0);
x_203 = x_222;
goto block_207;
}
}
block_242:
{
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
x_146 = x_227;
x_147 = x_228;
x_148 = x_230;
x_149 = x_229;
x_150 = x_232;
x_151 = x_231;
x_152 = x_236;
x_153 = x_235;
x_154 = x_234;
x_155 = x_233;
x_156 = x_237;
x_157 = x_238;
x_158 = x_240;
x_159 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_241; 
lean_dec(x_237);
lean_dec(x_228);
x_241 = lean_ctor_get(x_239, 0);
lean_inc(x_241);
lean_dec_ref(x_239);
x_163 = x_227;
x_164 = x_229;
x_165 = x_230;
x_166 = x_231;
x_167 = x_232;
x_168 = x_233;
x_169 = x_234;
x_170 = x_235;
x_171 = x_236;
x_172 = x_238;
x_173 = x_241;
x_174 = lean_box(0);
goto block_176;
}
}
block_261:
{
if (x_258 == 0)
{
lean_object* x_259; 
lean_dec_ref(x_253);
x_259 = l_Lean_Meta_SavedState_restore___redArg(x_254, x_255, x_247);
lean_dec_ref(x_254);
if (lean_obj_tag(x_259) == 0)
{
lean_dec_ref(x_259);
x_146 = x_250;
x_147 = x_243;
x_148 = x_251;
x_149 = x_245;
x_150 = x_246;
x_151 = x_252;
x_152 = x_247;
x_153 = x_255;
x_154 = x_248;
x_155 = x_249;
x_156 = x_256;
x_157 = x_257;
x_158 = x_29;
x_159 = lean_box(0);
goto block_162;
}
else
{
lean_object* x_260; 
lean_dec(x_256);
lean_dec(x_243);
lean_dec(x_29);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
lean_dec_ref(x_259);
x_163 = x_250;
x_164 = x_245;
x_165 = x_251;
x_166 = x_252;
x_167 = x_246;
x_168 = x_249;
x_169 = x_248;
x_170 = x_255;
x_171 = x_247;
x_172 = x_257;
x_173 = x_260;
x_174 = lean_box(0);
goto block_176;
}
}
else
{
lean_dec_ref(x_254);
lean_dec(x_29);
x_227 = x_250;
x_228 = x_243;
x_229 = x_245;
x_230 = x_251;
x_231 = x_252;
x_232 = x_246;
x_233 = x_249;
x_234 = x_248;
x_235 = x_255;
x_236 = x_247;
x_237 = x_256;
x_238 = x_257;
x_239 = x_253;
goto block_242;
}
}
block_283:
{
lean_object* x_276; 
x_276 = l_Lean_Meta_saveState___redArg(x_272, x_266);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
lean_dec_ref(x_276);
lean_inc(x_266);
lean_inc_ref(x_265);
lean_inc(x_272);
lean_inc_ref(x_269);
lean_inc(x_29);
lean_inc(x_2);
x_278 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_263, x_29, x_269, x_272, x_265, x_266);
if (lean_obj_tag(x_278) == 0)
{
lean_dec(x_277);
lean_dec(x_29);
x_227 = x_269;
x_228 = x_262;
x_229 = x_264;
x_230 = x_270;
x_231 = x_271;
x_232 = x_265;
x_233 = x_267;
x_234 = x_268;
x_235 = x_272;
x_236 = x_266;
x_237 = x_274;
x_238 = x_275;
x_239 = x_278;
goto block_242;
}
else
{
lean_object* x_279; uint8_t x_280; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = l_Lean_Exception_isInterrupt(x_279);
if (x_280 == 0)
{
uint8_t x_281; 
x_281 = l_Lean_Exception_isRuntime(x_279);
x_243 = x_262;
x_244 = lean_box(0);
x_245 = x_264;
x_246 = x_265;
x_247 = x_266;
x_248 = x_268;
x_249 = x_267;
x_250 = x_269;
x_251 = x_270;
x_252 = x_271;
x_253 = x_278;
x_254 = x_277;
x_255 = x_272;
x_256 = x_274;
x_257 = x_275;
x_258 = x_281;
goto block_261;
}
else
{
lean_dec(x_279);
x_243 = x_262;
x_244 = lean_box(0);
x_245 = x_264;
x_246 = x_265;
x_247 = x_266;
x_248 = x_268;
x_249 = x_267;
x_250 = x_269;
x_251 = x_270;
x_252 = x_271;
x_253 = x_278;
x_254 = x_277;
x_255 = x_272;
x_256 = x_274;
x_257 = x_275;
x_258 = x_280;
goto block_261;
}
}
}
else
{
lean_object* x_282; 
lean_dec(x_274);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_282 = lean_ctor_get(x_276, 0);
lean_inc(x_282);
lean_dec_ref(x_276);
x_163 = x_269;
x_164 = x_264;
x_165 = x_270;
x_166 = x_271;
x_167 = x_265;
x_168 = x_267;
x_169 = x_268;
x_170 = x_272;
x_171 = x_266;
x_172 = x_275;
x_173 = x_282;
x_174 = lean_box(0);
goto block_176;
}
}
block_302:
{
uint8_t x_299; lean_object* x_300; 
x_299 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_285);
x_300 = l_List_appendTR___redArg(x_297, x_285);
if (x_299 == 0)
{
x_208 = x_284;
x_209 = x_285;
x_210 = x_300;
x_211 = x_286;
x_212 = x_287;
x_213 = x_288;
x_214 = x_289;
x_215 = x_290;
x_216 = x_291;
x_217 = x_292;
x_218 = x_293;
x_219 = x_294;
x_220 = lean_box(0);
x_221 = x_295;
x_222 = x_296;
goto block_226;
}
else
{
uint8_t x_301; 
x_301 = l_List_isEmpty___redArg(x_285);
if (x_301 == 0)
{
x_262 = x_285;
x_263 = x_300;
x_264 = x_286;
x_265 = x_287;
x_266 = x_288;
x_267 = x_289;
x_268 = x_290;
x_269 = x_291;
x_270 = x_292;
x_271 = x_293;
x_272 = x_294;
x_273 = lean_box(0);
x_274 = x_295;
x_275 = x_296;
goto block_283;
}
else
{
if (x_81 == 0)
{
x_208 = x_284;
x_209 = x_285;
x_210 = x_300;
x_211 = x_286;
x_212 = x_287;
x_213 = x_288;
x_214 = x_289;
x_215 = x_290;
x_216 = x_291;
x_217 = x_292;
x_218 = x_293;
x_219 = x_294;
x_220 = lean_box(0);
x_221 = x_295;
x_222 = x_296;
goto block_226;
}
else
{
x_262 = x_285;
x_263 = x_300;
x_264 = x_286;
x_265 = x_287;
x_266 = x_288;
x_267 = x_289;
x_268 = x_290;
x_269 = x_291;
x_270 = x_292;
x_271 = x_293;
x_272 = x_294;
x_273 = lean_box(0);
x_274 = x_295;
x_275 = x_296;
goto block_283;
}
}
}
}
block_326:
{
lean_object* x_315; double x_316; double x_317; double x_318; double x_319; double x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_315 = lean_io_mono_nanos_now();
x_316 = lean_float_of_nat(x_305);
x_317 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0;
x_318 = lean_float_div(x_316, x_317);
x_319 = lean_float_of_nat(x_315);
x_320 = lean_float_div(x_319, x_317);
x_321 = lean_box_float(x_318);
x_322 = lean_box_float(x_320);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_313);
lean_ctor_set(x_324, 1, x_323);
x_325 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg(x_2, x_110, x_312, x_304, x_311, x_307, x_310, x_324, x_303, x_309, x_306, x_308);
lean_dec_ref(x_304);
return x_325;
}
block_340:
{
lean_object* x_339; 
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_337);
x_303 = x_327;
x_304 = x_329;
x_305 = x_328;
x_306 = x_331;
x_307 = x_330;
x_308 = x_335;
x_309 = x_334;
x_310 = x_333;
x_311 = x_332;
x_312 = x_336;
x_313 = x_339;
x_314 = lean_box(0);
goto block_326;
}
block_357:
{
lean_object* x_355; lean_object* x_356; 
x_355 = l_List_appendTR___redArg(x_342, x_351);
x_356 = l_List_appendTR___redArg(x_355, x_353);
x_327 = x_341;
x_328 = x_344;
x_329 = x_343;
x_330 = x_346;
x_331 = x_345;
x_332 = x_350;
x_333 = x_349;
x_334 = x_348;
x_335 = x_347;
x_336 = x_352;
x_337 = x_356;
x_338 = lean_box(0);
goto block_340;
}
block_371:
{
lean_object* x_370; 
x_370 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_370, 0, x_368);
x_303 = x_358;
x_304 = x_360;
x_305 = x_359;
x_306 = x_362;
x_307 = x_361;
x_308 = x_366;
x_309 = x_365;
x_310 = x_364;
x_311 = x_363;
x_312 = x_367;
x_313 = x_370;
x_314 = lean_box(0);
goto block_326;
}
block_385:
{
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
lean_dec_ref(x_382);
x_327 = x_372;
x_328 = x_374;
x_329 = x_373;
x_330 = x_376;
x_331 = x_375;
x_332 = x_380;
x_333 = x_379;
x_334 = x_378;
x_335 = x_377;
x_336 = x_381;
x_337 = x_383;
x_338 = lean_box(0);
goto block_340;
}
else
{
lean_object* x_384; 
x_384 = lean_ctor_get(x_382, 0);
lean_inc(x_384);
lean_dec_ref(x_382);
x_358 = x_372;
x_359 = x_374;
x_360 = x_373;
x_361 = x_376;
x_362 = x_375;
x_363 = x_380;
x_364 = x_379;
x_365 = x_378;
x_366 = x_377;
x_367 = x_381;
x_368 = x_384;
x_369 = lean_box(0);
goto block_371;
}
}
block_399:
{
lean_object* x_397; lean_object* x_398; 
x_397 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2;
x_398 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_397, x_386, x_395, x_390, x_394);
x_372 = x_386;
x_373 = x_388;
x_374 = x_387;
x_375 = x_390;
x_376 = x_389;
x_377 = x_394;
x_378 = x_395;
x_379 = x_393;
x_380 = x_392;
x_381 = x_396;
x_382 = x_398;
goto block_385;
}
block_419:
{
uint8_t x_415; 
x_415 = l_List_isEmpty___redArg(x_412);
lean_dec(x_412);
if (x_415 == 0)
{
lean_dec(x_413);
lean_dec(x_401);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_386 = x_407;
x_387 = x_402;
x_388 = x_408;
x_389 = x_409;
x_390 = x_403;
x_391 = lean_box(0);
x_392 = x_404;
x_393 = x_405;
x_394 = x_406;
x_395 = x_411;
x_396 = x_414;
goto block_399;
}
else
{
if (x_400 == 0)
{
lean_object* x_416; 
lean_inc(x_406);
lean_inc_ref(x_403);
lean_inc(x_411);
lean_inc_ref(x_407);
lean_inc(x_2);
x_416 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_413, x_29, x_407, x_411, x_403, x_406);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
lean_dec_ref(x_416);
x_418 = l_List_appendTR___redArg(x_401, x_417);
x_327 = x_407;
x_328 = x_402;
x_329 = x_408;
x_330 = x_409;
x_331 = x_403;
x_332 = x_404;
x_333 = x_405;
x_334 = x_411;
x_335 = x_406;
x_336 = x_414;
x_337 = x_418;
x_338 = lean_box(0);
goto block_340;
}
else
{
lean_dec(x_401);
x_372 = x_407;
x_373 = x_408;
x_374 = x_402;
x_375 = x_403;
x_376 = x_409;
x_377 = x_406;
x_378 = x_411;
x_379 = x_405;
x_380 = x_404;
x_381 = x_414;
x_382 = x_416;
goto block_385;
}
}
else
{
lean_dec(x_413);
lean_dec(x_401);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_386 = x_407;
x_387 = x_402;
x_388 = x_408;
x_389 = x_409;
x_390 = x_403;
x_391 = lean_box(0);
x_392 = x_404;
x_393 = x_405;
x_394 = x_406;
x_395 = x_411;
x_396 = x_414;
goto block_399;
}
}
}
block_435:
{
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
lean_dec_ref(x_432);
x_341 = x_420;
x_342 = x_421;
x_343 = x_423;
x_344 = x_422;
x_345 = x_425;
x_346 = x_424;
x_347 = x_429;
x_348 = x_428;
x_349 = x_427;
x_350 = x_426;
x_351 = x_430;
x_352 = x_431;
x_353 = x_433;
x_354 = lean_box(0);
goto block_357;
}
else
{
lean_object* x_434; 
lean_dec(x_430);
lean_dec(x_421);
x_434 = lean_ctor_get(x_432, 0);
lean_inc(x_434);
lean_dec_ref(x_432);
x_358 = x_420;
x_359 = x_422;
x_360 = x_423;
x_361 = x_424;
x_362 = x_425;
x_363 = x_426;
x_364 = x_427;
x_365 = x_428;
x_366 = x_429;
x_367 = x_431;
x_368 = x_434;
x_369 = lean_box(0);
goto block_371;
}
}
block_454:
{
if (x_451 == 0)
{
lean_object* x_452; 
lean_dec_ref(x_436);
x_452 = l_Lean_Meta_SavedState_restore___redArg(x_438, x_448, x_441);
lean_dec_ref(x_438);
if (lean_obj_tag(x_452) == 0)
{
lean_dec_ref(x_452);
x_341 = x_445;
x_342 = x_437;
x_343 = x_446;
x_344 = x_439;
x_345 = x_440;
x_346 = x_447;
x_347 = x_441;
x_348 = x_448;
x_349 = x_442;
x_350 = x_443;
x_351 = x_449;
x_352 = x_450;
x_353 = x_29;
x_354 = lean_box(0);
goto block_357;
}
else
{
lean_object* x_453; 
lean_dec(x_449);
lean_dec(x_437);
lean_dec(x_29);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
lean_dec_ref(x_452);
x_358 = x_445;
x_359 = x_439;
x_360 = x_446;
x_361 = x_447;
x_362 = x_440;
x_363 = x_443;
x_364 = x_442;
x_365 = x_448;
x_366 = x_441;
x_367 = x_450;
x_368 = x_453;
x_369 = lean_box(0);
goto block_371;
}
}
else
{
lean_dec_ref(x_438);
lean_dec(x_29);
x_420 = x_445;
x_421 = x_437;
x_422 = x_439;
x_423 = x_446;
x_424 = x_447;
x_425 = x_440;
x_426 = x_443;
x_427 = x_442;
x_428 = x_448;
x_429 = x_441;
x_430 = x_449;
x_431 = x_450;
x_432 = x_436;
goto block_435;
}
}
block_476:
{
lean_object* x_469; 
x_469 = l_Lean_Meta_saveState___redArg(x_465, x_458);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
lean_dec_ref(x_469);
lean_inc(x_458);
lean_inc_ref(x_457);
lean_inc(x_465);
lean_inc_ref(x_461);
lean_inc(x_29);
lean_inc(x_2);
x_471 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_467, x_29, x_461, x_465, x_457, x_458);
if (lean_obj_tag(x_471) == 0)
{
lean_dec(x_470);
lean_dec(x_29);
x_420 = x_461;
x_421 = x_455;
x_422 = x_456;
x_423 = x_462;
x_424 = x_463;
x_425 = x_457;
x_426 = x_459;
x_427 = x_460;
x_428 = x_465;
x_429 = x_458;
x_430 = x_466;
x_431 = x_468;
x_432 = x_471;
goto block_435;
}
else
{
lean_object* x_472; uint8_t x_473; 
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = l_Lean_Exception_isInterrupt(x_472);
if (x_473 == 0)
{
uint8_t x_474; 
x_474 = l_Lean_Exception_isRuntime(x_472);
x_436 = x_471;
x_437 = x_455;
x_438 = x_470;
x_439 = x_456;
x_440 = x_457;
x_441 = x_458;
x_442 = x_460;
x_443 = x_459;
x_444 = lean_box(0);
x_445 = x_461;
x_446 = x_462;
x_447 = x_463;
x_448 = x_465;
x_449 = x_466;
x_450 = x_468;
x_451 = x_474;
goto block_454;
}
else
{
lean_dec(x_472);
x_436 = x_471;
x_437 = x_455;
x_438 = x_470;
x_439 = x_456;
x_440 = x_457;
x_441 = x_458;
x_442 = x_460;
x_443 = x_459;
x_444 = lean_box(0);
x_445 = x_461;
x_446 = x_462;
x_447 = x_463;
x_448 = x_465;
x_449 = x_466;
x_450 = x_468;
x_451 = x_473;
goto block_454;
}
}
}
else
{
lean_object* x_475; 
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_455);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_475 = lean_ctor_get(x_469, 0);
lean_inc(x_475);
lean_dec_ref(x_469);
x_358 = x_461;
x_359 = x_456;
x_360 = x_462;
x_361 = x_463;
x_362 = x_457;
x_363 = x_459;
x_364 = x_460;
x_365 = x_465;
x_366 = x_458;
x_367 = x_468;
x_368 = x_475;
x_369 = lean_box(0);
goto block_371;
}
}
block_495:
{
uint8_t x_492; lean_object* x_493; 
x_492 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_478);
x_493 = l_List_appendTR___redArg(x_490, x_478);
if (x_492 == 0)
{
x_400 = x_477;
x_401 = x_478;
x_402 = x_479;
x_403 = x_480;
x_404 = x_481;
x_405 = x_482;
x_406 = x_483;
x_407 = x_484;
x_408 = x_485;
x_409 = x_486;
x_410 = lean_box(0);
x_411 = x_487;
x_412 = x_488;
x_413 = x_493;
x_414 = x_489;
goto block_419;
}
else
{
uint8_t x_494; 
x_494 = l_List_isEmpty___redArg(x_478);
if (x_494 == 0)
{
x_455 = x_478;
x_456 = x_479;
x_457 = x_480;
x_458 = x_483;
x_459 = x_481;
x_460 = x_482;
x_461 = x_484;
x_462 = x_485;
x_463 = x_486;
x_464 = lean_box(0);
x_465 = x_487;
x_466 = x_488;
x_467 = x_493;
x_468 = x_489;
goto block_476;
}
else
{
if (x_477 == 0)
{
x_400 = x_477;
x_401 = x_478;
x_402 = x_479;
x_403 = x_480;
x_404 = x_481;
x_405 = x_482;
x_406 = x_483;
x_407 = x_484;
x_408 = x_485;
x_409 = x_486;
x_410 = lean_box(0);
x_411 = x_487;
x_412 = x_488;
x_413 = x_493;
x_414 = x_489;
goto block_419;
}
else
{
x_455 = x_478;
x_456 = x_479;
x_457 = x_480;
x_458 = x_483;
x_459 = x_481;
x_460 = x_482;
x_461 = x_484;
x_462 = x_485;
x_463 = x_486;
x_464 = lean_box(0);
x_465 = x_487;
x_466 = x_488;
x_467 = x_493;
x_468 = x_489;
goto block_476;
}
}
}
}
block_527:
{
lean_object* x_508; 
x_508 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg(x_505);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; uint8_t x_511; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
lean_dec_ref(x_508);
x_510 = l_Lean_trace_profiler_useHeartbeats;
x_511 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_499, x_510);
if (x_511 == 0)
{
lean_object* x_512; lean_object* x_513; 
lean_dec(x_30);
x_512 = lean_io_mono_nanos_now();
x_513 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_81, x_5, x_498, x_503);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
lean_dec_ref(x_513);
x_515 = l_List_reverse___redArg(x_514);
x_477 = x_511;
x_478 = x_497;
x_479 = x_512;
x_480 = x_500;
x_481 = x_501;
x_482 = x_502;
x_483 = x_505;
x_484 = x_496;
x_485 = x_499;
x_486 = x_509;
x_487 = x_503;
x_488 = x_506;
x_489 = x_507;
x_490 = x_515;
x_491 = lean_box(0);
goto block_495;
}
else
{
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_516; 
x_516 = lean_ctor_get(x_513, 0);
lean_inc(x_516);
lean_dec_ref(x_513);
x_477 = x_511;
x_478 = x_497;
x_479 = x_512;
x_480 = x_500;
x_481 = x_501;
x_482 = x_502;
x_483 = x_505;
x_484 = x_496;
x_485 = x_499;
x_486 = x_509;
x_487 = x_503;
x_488 = x_506;
x_489 = x_507;
x_490 = x_516;
x_491 = lean_box(0);
goto block_495;
}
else
{
lean_object* x_517; 
lean_dec(x_506);
lean_dec(x_497);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_517 = lean_ctor_get(x_513, 0);
lean_inc(x_517);
lean_dec_ref(x_513);
x_358 = x_496;
x_359 = x_512;
x_360 = x_499;
x_361 = x_509;
x_362 = x_500;
x_363 = x_501;
x_364 = x_502;
x_365 = x_503;
x_366 = x_505;
x_367 = x_507;
x_368 = x_517;
x_369 = lean_box(0);
goto block_371;
}
}
}
else
{
lean_object* x_518; lean_object* x_519; 
x_518 = lean_io_get_num_heartbeats();
x_519 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_81, x_5, x_498, x_503);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
lean_dec_ref(x_519);
x_521 = l_List_reverse___redArg(x_520);
x_284 = x_511;
x_285 = x_497;
x_286 = x_518;
x_287 = x_500;
x_288 = x_505;
x_289 = x_501;
x_290 = x_502;
x_291 = x_496;
x_292 = x_499;
x_293 = x_509;
x_294 = x_503;
x_295 = x_506;
x_296 = x_507;
x_297 = x_521;
x_298 = lean_box(0);
goto block_302;
}
else
{
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_522; 
x_522 = lean_ctor_get(x_519, 0);
lean_inc(x_522);
lean_dec_ref(x_519);
x_284 = x_511;
x_285 = x_497;
x_286 = x_518;
x_287 = x_500;
x_288 = x_505;
x_289 = x_501;
x_290 = x_502;
x_291 = x_496;
x_292 = x_499;
x_293 = x_509;
x_294 = x_503;
x_295 = x_506;
x_296 = x_507;
x_297 = x_522;
x_298 = lean_box(0);
goto block_302;
}
else
{
lean_object* x_523; 
lean_dec(x_506);
lean_dec(x_497);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_523 = lean_ctor_get(x_519, 0);
lean_inc(x_523);
lean_dec_ref(x_519);
x_163 = x_496;
x_164 = x_518;
x_165 = x_499;
x_166 = x_509;
x_167 = x_500;
x_168 = x_501;
x_169 = x_502;
x_170 = x_503;
x_171 = x_505;
x_172 = x_507;
x_173 = x_523;
x_174 = lean_box(0);
goto block_176;
}
}
}
}
else
{
uint8_t x_524; 
lean_dec_ref(x_507);
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec_ref(x_500);
lean_dec_ref(x_499);
lean_dec(x_498);
lean_dec(x_497);
lean_dec_ref(x_496);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_524 = !lean_is_exclusive(x_508);
if (x_524 == 0)
{
return x_508;
}
else
{
lean_object* x_525; lean_object* x_526; 
x_525 = lean_ctor_get(x_508, 0);
lean_inc(x_525);
lean_dec(x_508);
x_526 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_526, 0, x_525);
return x_526;
}
}
}
block_556:
{
lean_object* x_533; 
lean_inc(x_531);
lean_inc_ref(x_530);
lean_inc(x_529);
lean_inc_ref(x_528);
x_533 = l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__2___redArg(x_28, x_109, x_528, x_529, x_530, x_531);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; lean_object* x_539; lean_object* x_540; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
lean_dec_ref(x_533);
x_535 = lean_ctor_get(x_530, 2);
x_536 = lean_ctor_get(x_534, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_534, 1);
lean_inc(x_537);
lean_dec(x_534);
x_538 = lean_ctor_get_uint8(x_535, sizeof(void*)*1);
x_539 = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__3(x_537, x_25);
x_540 = lean_box(0);
if (x_538 == 0)
{
lean_dec(x_30);
x_94 = x_539;
x_95 = x_540;
x_96 = x_536;
x_97 = x_528;
x_98 = x_529;
x_99 = x_530;
x_100 = x_531;
x_101 = lean_box(0);
goto block_106;
}
else
{
lean_object* x_541; 
lean_inc(x_2);
x_541 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__1___redArg(x_2, x_530);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
lean_dec_ref(x_541);
lean_inc(x_539);
lean_inc(x_536);
x_543 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___boxed), 8, 2);
lean_closure_set(x_543, 0, x_536);
lean_closure_set(x_543, 1, x_539);
x_544 = ((lean_object*)(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__7));
x_545 = lean_unbox(x_542);
if (x_545 == 0)
{
lean_object* x_546; uint8_t x_547; 
x_546 = l_Lean_trace_profiler;
x_547 = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__3(x_535, x_546);
if (x_547 == 0)
{
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec(x_30);
x_94 = x_539;
x_95 = x_540;
x_96 = x_536;
x_97 = x_528;
x_98 = x_529;
x_99 = x_530;
x_100 = x_531;
x_101 = lean_box(0);
goto block_106;
}
else
{
uint8_t x_548; 
lean_inc_ref(x_535);
x_548 = lean_unbox(x_542);
lean_dec(x_542);
x_496 = x_528;
x_497 = x_539;
x_498 = x_540;
x_499 = x_535;
x_500 = x_530;
x_501 = x_548;
x_502 = x_543;
x_503 = x_529;
x_504 = lean_box(0);
x_505 = x_531;
x_506 = x_536;
x_507 = x_544;
goto block_527;
}
}
else
{
uint8_t x_549; 
lean_inc_ref(x_535);
x_549 = lean_unbox(x_542);
lean_dec(x_542);
x_496 = x_528;
x_497 = x_539;
x_498 = x_540;
x_499 = x_535;
x_500 = x_530;
x_501 = x_549;
x_502 = x_543;
x_503 = x_529;
x_504 = lean_box(0);
x_505 = x_531;
x_506 = x_536;
x_507 = x_544;
goto block_527;
}
}
else
{
uint8_t x_550; 
lean_dec(x_539);
lean_dec(x_536);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_550 = !lean_is_exclusive(x_541);
if (x_550 == 0)
{
return x_541;
}
else
{
lean_object* x_551; lean_object* x_552; 
x_551 = lean_ctor_get(x_541, 0);
lean_inc(x_551);
lean_dec(x_541);
x_552 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_552, 0, x_551);
return x_552;
}
}
}
}
else
{
uint8_t x_553; 
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec_ref(x_528);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_553 = !lean_is_exclusive(x_533);
if (x_553 == 0)
{
return x_533;
}
else
{
lean_object* x_554; lean_object* x_555; 
x_554 = lean_ctor_get(x_533, 0);
lean_inc(x_554);
lean_dec(x_533);
x_555 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_555, 0, x_554);
return x_555;
}
}
}
}
else
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_5);
x_1461 = lean_ctor_get(x_1, 0);
lean_inc(x_1461);
x_1462 = lean_box(0);
x_1463 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run(x_1, x_2, x_3, x_4, x_1461, x_6, x_1462, x_7, x_8, x_9, x_10);
return x_1463;
}
block_43:
{
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_36);
x_39 = l_Lean_Meta_SavedState_restore___redArg(x_32, x_35, x_31);
lean_dec(x_31);
lean_dec(x_35);
lean_dec_ref(x_32);
if (lean_obj_tag(x_39) == 0)
{
lean_dec_ref(x_39);
x_12 = x_34;
x_13 = x_37;
x_14 = x_29;
x_15 = lean_box(0);
goto block_19;
}
else
{
uint8_t x_40; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_29);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_dec(x_35);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_29);
x_20 = x_34;
x_21 = x_37;
x_22 = x_36;
goto block_24;
}
}
block_61:
{
lean_object* x_52; 
x_52 = l_Lean_Meta_saveState___redArg(x_48, x_44);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_inc(x_44);
lean_inc(x_48);
lean_inc(x_29);
x_54 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_45, x_29, x_51, x_48, x_49, x_44);
if (lean_obj_tag(x_54) == 0)
{
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_29);
x_20 = x_46;
x_21 = x_50;
x_22 = x_54;
goto block_24;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = l_Lean_Exception_isInterrupt(x_55);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Exception_isRuntime(x_55);
x_31 = x_44;
x_32 = x_53;
x_33 = lean_box(0);
x_34 = x_46;
x_35 = x_48;
x_36 = x_54;
x_37 = x_50;
x_38 = x_57;
goto block_43;
}
else
{
lean_dec(x_55);
x_31 = x_44;
x_32 = x_53;
x_33 = lean_box(0);
x_34 = x_46;
x_35 = x_48;
x_36 = x_54;
x_37 = x_50;
x_38 = x_56;
goto block_43;
}
}
}
else
{
uint8_t x_58; 
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_58 = !lean_is_exclusive(x_52);
if (x_58 == 0)
{
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
block_80:
{
uint8_t x_70; 
x_70 = l_List_isEmpty___redArg(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2;
x_72 = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__0___redArg(x_71, x_68, x_66, x_67, x_62);
lean_dec(x_62);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_68);
return x_72;
}
else
{
lean_object* x_73; 
x_73 = l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals(x_1, x_2, x_3, x_4, x_63, x_29, x_68, x_66, x_67, x_62);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l_List_appendTR___redArg(x_64, x_75);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
lean_dec(x_73);
x_78 = l_List_appendTR___redArg(x_64, x_77);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
else
{
lean_dec(x_64);
return x_73;
}
}
}
block_93:
{
uint8_t x_90; lean_object* x_91; 
x_90 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_inc(x_83);
x_91 = l_List_appendTR___redArg(x_88, x_83);
if (x_90 == 0)
{
x_62 = x_82;
x_63 = x_91;
x_64 = x_83;
x_65 = lean_box(0);
x_66 = x_84;
x_67 = x_85;
x_68 = x_86;
x_69 = x_87;
goto block_80;
}
else
{
uint8_t x_92; 
x_92 = l_List_isEmpty___redArg(x_83);
if (x_92 == 0)
{
x_44 = x_82;
x_45 = x_91;
x_46 = x_83;
x_47 = lean_box(0);
x_48 = x_84;
x_49 = x_85;
x_50 = x_87;
x_51 = x_86;
goto block_61;
}
else
{
if (x_81 == 0)
{
x_62 = x_82;
x_63 = x_91;
x_64 = x_83;
x_65 = lean_box(0);
x_66 = x_84;
x_67 = x_85;
x_68 = x_86;
x_69 = x_87;
goto block_80;
}
else
{
x_44 = x_82;
x_45 = x_91;
x_46 = x_83;
x_47 = lean_box(0);
x_48 = x_84;
x_49 = x_85;
x_50 = x_87;
x_51 = x_86;
goto block_61;
}
}
}
}
block_106:
{
lean_object* x_102; 
x_102 = l_List_filterAuxM___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals_spec__4___redArg(x_81, x_5, x_95, x_98);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_104 = l_List_reverse___redArg(x_103);
x_82 = x_100;
x_83 = x_94;
x_84 = x_98;
x_85 = x_99;
x_86 = x_97;
x_87 = x_96;
x_88 = x_104;
x_89 = lean_box(0);
goto block_93;
}
else
{
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
lean_dec_ref(x_102);
x_82 = x_100;
x_83 = x_94;
x_84 = x_98;
x_85 = x_99;
x_86 = x_97;
x_87 = x_96;
x_88 = x_105;
x_89 = lean_box(0);
goto block_93;
}
else
{
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec(x_94);
lean_dec(x_29);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_102;
}
}
}
}
else
{
uint8_t x_1464; 
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
x_1464 = !lean_is_exclusive(x_26);
if (x_1464 == 0)
{
return x_26;
}
else
{
lean_object* x_1465; lean_object* x_1466; 
x_1465 = lean_ctor_get(x_26, 0);
lean_inc(x_1465);
lean_dec(x_26);
x_1466 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1466, 0, x_1465);
return x_1466;
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_List_appendTR___redArg(x_12, x_13);
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
x_12 = x_20;
x_13 = x_21;
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
uint8_t x_12; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
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
l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0 = _init_l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0();
lean_mark_persistent(l_Lean_Meta_Tactic_Backtrack_Backtrack_tryAllM___redArg___lam__3___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__0);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__2___redArg___closed__2);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__0___closed__1);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__1___closed__1);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__2___closed__1);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__9___closed__1);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__4___closed__1);
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__0 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__0();
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__7_spec__10_spec__12___redArg___closed__1();
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__5___closed__1);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___lam__6___closed__1);
l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0 = _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__0();
l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__2);
l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3 = _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run_spec__4___redArg___closed__3();
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__0();
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___closed__2);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__1);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__1___closed__3);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__1);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__3);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___lam__2___closed__5);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__0);
l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2 = _init_l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_processIndependentGoals___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

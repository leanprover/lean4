// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Prover.Cegar.Lemmas
// Imports: public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic import Lean.Meta.Tactic.BVDecide.Normalize import Lean.Meta.Tactic.Grind.Main
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Failed to reify CEGAR lemma "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___boxed(lean_object**);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Processing new lemmas"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__10___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___boxed(lean_object**);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___boxed, .m_arity = 16, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__9_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__10_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__11_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__10_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__11_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__12_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__14_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__15_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___redArg(lean_object* v_solved_22_){
_start:
{
lean_inc(v_solved_22_);
return v_solved_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___redArg___boxed(lean_object* v_solved_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___redArg(v_solved_23_);
lean_dec(v_solved_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_solved_28_){
_start:
{
lean_inc(v_solved_28_);
return v_solved_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_solved_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_solved_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_solved_32_);
lean_dec(v_solved_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___redArg(lean_object* v_newHyps_35_){
_start:
{
lean_inc(v_newHyps_35_);
return v_newHyps_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___redArg___boxed(lean_object* v_newHyps_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___redArg(v_newHyps_36_);
lean_dec(v_newHyps_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_newHyps_41_){
_start:
{
lean_inc(v_newHyps_41_);
return v_newHyps_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_newHyps_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_newHyps_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_newHyps_45_);
lean_dec(v_newHyps_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___redArg(lean_object* v_none_48_){
_start:
{
lean_inc(v_none_48_);
return v_none_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___redArg___boxed(lean_object* v_none_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___redArg(v_none_49_);
lean_dec(v_none_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_none_54_){
_start:
{
lean_inc(v_none_54_);
return v_none_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_none_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lean_Meta_Tactic_BVDecide_ProcessHypResult_none_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_none_58_);
lean_dec(v_none_58_);
return v_res_60_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_unsigned_to_nat(32u);
v___x_62_ = lean_mk_empty_array_with_capacity(v___x_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_64_ = ((size_t)5ULL);
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_unsigned_to_nat(32u);
v___x_67_ = lean_mk_empty_array_with_capacity(v___x_66_);
v___x_68_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__0);
v___x_69_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_65_);
lean_ctor_set(v___x_69_, 3, v___x_65_);
lean_ctor_set_usize(v___x_69_, 4, v___x_64_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg(lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; lean_object* v_traceState_73_; lean_object* v_traces_74_; lean_object* v___x_75_; lean_object* v_traceState_76_; lean_object* v_env_77_; lean_object* v_nextMacroScope_78_; lean_object* v_ngen_79_; lean_object* v_auxDeclNGen_80_; lean_object* v_cache_81_; lean_object* v_recordedDeps_82_; lean_object* v_messages_83_; lean_object* v_infoState_84_; lean_object* v_snapshotTasks_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_104_; 
v___x_72_ = lean_st_ref_get(v___y_70_);
v_traceState_73_ = lean_ctor_get(v___x_72_, 4);
lean_inc_ref(v_traceState_73_);
lean_dec(v___x_72_);
v_traces_74_ = lean_ctor_get(v_traceState_73_, 0);
lean_inc_ref(v_traces_74_);
lean_dec_ref(v_traceState_73_);
v___x_75_ = lean_st_ref_take(v___y_70_);
v_traceState_76_ = lean_ctor_get(v___x_75_, 4);
v_env_77_ = lean_ctor_get(v___x_75_, 0);
v_nextMacroScope_78_ = lean_ctor_get(v___x_75_, 1);
v_ngen_79_ = lean_ctor_get(v___x_75_, 2);
v_auxDeclNGen_80_ = lean_ctor_get(v___x_75_, 3);
v_cache_81_ = lean_ctor_get(v___x_75_, 5);
v_recordedDeps_82_ = lean_ctor_get(v___x_75_, 6);
v_messages_83_ = lean_ctor_get(v___x_75_, 7);
v_infoState_84_ = lean_ctor_get(v___x_75_, 8);
v_snapshotTasks_85_ = lean_ctor_get(v___x_75_, 9);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_104_ == 0)
{
v___x_87_ = v___x_75_;
v_isShared_88_ = v_isSharedCheck_104_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_snapshotTasks_85_);
lean_inc(v_infoState_84_);
lean_inc(v_messages_83_);
lean_inc(v_recordedDeps_82_);
lean_inc(v_cache_81_);
lean_inc(v_traceState_76_);
lean_inc(v_auxDeclNGen_80_);
lean_inc(v_ngen_79_);
lean_inc(v_nextMacroScope_78_);
lean_inc(v_env_77_);
lean_dec(v___x_75_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_104_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
uint64_t v_tid_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_102_; 
v_tid_89_ = lean_ctor_get_uint64(v_traceState_76_, sizeof(void*)*1);
v_isSharedCheck_102_ = !lean_is_exclusive(v_traceState_76_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v_traceState_76_, 0);
lean_dec(v_unused_103_);
v___x_91_ = v_traceState_76_;
v_isShared_92_ = v_isSharedCheck_102_;
goto v_resetjp_90_;
}
else
{
lean_dec(v_traceState_76_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_102_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___closed__1);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_93_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_93_);
lean_ctor_set_uint64(v_reuseFailAlloc_101_, sizeof(void*)*1, v_tid_89_);
v___x_95_ = v_reuseFailAlloc_101_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_97_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v___x_95_);
v___x_97_ = v___x_87_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_env_77_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_nextMacroScope_78_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_ngen_79_);
lean_ctor_set(v_reuseFailAlloc_100_, 3, v_auxDeclNGen_80_);
lean_ctor_set(v_reuseFailAlloc_100_, 4, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_100_, 5, v_cache_81_);
lean_ctor_set(v_reuseFailAlloc_100_, 6, v_recordedDeps_82_);
lean_ctor_set(v_reuseFailAlloc_100_, 7, v_messages_83_);
lean_ctor_set(v_reuseFailAlloc_100_, 8, v_infoState_84_);
lean_ctor_set(v_reuseFailAlloc_100_, 9, v_snapshotTasks_85_);
v___x_97_ = v_reuseFailAlloc_100_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_st_ref_put(v___y_70_, v___x_97_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v_traces_74_);
return v___x_99_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg___boxed(lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg(v___y_105_);
lean_dec(v___y_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg(v___y_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___boxed(lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_139_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(lean_object* v_opts_140_, lean_object* v_opt_141_){
_start:
{
lean_object* v_name_142_; lean_object* v_defValue_143_; lean_object* v_map_144_; lean_object* v___x_145_; 
v_name_142_ = lean_ctor_get(v_opt_141_, 0);
v_defValue_143_ = lean_ctor_get(v_opt_141_, 1);
v_map_144_ = lean_ctor_get(v_opts_140_, 0);
v___x_145_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_144_, v_name_142_);
if (lean_obj_tag(v___x_145_) == 0)
{
uint8_t v___x_146_; 
v___x_146_ = lean_unbox(v_defValue_143_);
return v___x_146_;
}
else
{
lean_object* v_val_147_; 
v_val_147_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_val_147_);
lean_dec_ref_known(v___x_145_, 1);
if (lean_obj_tag(v_val_147_) == 1)
{
uint8_t v_v_148_; 
v_v_148_ = lean_ctor_get_uint8(v_val_147_, 0);
lean_dec_ref_known(v_val_147_, 0);
return v_v_148_;
}
else
{
uint8_t v___x_149_; 
lean_dec(v_val_147_);
v___x_149_ = lean_unbox(v_defValue_143_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___boxed(lean_object* v_opts_150_, lean_object* v_opt_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v_opts_150_, v_opt_151_);
lean_dec_ref(v_opt_151_);
lean_dec_ref(v_opts_150_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___redArg(lean_object* v_as_154_, size_t v_i_155_, size_t v_stop_156_, lean_object* v_b_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = lean_usize_dec_eq(v_i_155_, v_stop_156_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_array_uget_borrowed(v_as_154_, v_i_155_);
lean_inc(v___x_166_);
v___x_167_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_157_, v___x_166_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; size_t v___x_169_; size_t v___x_170_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_167_, 1);
v___x_169_ = ((size_t)1ULL);
v___x_170_ = lean_usize_add(v_i_155_, v___x_169_);
v_i_155_ = v___x_170_;
v_b_157_ = v_a_168_;
goto _start;
}
else
{
return v___x_167_;
}
}
else
{
lean_object* v___x_172_; 
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v_b_157_);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___redArg___boxed(lean_object* v_as_173_, lean_object* v_i_174_, lean_object* v_stop_175_, lean_object* v_b_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
size_t v_i_boxed_184_; size_t v_stop_boxed_185_; lean_object* v_res_186_; 
v_i_boxed_184_ = lean_unbox_usize(v_i_174_);
lean_dec(v_i_174_);
v_stop_boxed_185_ = lean_unbox_usize(v_stop_175_);
lean_dec(v_stop_175_);
v_res_186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___redArg(v_as_173_, v_i_boxed_184_, v_stop_boxed_185_, v_b_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec_ref(v_as_173_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(lean_object* v_msgData_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; lean_object* v_env_194_; uint8_t v___x_195_; lean_object* v_env_196_; lean_object* v___x_197_; lean_object* v_toCold_198_; lean_object* v_mctx_199_; lean_object* v_lctx_200_; lean_object* v_options_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_193_ = lean_st_ref_get(v___y_191_);
v_env_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc_ref(v_env_194_);
lean_dec(v___x_193_);
v___x_195_ = 0;
v_env_196_ = l_Lean_Environment_setRecordingDeps(v_env_194_, v___x_195_);
v___x_197_ = lean_st_ref_get(v___y_189_);
v_toCold_198_ = lean_ctor_get(v___y_190_, 0);
v_mctx_199_ = lean_ctor_get(v___x_197_, 0);
lean_inc_ref(v_mctx_199_);
lean_dec(v___x_197_);
v_lctx_200_ = lean_ctor_get(v___y_188_, 2);
v_options_201_ = lean_ctor_get(v_toCold_198_, 2);
lean_inc_ref(v_options_201_);
lean_inc_ref(v_lctx_200_);
v___x_202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_202_, 0, v_env_196_);
lean_ctor_set(v___x_202_, 1, v_mctx_199_);
lean_ctor_set(v___x_202_, 2, v_lctx_200_);
lean_ctor_set(v___x_202_, 3, v_options_201_);
v___x_203_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_msgData_187_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0___boxed(lean_object* v_msgData_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msgData_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_ref_218_; lean_object* v___x_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_ref_218_ = lean_ctor_get(v___y_215_, 2);
v___x_219_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msg_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
lean_inc(v_ref_218_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v_ref_218_);
lean_ctor_set(v___x_224_, 1, v_a_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 1);
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg___boxed(lean_object* v_msg_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_235_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__4(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__3));
v___x_242_ = l_Lean_stringToMessageData(v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(lean_object* v_as_243_, size_t v_sz_244_, size_t v_i_245_, lean_object* v_b_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_a_263_; uint8_t v___x_267_; 
v___x_267_ = lean_usize_dec_lt(v_i_245_, v_sz_244_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v_b_246_);
return v___x_268_;
}
else
{
lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_a_269_ = lean_array_uget_borrowed(v_as_243_, v_i_245_);
v___x_270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__0));
v___x_271_ = l_Lean_Core_checkSystem(v___x_270_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_type_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
lean_dec_ref_known(v___x_271_, 1);
v_type_272_ = lean_ctor_get(v_a_269_, 1);
v___x_273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__2));
v___x_274_ = l_Lean_Expr_isConstOf(v_type_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(v___y_249_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v___x_276_; 
lean_dec_ref_known(v___x_275_, 1);
lean_inc(v_a_269_);
v___x_276_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(v_a_269_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_276_, 1);
if (lean_obj_tag(v_a_277_) == 1)
{
lean_object* v_val_278_; lean_object* v___x_279_; 
v_val_278_ = lean_ctor_get(v_a_277_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v_a_277_, 1);
v___x_279_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(v___y_249_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_a_280_);
lean_dec_ref_known(v___x_279_, 1);
v___x_281_ = l_Array_append___redArg(v_b_246_, v_a_280_);
lean_dec(v_a_280_);
v___x_282_ = lean_array_push(v___x_281_, v_val_278_);
v_a_263_ = v___x_282_;
goto v___jp_262_;
}
else
{
lean_dec(v_val_278_);
lean_dec_ref(v_b_246_);
return v___x_279_;
}
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec(v_a_277_);
v___x_283_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___closed__4);
lean_inc_ref(v_type_272_);
v___x_284_ = l_Lean_MessageData_ofExpr(v_type_272_);
v___x_285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v___x_285_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_dec_ref_known(v___x_286_, 1);
v_a_263_ = v_b_246_;
goto v___jp_262_;
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v_b_246_);
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
lean_dec_ref(v_b_246_);
v_a_295_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_276_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_276_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec_ref(v_b_246_);
v_a_303_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_275_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_275_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
else
{
v_a_263_ = v_b_246_;
goto v___jp_262_;
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec_ref(v_b_246_);
v_a_311_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_271_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_271_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
v___jp_262_:
{
size_t v___x_264_; size_t v___x_265_; 
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_add(v_i_245_, v___x_264_);
v_i_245_ = v___x_265_;
v_b_246_ = v_a_263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___boxed(lean_object** _args){
lean_object* v_as_319_ = _args[0];
lean_object* v_sz_320_ = _args[1];
lean_object* v_i_321_ = _args[2];
lean_object* v_b_322_ = _args[3];
lean_object* v___y_323_ = _args[4];
lean_object* v___y_324_ = _args[5];
lean_object* v___y_325_ = _args[6];
lean_object* v___y_326_ = _args[7];
lean_object* v___y_327_ = _args[8];
lean_object* v___y_328_ = _args[9];
lean_object* v___y_329_ = _args[10];
lean_object* v___y_330_ = _args[11];
lean_object* v___y_331_ = _args[12];
lean_object* v___y_332_ = _args[13];
lean_object* v___y_333_ = _args[14];
lean_object* v___y_334_ = _args[15];
lean_object* v___y_335_ = _args[16];
lean_object* v___y_336_ = _args[17];
lean_object* v___y_337_ = _args[18];
_start:
{
size_t v_sz_boxed_338_; size_t v_i_boxed_339_; lean_object* v_res_340_; 
v_sz_boxed_338_ = lean_unbox_usize(v_sz_320_);
lean_dec(v_sz_320_);
v_i_boxed_339_ = lean_unbox_usize(v_i_321_);
lean_dec(v_i_321_);
v_res_340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_as_319_, v_sz_boxed_338_, v_i_boxed_339_, v_b_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec_ref(v_as_319_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(lean_object* v_____r_343_, lean_object* v_hypQueue_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_a_361_; lean_object* v___x_381_; lean_object* v___x_382_; size_t v_sz_383_; size_t v___x_384_; lean_object* v___x_385_; 
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__0));
v_sz_383_ = lean_array_size(v_hypQueue_344_);
v___x_384_ = ((size_t)0ULL);
v___x_385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_hypQueue_344_, v_sz_383_, v___x_384_, v___x_382_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_411_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_411_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_411_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_411_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = lean_array_get_size(v_a_386_);
v___x_391_ = lean_nat_dec_eq(v___x_390_, v___x_381_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v_satExpr_393_; uint8_t v___x_394_; 
lean_del_object(v___x_388_);
v___x_392_ = lean_st_ref_get(v___y_346_);
v_satExpr_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_satExpr_393_);
lean_dec(v___x_392_);
v___x_394_ = lean_nat_dec_lt(v___x_381_, v___x_390_);
if (v___x_394_ == 0)
{
lean_dec(v_a_386_);
v_a_361_ = v_satExpr_393_;
goto v___jp_360_;
}
else
{
size_t v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_usize_of_nat(v___x_390_);
v___x_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___redArg(v_a_386_, v___x_384_, v___x_395_, v_satExpr_393_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v_a_386_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref_known(v___x_396_, 1);
v_a_361_ = v_a_397_;
goto v___jp_360_;
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
v_a_398_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_396_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
else
{
uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
lean_dec(v_a_386_);
v___x_406_ = 2;
v___x_407_ = lean_box(v___x_406_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_407_);
v___x_409_ = v___x_388_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_a_412_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_385_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_385_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
v___jp_360_:
{
lean_object* v___x_362_; lean_object* v_hypQueue_363_; lean_object* v_usedHyps_364_; uint8_t v_didChange_365_; lean_object* v_theoryState_366_; lean_object* v_solverTimeBudgetMs_367_; lean_object* v_roundBudget_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_379_; 
v___x_362_ = lean_st_ref_take(v___y_346_);
v_hypQueue_363_ = lean_ctor_get(v___x_362_, 1);
v_usedHyps_364_ = lean_ctor_get(v___x_362_, 2);
v_didChange_365_ = lean_ctor_get_uint8(v___x_362_, sizeof(void*)*6);
v_theoryState_366_ = lean_ctor_get(v___x_362_, 3);
v_solverTimeBudgetMs_367_ = lean_ctor_get(v___x_362_, 4);
v_roundBudget_368_ = lean_ctor_get(v___x_362_, 5);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v___x_362_, 0);
lean_dec(v_unused_380_);
v___x_370_ = v___x_362_;
v_isShared_371_ = v_isSharedCheck_379_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_roundBudget_368_);
lean_inc(v_solverTimeBudgetMs_367_);
lean_inc(v_theoryState_366_);
lean_inc(v_usedHyps_364_);
lean_inc(v_hypQueue_363_);
lean_dec(v___x_362_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_379_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v_a_361_);
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_361_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_hypQueue_363_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_usedHyps_364_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_theoryState_366_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v_solverTimeBudgetMs_367_);
lean_ctor_set(v_reuseFailAlloc_378_, 5, v_roundBudget_368_);
lean_ctor_set_uint8(v_reuseFailAlloc_378_, sizeof(void*)*6, v_didChange_365_);
v___x_373_ = v_reuseFailAlloc_378_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_374_ = lean_st_ref_put(v___y_346_, v___x_373_);
v___x_375_ = 1;
v___x_376_ = lean_box(v___x_375_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___boxed(lean_object** _args){
lean_object* v_____r_420_ = _args[0];
lean_object* v_hypQueue_421_ = _args[1];
lean_object* v___y_422_ = _args[2];
lean_object* v___y_423_ = _args[3];
lean_object* v___y_424_ = _args[4];
lean_object* v___y_425_ = _args[5];
lean_object* v___y_426_ = _args[6];
lean_object* v___y_427_ = _args[7];
lean_object* v___y_428_ = _args[8];
lean_object* v___y_429_ = _args[9];
lean_object* v___y_430_ = _args[10];
lean_object* v___y_431_ = _args[11];
lean_object* v___y_432_ = _args[12];
lean_object* v___y_433_ = _args[13];
lean_object* v___y_434_ = _args[14];
lean_object* v___y_435_ = _args[15];
lean_object* v___y_436_ = _args[16];
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(v_____r_420_, v_hypQueue_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec_ref(v_hypQueue_421_);
return v_res_437_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___closed__1(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___closed__0));
v___x_440_ = l_Lean_stringToMessageData(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2(lean_object* v_x_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___closed__1);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2___boxed(lean_object* v_x_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__2(v_x_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec_ref(v_x_459_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(size_t v_sz_476_, size_t v_i_477_, lean_object* v_bs_478_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = lean_usize_dec_lt(v_i_477_, v_sz_476_);
if (v___x_479_ == 0)
{
return v_bs_478_;
}
else
{
lean_object* v_v_480_; lean_object* v_hyp_481_; lean_object* v___x_482_; lean_object* v_bs_x27_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; 
v_v_480_ = lean_array_uget_borrowed(v_bs_478_, v_i_477_);
v_hyp_481_ = lean_ctor_get(v_v_480_, 0);
lean_inc_ref(v_hyp_481_);
v___x_482_ = lean_unsigned_to_nat(0u);
v_bs_x27_483_ = lean_array_uset(v_bs_478_, v_i_477_, v___x_482_);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_add(v_i_477_, v___x_484_);
v___x_486_ = lean_array_uset(v_bs_x27_483_, v_i_477_, v_hyp_481_);
v_i_477_ = v___x_485_;
v_bs_478_ = v___x_486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___boxed(lean_object* v_sz_488_, lean_object* v_i_489_, lean_object* v_bs_490_){
_start:
{
size_t v_sz_boxed_491_; size_t v_i_boxed_492_; lean_object* v_res_493_; 
v_sz_boxed_491_ = lean_unbox_usize(v_sz_488_);
lean_dec(v_sz_488_);
v_i_boxed_492_ = lean_unbox_usize(v_i_489_);
lean_dec(v_i_489_);
v_res_493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(v_sz_boxed_491_, v_i_boxed_492_, v_bs_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(lean_object* v_as_494_, size_t v_sz_495_, size_t v_i_496_, lean_object* v_b_497_){
_start:
{
lean_object* v_a_499_; uint8_t v___x_503_; 
v___x_503_ = lean_usize_dec_lt(v_i_496_, v_sz_495_);
if (v___x_503_ == 0)
{
return v_b_497_;
}
else
{
lean_object* v_fst_504_; lean_object* v_snd_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_519_; 
v_fst_504_ = lean_ctor_get(v_b_497_, 0);
v_snd_505_ = lean_ctor_get(v_b_497_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_b_497_);
if (v_isSharedCheck_519_ == 0)
{
v___x_507_ = v_b_497_;
v_isShared_508_ = v_isSharedCheck_519_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_snd_505_);
lean_inc(v_fst_504_);
lean_dec(v_b_497_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_519_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_a_509_; uint8_t v_isNormalized_510_; 
v_a_509_ = lean_array_uget_borrowed(v_as_494_, v_i_496_);
v_isNormalized_510_ = lean_ctor_get_uint8(v_a_509_, sizeof(void*)*3);
if (v_isNormalized_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_513_; 
lean_inc(v_a_509_);
v___x_511_ = lean_array_push(v_snd_505_, v_a_509_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_511_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_fst_504_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
v_a_499_ = v___x_513_;
goto v___jp_498_;
}
}
else
{
lean_object* v___x_515_; lean_object* v___x_517_; 
lean_inc(v_a_509_);
v___x_515_ = lean_array_push(v_fst_504_, v_a_509_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_515_);
v___x_517_ = v___x_507_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_snd_505_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
v_a_499_ = v___x_517_;
goto v___jp_498_;
}
}
}
}
v___jp_498_:
{
size_t v___x_500_; size_t v___x_501_; 
v___x_500_ = ((size_t)1ULL);
v___x_501_ = lean_usize_add(v_i_496_, v___x_500_);
v_i_496_ = v___x_501_;
v_b_497_ = v_a_499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___boxed(lean_object* v_as_520_, lean_object* v_sz_521_, lean_object* v_i_522_, lean_object* v_b_523_){
_start:
{
size_t v_sz_boxed_524_; size_t v_i_boxed_525_; lean_object* v_res_526_; 
v_sz_boxed_524_ = lean_unbox_usize(v_sz_521_);
lean_dec(v_sz_521_);
v_i_boxed_525_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_res_526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(v_as_520_, v_sz_boxed_524_, v_i_boxed_525_, v_b_523_);
lean_dec_ref(v_as_520_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__11(lean_object* v_opts_527_, lean_object* v_opt_528_){
_start:
{
lean_object* v_name_529_; lean_object* v_defValue_530_; lean_object* v_map_531_; lean_object* v___x_532_; 
v_name_529_ = lean_ctor_get(v_opt_528_, 0);
v_defValue_530_ = lean_ctor_get(v_opt_528_, 1);
v_map_531_ = lean_ctor_get(v_opts_527_, 0);
v___x_532_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_531_, v_name_529_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_inc(v_defValue_530_);
return v_defValue_530_;
}
else
{
lean_object* v_val_533_; 
v_val_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_val_533_);
lean_dec_ref_known(v___x_532_, 1);
if (lean_obj_tag(v_val_533_) == 3)
{
lean_object* v_v_534_; 
v_v_534_ = lean_ctor_get(v_val_533_, 0);
lean_inc(v_v_534_);
lean_dec_ref_known(v_val_533_, 1);
return v_v_534_;
}
else
{
lean_dec(v_val_533_);
lean_inc(v_defValue_530_);
return v_defValue_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__11___boxed(lean_object* v_opts_535_, lean_object* v_opt_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__11(v_opts_535_, v_opt_536_);
lean_dec_ref(v_opt_536_);
lean_dec_ref(v_opts_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8_spec__9(size_t v_sz_538_, size_t v_i_539_, lean_object* v_bs_540_){
_start:
{
uint8_t v___x_541_; 
v___x_541_ = lean_usize_dec_lt(v_i_539_, v_sz_538_);
if (v___x_541_ == 0)
{
return v_bs_540_;
}
else
{
lean_object* v_v_542_; lean_object* v_msg_543_; lean_object* v___x_544_; lean_object* v_bs_x27_545_; size_t v___x_546_; size_t v___x_547_; lean_object* v___x_548_; 
v_v_542_ = lean_array_uget_borrowed(v_bs_540_, v_i_539_);
v_msg_543_ = lean_ctor_get(v_v_542_, 1);
lean_inc_ref(v_msg_543_);
v___x_544_ = lean_unsigned_to_nat(0u);
v_bs_x27_545_ = lean_array_uset(v_bs_540_, v_i_539_, v___x_544_);
v___x_546_ = ((size_t)1ULL);
v___x_547_ = lean_usize_add(v_i_539_, v___x_546_);
v___x_548_ = lean_array_uset(v_bs_x27_545_, v_i_539_, v_msg_543_);
v_i_539_ = v___x_547_;
v_bs_540_ = v___x_548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8_spec__9___boxed(lean_object* v_sz_550_, lean_object* v_i_551_, lean_object* v_bs_552_){
_start:
{
size_t v_sz_boxed_553_; size_t v_i_boxed_554_; lean_object* v_res_555_; 
v_sz_boxed_553_ = lean_unbox_usize(v_sz_550_);
lean_dec(v_sz_550_);
v_i_boxed_554_ = lean_unbox_usize(v_i_551_);
lean_dec(v_i_551_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8_spec__9(v_sz_boxed_553_, v_i_boxed_554_, v_bs_552_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8___redArg(lean_object* v_oldTraces_556_, lean_object* v_data_557_, lean_object* v_ref_558_, lean_object* v_msg_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_toCold_565_; lean_object* v_currRecDepth_566_; lean_object* v_ref_567_; uint16_t v_optionFlags_568_; uint8_t v_suppressElabErrors_569_; uint8_t v_checkDeprecated_570_; uint8_t v_isRecordingDeps_571_; lean_object* v_ref_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v_traceState_575_; lean_object* v_traces_576_; lean_object* v___x_577_; size_t v_sz_578_; size_t v___x_579_; lean_object* v___x_580_; lean_object* v_msg_581_; lean_object* v___x_582_; lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_621_; 
v_toCold_565_ = lean_ctor_get(v___y_562_, 0);
v_currRecDepth_566_ = lean_ctor_get(v___y_562_, 1);
v_ref_567_ = lean_ctor_get(v___y_562_, 2);
v_optionFlags_568_ = lean_ctor_get_uint16(v___y_562_, sizeof(void*)*3);
v_suppressElabErrors_569_ = lean_ctor_get_uint8(v___y_562_, sizeof(void*)*3 + 2);
v_checkDeprecated_570_ = lean_ctor_get_uint8(v___y_562_, sizeof(void*)*3 + 3);
v_isRecordingDeps_571_ = lean_ctor_get_uint8(v___y_562_, sizeof(void*)*3 + 4);
v_ref_572_ = l_Lean_replaceRef(v_ref_558_, v_ref_567_);
lean_inc(v_currRecDepth_566_);
lean_inc_ref(v_toCold_565_);
v___x_573_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_573_, 0, v_toCold_565_);
lean_ctor_set(v___x_573_, 1, v_currRecDepth_566_);
lean_ctor_set(v___x_573_, 2, v_ref_572_);
lean_ctor_set_uint16(v___x_573_, sizeof(void*)*3, v_optionFlags_568_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*3 + 2, v_suppressElabErrors_569_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*3 + 3, v_checkDeprecated_570_);
lean_ctor_set_uint8(v___x_573_, sizeof(void*)*3 + 4, v_isRecordingDeps_571_);
v___x_574_ = lean_st_ref_get(v___y_563_);
v_traceState_575_ = lean_ctor_get(v___x_574_, 4);
lean_inc_ref(v_traceState_575_);
lean_dec(v___x_574_);
v_traces_576_ = lean_ctor_get(v_traceState_575_, 0);
lean_inc_ref(v_traces_576_);
lean_dec_ref(v_traceState_575_);
v___x_577_ = l_Lean_PersistentArray_toArray___redArg(v_traces_576_);
lean_dec_ref(v_traces_576_);
v_sz_578_ = lean_array_size(v___x_577_);
v___x_579_ = ((size_t)0ULL);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8_spec__9(v_sz_578_, v___x_579_, v___x_577_);
v_msg_581_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_581_, 0, v_data_557_);
lean_ctor_set(v_msg_581_, 1, v_msg_559_);
lean_ctor_set(v_msg_581_, 2, v___x_580_);
v___x_582_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msg_581_, v___y_560_, v___y_561_, v___x_573_, v___y_563_);
lean_dec_ref_known(v___x_573_, 3);
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_621_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_621_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_621_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v_traceState_588_; lean_object* v_env_589_; lean_object* v_nextMacroScope_590_; lean_object* v_ngen_591_; lean_object* v_auxDeclNGen_592_; lean_object* v_cache_593_; lean_object* v_recordedDeps_594_; lean_object* v_messages_595_; lean_object* v_infoState_596_; lean_object* v_snapshotTasks_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_620_; 
v___x_587_ = lean_st_ref_take(v___y_563_);
v_traceState_588_ = lean_ctor_get(v___x_587_, 4);
v_env_589_ = lean_ctor_get(v___x_587_, 0);
v_nextMacroScope_590_ = lean_ctor_get(v___x_587_, 1);
v_ngen_591_ = lean_ctor_get(v___x_587_, 2);
v_auxDeclNGen_592_ = lean_ctor_get(v___x_587_, 3);
v_cache_593_ = lean_ctor_get(v___x_587_, 5);
v_recordedDeps_594_ = lean_ctor_get(v___x_587_, 6);
v_messages_595_ = lean_ctor_get(v___x_587_, 7);
v_infoState_596_ = lean_ctor_get(v___x_587_, 8);
v_snapshotTasks_597_ = lean_ctor_get(v___x_587_, 9);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_620_ == 0)
{
v___x_599_ = v___x_587_;
v_isShared_600_ = v_isSharedCheck_620_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_snapshotTasks_597_);
lean_inc(v_infoState_596_);
lean_inc(v_messages_595_);
lean_inc(v_recordedDeps_594_);
lean_inc(v_cache_593_);
lean_inc(v_traceState_588_);
lean_inc(v_auxDeclNGen_592_);
lean_inc(v_ngen_591_);
lean_inc(v_nextMacroScope_590_);
lean_inc(v_env_589_);
lean_dec(v___x_587_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_620_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
uint64_t v_tid_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_618_; 
v_tid_601_ = lean_ctor_get_uint64(v_traceState_588_, sizeof(void*)*1);
v_isSharedCheck_618_ = !lean_is_exclusive(v_traceState_588_);
if (v_isSharedCheck_618_ == 0)
{
lean_object* v_unused_619_; 
v_unused_619_ = lean_ctor_get(v_traceState_588_, 0);
lean_dec(v_unused_619_);
v___x_603_ = v_traceState_588_;
v_isShared_604_ = v_isSharedCheck_618_;
goto v_resetjp_602_;
}
else
{
lean_dec(v_traceState_588_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_618_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_605_ = lean_box(0);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v_ref_558_);
lean_ctor_set(v___x_606_, 1, v_a_583_);
v___x_607_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_556_, v___x_606_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_607_);
v___x_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_607_);
lean_ctor_set_uint64(v_reuseFailAlloc_617_, sizeof(void*)*1, v_tid_601_);
v___x_609_ = v_reuseFailAlloc_617_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 4, v___x_609_);
v___x_611_ = v___x_599_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_env_589_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v_nextMacroScope_590_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_ngen_591_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_auxDeclNGen_592_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v_cache_593_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_recordedDeps_594_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v_messages_595_);
lean_ctor_set(v_reuseFailAlloc_616_, 8, v_infoState_596_);
lean_ctor_set(v_reuseFailAlloc_616_, 9, v_snapshotTasks_597_);
v___x_611_ = v_reuseFailAlloc_616_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_st_ref_put(v___y_563_, v___x_611_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_605_);
v___x_614_ = v___x_585_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_605_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8___redArg___boxed(lean_object* v_oldTraces_622_, lean_object* v_data_623_, lean_object* v_ref_624_, lean_object* v_msg_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8___redArg(v_oldTraces_622_, v_data_623_, v_ref_624_, v_msg_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
return v_res_631_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__10(lean_object* v_e_632_){
_start:
{
if (lean_obj_tag(v_e_632_) == 0)
{
uint8_t v___x_633_; 
v___x_633_ = 2;
return v___x_633_;
}
else
{
uint8_t v___x_634_; 
v___x_634_ = 0;
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__10___boxed(lean_object* v_e_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__10(v_e_635_);
lean_dec_ref(v_e_635_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9___redArg(lean_object* v_x_638_){
_start:
{
if (lean_obj_tag(v_x_638_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_640_ = lean_ctor_get(v_x_638_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_638_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v_x_638_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v_x_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 1);
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_a_648_ = lean_ctor_get(v_x_638_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v_x_638_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v_x_638_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v_x_638_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 0);
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9___redArg___boxed(lean_object* v_x_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9___redArg(v_x_656_);
return v_res_658_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__0(void){
_start:
{
lean_object* v___x_659_; double v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_float_of_nat(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__2(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__1));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__3(void){
_start:
{
lean_object* v___x_664_; double v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(1000u);
v___x_665_ = lean_float_of_nat(v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7(lean_object* v_cls_666_, uint8_t v_collapsed_667_, lean_object* v_tag_668_, lean_object* v_opts_669_, uint8_t v_clsEnabled_670_, lean_object* v_oldTraces_671_, lean_object* v_msg_672_, lean_object* v_resStartStop_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_fst_689_; lean_object* v_snd_690_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v_data_694_; lean_object* v_fst_705_; lean_object* v_snd_706_; lean_object* v___x_707_; uint8_t v___x_708_; lean_object* v___y_710_; lean_object* v_a_711_; uint8_t v___y_726_; double v___y_758_; 
v_fst_689_ = lean_ctor_get(v_resStartStop_673_, 0);
lean_inc(v_fst_689_);
v_snd_690_ = lean_ctor_get(v_resStartStop_673_, 1);
lean_inc(v_snd_690_);
lean_dec_ref(v_resStartStop_673_);
v_fst_705_ = lean_ctor_get(v_snd_690_, 0);
lean_inc(v_fst_705_);
v_snd_706_ = lean_ctor_get(v_snd_690_, 1);
lean_inc(v_snd_706_);
lean_dec(v_snd_690_);
v___x_707_ = l_Lean_trace_profiler;
v___x_708_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v_opts_669_, v___x_707_);
if (v___x_708_ == 0)
{
v___y_726_ = v___x_708_;
goto v___jp_725_;
}
else
{
lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_763_ = l_Lean_trace_profiler_useHeartbeats;
v___x_764_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v_opts_669_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; double v___x_767_; double v___x_768_; double v___x_769_; 
v___x_765_ = l_Lean_trace_profiler_threshold;
v___x_766_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__11(v_opts_669_, v___x_765_);
v___x_767_ = lean_float_of_nat(v___x_766_);
v___x_768_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__3);
v___x_769_ = lean_float_div(v___x_767_, v___x_768_);
v___y_758_ = v___x_769_;
goto v___jp_757_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; double v___x_772_; 
v___x_770_ = l_Lean_trace_profiler_threshold;
v___x_771_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__11(v_opts_669_, v___x_770_);
v___x_772_ = lean_float_of_nat(v___x_771_);
v___y_758_ = v___x_772_;
goto v___jp_757_;
}
}
v___jp_691_:
{
lean_object* v___x_695_; 
lean_inc(v___y_693_);
v___x_695_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8___redArg(v_oldTraces_671_, v_data_694_, v___y_693_, v___y_692_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_696_; 
lean_dec_ref_known(v___x_695_, 1);
v___x_696_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9___redArg(v_fst_689_);
return v___x_696_;
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_fst_689_);
v_a_697_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_695_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_695_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
v___jp_709_:
{
uint8_t v_result_712_; lean_object* v___x_713_; lean_object* v___x_714_; double v___x_715_; lean_object* v_data_716_; 
v_result_712_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__10(v_fst_689_);
v___x_713_ = lean_box(v_result_712_);
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
v___x_715_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__0);
lean_inc_ref(v_tag_668_);
lean_inc_ref(v___x_714_);
lean_inc(v_cls_666_);
v_data_716_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_716_, 0, v_cls_666_);
lean_ctor_set(v_data_716_, 1, v___x_714_);
lean_ctor_set(v_data_716_, 2, v_tag_668_);
lean_ctor_set_float(v_data_716_, sizeof(void*)*3, v___x_715_);
lean_ctor_set_float(v_data_716_, sizeof(void*)*3 + 8, v___x_715_);
lean_ctor_set_uint8(v_data_716_, sizeof(void*)*3 + 16, v_collapsed_667_);
if (v___x_708_ == 0)
{
lean_dec_ref_known(v___x_714_, 1);
lean_dec(v_snd_706_);
lean_dec(v_fst_705_);
lean_dec_ref(v_tag_668_);
lean_dec(v_cls_666_);
v___y_692_ = v_a_711_;
v___y_693_ = v___y_710_;
v_data_694_ = v_data_716_;
goto v___jp_691_;
}
else
{
lean_object* v_data_717_; double v___x_718_; double v___x_719_; 
lean_dec_ref_known(v_data_716_, 3);
v_data_717_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_717_, 0, v_cls_666_);
lean_ctor_set(v_data_717_, 1, v___x_714_);
lean_ctor_set(v_data_717_, 2, v_tag_668_);
v___x_718_ = lean_unbox_float(v_fst_705_);
lean_dec(v_fst_705_);
lean_ctor_set_float(v_data_717_, sizeof(void*)*3, v___x_718_);
v___x_719_ = lean_unbox_float(v_snd_706_);
lean_dec(v_snd_706_);
lean_ctor_set_float(v_data_717_, sizeof(void*)*3 + 8, v___x_719_);
lean_ctor_set_uint8(v_data_717_, sizeof(void*)*3 + 16, v_collapsed_667_);
v___y_692_ = v_a_711_;
v___y_693_ = v___y_710_;
v_data_694_ = v_data_717_;
goto v___jp_691_;
}
}
v___jp_720_:
{
lean_object* v_ref_721_; lean_object* v___x_722_; 
v_ref_721_ = lean_ctor_get(v___y_686_, 2);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
lean_inc(v___y_685_);
lean_inc_ref(v___y_684_);
lean_inc(v___y_683_);
lean_inc_ref(v___y_682_);
lean_inc(v___y_681_);
lean_inc_ref(v___y_680_);
lean_inc(v___y_679_);
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
lean_inc(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v_fst_689_);
v___x_722_ = lean_apply_16(v_msg_672_, v_fst_689_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, lean_box(0));
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v___y_710_ = v_ref_721_;
v_a_711_ = v_a_723_;
goto v___jp_709_;
}
else
{
lean_object* v___x_724_; 
lean_dec_ref_known(v___x_722_, 1);
v___x_724_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___closed__2);
v___y_710_ = v_ref_721_;
v_a_711_ = v___x_724_;
goto v___jp_709_;
}
}
v___jp_725_:
{
if (v_clsEnabled_670_ == 0)
{
if (v___y_726_ == 0)
{
lean_object* v___x_727_; lean_object* v_traceState_728_; lean_object* v_env_729_; lean_object* v_nextMacroScope_730_; lean_object* v_ngen_731_; lean_object* v_auxDeclNGen_732_; lean_object* v_cache_733_; lean_object* v_recordedDeps_734_; lean_object* v_messages_735_; lean_object* v_infoState_736_; lean_object* v_snapshotTasks_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_snd_706_);
lean_dec(v_fst_705_);
lean_dec_ref(v_msg_672_);
lean_dec_ref(v_tag_668_);
lean_dec(v_cls_666_);
v___x_727_ = lean_st_ref_take(v___y_687_);
v_traceState_728_ = lean_ctor_get(v___x_727_, 4);
v_env_729_ = lean_ctor_get(v___x_727_, 0);
v_nextMacroScope_730_ = lean_ctor_get(v___x_727_, 1);
v_ngen_731_ = lean_ctor_get(v___x_727_, 2);
v_auxDeclNGen_732_ = lean_ctor_get(v___x_727_, 3);
v_cache_733_ = lean_ctor_get(v___x_727_, 5);
v_recordedDeps_734_ = lean_ctor_get(v___x_727_, 6);
v_messages_735_ = lean_ctor_get(v___x_727_, 7);
v_infoState_736_ = lean_ctor_get(v___x_727_, 8);
v_snapshotTasks_737_ = lean_ctor_get(v___x_727_, 9);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_756_ == 0)
{
v___x_739_ = v___x_727_;
v_isShared_740_ = v_isSharedCheck_756_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snapshotTasks_737_);
lean_inc(v_infoState_736_);
lean_inc(v_messages_735_);
lean_inc(v_recordedDeps_734_);
lean_inc(v_cache_733_);
lean_inc(v_traceState_728_);
lean_inc(v_auxDeclNGen_732_);
lean_inc(v_ngen_731_);
lean_inc(v_nextMacroScope_730_);
lean_inc(v_env_729_);
lean_dec(v___x_727_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_756_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
uint64_t v_tid_741_; lean_object* v_traces_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_755_; 
v_tid_741_ = lean_ctor_get_uint64(v_traceState_728_, sizeof(void*)*1);
v_traces_742_ = lean_ctor_get(v_traceState_728_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v_traceState_728_);
if (v_isSharedCheck_755_ == 0)
{
v___x_744_ = v_traceState_728_;
v_isShared_745_ = v_isSharedCheck_755_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_traces_742_);
lean_dec(v_traceState_728_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_755_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_671_, v_traces_742_);
lean_dec_ref(v_traces_742_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_746_);
lean_ctor_set_uint64(v_reuseFailAlloc_754_, sizeof(void*)*1, v_tid_741_);
v___x_748_ = v_reuseFailAlloc_754_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 4, v___x_748_);
v___x_750_ = v___x_739_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_env_729_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_nextMacroScope_730_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_ngen_731_);
lean_ctor_set(v_reuseFailAlloc_753_, 3, v_auxDeclNGen_732_);
lean_ctor_set(v_reuseFailAlloc_753_, 4, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_753_, 5, v_cache_733_);
lean_ctor_set(v_reuseFailAlloc_753_, 6, v_recordedDeps_734_);
lean_ctor_set(v_reuseFailAlloc_753_, 7, v_messages_735_);
lean_ctor_set(v_reuseFailAlloc_753_, 8, v_infoState_736_);
lean_ctor_set(v_reuseFailAlloc_753_, 9, v_snapshotTasks_737_);
v___x_750_ = v_reuseFailAlloc_753_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_st_ref_put(v___y_687_, v___x_750_);
v___x_752_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9___redArg(v_fst_689_);
return v___x_752_;
}
}
}
}
}
else
{
goto v___jp_720_;
}
}
else
{
goto v___jp_720_;
}
}
v___jp_757_:
{
double v___x_759_; double v___x_760_; double v___x_761_; uint8_t v___x_762_; 
v___x_759_ = lean_unbox_float(v_snd_706_);
v___x_760_ = lean_unbox_float(v_fst_705_);
v___x_761_ = lean_float_sub(v___x_759_, v___x_760_);
v___x_762_ = lean_float_decLt(v___y_758_, v___x_761_);
v___y_726_ = v___x_762_;
goto v___jp_725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7___boxed(lean_object** _args){
lean_object* v_cls_773_ = _args[0];
lean_object* v_collapsed_774_ = _args[1];
lean_object* v_tag_775_ = _args[2];
lean_object* v_opts_776_ = _args[3];
lean_object* v_clsEnabled_777_ = _args[4];
lean_object* v_oldTraces_778_ = _args[5];
lean_object* v_msg_779_ = _args[6];
lean_object* v_resStartStop_780_ = _args[7];
lean_object* v___y_781_ = _args[8];
lean_object* v___y_782_ = _args[9];
lean_object* v___y_783_ = _args[10];
lean_object* v___y_784_ = _args[11];
lean_object* v___y_785_ = _args[12];
lean_object* v___y_786_ = _args[13];
lean_object* v___y_787_ = _args[14];
lean_object* v___y_788_ = _args[15];
lean_object* v___y_789_ = _args[16];
lean_object* v___y_790_ = _args[17];
lean_object* v___y_791_ = _args[18];
lean_object* v___y_792_ = _args[19];
lean_object* v___y_793_ = _args[20];
lean_object* v___y_794_ = _args[21];
lean_object* v___y_795_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_796_; uint8_t v_clsEnabled_boxed_797_; lean_object* v_res_798_; 
v_collapsed_boxed_796_ = lean_unbox(v_collapsed_774_);
v_clsEnabled_boxed_797_ = lean_unbox(v_clsEnabled_777_);
v_res_798_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7(v_cls_773_, v_collapsed_boxed_796_, v_tag_775_, v_opts_776_, v_clsEnabled_boxed_797_, v_oldTraces_778_, v_msg_779_, v_resStartStop_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec_ref(v_opts_776_);
return v_res_798_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3(void){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_806_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4);
v___x_810_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
lean_ctor_set(v___x_810_, 2, v___x_809_);
lean_ctor_set(v___x_810_, 3, v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = lean_box(0);
v___x_812_ = lean_unsigned_to_nat(16u);
v___x_813_ = lean_mk_array(v___x_812_, v___x_811_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___x_814_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7);
v___x_818_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
lean_ctor_set(v___x_818_, 2, v___x_817_);
lean_ctor_set(v___x_818_, 3, v___x_817_);
return v___x_818_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13));
v___x_832_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__16));
v___x_833_ = l_Lean_Name_append(v___x_832_, v___x_831_);
return v___x_833_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18(void){
_start:
{
lean_object* v___x_834_; double v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(1000000000u);
v___x_835_ = lean_float_of_nat(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___y_852_; lean_object* v_a_853_; lean_object* v_hypQueue_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v_hypQueue_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v_toCold_1086_; lean_object* v_options_1087_; uint8_t v_hasTrace_1088_; 
v_toCold_1086_ = lean_ctor_get(v_a_848_, 0);
v_options_1087_ = lean_ctor_get(v_toCold_1086_, 2);
v_hasTrace_1088_ = lean_ctor_get_uint8(v_options_1087_, sizeof(void*)*1);
if (v_hasTrace_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v_satExpr_1090_; lean_object* v_hypQueue_1091_; lean_object* v_usedHyps_1092_; uint8_t v_didChange_1093_; lean_object* v_theoryState_1094_; lean_object* v_solverTimeBudgetMs_1095_; lean_object* v_roundBudget_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1106_; 
v___x_1089_ = lean_st_ref_take(v_a_837_);
v_satExpr_1090_ = lean_ctor_get(v___x_1089_, 0);
v_hypQueue_1091_ = lean_ctor_get(v___x_1089_, 1);
v_usedHyps_1092_ = lean_ctor_get(v___x_1089_, 2);
v_didChange_1093_ = lean_ctor_get_uint8(v___x_1089_, sizeof(void*)*6);
v_theoryState_1094_ = lean_ctor_get(v___x_1089_, 3);
v_solverTimeBudgetMs_1095_ = lean_ctor_get(v___x_1089_, 4);
v_roundBudget_1096_ = lean_ctor_get(v___x_1089_, 5);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1098_ = v___x_1089_;
v_isShared_1099_ = v_isSharedCheck_1106_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_roundBudget_1096_);
lean_inc(v_solverTimeBudgetMs_1095_);
lean_inc(v_theoryState_1094_);
lean_inc(v_usedHyps_1092_);
lean_inc(v_hypQueue_1091_);
lean_inc(v_satExpr_1090_);
lean_dec(v___x_1089_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1106_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1100_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0));
v___x_1101_ = l_Array_append___redArg(v_usedHyps_1092_, v_hypQueue_1091_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 2, v___x_1101_);
lean_ctor_set(v___x_1098_, 1, v___x_1100_);
v___x_1103_ = v___x_1098_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_satExpr_1090_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_theoryState_1094_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_solverTimeBudgetMs_1095_);
lean_ctor_set(v_reuseFailAlloc_1105_, 5, v_roundBudget_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*6, v_didChange_1093_);
v___x_1103_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_st_ref_put(v_a_837_, v___x_1103_);
v_hypQueue_929_ = v_hypQueue_1091_;
v___y_930_ = v_a_836_;
v___y_931_ = v_a_837_;
v___y_932_ = v_a_838_;
v___y_933_ = v_a_839_;
v___y_934_ = v_a_840_;
v___y_935_ = v_a_841_;
v___y_936_ = v_a_842_;
v___y_937_ = v_a_843_;
v___y_938_ = v_a_844_;
v___y_939_ = v_a_845_;
v___y_940_ = v_a_846_;
v___y_941_ = v_a_847_;
v___y_942_ = v_a_848_;
v___y_943_ = v_a_849_;
goto v___jp_928_;
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v_a_1116_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v_a_1131_; lean_object* v___y_1134_; lean_object* v___y_1135_; uint8_t v_a_1136_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v_a_1149_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v_a_1161_; lean_object* v___y_1164_; lean_object* v___y_1165_; uint8_t v_a_1166_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; 
v_inheritedTraceOptions_1107_ = lean_ctor_get(v_toCold_1086_, 11);
v___f_1108_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__9));
v___x_1109_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13));
v___x_1110_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__14));
v___x_1111_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17);
v___x_1112_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1107_, v_options_1087_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = l_Lean_trace_profiler;
v___x_1486_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v_options_1087_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v_satExpr_1488_; lean_object* v_hypQueue_1489_; lean_object* v_usedHyps_1490_; uint8_t v_didChange_1491_; lean_object* v_theoryState_1492_; lean_object* v_solverTimeBudgetMs_1493_; lean_object* v_roundBudget_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1504_; 
v___x_1487_ = lean_st_ref_take(v_a_837_);
v_satExpr_1488_ = lean_ctor_get(v___x_1487_, 0);
v_hypQueue_1489_ = lean_ctor_get(v___x_1487_, 1);
v_usedHyps_1490_ = lean_ctor_get(v___x_1487_, 2);
v_didChange_1491_ = lean_ctor_get_uint8(v___x_1487_, sizeof(void*)*6);
v_theoryState_1492_ = lean_ctor_get(v___x_1487_, 3);
v_solverTimeBudgetMs_1493_ = lean_ctor_get(v___x_1487_, 4);
v_roundBudget_1494_ = lean_ctor_get(v___x_1487_, 5);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1496_ = v___x_1487_;
v_isShared_1497_ = v_isSharedCheck_1504_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_roundBudget_1494_);
lean_inc(v_solverTimeBudgetMs_1493_);
lean_inc(v_theoryState_1492_);
lean_inc(v_usedHyps_1490_);
lean_inc(v_hypQueue_1489_);
lean_inc(v_satExpr_1488_);
lean_dec(v___x_1487_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1504_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1498_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0));
v___x_1499_ = l_Array_append___redArg(v_usedHyps_1490_, v_hypQueue_1489_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 2, v___x_1499_);
lean_ctor_set(v___x_1496_, 1, v___x_1498_);
v___x_1501_ = v___x_1496_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_satExpr_1488_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_theoryState_1492_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v_solverTimeBudgetMs_1493_);
lean_ctor_set(v_reuseFailAlloc_1503_, 5, v_roundBudget_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1503_, sizeof(void*)*6, v_didChange_1491_);
v___x_1501_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_st_ref_put(v_a_837_, v___x_1501_);
v_hypQueue_929_ = v_hypQueue_1489_;
v___y_930_ = v_a_836_;
v___y_931_ = v_a_837_;
v___y_932_ = v_a_838_;
v___y_933_ = v_a_839_;
v___y_934_ = v_a_840_;
v___y_935_ = v_a_841_;
v___y_936_ = v_a_842_;
v___y_937_ = v_a_843_;
v___y_938_ = v_a_844_;
v___y_939_ = v_a_845_;
v___y_940_ = v_a_846_;
v___y_941_ = v_a_847_;
v___y_942_ = v_a_848_;
v___y_943_ = v_a_849_;
goto v___jp_928_;
}
}
}
else
{
goto v___jp_1176_;
}
}
else
{
goto v___jp_1176_;
}
v___jp_1113_:
{
lean_object* v___x_1117_; double v___x_1118_; double v___x_1119_; double v___x_1120_; double v___x_1121_; double v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1117_ = lean_io_mono_nanos_now();
v___x_1118_ = lean_float_of_nat(v___y_1114_);
v___x_1119_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18);
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
v___x_1127_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7(v___x_1109_, v_hasTrace_1088_, v___x_1110_, v_options_1087_, v___x_1112_, v___y_1115_, v___f_1108_, v___x_1126_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
return v___x_1127_;
}
v___jp_1128_:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_a_1131_);
v___y_1114_ = v___y_1129_;
v___y_1115_ = v___y_1130_;
v_a_1116_ = v___x_1132_;
goto v___jp_1113_;
}
v___jp_1133_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_box(v_a_1136_);
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
v___y_1114_ = v___y_1134_;
v___y_1115_ = v___y_1135_;
v_a_1116_ = v___x_1138_;
goto v___jp_1113_;
}
v___jp_1139_:
{
if (lean_obj_tag(v___y_1142_) == 0)
{
lean_object* v_a_1143_; uint8_t v___x_1144_; 
v_a_1143_ = lean_ctor_get(v___y_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___y_1142_, 1);
v___x_1144_ = lean_unbox(v_a_1143_);
lean_dec(v_a_1143_);
v___y_1134_ = v___y_1140_;
v___y_1135_ = v___y_1141_;
v_a_1136_ = v___x_1144_;
goto v___jp_1133_;
}
else
{
lean_object* v_a_1145_; 
v_a_1145_ = lean_ctor_get(v___y_1142_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___y_1142_, 1);
v___y_1129_ = v___y_1140_;
v___y_1130_ = v___y_1141_;
v_a_1131_ = v_a_1145_;
goto v___jp_1128_;
}
}
v___jp_1146_:
{
lean_object* v___x_1150_; double v___x_1151_; double v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1150_ = lean_io_get_num_heartbeats();
v___x_1151_ = lean_float_of_nat(v___y_1147_);
v___x_1152_ = lean_float_of_nat(v___x_1150_);
v___x_1153_ = lean_box_float(v___x_1151_);
v___x_1154_ = lean_box_float(v___x_1152_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v_a_1149_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7(v___x_1109_, v_hasTrace_1088_, v___x_1110_, v_options_1087_, v___x_1112_, v___y_1148_, v___f_1108_, v___x_1156_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
return v___x_1157_;
}
v___jp_1158_:
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v_a_1161_);
v___y_1147_ = v___y_1159_;
v___y_1148_ = v___y_1160_;
v_a_1149_ = v___x_1162_;
goto v___jp_1146_;
}
v___jp_1163_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_box(v_a_1166_);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
v___y_1147_ = v___y_1164_;
v___y_1148_ = v___y_1165_;
v_a_1149_ = v___x_1168_;
goto v___jp_1146_;
}
v___jp_1169_:
{
if (lean_obj_tag(v___y_1172_) == 0)
{
lean_object* v_a_1173_; uint8_t v___x_1174_; 
v_a_1173_ = lean_ctor_get(v___y_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___y_1172_, 1);
v___x_1174_ = lean_unbox(v_a_1173_);
lean_dec(v_a_1173_);
v___y_1164_ = v___y_1170_;
v___y_1165_ = v___y_1171_;
v_a_1166_ = v___x_1174_;
goto v___jp_1163_;
}
else
{
lean_object* v_a_1175_; 
v_a_1175_ = lean_ctor_get(v___y_1172_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___y_1172_, 1);
v___y_1159_ = v___y_1170_;
v___y_1160_ = v___y_1171_;
v_a_1161_ = v_a_1175_;
goto v___jp_1158_;
}
}
v___jp_1176_:
{
lean_object* v___x_1177_; lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1484_; 
v___x_1177_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___redArg(v_a_849_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1484_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1484_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1183_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v_options_1087_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v_satExpr_1186_; lean_object* v_hypQueue_1187_; lean_object* v_usedHyps_1188_; uint8_t v_didChange_1189_; lean_object* v_theoryState_1190_; lean_object* v_solverTimeBudgetMs_1191_; lean_object* v_roundBudget_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1333_; 
v___x_1184_ = lean_io_mono_nanos_now();
v___x_1185_ = lean_st_ref_take(v_a_837_);
v_satExpr_1186_ = lean_ctor_get(v___x_1185_, 0);
v_hypQueue_1187_ = lean_ctor_get(v___x_1185_, 1);
v_usedHyps_1188_ = lean_ctor_get(v___x_1185_, 2);
v_didChange_1189_ = lean_ctor_get_uint8(v___x_1185_, sizeof(void*)*6);
v_theoryState_1190_ = lean_ctor_get(v___x_1185_, 3);
v_solverTimeBudgetMs_1191_ = lean_ctor_get(v___x_1185_, 4);
v_roundBudget_1192_ = lean_ctor_get(v___x_1185_, 5);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1194_ = v___x_1185_;
v_isShared_1195_ = v_isSharedCheck_1333_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_roundBudget_1192_);
lean_inc(v_solverTimeBudgetMs_1191_);
lean_inc(v_theoryState_1190_);
lean_inc(v_usedHyps_1188_);
lean_inc(v_hypQueue_1187_);
lean_inc(v_satExpr_1186_);
lean_dec(v___x_1185_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1333_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0));
v___x_1198_ = l_Array_append___redArg(v_usedHyps_1188_, v_hypQueue_1187_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 2, v___x_1198_);
lean_ctor_set(v___x_1194_, 1, v___x_1197_);
v___x_1200_ = v___x_1194_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_satExpr_1186_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_theoryState_1190_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v_solverTimeBudgetMs_1191_);
lean_ctor_set(v_reuseFailAlloc_1332_, 5, v_roundBudget_1192_);
lean_ctor_set_uint8(v_reuseFailAlloc_1332_, sizeof(void*)*6, v_didChange_1189_);
v___x_1200_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = lean_st_ref_put(v_a_837_, v___x_1200_);
v___x_1202_ = lean_array_get_size(v_hypQueue_1187_);
v___x_1203_ = lean_nat_dec_eq(v___x_1202_, v___x_1196_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; size_t v_sz_1205_; size_t v___x_1206_; lean_object* v___x_1207_; lean_object* v_fst_1208_; lean_object* v_snd_1209_; size_t v_sz_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1204_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1));
v_sz_1205_ = lean_array_size(v_hypQueue_1187_);
v___x_1206_ = ((size_t)0ULL);
v___x_1207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(v_hypQueue_1187_, v_sz_1205_, v___x_1206_, v___x_1204_);
lean_dec_ref(v_hypQueue_1187_);
v_fst_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_fst_1208_);
v_snd_1209_ = lean_ctor_get(v___x_1207_, 1);
lean_inc(v_snd_1209_);
lean_dec_ref(v___x_1207_);
v_sz_1210_ = lean_array_size(v_fst_1208_);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(v_sz_1210_, v___x_1206_, v_fst_1208_);
v___x_1212_ = lean_array_get_size(v_snd_1209_);
v___x_1213_ = lean_nat_dec_eq(v___x_1212_, v___x_1196_);
if (v___x_1213_ == 0)
{
lean_object* v_goal_1214_; lean_object* v_tacticContext_1215_; lean_object* v___x_1216_; lean_object* v_config_1217_; lean_object* v_mode_1218_; lean_object* v_timeout_1219_; uint8_t v_trimProofs_1220_; uint8_t v_binaryProofs_1221_; uint8_t v_acNf_1222_; uint8_t v_andFlattening_1223_; uint8_t v_embeddedConstraintSubst_1224_; uint8_t v_graphviz_1225_; lean_object* v_maxSteps_1226_; uint8_t v_solverMode_1227_; uint8_t v_uf_1228_; lean_object* v_cegarRounds_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1328_; 
v_goal_1214_ = lean_ctor_get(v_a_836_, 0);
v_tacticContext_1215_ = lean_ctor_get(v_a_836_, 2);
lean_inc_ref(v_tacticContext_1215_);
v___x_1216_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1215_);
v_config_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc_ref(v_config_1217_);
v_mode_1218_ = lean_ctor_get(v___x_1216_, 1);
lean_inc(v_mode_1218_);
lean_dec_ref(v___x_1216_);
v_timeout_1219_ = lean_ctor_get(v_config_1217_, 0);
v_trimProofs_1220_ = lean_ctor_get_uint8(v_config_1217_, sizeof(void*)*3);
v_binaryProofs_1221_ = lean_ctor_get_uint8(v_config_1217_, sizeof(void*)*3 + 1);
v_acNf_1222_ = lean_ctor_get_uint8(v_config_1217_, sizeof(void*)*3 + 2);
v_andFlattening_1223_ = lean_ctor_get_uint8(v_config_1217_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1224_ = lean_ctor_get_uint8(v_config_1217_, sizeof(void*)*3 + 4);
v_graphviz_1225_ = lean_ctor_get_uint8(v_config_1217_, sizeof(void*)*3 + 8);
v_maxSteps_1226_ = lean_ctor_get(v_config_1217_, 1);
v_solverMode_1227_ = lean_ctor_get_uint8(v_config_1217_, sizeof(void*)*3 + 10);
v_uf_1228_ = lean_ctor_get_uint8(v_config_1217_, sizeof(void*)*3 + 11);
v_cegarRounds_1229_ = lean_ctor_get(v_config_1217_, 2);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_config_1217_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1231_ = v_config_1217_;
v_isShared_1232_ = v_isSharedCheck_1328_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_cegarRounds_1229_);
lean_inc(v_maxSteps_1226_);
lean_inc(v_timeout_1219_);
lean_dec(v_config_1217_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1328_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
lean_inc(v_goal_1214_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v_goal_1214_);
v___x_1234_ = v___x_1180_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_goal_1214_);
v___x_1234_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1236_; 
if (v_isShared_1232_ == 0)
{
v___x_1236_ = v___x_1231_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_timeout_1219_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_maxSteps_1226_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_cegarRounds_1229_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*3, v_trimProofs_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*3 + 1, v_binaryProofs_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*3 + 2, v_acNf_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*3 + 3, v_andFlattening_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1224_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*3 + 8, v_graphviz_1225_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*3 + 10, v_solverMode_1227_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*3 + 11, v_uf_1228_);
v___x_1236_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_theoryState_1241_; lean_object* v_satExpr_1242_; lean_object* v_hypQueue_1243_; lean_object* v_usedHyps_1244_; uint8_t v_didChange_1245_; lean_object* v_solverTimeBudgetMs_1246_; lean_object* v_roundBudget_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1325_; 
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*3 + 5, v___x_1213_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*3 + 6, v___x_1213_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*3 + 7, v___x_1213_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*3 + 9, v___x_1213_);
v___x_1237_ = lean_box(v_hasTrace_1088_);
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
v___x_1239_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1218_, v___x_1236_, v___x_1238_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = lean_st_ref_take(v_a_837_);
v_theoryState_1241_ = lean_ctor_get(v___x_1240_, 3);
v_satExpr_1242_ = lean_ctor_get(v___x_1240_, 0);
v_hypQueue_1243_ = lean_ctor_get(v___x_1240_, 1);
v_usedHyps_1244_ = lean_ctor_get(v___x_1240_, 2);
v_didChange_1245_ = lean_ctor_get_uint8(v___x_1240_, sizeof(void*)*6);
v_solverTimeBudgetMs_1246_ = lean_ctor_get(v___x_1240_, 4);
v_roundBudget_1247_ = lean_ctor_get(v___x_1240_, 5);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1249_ = v___x_1240_;
v_isShared_1250_ = v_isSharedCheck_1325_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_roundBudget_1247_);
lean_inc(v_solverTimeBudgetMs_1246_);
lean_inc(v_theoryState_1241_);
lean_inc(v_usedHyps_1244_);
lean_inc(v_hypQueue_1243_);
lean_inc(v_satExpr_1242_);
lean_dec(v___x_1240_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1325_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_funState_1251_; lean_object* v_bitvecState_1252_; lean_object* v_preprocessCaches_1253_; lean_object* v_satSolver_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1324_; 
v_funState_1251_ = lean_ctor_get(v_theoryState_1241_, 0);
v_bitvecState_1252_ = lean_ctor_get(v_theoryState_1241_, 1);
v_preprocessCaches_1253_ = lean_ctor_get(v_theoryState_1241_, 2);
v_satSolver_1254_ = lean_ctor_get(v_theoryState_1241_, 3);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_theoryState_1241_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1256_ = v_theoryState_1241_;
v_isShared_1257_ = v_isSharedCheck_1324_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_satSolver_1254_);
lean_inc(v_preprocessCaches_1253_);
lean_inc(v_bitvecState_1252_);
lean_inc(v_funState_1251_);
lean_dec(v_theoryState_1241_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1324_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 2, v___x_1258_);
v___x_1260_ = v___x_1256_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_funState_1251_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_bitvecState_1252_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_satSolver_1254_);
v___x_1260_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1262_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 3, v___x_1260_);
v___x_1262_ = v___x_1249_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_satExpr_1242_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_hypQueue_1243_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_usedHyps_1244_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_solverTimeBudgetMs_1246_);
lean_ctor_set(v_reuseFailAlloc_1322_, 5, v_roundBudget_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1322_, sizeof(void*)*6, v_didChange_1245_);
v___x_1262_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v_typeAnalysis_1268_; lean_object* v_target_1269_; lean_object* v_hypotheses_1270_; uint8_t v_didChange_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1320_; 
v___x_1263_ = lean_st_ref_put(v_a_837_, v___x_1262_);
v___x_1264_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8);
v___x_1265_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1265_, 0, v___x_1258_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
lean_ctor_set(v___x_1265_, 2, v___x_1234_);
lean_ctor_set(v___x_1265_, 3, v___x_1197_);
lean_ctor_set_uint8(v___x_1265_, sizeof(void*)*4, v___x_1213_);
v___x_1266_ = lean_st_mk_ref(v___x_1265_);
v___x_1267_ = lean_st_ref_take(v___x_1266_);
v_typeAnalysis_1268_ = lean_ctor_get(v___x_1267_, 1);
v_target_1269_ = lean_ctor_get(v___x_1267_, 2);
v_hypotheses_1270_ = lean_ctor_get(v___x_1267_, 3);
v_didChange_1271_ = lean_ctor_get_uint8(v___x_1267_, sizeof(void*)*4);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v___x_1267_, 0);
lean_dec(v_unused_1321_);
v___x_1273_ = v___x_1267_;
v_isShared_1274_ = v_isSharedCheck_1320_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_hypotheses_1270_);
lean_inc(v_target_1269_);
lean_inc(v_typeAnalysis_1268_);
lean_dec(v___x_1267_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1320_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_preprocessCaches_1253_);
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_preprocessCaches_1253_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_typeAnalysis_1268_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_target_1269_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_hypotheses_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*4, v_didChange_1271_);
v___x_1276_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; size_t v_sz_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1277_ = lean_st_ref_put(v___x_1266_, v___x_1276_);
v_sz_1278_ = lean_array_size(v_snd_1209_);
v___x_1279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(v_sz_1278_, v___x_1206_, v_snd_1209_);
v___x_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
v___x_1281_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1280_, v___x_1239_, v___x_1266_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec_ref(v___x_1239_);
lean_dec_ref_known(v___x_1280_, 1);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 1);
v___x_1283_ = lean_st_ref_get(v___x_1266_);
lean_dec(v___x_1266_);
v___x_1284_ = lean_unbox(v_a_1282_);
lean_dec(v_a_1282_);
if (v___x_1284_ == 0)
{
lean_object* v_caches_1285_; lean_object* v_hypotheses_1286_; lean_object* v___x_1287_; lean_object* v_theoryState_1288_; lean_object* v_satExpr_1289_; lean_object* v_hypQueue_1290_; lean_object* v_usedHyps_1291_; uint8_t v_didChange_1292_; lean_object* v_solverTimeBudgetMs_1293_; lean_object* v_roundBudget_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1316_; 
v_caches_1285_ = lean_ctor_get(v___x_1283_, 0);
lean_inc_ref(v_caches_1285_);
v_hypotheses_1286_ = lean_ctor_get(v___x_1283_, 3);
lean_inc_ref(v_hypotheses_1286_);
lean_dec(v___x_1283_);
v___x_1287_ = lean_st_ref_take(v_a_837_);
v_theoryState_1288_ = lean_ctor_get(v___x_1287_, 3);
v_satExpr_1289_ = lean_ctor_get(v___x_1287_, 0);
v_hypQueue_1290_ = lean_ctor_get(v___x_1287_, 1);
v_usedHyps_1291_ = lean_ctor_get(v___x_1287_, 2);
v_didChange_1292_ = lean_ctor_get_uint8(v___x_1287_, sizeof(void*)*6);
v_solverTimeBudgetMs_1293_ = lean_ctor_get(v___x_1287_, 4);
v_roundBudget_1294_ = lean_ctor_get(v___x_1287_, 5);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1296_ = v___x_1287_;
v_isShared_1297_ = v_isSharedCheck_1316_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_roundBudget_1294_);
lean_inc(v_solverTimeBudgetMs_1293_);
lean_inc(v_theoryState_1288_);
lean_inc(v_usedHyps_1291_);
lean_inc(v_hypQueue_1290_);
lean_inc(v_satExpr_1289_);
lean_dec(v___x_1287_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1316_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_funState_1298_; lean_object* v_bitvecState_1299_; lean_object* v_satSolver_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1314_; 
v_funState_1298_ = lean_ctor_get(v_theoryState_1288_, 0);
v_bitvecState_1299_ = lean_ctor_get(v_theoryState_1288_, 1);
v_satSolver_1300_ = lean_ctor_get(v_theoryState_1288_, 3);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_theoryState_1288_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v_theoryState_1288_, 2);
lean_dec(v_unused_1315_);
v___x_1302_ = v_theoryState_1288_;
v_isShared_1303_ = v_isSharedCheck_1314_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_satSolver_1300_);
lean_inc(v_bitvecState_1299_);
lean_inc(v_funState_1298_);
lean_dec(v_theoryState_1288_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1314_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 2, v_caches_1285_);
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_funState_1298_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_bitvecState_1299_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_caches_1285_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_satSolver_1300_);
v___x_1305_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1307_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 3, v___x_1305_);
v___x_1307_ = v___x_1296_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_satExpr_1289_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_hypQueue_1290_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_usedHyps_1291_);
lean_ctor_set(v_reuseFailAlloc_1312_, 3, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1312_, 4, v_solverTimeBudgetMs_1293_);
lean_ctor_set(v_reuseFailAlloc_1312_, 5, v_roundBudget_1294_);
lean_ctor_set_uint8(v_reuseFailAlloc_1312_, sizeof(void*)*6, v_didChange_1292_);
v___x_1307_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1308_ = lean_st_ref_put(v_a_837_, v___x_1307_);
v___x_1309_ = l_Array_append___redArg(v___x_1211_, v_hypotheses_1286_);
lean_dec_ref(v_hypotheses_1286_);
v___x_1310_ = lean_box(0);
v___x_1311_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(v___x_1310_, v___x_1309_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec_ref(v___x_1309_);
v___y_1140_ = v___x_1184_;
v___y_1141_ = v_a_1178_;
v___y_1142_ = v___x_1311_;
goto v___jp_1139_;
}
}
}
}
}
else
{
uint8_t v___x_1317_; 
lean_dec(v___x_1283_);
lean_dec_ref(v___x_1211_);
v___x_1317_ = 0;
v___y_1134_ = v___x_1184_;
v___y_1135_ = v_a_1178_;
v_a_1136_ = v___x_1317_;
goto v___jp_1133_;
}
}
else
{
lean_object* v_a_1318_; 
lean_dec(v___x_1266_);
lean_dec_ref(v___x_1211_);
v_a_1318_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1281_, 1);
v___y_1129_ = v___x_1184_;
v___y_1130_ = v_a_1178_;
v_a_1131_ = v_a_1318_;
goto v___jp_1128_;
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
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec(v_snd_1209_);
lean_del_object(v___x_1180_);
v___x_1329_ = lean_box(0);
v___x_1330_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(v___x_1329_, v___x_1211_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec_ref(v___x_1211_);
v___y_1140_ = v___x_1184_;
v___y_1141_ = v_a_1178_;
v___y_1142_ = v___x_1330_;
goto v___jp_1139_;
}
}
else
{
uint8_t v___x_1331_; 
lean_dec_ref(v_hypQueue_1187_);
lean_del_object(v___x_1180_);
v___x_1331_ = 2;
v___y_1134_ = v___x_1184_;
v___y_1135_ = v_a_1178_;
v_a_1136_ = v___x_1331_;
goto v___jp_1133_;
}
}
}
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_satExpr_1336_; lean_object* v_hypQueue_1337_; lean_object* v_usedHyps_1338_; uint8_t v_didChange_1339_; lean_object* v_theoryState_1340_; lean_object* v_solverTimeBudgetMs_1341_; lean_object* v_roundBudget_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1483_; 
v___x_1334_ = lean_io_get_num_heartbeats();
v___x_1335_ = lean_st_ref_take(v_a_837_);
v_satExpr_1336_ = lean_ctor_get(v___x_1335_, 0);
v_hypQueue_1337_ = lean_ctor_get(v___x_1335_, 1);
v_usedHyps_1338_ = lean_ctor_get(v___x_1335_, 2);
v_didChange_1339_ = lean_ctor_get_uint8(v___x_1335_, sizeof(void*)*6);
v_theoryState_1340_ = lean_ctor_get(v___x_1335_, 3);
v_solverTimeBudgetMs_1341_ = lean_ctor_get(v___x_1335_, 4);
v_roundBudget_1342_ = lean_ctor_get(v___x_1335_, 5);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1344_ = v___x_1335_;
v_isShared_1345_ = v_isSharedCheck_1483_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_roundBudget_1342_);
lean_inc(v_solverTimeBudgetMs_1341_);
lean_inc(v_theoryState_1340_);
lean_inc(v_usedHyps_1338_);
lean_inc(v_hypQueue_1337_);
lean_inc(v_satExpr_1336_);
lean_dec(v___x_1335_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1483_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0));
v___x_1348_ = l_Array_append___redArg(v_usedHyps_1338_, v_hypQueue_1337_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 2, v___x_1348_);
lean_ctor_set(v___x_1344_, 1, v___x_1347_);
v___x_1350_ = v___x_1344_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_satExpr_1336_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_theoryState_1340_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_solverTimeBudgetMs_1341_);
lean_ctor_set(v_reuseFailAlloc_1482_, 5, v_roundBudget_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1482_, sizeof(void*)*6, v_didChange_1339_);
v___x_1350_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1351_ = lean_st_ref_put(v_a_837_, v___x_1350_);
v___x_1352_ = lean_array_get_size(v_hypQueue_1337_);
v___x_1353_ = lean_nat_dec_eq(v___x_1352_, v___x_1346_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; size_t v_sz_1355_; size_t v___x_1356_; lean_object* v___x_1357_; lean_object* v_fst_1358_; lean_object* v_snd_1359_; size_t v_sz_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1354_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1));
v_sz_1355_ = lean_array_size(v_hypQueue_1337_);
v___x_1356_ = ((size_t)0ULL);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(v_hypQueue_1337_, v_sz_1355_, v___x_1356_, v___x_1354_);
lean_dec_ref(v_hypQueue_1337_);
v_fst_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_fst_1358_);
v_snd_1359_ = lean_ctor_get(v___x_1357_, 1);
lean_inc(v_snd_1359_);
lean_dec_ref(v___x_1357_);
v_sz_1360_ = lean_array_size(v_fst_1358_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(v_sz_1360_, v___x_1356_, v_fst_1358_);
v___x_1362_ = lean_array_get_size(v_snd_1359_);
v___x_1363_ = lean_nat_dec_eq(v___x_1362_, v___x_1346_);
if (v___x_1363_ == 0)
{
lean_object* v_goal_1364_; lean_object* v_tacticContext_1365_; lean_object* v___x_1366_; lean_object* v_config_1367_; lean_object* v_mode_1368_; lean_object* v_timeout_1369_; uint8_t v_trimProofs_1370_; uint8_t v_binaryProofs_1371_; uint8_t v_acNf_1372_; uint8_t v_andFlattening_1373_; uint8_t v_embeddedConstraintSubst_1374_; uint8_t v_graphviz_1375_; lean_object* v_maxSteps_1376_; uint8_t v_solverMode_1377_; uint8_t v_uf_1378_; lean_object* v_cegarRounds_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1478_; 
v_goal_1364_ = lean_ctor_get(v_a_836_, 0);
v_tacticContext_1365_ = lean_ctor_get(v_a_836_, 2);
lean_inc_ref(v_tacticContext_1365_);
v___x_1366_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1365_);
v_config_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc_ref(v_config_1367_);
v_mode_1368_ = lean_ctor_get(v___x_1366_, 1);
lean_inc(v_mode_1368_);
lean_dec_ref(v___x_1366_);
v_timeout_1369_ = lean_ctor_get(v_config_1367_, 0);
v_trimProofs_1370_ = lean_ctor_get_uint8(v_config_1367_, sizeof(void*)*3);
v_binaryProofs_1371_ = lean_ctor_get_uint8(v_config_1367_, sizeof(void*)*3 + 1);
v_acNf_1372_ = lean_ctor_get_uint8(v_config_1367_, sizeof(void*)*3 + 2);
v_andFlattening_1373_ = lean_ctor_get_uint8(v_config_1367_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1374_ = lean_ctor_get_uint8(v_config_1367_, sizeof(void*)*3 + 4);
v_graphviz_1375_ = lean_ctor_get_uint8(v_config_1367_, sizeof(void*)*3 + 8);
v_maxSteps_1376_ = lean_ctor_get(v_config_1367_, 1);
v_solverMode_1377_ = lean_ctor_get_uint8(v_config_1367_, sizeof(void*)*3 + 10);
v_uf_1378_ = lean_ctor_get_uint8(v_config_1367_, sizeof(void*)*3 + 11);
v_cegarRounds_1379_ = lean_ctor_get(v_config_1367_, 2);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_config_1367_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1381_ = v_config_1367_;
v_isShared_1382_ = v_isSharedCheck_1478_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_cegarRounds_1379_);
lean_inc(v_maxSteps_1376_);
lean_inc(v_timeout_1369_);
lean_dec(v_config_1367_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1478_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
lean_inc(v_goal_1364_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v_goal_1364_);
v___x_1384_ = v___x_1180_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_goal_1364_);
v___x_1384_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1386_; 
if (v_isShared_1382_ == 0)
{
v___x_1386_ = v___x_1381_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_timeout_1369_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_maxSteps_1376_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_cegarRounds_1379_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*3, v_trimProofs_1370_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*3 + 1, v_binaryProofs_1371_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*3 + 2, v_acNf_1372_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*3 + 3, v_andFlattening_1373_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1374_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*3 + 8, v_graphviz_1375_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*3 + 10, v_solverMode_1377_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*3 + 11, v_uf_1378_);
v___x_1386_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v_theoryState_1391_; lean_object* v_satExpr_1392_; lean_object* v_hypQueue_1393_; lean_object* v_usedHyps_1394_; uint8_t v_didChange_1395_; lean_object* v_solverTimeBudgetMs_1396_; lean_object* v_roundBudget_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1475_; 
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*3 + 5, v___x_1363_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*3 + 6, v___x_1363_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*3 + 7, v___x_1363_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*3 + 9, v___x_1363_);
v___x_1387_ = lean_box(v___x_1183_);
v___x_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
v___x_1389_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1368_, v___x_1386_, v___x_1388_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = lean_st_ref_take(v_a_837_);
v_theoryState_1391_ = lean_ctor_get(v___x_1390_, 3);
v_satExpr_1392_ = lean_ctor_get(v___x_1390_, 0);
v_hypQueue_1393_ = lean_ctor_get(v___x_1390_, 1);
v_usedHyps_1394_ = lean_ctor_get(v___x_1390_, 2);
v_didChange_1395_ = lean_ctor_get_uint8(v___x_1390_, sizeof(void*)*6);
v_solverTimeBudgetMs_1396_ = lean_ctor_get(v___x_1390_, 4);
v_roundBudget_1397_ = lean_ctor_get(v___x_1390_, 5);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1399_ = v___x_1390_;
v_isShared_1400_ = v_isSharedCheck_1475_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_roundBudget_1397_);
lean_inc(v_solverTimeBudgetMs_1396_);
lean_inc(v_theoryState_1391_);
lean_inc(v_usedHyps_1394_);
lean_inc(v_hypQueue_1393_);
lean_inc(v_satExpr_1392_);
lean_dec(v___x_1390_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1475_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_funState_1401_; lean_object* v_bitvecState_1402_; lean_object* v_preprocessCaches_1403_; lean_object* v_satSolver_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1474_; 
v_funState_1401_ = lean_ctor_get(v_theoryState_1391_, 0);
v_bitvecState_1402_ = lean_ctor_get(v_theoryState_1391_, 1);
v_preprocessCaches_1403_ = lean_ctor_get(v_theoryState_1391_, 2);
v_satSolver_1404_ = lean_ctor_get(v_theoryState_1391_, 3);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_theoryState_1391_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1406_ = v_theoryState_1391_;
v_isShared_1407_ = v_isSharedCheck_1474_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_satSolver_1404_);
lean_inc(v_preprocessCaches_1403_);
lean_inc(v_bitvecState_1402_);
lean_inc(v_funState_1401_);
lean_dec(v_theoryState_1391_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1474_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 2, v___x_1408_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_funState_1401_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_bitvecState_1402_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1473_, 3, v_satSolver_1404_);
v___x_1410_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 3, v___x_1410_);
v___x_1412_ = v___x_1399_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_satExpr_1392_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_hypQueue_1393_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_usedHyps_1394_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v_solverTimeBudgetMs_1396_);
lean_ctor_set(v_reuseFailAlloc_1472_, 5, v_roundBudget_1397_);
lean_ctor_set_uint8(v_reuseFailAlloc_1472_, sizeof(void*)*6, v_didChange_1395_);
v___x_1412_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v_typeAnalysis_1418_; lean_object* v_target_1419_; lean_object* v_hypotheses_1420_; uint8_t v_didChange_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1470_; 
v___x_1413_ = lean_st_ref_put(v_a_837_, v___x_1412_);
v___x_1414_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8);
v___x_1415_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1415_, 0, v___x_1408_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
lean_ctor_set(v___x_1415_, 2, v___x_1384_);
lean_ctor_set(v___x_1415_, 3, v___x_1347_);
lean_ctor_set_uint8(v___x_1415_, sizeof(void*)*4, v___x_1363_);
v___x_1416_ = lean_st_mk_ref(v___x_1415_);
v___x_1417_ = lean_st_ref_take(v___x_1416_);
v_typeAnalysis_1418_ = lean_ctor_get(v___x_1417_, 1);
v_target_1419_ = lean_ctor_get(v___x_1417_, 2);
v_hypotheses_1420_ = lean_ctor_get(v___x_1417_, 3);
v_didChange_1421_ = lean_ctor_get_uint8(v___x_1417_, sizeof(void*)*4);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1417_, 0);
lean_dec(v_unused_1471_);
v___x_1423_ = v___x_1417_;
v_isShared_1424_ = v_isSharedCheck_1470_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_hypotheses_1420_);
lean_inc(v_target_1419_);
lean_inc(v_typeAnalysis_1418_);
lean_dec(v___x_1417_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1470_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v_preprocessCaches_1403_);
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_preprocessCaches_1403_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_typeAnalysis_1418_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_target_1419_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_hypotheses_1420_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*4, v_didChange_1421_);
v___x_1426_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; size_t v_sz_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1427_ = lean_st_ref_put(v___x_1416_, v___x_1426_);
v_sz_1428_ = lean_array_size(v_snd_1359_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(v_sz_1428_, v___x_1356_, v_snd_1359_);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
v___x_1431_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1430_, v___x_1389_, v___x_1416_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec_ref(v___x_1389_);
lean_dec_ref_known(v___x_1430_, 1);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = lean_st_ref_get(v___x_1416_);
lean_dec(v___x_1416_);
v___x_1434_ = lean_unbox(v_a_1432_);
lean_dec(v_a_1432_);
if (v___x_1434_ == 0)
{
lean_object* v_caches_1435_; lean_object* v_hypotheses_1436_; lean_object* v___x_1437_; lean_object* v_theoryState_1438_; lean_object* v_satExpr_1439_; lean_object* v_hypQueue_1440_; lean_object* v_usedHyps_1441_; uint8_t v_didChange_1442_; lean_object* v_solverTimeBudgetMs_1443_; lean_object* v_roundBudget_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1466_; 
v_caches_1435_ = lean_ctor_get(v___x_1433_, 0);
lean_inc_ref(v_caches_1435_);
v_hypotheses_1436_ = lean_ctor_get(v___x_1433_, 3);
lean_inc_ref(v_hypotheses_1436_);
lean_dec(v___x_1433_);
v___x_1437_ = lean_st_ref_take(v_a_837_);
v_theoryState_1438_ = lean_ctor_get(v___x_1437_, 3);
v_satExpr_1439_ = lean_ctor_get(v___x_1437_, 0);
v_hypQueue_1440_ = lean_ctor_get(v___x_1437_, 1);
v_usedHyps_1441_ = lean_ctor_get(v___x_1437_, 2);
v_didChange_1442_ = lean_ctor_get_uint8(v___x_1437_, sizeof(void*)*6);
v_solverTimeBudgetMs_1443_ = lean_ctor_get(v___x_1437_, 4);
v_roundBudget_1444_ = lean_ctor_get(v___x_1437_, 5);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1446_ = v___x_1437_;
v_isShared_1447_ = v_isSharedCheck_1466_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_roundBudget_1444_);
lean_inc(v_solverTimeBudgetMs_1443_);
lean_inc(v_theoryState_1438_);
lean_inc(v_usedHyps_1441_);
lean_inc(v_hypQueue_1440_);
lean_inc(v_satExpr_1439_);
lean_dec(v___x_1437_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1466_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v_funState_1448_; lean_object* v_bitvecState_1449_; lean_object* v_satSolver_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1464_; 
v_funState_1448_ = lean_ctor_get(v_theoryState_1438_, 0);
v_bitvecState_1449_ = lean_ctor_get(v_theoryState_1438_, 1);
v_satSolver_1450_ = lean_ctor_get(v_theoryState_1438_, 3);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_theoryState_1438_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v_theoryState_1438_, 2);
lean_dec(v_unused_1465_);
v___x_1452_ = v_theoryState_1438_;
v_isShared_1453_ = v_isSharedCheck_1464_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_satSolver_1450_);
lean_inc(v_bitvecState_1449_);
lean_inc(v_funState_1448_);
lean_dec(v_theoryState_1438_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1464_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 2, v_caches_1435_);
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_funState_1448_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_bitvecState_1449_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_caches_1435_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v_satSolver_1450_);
v___x_1455_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 3, v___x_1455_);
v___x_1457_ = v___x_1446_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_satExpr_1439_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_hypQueue_1440_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_usedHyps_1441_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_solverTimeBudgetMs_1443_);
lean_ctor_set(v_reuseFailAlloc_1462_, 5, v_roundBudget_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1462_, sizeof(void*)*6, v_didChange_1442_);
v___x_1457_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1458_ = lean_st_ref_put(v_a_837_, v___x_1457_);
v___x_1459_ = l_Array_append___redArg(v___x_1361_, v_hypotheses_1436_);
lean_dec_ref(v_hypotheses_1436_);
v___x_1460_ = lean_box(0);
v___x_1461_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(v___x_1460_, v___x_1459_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec_ref(v___x_1459_);
v___y_1170_ = v___x_1334_;
v___y_1171_ = v_a_1178_;
v___y_1172_ = v___x_1461_;
goto v___jp_1169_;
}
}
}
}
}
else
{
uint8_t v___x_1467_; 
lean_dec(v___x_1433_);
lean_dec_ref(v___x_1361_);
v___x_1467_ = 0;
v___y_1164_ = v___x_1334_;
v___y_1165_ = v_a_1178_;
v_a_1166_ = v___x_1467_;
goto v___jp_1163_;
}
}
else
{
lean_object* v_a_1468_; 
lean_dec(v___x_1416_);
lean_dec_ref(v___x_1361_);
v_a_1468_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___x_1431_, 1);
v___y_1159_ = v___x_1334_;
v___y_1160_ = v_a_1178_;
v_a_1161_ = v_a_1468_;
goto v___jp_1158_;
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
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec(v_snd_1359_);
lean_del_object(v___x_1180_);
v___x_1479_ = lean_box(0);
v___x_1480_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(v___x_1479_, v___x_1361_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec_ref(v___x_1361_);
v___y_1170_ = v___x_1334_;
v___y_1171_ = v_a_1178_;
v___y_1172_ = v___x_1480_;
goto v___jp_1169_;
}
}
else
{
uint8_t v___x_1481_; 
lean_dec_ref(v_hypQueue_1337_);
lean_del_object(v___x_1180_);
v___x_1481_ = 2;
v___y_1164_ = v___x_1334_;
v___y_1165_ = v_a_1178_;
v_a_1166_ = v___x_1481_;
goto v___jp_1163_;
}
}
}
}
}
}
}
v___jp_851_:
{
lean_object* v___x_854_; lean_object* v_hypQueue_855_; lean_object* v_usedHyps_856_; uint8_t v_didChange_857_; lean_object* v_theoryState_858_; lean_object* v_solverTimeBudgetMs_859_; lean_object* v_roundBudget_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_871_; 
v___x_854_ = lean_st_ref_take(v___y_852_);
v_hypQueue_855_ = lean_ctor_get(v___x_854_, 1);
v_usedHyps_856_ = lean_ctor_get(v___x_854_, 2);
v_didChange_857_ = lean_ctor_get_uint8(v___x_854_, sizeof(void*)*6);
v_theoryState_858_ = lean_ctor_get(v___x_854_, 3);
v_solverTimeBudgetMs_859_ = lean_ctor_get(v___x_854_, 4);
v_roundBudget_860_ = lean_ctor_get(v___x_854_, 5);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_854_, 0);
lean_dec(v_unused_872_);
v___x_862_ = v___x_854_;
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_roundBudget_860_);
lean_inc(v_solverTimeBudgetMs_859_);
lean_inc(v_theoryState_858_);
lean_inc(v_usedHyps_856_);
lean_inc(v_hypQueue_855_);
lean_dec(v___x_854_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v_a_853_);
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_853_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_hypQueue_855_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_usedHyps_856_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_theoryState_858_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_solverTimeBudgetMs_859_);
lean_ctor_set(v_reuseFailAlloc_870_, 5, v_roundBudget_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_870_, sizeof(void*)*6, v_didChange_857_);
v___x_865_ = v_reuseFailAlloc_870_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_866_ = lean_st_ref_put(v___y_852_, v___x_865_);
v___x_867_ = 1;
v___x_868_ = lean_box(v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
}
v___jp_873_:
{
lean_object* v___x_889_; lean_object* v_sats_890_; size_t v_sz_891_; size_t v___x_892_; lean_object* v___x_893_; 
v___x_889_ = lean_unsigned_to_nat(0u);
v_sats_890_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__0));
v_sz_891_ = lean_array_size(v_hypQueue_874_);
v___x_892_ = ((size_t)0ULL);
v___x_893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_hypQueue_874_, v_sz_891_, v___x_892_, v_sats_890_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec_ref(v_hypQueue_874_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_919_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_919_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_919_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_919_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_array_get_size(v_a_894_);
v___x_899_ = lean_nat_dec_eq(v___x_898_, v___x_889_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v_satExpr_901_; uint8_t v___x_902_; 
lean_del_object(v___x_896_);
v___x_900_ = lean_st_ref_get(v___y_876_);
v_satExpr_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc_ref(v_satExpr_901_);
lean_dec(v___x_900_);
v___x_902_ = lean_nat_dec_lt(v___x_889_, v___x_898_);
if (v___x_902_ == 0)
{
lean_dec(v_a_894_);
v___y_852_ = v___y_876_;
v_a_853_ = v_satExpr_901_;
goto v___jp_851_;
}
else
{
size_t v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_usize_of_nat(v___x_898_);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___redArg(v_a_894_, v___x_892_, v___x_903_, v_satExpr_901_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v_a_894_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___y_852_ = v___y_876_;
v_a_853_ = v_a_905_;
goto v___jp_851_;
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
v_a_906_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_904_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
else
{
uint8_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
lean_dec(v_a_894_);
v___x_914_ = 2;
v___x_915_ = lean_box(v___x_914_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_915_);
v___x_917_ = v___x_896_;
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
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_a_920_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_893_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_893_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
v___jp_928_:
{
lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_944_ = lean_array_get_size(v_hypQueue_929_);
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_nat_dec_eq(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v_bs_947_; lean_object* v___x_948_; size_t v_sz_949_; size_t v___x_950_; lean_object* v___x_951_; lean_object* v_fst_952_; lean_object* v_snd_953_; size_t v_sz_954_; lean_object* v_hypQueue_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_bs_947_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0));
v___x_948_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1));
v_sz_949_ = lean_array_size(v_hypQueue_929_);
v___x_950_ = ((size_t)0ULL);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(v_hypQueue_929_, v_sz_949_, v___x_950_, v___x_948_);
lean_dec_ref(v_hypQueue_929_);
v_fst_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_fst_952_);
v_snd_953_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_snd_953_);
lean_dec_ref(v___x_951_);
v_sz_954_ = lean_array_size(v_fst_952_);
v_hypQueue_955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(v_sz_954_, v___x_950_, v_fst_952_);
v___x_956_ = lean_array_get_size(v_snd_953_);
v___x_957_ = lean_nat_dec_eq(v___x_956_, v___x_945_);
if (v___x_957_ == 0)
{
lean_object* v_goal_958_; lean_object* v_tacticContext_959_; lean_object* v___x_960_; lean_object* v_config_961_; lean_object* v_mode_962_; lean_object* v_timeout_963_; uint8_t v_trimProofs_964_; uint8_t v_binaryProofs_965_; uint8_t v_acNf_966_; uint8_t v_andFlattening_967_; uint8_t v_embeddedConstraintSubst_968_; uint8_t v_graphviz_969_; lean_object* v_maxSteps_970_; uint8_t v_solverMode_971_; uint8_t v_uf_972_; lean_object* v_cegarRounds_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1082_; 
v_goal_958_ = lean_ctor_get(v___y_930_, 0);
v_tacticContext_959_ = lean_ctor_get(v___y_930_, 2);
lean_inc_ref(v_tacticContext_959_);
v___x_960_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_959_);
v_config_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc_ref(v_config_961_);
v_mode_962_ = lean_ctor_get(v___x_960_, 1);
lean_inc(v_mode_962_);
lean_dec_ref(v___x_960_);
v_timeout_963_ = lean_ctor_get(v_config_961_, 0);
v_trimProofs_964_ = lean_ctor_get_uint8(v_config_961_, sizeof(void*)*3);
v_binaryProofs_965_ = lean_ctor_get_uint8(v_config_961_, sizeof(void*)*3 + 1);
v_acNf_966_ = lean_ctor_get_uint8(v_config_961_, sizeof(void*)*3 + 2);
v_andFlattening_967_ = lean_ctor_get_uint8(v_config_961_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_968_ = lean_ctor_get_uint8(v_config_961_, sizeof(void*)*3 + 4);
v_graphviz_969_ = lean_ctor_get_uint8(v_config_961_, sizeof(void*)*3 + 8);
v_maxSteps_970_ = lean_ctor_get(v_config_961_, 1);
v_solverMode_971_ = lean_ctor_get_uint8(v_config_961_, sizeof(void*)*3 + 10);
v_uf_972_ = lean_ctor_get_uint8(v_config_961_, sizeof(void*)*3 + 11);
v_cegarRounds_973_ = lean_ctor_get(v_config_961_, 2);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_config_961_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_975_ = v_config_961_;
v_isShared_976_ = v_isSharedCheck_1082_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_cegarRounds_973_);
lean_inc(v_maxSteps_970_);
lean_inc(v_timeout_963_);
lean_dec(v_config_961_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1082_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
lean_inc(v_goal_958_);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v_goal_958_);
if (v_isShared_976_ == 0)
{
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_timeout_963_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_maxSteps_970_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_cegarRounds_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3, v_trimProofs_964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3 + 1, v_binaryProofs_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3 + 2, v_acNf_966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3 + 3, v_andFlattening_967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3 + 8, v_graphviz_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3 + 10, v_solverMode_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1081_, sizeof(void*)*3 + 11, v_uf_972_);
v___x_979_ = v_reuseFailAlloc_1081_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_theoryState_983_; lean_object* v_satExpr_984_; lean_object* v_hypQueue_985_; lean_object* v_usedHyps_986_; uint8_t v_didChange_987_; lean_object* v_solverTimeBudgetMs_988_; lean_object* v_roundBudget_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1080_; 
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*3 + 5, v___x_957_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*3 + 6, v___x_957_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*3 + 7, v___x_957_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*3 + 9, v___x_957_);
v___x_980_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2));
v___x_981_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_962_, v___x_979_, v___x_980_);
v___x_982_ = lean_st_ref_take(v___y_931_);
v_theoryState_983_ = lean_ctor_get(v___x_982_, 3);
v_satExpr_984_ = lean_ctor_get(v___x_982_, 0);
v_hypQueue_985_ = lean_ctor_get(v___x_982_, 1);
v_usedHyps_986_ = lean_ctor_get(v___x_982_, 2);
v_didChange_987_ = lean_ctor_get_uint8(v___x_982_, sizeof(void*)*6);
v_solverTimeBudgetMs_988_ = lean_ctor_get(v___x_982_, 4);
v_roundBudget_989_ = lean_ctor_get(v___x_982_, 5);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_991_ = v___x_982_;
v_isShared_992_ = v_isSharedCheck_1080_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_roundBudget_989_);
lean_inc(v_solverTimeBudgetMs_988_);
lean_inc(v_theoryState_983_);
lean_inc(v_usedHyps_986_);
lean_inc(v_hypQueue_985_);
lean_inc(v_satExpr_984_);
lean_dec(v___x_982_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1080_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_funState_993_; lean_object* v_bitvecState_994_; lean_object* v_preprocessCaches_995_; lean_object* v_satSolver_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1079_; 
v_funState_993_ = lean_ctor_get(v_theoryState_983_, 0);
v_bitvecState_994_ = lean_ctor_get(v_theoryState_983_, 1);
v_preprocessCaches_995_ = lean_ctor_get(v_theoryState_983_, 2);
v_satSolver_996_ = lean_ctor_get(v_theoryState_983_, 3);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_theoryState_983_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_998_ = v_theoryState_983_;
v_isShared_999_ = v_isSharedCheck_1079_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_satSolver_996_);
lean_inc(v_preprocessCaches_995_);
lean_inc(v_bitvecState_994_);
lean_inc(v_funState_993_);
lean_dec(v_theoryState_983_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1079_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 2, v___x_1000_);
v___x_1002_ = v___x_998_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_funState_993_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_bitvecState_994_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_satSolver_996_);
v___x_1002_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 3, v___x_1002_);
v___x_1004_ = v___x_991_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_satExpr_984_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_hypQueue_985_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_usedHyps_986_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v_solverTimeBudgetMs_988_);
lean_ctor_set(v_reuseFailAlloc_1077_, 5, v_roundBudget_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_1077_, sizeof(void*)*6, v_didChange_987_);
v___x_1004_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_typeAnalysis_1010_; lean_object* v_target_1011_; lean_object* v_hypotheses_1012_; uint8_t v_didChange_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1075_; 
v___x_1005_ = lean_st_ref_put(v___y_931_, v___x_1004_);
v___x_1006_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8);
v___x_1007_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1007_, 0, v___x_1000_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
lean_ctor_set(v___x_1007_, 2, v___x_977_);
lean_ctor_set(v___x_1007_, 3, v_bs_947_);
lean_ctor_set_uint8(v___x_1007_, sizeof(void*)*4, v___x_957_);
v___x_1008_ = lean_st_mk_ref(v___x_1007_);
v___x_1009_ = lean_st_ref_take(v___x_1008_);
v_typeAnalysis_1010_ = lean_ctor_get(v___x_1009_, 1);
v_target_1011_ = lean_ctor_get(v___x_1009_, 2);
v_hypotheses_1012_ = lean_ctor_get(v___x_1009_, 3);
v_didChange_1013_ = lean_ctor_get_uint8(v___x_1009_, sizeof(void*)*4);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v___x_1009_, 0);
lean_dec(v_unused_1076_);
v___x_1015_ = v___x_1009_;
v_isShared_1016_ = v_isSharedCheck_1075_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_hypotheses_1012_);
lean_inc(v_target_1011_);
lean_inc(v_typeAnalysis_1010_);
lean_dec(v___x_1009_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1075_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v_preprocessCaches_995_);
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_preprocessCaches_995_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_typeAnalysis_1010_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_target_1011_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v_hypotheses_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1074_, sizeof(void*)*4, v_didChange_1013_);
v___x_1018_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; size_t v_sz_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1019_ = lean_st_ref_put(v___x_1008_, v___x_1018_);
v_sz_1020_ = lean_array_size(v_snd_953_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(v_sz_1020_, v___x_950_, v_snd_953_);
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
v___x_1023_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1022_, v___x_981_, v___x_1008_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec_ref(v___x_981_);
lean_dec_ref_known(v___x_1022_, 1);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1065_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1065_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1065_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_st_ref_get(v___x_1008_);
lean_dec(v___x_1008_);
v___x_1029_ = lean_unbox(v_a_1024_);
lean_dec(v_a_1024_);
if (v___x_1029_ == 0)
{
lean_object* v_caches_1030_; lean_object* v_hypotheses_1031_; lean_object* v___x_1032_; lean_object* v_theoryState_1033_; lean_object* v_satExpr_1034_; lean_object* v_hypQueue_1035_; lean_object* v_usedHyps_1036_; uint8_t v_didChange_1037_; lean_object* v_solverTimeBudgetMs_1038_; lean_object* v_roundBudget_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1059_; 
lean_del_object(v___x_1026_);
v_caches_1030_ = lean_ctor_get(v___x_1028_, 0);
lean_inc_ref(v_caches_1030_);
v_hypotheses_1031_ = lean_ctor_get(v___x_1028_, 3);
lean_inc_ref(v_hypotheses_1031_);
lean_dec(v___x_1028_);
v___x_1032_ = lean_st_ref_take(v___y_931_);
v_theoryState_1033_ = lean_ctor_get(v___x_1032_, 3);
v_satExpr_1034_ = lean_ctor_get(v___x_1032_, 0);
v_hypQueue_1035_ = lean_ctor_get(v___x_1032_, 1);
v_usedHyps_1036_ = lean_ctor_get(v___x_1032_, 2);
v_didChange_1037_ = lean_ctor_get_uint8(v___x_1032_, sizeof(void*)*6);
v_solverTimeBudgetMs_1038_ = lean_ctor_get(v___x_1032_, 4);
v_roundBudget_1039_ = lean_ctor_get(v___x_1032_, 5);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1041_ = v___x_1032_;
v_isShared_1042_ = v_isSharedCheck_1059_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_roundBudget_1039_);
lean_inc(v_solverTimeBudgetMs_1038_);
lean_inc(v_theoryState_1033_);
lean_inc(v_usedHyps_1036_);
lean_inc(v_hypQueue_1035_);
lean_inc(v_satExpr_1034_);
lean_dec(v___x_1032_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1059_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_funState_1043_; lean_object* v_bitvecState_1044_; lean_object* v_satSolver_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1057_; 
v_funState_1043_ = lean_ctor_get(v_theoryState_1033_, 0);
v_bitvecState_1044_ = lean_ctor_get(v_theoryState_1033_, 1);
v_satSolver_1045_ = lean_ctor_get(v_theoryState_1033_, 3);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_theoryState_1033_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v_theoryState_1033_, 2);
lean_dec(v_unused_1058_);
v___x_1047_ = v_theoryState_1033_;
v_isShared_1048_ = v_isSharedCheck_1057_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_satSolver_1045_);
lean_inc(v_bitvecState_1044_);
lean_inc(v_funState_1043_);
lean_dec(v_theoryState_1033_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1057_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 2, v_caches_1030_);
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_funState_1043_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_bitvecState_1044_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_caches_1030_);
lean_ctor_set(v_reuseFailAlloc_1056_, 3, v_satSolver_1045_);
v___x_1050_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1052_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 3, v___x_1050_);
v___x_1052_ = v___x_1041_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_satExpr_1034_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_hypQueue_1035_);
lean_ctor_set(v_reuseFailAlloc_1055_, 2, v_usedHyps_1036_);
lean_ctor_set(v_reuseFailAlloc_1055_, 3, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1055_, 4, v_solverTimeBudgetMs_1038_);
lean_ctor_set(v_reuseFailAlloc_1055_, 5, v_roundBudget_1039_);
lean_ctor_set_uint8(v_reuseFailAlloc_1055_, sizeof(void*)*6, v_didChange_1037_);
v___x_1052_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = lean_st_ref_put(v___y_931_, v___x_1052_);
v___x_1054_ = l_Array_append___redArg(v_hypQueue_955_, v_hypotheses_1031_);
lean_dec_ref(v_hypotheses_1031_);
v_hypQueue_874_ = v___x_1054_;
v___y_875_ = v___y_930_;
v___y_876_ = v___y_931_;
v___y_877_ = v___y_932_;
v___y_878_ = v___y_933_;
v___y_879_ = v___y_934_;
v___y_880_ = v___y_935_;
v___y_881_ = v___y_936_;
v___y_882_ = v___y_937_;
v___y_883_ = v___y_938_;
v___y_884_ = v___y_939_;
v___y_885_ = v___y_940_;
v___y_886_ = v___y_941_;
v___y_887_ = v___y_942_;
v___y_888_ = v___y_943_;
goto v___jp_873_;
}
}
}
}
}
else
{
uint8_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_dec(v___x_1028_);
lean_dec_ref(v_hypQueue_955_);
v___x_1060_ = 0;
v___x_1061_ = lean_box(v___x_1060_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1061_);
v___x_1063_ = v___x_1026_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v___x_1008_);
lean_dec_ref(v_hypQueue_955_);
v_a_1066_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1023_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1023_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
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
}
}
else
{
lean_dec(v_snd_953_);
v_hypQueue_874_ = v_hypQueue_955_;
v___y_875_ = v___y_930_;
v___y_876_ = v___y_931_;
v___y_877_ = v___y_932_;
v___y_878_ = v___y_933_;
v___y_879_ = v___y_934_;
v___y_880_ = v___y_935_;
v___y_881_ = v___y_936_;
v___y_882_ = v___y_937_;
v___y_883_ = v___y_938_;
v___y_884_ = v___y_939_;
v___y_885_ = v___y_940_;
v___y_886_ = v___y_941_;
v___y_887_ = v___y_942_;
v___y_888_ = v___y_943_;
goto v___jp_873_;
}
}
else
{
uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec_ref(v_hypQueue_929_);
v___x_1083_ = 2;
v___x_1084_ = lean_box(v___x_1083_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___boxed(lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(lean_object* v_00_u03b1_1521_, lean_object* v_msg_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_1522_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_1539_ = _args[0];
lean_object* v_msg_1540_ = _args[1];
lean_object* v___y_1541_ = _args[2];
lean_object* v___y_1542_ = _args[3];
lean_object* v___y_1543_ = _args[4];
lean_object* v___y_1544_ = _args[5];
lean_object* v___y_1545_ = _args[6];
lean_object* v___y_1546_ = _args[7];
lean_object* v___y_1547_ = _args[8];
lean_object* v___y_1548_ = _args[9];
lean_object* v___y_1549_ = _args[10];
lean_object* v___y_1550_ = _args[11];
lean_object* v___y_1551_ = _args[12];
lean_object* v___y_1552_ = _args[13];
lean_object* v___y_1553_ = _args[14];
lean_object* v___y_1554_ = _args[15];
lean_object* v___y_1555_ = _args[16];
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(v_00_u03b1_1539_, v_msg_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(lean_object* v_as_1557_, size_t v_i_1558_, size_t v_stop_1559_, lean_object* v_b_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___redArg(v_as_1557_, v_i_1558_, v_stop_1559_, v_b_1560_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___boxed(lean_object** _args){
lean_object* v_as_1577_ = _args[0];
lean_object* v_i_1578_ = _args[1];
lean_object* v_stop_1579_ = _args[2];
lean_object* v_b_1580_ = _args[3];
lean_object* v___y_1581_ = _args[4];
lean_object* v___y_1582_ = _args[5];
lean_object* v___y_1583_ = _args[6];
lean_object* v___y_1584_ = _args[7];
lean_object* v___y_1585_ = _args[8];
lean_object* v___y_1586_ = _args[9];
lean_object* v___y_1587_ = _args[10];
lean_object* v___y_1588_ = _args[11];
lean_object* v___y_1589_ = _args[12];
lean_object* v___y_1590_ = _args[13];
lean_object* v___y_1591_ = _args[14];
lean_object* v___y_1592_ = _args[15];
lean_object* v___y_1593_ = _args[16];
lean_object* v___y_1594_ = _args[17];
lean_object* v___y_1595_ = _args[18];
_start:
{
size_t v_i_boxed_1596_; size_t v_stop_boxed_1597_; lean_object* v_res_1598_; 
v_i_boxed_1596_ = lean_unbox_usize(v_i_1578_);
lean_dec(v_i_1578_);
v_stop_boxed_1597_ = lean_unbox_usize(v_stop_1579_);
lean_dec(v_stop_1579_);
v_res_1598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_as_1577_, v_i_boxed_1596_, v_stop_boxed_1597_, v_b_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec_ref(v_as_1577_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9(lean_object* v_00_u03b1_1599_, lean_object* v_x_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9___redArg(v_x_1600_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9___boxed(lean_object** _args){
lean_object* v_00_u03b1_1617_ = _args[0];
lean_object* v_x_1618_ = _args[1];
lean_object* v___y_1619_ = _args[2];
lean_object* v___y_1620_ = _args[3];
lean_object* v___y_1621_ = _args[4];
lean_object* v___y_1622_ = _args[5];
lean_object* v___y_1623_ = _args[6];
lean_object* v___y_1624_ = _args[7];
lean_object* v___y_1625_ = _args[8];
lean_object* v___y_1626_ = _args[9];
lean_object* v___y_1627_ = _args[10];
lean_object* v___y_1628_ = _args[11];
lean_object* v___y_1629_ = _args[12];
lean_object* v___y_1630_ = _args[13];
lean_object* v___y_1631_ = _args[14];
lean_object* v___y_1632_ = _args[15];
lean_object* v___y_1633_ = _args[16];
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__9(v_00_u03b1_1617_, v_x_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8(lean_object* v_oldTraces_1635_, lean_object* v_data_1636_, lean_object* v_ref_1637_, lean_object* v_msg_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8___redArg(v_oldTraces_1635_, v_data_1636_, v_ref_1637_, v_msg_1638_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8___boxed(lean_object** _args){
lean_object* v_oldTraces_1655_ = _args[0];
lean_object* v_data_1656_ = _args[1];
lean_object* v_ref_1657_ = _args[2];
lean_object* v_msg_1658_ = _args[3];
lean_object* v___y_1659_ = _args[4];
lean_object* v___y_1660_ = _args[5];
lean_object* v___y_1661_ = _args[6];
lean_object* v___y_1662_ = _args[7];
lean_object* v___y_1663_ = _args[8];
lean_object* v___y_1664_ = _args[9];
lean_object* v___y_1665_ = _args[10];
lean_object* v___y_1666_ = _args[11];
lean_object* v___y_1667_ = _args[12];
lean_object* v___y_1668_ = _args[13];
lean_object* v___y_1669_ = _args[14];
lean_object* v___y_1670_ = _args[15];
lean_object* v___y_1671_ = _args[16];
lean_object* v___y_1672_ = _args[17];
lean_object* v___y_1673_ = _args[18];
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__7_spec__8(v_oldTraces_1655_, v_data_1656_, v_ref_1657_, v_msg_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1674_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Prover_Cegar_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif

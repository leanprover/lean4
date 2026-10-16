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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Processing new lemmas"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Failed to reify CEGAR lemma "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7_value;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___boxed, .m_arity = 16, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___boxed(lean_object**);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_64_ = ((size_t)5ULL);
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_unsigned_to_nat(32u);
v___x_67_ = lean_mk_empty_array_with_capacity(v___x_66_);
v___x_68_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__0);
v___x_69_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
lean_ctor_set(v___x_69_, 2, v___x_65_);
lean_ctor_set(v___x_69_, 3, v___x_65_);
lean_ctor_set_usize(v___x_69_, 4, v___x_64_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(lean_object* v___y_70_){
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
v___x_93_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___closed__1);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg___boxed(lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v___y_105_);
lean_dec(v___y_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v___y_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___boxed(lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4(v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(lean_object* v_opts_140_, lean_object* v_opt_141_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5___boxed(lean_object* v_opts_150_, lean_object* v_opt_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_150_, v_opt_151_);
lean_dec_ref(v_opt_151_);
lean_dec_ref(v_opts_150_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__0));
v___x_156_ = l_Lean_stringToMessageData(v___x_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___closed__1);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0___boxed(lean_object* v_x_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___lam__0(v_x_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec_ref(v_x_175_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_192_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
v_a_194_ = lean_ctor_get(v_x_192_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v_x_192_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v_x_192_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 1);
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_a_202_ = lean_ctor_get(v_x_192_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v_x_192_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v_x_192_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
lean_ctor_set_tag(v___x_204_, 0);
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg___boxed(lean_object* v_x_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_x_210_);
return v_res_212_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(lean_object* v_e_213_){
_start:
{
if (lean_obj_tag(v_e_213_) == 0)
{
uint8_t v___x_214_; 
v___x_214_ = 2;
return v___x_214_;
}
else
{
uint8_t v___x_215_; 
v___x_215_ = 0;
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9___boxed(lean_object* v_e_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(v_e_216_);
lean_dec_ref(v_e_216_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(lean_object* v_opts_219_, lean_object* v_opt_220_){
_start:
{
lean_object* v_name_221_; lean_object* v_defValue_222_; lean_object* v_map_223_; lean_object* v___x_224_; 
v_name_221_ = lean_ctor_get(v_opt_220_, 0);
v_defValue_222_ = lean_ctor_get(v_opt_220_, 1);
v_map_223_ = lean_ctor_get(v_opts_219_, 0);
v___x_224_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_223_, v_name_221_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_inc(v_defValue_222_);
return v_defValue_222_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_224_, 1);
if (lean_obj_tag(v_val_225_) == 3)
{
lean_object* v_v_226_; 
v_v_226_ = lean_ctor_get(v_val_225_, 0);
lean_inc(v_v_226_);
lean_dec_ref_known(v_val_225_, 1);
return v_v_226_;
}
else
{
lean_dec(v_val_225_);
lean_inc(v_defValue_222_);
return v_defValue_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10___boxed(lean_object* v_opts_227_, lean_object* v_opt_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(v_opts_227_, v_opt_228_);
lean_dec_ref(v_opt_228_);
lean_dec_ref(v_opts_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(size_t v_sz_230_, size_t v_i_231_, lean_object* v_bs_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = lean_usize_dec_lt(v_i_231_, v_sz_230_);
if (v___x_233_ == 0)
{
return v_bs_232_;
}
else
{
lean_object* v_v_234_; lean_object* v_msg_235_; lean_object* v___x_236_; lean_object* v_bs_x27_237_; size_t v___x_238_; size_t v___x_239_; lean_object* v___x_240_; 
v_v_234_ = lean_array_uget_borrowed(v_bs_232_, v_i_231_);
v_msg_235_ = lean_ctor_get(v_v_234_, 1);
lean_inc_ref(v_msg_235_);
v___x_236_ = lean_unsigned_to_nat(0u);
v_bs_x27_237_ = lean_array_uset(v_bs_232_, v_i_231_, v___x_236_);
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_add(v_i_231_, v___x_238_);
v___x_240_ = lean_array_uset(v_bs_x27_237_, v_i_231_, v_msg_235_);
v_i_231_ = v___x_239_;
v_bs_232_ = v___x_240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8___boxed(lean_object* v_sz_242_, lean_object* v_i_243_, lean_object* v_bs_244_){
_start:
{
size_t v_sz_boxed_245_; size_t v_i_boxed_246_; lean_object* v_res_247_; 
v_sz_boxed_245_ = lean_unbox_usize(v_sz_242_);
lean_dec(v_sz_242_);
v_i_boxed_246_ = lean_unbox_usize(v_i_243_);
lean_dec(v_i_243_);
v_res_247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(v_sz_boxed_245_, v_i_boxed_246_, v_bs_244_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(lean_object* v_msgData_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; lean_object* v_env_255_; uint8_t v___x_256_; lean_object* v_env_257_; lean_object* v___x_258_; lean_object* v_toCold_259_; lean_object* v_mctx_260_; lean_object* v_lctx_261_; lean_object* v_options_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_254_ = lean_st_ref_get(v___y_252_);
v_env_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc_ref(v_env_255_);
lean_dec(v___x_254_);
v___x_256_ = 0;
v_env_257_ = l_Lean_Environment_setRecordingDeps(v_env_255_, v___x_256_);
v___x_258_ = lean_st_ref_get(v___y_250_);
v_toCold_259_ = lean_ctor_get(v___y_251_, 0);
v_mctx_260_ = lean_ctor_get(v___x_258_, 0);
lean_inc_ref(v_mctx_260_);
lean_dec(v___x_258_);
v_lctx_261_ = lean_ctor_get(v___y_249_, 2);
v_options_262_ = lean_ctor_get(v_toCold_259_, 2);
lean_inc_ref(v_options_262_);
lean_inc_ref(v_lctx_261_);
v___x_263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_263_, 0, v_env_257_);
lean_ctor_set(v___x_263_, 1, v_mctx_260_);
lean_ctor_set(v___x_263_, 2, v_lctx_261_);
lean_ctor_set(v___x_263_, 3, v_options_262_);
v___x_264_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_msgData_248_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0___boxed(lean_object* v_msgData_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msgData_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(lean_object* v_oldTraces_273_, lean_object* v_data_274_, lean_object* v_ref_275_, lean_object* v_msg_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_toCold_282_; lean_object* v_currRecDepth_283_; lean_object* v_ref_284_; uint16_t v_optionFlags_285_; uint8_t v_suppressElabErrors_286_; uint8_t v_isRecordingDeps_287_; lean_object* v_ref_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_traceState_291_; lean_object* v_traces_292_; lean_object* v___x_293_; size_t v_sz_294_; size_t v___x_295_; lean_object* v___x_296_; lean_object* v_msg_297_; lean_object* v___x_298_; lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_337_; 
v_toCold_282_ = lean_ctor_get(v___y_279_, 0);
v_currRecDepth_283_ = lean_ctor_get(v___y_279_, 1);
v_ref_284_ = lean_ctor_get(v___y_279_, 2);
v_optionFlags_285_ = lean_ctor_get_uint16(v___y_279_, sizeof(void*)*3);
v_suppressElabErrors_286_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 2);
v_isRecordingDeps_287_ = lean_ctor_get_uint8(v___y_279_, sizeof(void*)*3 + 3);
v_ref_288_ = l_Lean_replaceRef(v_ref_275_, v_ref_284_);
lean_inc(v_currRecDepth_283_);
lean_inc_ref(v_toCold_282_);
v___x_289_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_289_, 0, v_toCold_282_);
lean_ctor_set(v___x_289_, 1, v_currRecDepth_283_);
lean_ctor_set(v___x_289_, 2, v_ref_288_);
lean_ctor_set_uint16(v___x_289_, sizeof(void*)*3, v_optionFlags_285_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*3 + 2, v_suppressElabErrors_286_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*3 + 3, v_isRecordingDeps_287_);
v___x_290_ = lean_st_ref_get(v___y_280_);
v_traceState_291_ = lean_ctor_get(v___x_290_, 4);
lean_inc_ref(v_traceState_291_);
lean_dec(v___x_290_);
v_traces_292_ = lean_ctor_get(v_traceState_291_, 0);
lean_inc_ref(v_traces_292_);
lean_dec_ref(v_traceState_291_);
v___x_293_ = l_Lean_PersistentArray_toArray___redArg(v_traces_292_);
lean_dec_ref(v_traces_292_);
v_sz_294_ = lean_array_size(v___x_293_);
v___x_295_ = ((size_t)0ULL);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7_spec__8(v_sz_294_, v___x_295_, v___x_293_);
v_msg_297_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_297_, 0, v_data_274_);
lean_ctor_set(v_msg_297_, 1, v_msg_276_);
lean_ctor_set(v_msg_297_, 2, v___x_296_);
v___x_298_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msg_297_, v___y_277_, v___y_278_, v___x_289_, v___y_280_);
lean_dec_ref_known(v___x_289_, 3);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_337_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_337_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_337_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v_traceState_304_; lean_object* v_env_305_; lean_object* v_nextMacroScope_306_; lean_object* v_ngen_307_; lean_object* v_auxDeclNGen_308_; lean_object* v_cache_309_; lean_object* v_recordedDeps_310_; lean_object* v_messages_311_; lean_object* v_infoState_312_; lean_object* v_snapshotTasks_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_336_; 
v___x_303_ = lean_st_ref_take(v___y_280_);
v_traceState_304_ = lean_ctor_get(v___x_303_, 4);
v_env_305_ = lean_ctor_get(v___x_303_, 0);
v_nextMacroScope_306_ = lean_ctor_get(v___x_303_, 1);
v_ngen_307_ = lean_ctor_get(v___x_303_, 2);
v_auxDeclNGen_308_ = lean_ctor_get(v___x_303_, 3);
v_cache_309_ = lean_ctor_get(v___x_303_, 5);
v_recordedDeps_310_ = lean_ctor_get(v___x_303_, 6);
v_messages_311_ = lean_ctor_get(v___x_303_, 7);
v_infoState_312_ = lean_ctor_get(v___x_303_, 8);
v_snapshotTasks_313_ = lean_ctor_get(v___x_303_, 9);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_336_ == 0)
{
v___x_315_ = v___x_303_;
v_isShared_316_ = v_isSharedCheck_336_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_snapshotTasks_313_);
lean_inc(v_infoState_312_);
lean_inc(v_messages_311_);
lean_inc(v_recordedDeps_310_);
lean_inc(v_cache_309_);
lean_inc(v_traceState_304_);
lean_inc(v_auxDeclNGen_308_);
lean_inc(v_ngen_307_);
lean_inc(v_nextMacroScope_306_);
lean_inc(v_env_305_);
lean_dec(v___x_303_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_336_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
uint64_t v_tid_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_334_; 
v_tid_317_ = lean_ctor_get_uint64(v_traceState_304_, sizeof(void*)*1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_traceState_304_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v_traceState_304_, 0);
lean_dec(v_unused_335_);
v___x_319_ = v_traceState_304_;
v_isShared_320_ = v_isSharedCheck_334_;
goto v_resetjp_318_;
}
else
{
lean_dec(v_traceState_304_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_334_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_321_ = lean_box(0);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v_ref_275_);
lean_ctor_set(v___x_322_, 1, v_a_299_);
v___x_323_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_273_, v___x_322_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_323_);
v___x_325_ = v___x_319_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_323_);
lean_ctor_set_uint64(v_reuseFailAlloc_333_, sizeof(void*)*1, v_tid_317_);
v___x_325_ = v_reuseFailAlloc_333_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_327_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 4, v___x_325_);
v___x_327_ = v___x_315_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_env_305_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_nextMacroScope_306_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_ngen_307_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v_auxDeclNGen_308_);
lean_ctor_set(v_reuseFailAlloc_332_, 4, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_332_, 5, v_cache_309_);
lean_ctor_set(v_reuseFailAlloc_332_, 6, v_recordedDeps_310_);
lean_ctor_set(v_reuseFailAlloc_332_, 7, v_messages_311_);
lean_ctor_set(v_reuseFailAlloc_332_, 8, v_infoState_312_);
lean_ctor_set(v_reuseFailAlloc_332_, 9, v_snapshotTasks_313_);
v___x_327_ = v_reuseFailAlloc_332_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = lean_st_ref_put(v___y_280_, v___x_327_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_321_);
v___x_330_ = v___x_301_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_321_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg___boxed(lean_object* v_oldTraces_338_, lean_object* v_data_339_, lean_object* v_ref_340_, lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_338_, v_data_339_, v_ref_340_, v_msg_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_347_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0(void){
_start:
{
lean_object* v___x_348_; double v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_float_of_nat(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__1));
v___x_352_ = l_Lean_stringToMessageData(v___x_351_);
return v___x_352_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3(void){
_start:
{
lean_object* v___x_353_; double v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(1000u);
v___x_354_ = lean_float_of_nat(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(lean_object* v_cls_355_, uint8_t v_collapsed_356_, lean_object* v_tag_357_, lean_object* v_opts_358_, uint8_t v_clsEnabled_359_, lean_object* v_oldTraces_360_, lean_object* v_msg_361_, lean_object* v_resStartStop_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_fst_378_; lean_object* v_snd_379_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v_data_383_; lean_object* v_fst_394_; lean_object* v_snd_395_; lean_object* v___x_396_; uint8_t v___x_397_; lean_object* v___y_399_; lean_object* v_a_400_; uint8_t v___y_415_; double v___y_447_; 
v_fst_378_ = lean_ctor_get(v_resStartStop_362_, 0);
lean_inc(v_fst_378_);
v_snd_379_ = lean_ctor_get(v_resStartStop_362_, 1);
lean_inc(v_snd_379_);
lean_dec_ref(v_resStartStop_362_);
v_fst_394_ = lean_ctor_get(v_snd_379_, 0);
lean_inc(v_fst_394_);
v_snd_395_ = lean_ctor_get(v_snd_379_, 1);
lean_inc(v_snd_395_);
lean_dec(v_snd_379_);
v___x_396_ = l_Lean_trace_profiler;
v___x_397_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_358_, v___x_396_);
if (v___x_397_ == 0)
{
v___y_415_ = v___x_397_;
goto v___jp_414_;
}
else
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = l_Lean_trace_profiler_useHeartbeats;
v___x_453_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_opts_358_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; double v___x_456_; double v___x_457_; double v___x_458_; 
v___x_454_ = l_Lean_trace_profiler_threshold;
v___x_455_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(v_opts_358_, v___x_454_);
v___x_456_ = lean_float_of_nat(v___x_455_);
v___x_457_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__3);
v___x_458_ = lean_float_div(v___x_456_, v___x_457_);
v___y_447_ = v___x_458_;
goto v___jp_446_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; double v___x_461_; 
v___x_459_ = l_Lean_trace_profiler_threshold;
v___x_460_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__10(v_opts_358_, v___x_459_);
v___x_461_ = lean_float_of_nat(v___x_460_);
v___y_447_ = v___x_461_;
goto v___jp_446_;
}
}
v___jp_380_:
{
lean_object* v___x_384_; 
lean_inc(v___y_382_);
v___x_384_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_360_, v_data_383_, v___y_382_, v___y_381_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v___x_385_; 
lean_dec_ref_known(v___x_384_, 1);
v___x_385_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_fst_378_);
return v___x_385_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec(v_fst_378_);
v_a_386_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_384_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_384_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
v___jp_398_:
{
uint8_t v_result_401_; lean_object* v___x_402_; lean_object* v___x_403_; double v___x_404_; lean_object* v_data_405_; 
v_result_401_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__9(v_fst_378_);
v___x_402_ = lean_box(v_result_401_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
v___x_404_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__0);
lean_inc_ref(v_tag_357_);
lean_inc_ref(v___x_403_);
lean_inc(v_cls_355_);
v_data_405_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_405_, 0, v_cls_355_);
lean_ctor_set(v_data_405_, 1, v___x_403_);
lean_ctor_set(v_data_405_, 2, v_tag_357_);
lean_ctor_set_float(v_data_405_, sizeof(void*)*3, v___x_404_);
lean_ctor_set_float(v_data_405_, sizeof(void*)*3 + 8, v___x_404_);
lean_ctor_set_uint8(v_data_405_, sizeof(void*)*3 + 16, v_collapsed_356_);
if (v___x_397_ == 0)
{
lean_dec_ref_known(v___x_403_, 1);
lean_dec(v_snd_395_);
lean_dec(v_fst_394_);
lean_dec_ref(v_tag_357_);
lean_dec(v_cls_355_);
v___y_381_ = v_a_400_;
v___y_382_ = v___y_399_;
v_data_383_ = v_data_405_;
goto v___jp_380_;
}
else
{
lean_object* v_data_406_; double v___x_407_; double v___x_408_; 
lean_dec_ref_known(v_data_405_, 3);
v_data_406_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_406_, 0, v_cls_355_);
lean_ctor_set(v_data_406_, 1, v___x_403_);
lean_ctor_set(v_data_406_, 2, v_tag_357_);
v___x_407_ = lean_unbox_float(v_fst_394_);
lean_dec(v_fst_394_);
lean_ctor_set_float(v_data_406_, sizeof(void*)*3, v___x_407_);
v___x_408_ = lean_unbox_float(v_snd_395_);
lean_dec(v_snd_395_);
lean_ctor_set_float(v_data_406_, sizeof(void*)*3 + 8, v___x_408_);
lean_ctor_set_uint8(v_data_406_, sizeof(void*)*3 + 16, v_collapsed_356_);
v___y_381_ = v_a_400_;
v___y_382_ = v___y_399_;
v_data_383_ = v_data_406_;
goto v___jp_380_;
}
}
v___jp_409_:
{
lean_object* v_ref_410_; lean_object* v___x_411_; 
v_ref_410_ = lean_ctor_get(v___y_375_, 2);
lean_inc(v___y_376_);
lean_inc_ref(v___y_375_);
lean_inc(v___y_374_);
lean_inc_ref(v___y_373_);
lean_inc(v___y_372_);
lean_inc_ref(v___y_371_);
lean_inc(v___y_370_);
lean_inc_ref(v___y_369_);
lean_inc(v___y_368_);
lean_inc(v___y_367_);
lean_inc_ref(v___y_366_);
lean_inc(v___y_365_);
lean_inc(v___y_364_);
lean_inc_ref(v___y_363_);
lean_inc(v_fst_378_);
v___x_411_ = lean_apply_16(v_msg_361_, v_fst_378_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, lean_box(0));
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___y_399_ = v_ref_410_;
v_a_400_ = v_a_412_;
goto v___jp_398_;
}
else
{
lean_object* v___x_413_; 
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___closed__2);
v___y_399_ = v_ref_410_;
v_a_400_ = v___x_413_;
goto v___jp_398_;
}
}
v___jp_414_:
{
if (v_clsEnabled_359_ == 0)
{
if (v___y_415_ == 0)
{
lean_object* v___x_416_; lean_object* v_traceState_417_; lean_object* v_env_418_; lean_object* v_nextMacroScope_419_; lean_object* v_ngen_420_; lean_object* v_auxDeclNGen_421_; lean_object* v_cache_422_; lean_object* v_recordedDeps_423_; lean_object* v_messages_424_; lean_object* v_infoState_425_; lean_object* v_snapshotTasks_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_445_; 
lean_dec(v_snd_395_);
lean_dec(v_fst_394_);
lean_dec_ref(v_msg_361_);
lean_dec_ref(v_tag_357_);
lean_dec(v_cls_355_);
v___x_416_ = lean_st_ref_take(v___y_376_);
v_traceState_417_ = lean_ctor_get(v___x_416_, 4);
v_env_418_ = lean_ctor_get(v___x_416_, 0);
v_nextMacroScope_419_ = lean_ctor_get(v___x_416_, 1);
v_ngen_420_ = lean_ctor_get(v___x_416_, 2);
v_auxDeclNGen_421_ = lean_ctor_get(v___x_416_, 3);
v_cache_422_ = lean_ctor_get(v___x_416_, 5);
v_recordedDeps_423_ = lean_ctor_get(v___x_416_, 6);
v_messages_424_ = lean_ctor_get(v___x_416_, 7);
v_infoState_425_ = lean_ctor_get(v___x_416_, 8);
v_snapshotTasks_426_ = lean_ctor_get(v___x_416_, 9);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_445_ == 0)
{
v___x_428_ = v___x_416_;
v_isShared_429_ = v_isSharedCheck_445_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_snapshotTasks_426_);
lean_inc(v_infoState_425_);
lean_inc(v_messages_424_);
lean_inc(v_recordedDeps_423_);
lean_inc(v_cache_422_);
lean_inc(v_traceState_417_);
lean_inc(v_auxDeclNGen_421_);
lean_inc(v_ngen_420_);
lean_inc(v_nextMacroScope_419_);
lean_inc(v_env_418_);
lean_dec(v___x_416_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_445_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
uint64_t v_tid_430_; lean_object* v_traces_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_444_; 
v_tid_430_ = lean_ctor_get_uint64(v_traceState_417_, sizeof(void*)*1);
v_traces_431_ = lean_ctor_get(v_traceState_417_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v_traceState_417_);
if (v_isSharedCheck_444_ == 0)
{
v___x_433_ = v_traceState_417_;
v_isShared_434_ = v_isSharedCheck_444_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_traces_431_);
lean_dec(v_traceState_417_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_444_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_360_, v_traces_431_);
lean_dec_ref(v_traces_431_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_435_);
lean_ctor_set_uint64(v_reuseFailAlloc_443_, sizeof(void*)*1, v_tid_430_);
v___x_437_ = v_reuseFailAlloc_443_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 4, v___x_437_);
v___x_439_ = v___x_428_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_env_418_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_nextMacroScope_419_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_ngen_420_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v_auxDeclNGen_421_);
lean_ctor_set(v_reuseFailAlloc_442_, 4, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_442_, 5, v_cache_422_);
lean_ctor_set(v_reuseFailAlloc_442_, 6, v_recordedDeps_423_);
lean_ctor_set(v_reuseFailAlloc_442_, 7, v_messages_424_);
lean_ctor_set(v_reuseFailAlloc_442_, 8, v_infoState_425_);
lean_ctor_set(v_reuseFailAlloc_442_, 9, v_snapshotTasks_426_);
v___x_439_ = v_reuseFailAlloc_442_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_st_ref_put(v___y_376_, v___x_439_);
v___x_441_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_fst_378_);
return v___x_441_;
}
}
}
}
}
else
{
goto v___jp_409_;
}
}
else
{
goto v___jp_409_;
}
}
v___jp_446_:
{
double v___x_448_; double v___x_449_; double v___x_450_; uint8_t v___x_451_; 
v___x_448_ = lean_unbox_float(v_snd_395_);
v___x_449_ = lean_unbox_float(v_fst_394_);
v___x_450_ = lean_float_sub(v___x_448_, v___x_449_);
v___x_451_ = lean_float_decLt(v___y_447_, v___x_450_);
v___y_415_ = v___x_451_;
goto v___jp_414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6___boxed(lean_object** _args){
lean_object* v_cls_462_ = _args[0];
lean_object* v_collapsed_463_ = _args[1];
lean_object* v_tag_464_ = _args[2];
lean_object* v_opts_465_ = _args[3];
lean_object* v_clsEnabled_466_ = _args[4];
lean_object* v_oldTraces_467_ = _args[5];
lean_object* v_msg_468_ = _args[6];
lean_object* v_resStartStop_469_ = _args[7];
lean_object* v___y_470_ = _args[8];
lean_object* v___y_471_ = _args[9];
lean_object* v___y_472_ = _args[10];
lean_object* v___y_473_ = _args[11];
lean_object* v___y_474_ = _args[12];
lean_object* v___y_475_ = _args[13];
lean_object* v___y_476_ = _args[14];
lean_object* v___y_477_ = _args[15];
lean_object* v___y_478_ = _args[16];
lean_object* v___y_479_ = _args[17];
lean_object* v___y_480_ = _args[18];
lean_object* v___y_481_ = _args[19];
lean_object* v___y_482_ = _args[20];
lean_object* v___y_483_ = _args[21];
lean_object* v___y_484_ = _args[22];
_start:
{
uint8_t v_collapsed_boxed_485_; uint8_t v_clsEnabled_boxed_486_; lean_object* v_res_487_; 
v_collapsed_boxed_485_ = lean_unbox(v_collapsed_463_);
v_clsEnabled_boxed_486_ = lean_unbox(v_clsEnabled_466_);
v_res_487_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v_cls_462_, v_collapsed_boxed_485_, v_tag_464_, v_opts_465_, v_clsEnabled_boxed_486_, v_oldTraces_467_, v_msg_468_, v_resStartStop_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec_ref(v_opts_465_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(size_t v_sz_488_, size_t v_i_489_, lean_object* v_bs_490_){
_start:
{
uint8_t v___x_491_; 
v___x_491_ = lean_usize_dec_lt(v_i_489_, v_sz_488_);
if (v___x_491_ == 0)
{
return v_bs_490_;
}
else
{
lean_object* v_v_492_; lean_object* v_hyp_493_; lean_object* v___x_494_; lean_object* v_bs_x27_495_; size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v_v_492_ = lean_array_uget_borrowed(v_bs_490_, v_i_489_);
v_hyp_493_ = lean_ctor_get(v_v_492_, 0);
lean_inc_ref(v_hyp_493_);
v___x_494_ = lean_unsigned_to_nat(0u);
v_bs_x27_495_ = lean_array_uset(v_bs_490_, v_i_489_, v___x_494_);
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_489_, v___x_496_);
v___x_498_ = lean_array_uset(v_bs_x27_495_, v_i_489_, v_hyp_493_);
v_i_489_ = v___x_497_;
v_bs_490_ = v___x_498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1___boxed(lean_object* v_sz_500_, lean_object* v_i_501_, lean_object* v_bs_502_){
_start:
{
size_t v_sz_boxed_503_; size_t v_i_boxed_504_; lean_object* v_res_505_; 
v_sz_boxed_503_ = lean_unbox_usize(v_sz_500_);
lean_dec(v_sz_500_);
v_i_boxed_504_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_boxed_503_, v_i_boxed_504_, v_bs_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(lean_object* v_msg_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_ref_512_; lean_object* v___x_513_; lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_522_; 
v_ref_512_ = lean_ctor_get(v___y_509_, 2);
v___x_513_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0_spec__0(v_msg_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_522_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_522_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_520_; 
lean_inc(v_ref_512_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v_ref_512_);
lean_ctor_set(v___x_518_, 1, v_a_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 1);
lean_ctor_set(v___x_516_, 0, v___x_518_);
v___x_520_ = v___x_516_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg___boxed(lean_object* v_msg_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_529_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__3));
v___x_536_ = l_Lean_stringToMessageData(v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(lean_object* v_as_537_, size_t v_sz_538_, size_t v_i_539_, lean_object* v_b_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_a_557_; uint8_t v___x_561_; 
v___x_561_ = lean_usize_dec_lt(v_i_539_, v_sz_538_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v_b_540_);
return v___x_562_;
}
else
{
lean_object* v_a_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_a_563_ = lean_array_uget_borrowed(v_as_537_, v_i_539_);
v___x_564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__0));
v___x_565_ = l_Lean_Core_checkSystem(v___x_564_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_type_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
lean_dec_ref_known(v___x_565_, 1);
v_type_566_ = lean_ctor_get(v_a_563_, 1);
v___x_567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__2));
v___x_568_ = l_Lean_Expr_isConstOf(v_type_566_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(v___y_543_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v___x_570_; 
lean_dec_ref_known(v___x_569_, 1);
lean_inc(v_a_563_);
v___x_570_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(v_a_563_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
if (lean_obj_tag(v_a_571_) == 1)
{
lean_object* v_val_572_; lean_object* v___x_573_; 
v_val_572_ = lean_ctor_get(v_a_571_, 0);
lean_inc(v_val_572_);
lean_dec_ref_known(v_a_571_, 1);
v___x_573_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(v___y_543_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v___x_575_ = l_Array_append___redArg(v_b_540_, v_a_574_);
lean_dec(v_a_574_);
v___x_576_ = lean_array_push(v___x_575_, v_val_572_);
v_a_557_ = v___x_576_;
goto v___jp_556_;
}
else
{
lean_dec(v_val_572_);
lean_dec_ref(v_b_540_);
return v___x_573_;
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_a_571_);
v___x_577_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___closed__4);
lean_inc_ref(v_type_566_);
v___x_578_ = l_Lean_MessageData_ofExpr(v_type_566_);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v___x_579_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_dec_ref_known(v___x_580_, 1);
v_a_557_ = v_b_540_;
goto v___jp_556_;
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v_b_540_);
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v_b_540_);
v_a_589_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_570_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_570_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v_b_540_);
v_a_597_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_569_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_569_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
v_a_557_ = v_b_540_;
goto v___jp_556_;
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v_b_540_);
v_a_605_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_565_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_565_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
v___jp_556_:
{
size_t v___x_558_; size_t v___x_559_; 
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_add(v_i_539_, v___x_558_);
v_i_539_ = v___x_559_;
v_b_540_ = v_a_557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2___boxed(lean_object** _args){
lean_object* v_as_613_ = _args[0];
lean_object* v_sz_614_ = _args[1];
lean_object* v_i_615_ = _args[2];
lean_object* v_b_616_ = _args[3];
lean_object* v___y_617_ = _args[4];
lean_object* v___y_618_ = _args[5];
lean_object* v___y_619_ = _args[6];
lean_object* v___y_620_ = _args[7];
lean_object* v___y_621_ = _args[8];
lean_object* v___y_622_ = _args[9];
lean_object* v___y_623_ = _args[10];
lean_object* v___y_624_ = _args[11];
lean_object* v___y_625_ = _args[12];
lean_object* v___y_626_ = _args[13];
lean_object* v___y_627_ = _args[14];
lean_object* v___y_628_ = _args[15];
lean_object* v___y_629_ = _args[16];
lean_object* v___y_630_ = _args[17];
lean_object* v___y_631_ = _args[18];
_start:
{
size_t v_sz_boxed_632_; size_t v_i_boxed_633_; lean_object* v_res_634_; 
v_sz_boxed_632_ = lean_unbox_usize(v_sz_614_);
lean_dec(v_sz_614_);
v_i_boxed_633_ = lean_unbox_usize(v_i_615_);
lean_dec(v_i_615_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_as_613_, v_sz_boxed_632_, v_i_boxed_633_, v_b_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec_ref(v_as_613_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(lean_object* v_as_635_, size_t v_i_636_, size_t v_stop_637_, lean_object* v_b_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = lean_usize_dec_eq(v_i_636_, v_stop_637_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_array_uget_borrowed(v_as_635_, v_i_636_);
lean_inc(v___x_647_);
v___x_648_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_b_638_, v___x_647_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; size_t v___x_650_; size_t v___x_651_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 1);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_add(v_i_636_, v___x_650_);
v_i_636_ = v___x_651_;
v_b_638_ = v_a_649_;
goto _start;
}
else
{
return v___x_648_;
}
}
else
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v_b_638_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg___boxed(lean_object* v_as_654_, lean_object* v_i_655_, lean_object* v_stop_656_, lean_object* v_b_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
size_t v_i_boxed_665_; size_t v_stop_boxed_666_; lean_object* v_res_667_; 
v_i_boxed_665_ = lean_unbox_usize(v_i_655_);
lean_dec(v_i_655_);
v_stop_boxed_666_ = lean_unbox_usize(v_stop_656_);
lean_dec(v_stop_656_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_as_654_, v_i_boxed_665_, v_stop_boxed_666_, v_b_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec_ref(v_as_654_);
return v_res_667_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1(void){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__1);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__2);
v___x_675_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
lean_ctor_set(v___x_675_, 2, v___x_674_);
lean_ctor_set(v___x_675_, 3, v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = lean_box(0);
v___x_677_ = lean_unsigned_to_nat(16u);
v___x_678_ = lean_mk_array(v___x_677_, v___x_676_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__4);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__5);
v___x_683_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
lean_ctor_set(v___x_683_, 2, v___x_682_);
lean_ctor_set(v___x_683_, 3, v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13));
v___x_701_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__16));
v___x_702_ = l_Lean_Name_append(v___x_701_, v___x_700_);
return v___x_702_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18(void){
_start:
{
lean_object* v___x_703_; double v___x_704_; 
v___x_703_ = lean_unsigned_to_nat(1000000000u);
v___x_704_ = lean_float_of_nat(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___y_721_; lean_object* v_a_722_; lean_object* v_hypQueue_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v_toCold_926_; lean_object* v_options_927_; uint8_t v_hasTrace_928_; 
v_toCold_926_ = lean_ctor_get(v_a_717_, 0);
v_options_927_ = lean_ctor_get(v_toCold_926_, 2);
v_hasTrace_928_ = lean_ctor_get_uint8(v_options_927_, sizeof(void*)*1);
if (v_hasTrace_928_ == 0)
{
lean_object* v___x_929_; lean_object* v_satExpr_930_; lean_object* v_hypQueue_931_; lean_object* v_usedHyps_932_; uint8_t v_didChange_933_; lean_object* v_theoryState_934_; lean_object* v_solverTimeBudgetMs_935_; lean_object* v_roundBudget_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_946_; 
v___x_929_ = lean_st_ref_take(v_a_706_);
v_satExpr_930_ = lean_ctor_get(v___x_929_, 0);
v_hypQueue_931_ = lean_ctor_get(v___x_929_, 1);
v_usedHyps_932_ = lean_ctor_get(v___x_929_, 2);
v_didChange_933_ = lean_ctor_get_uint8(v___x_929_, sizeof(void*)*6);
v_theoryState_934_ = lean_ctor_get(v___x_929_, 3);
v_solverTimeBudgetMs_935_ = lean_ctor_get(v___x_929_, 4);
v_roundBudget_936_ = lean_ctor_get(v___x_929_, 5);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_946_ == 0)
{
v___x_938_ = v___x_929_;
v_isShared_939_ = v_isSharedCheck_946_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_roundBudget_936_);
lean_inc(v_solverTimeBudgetMs_935_);
lean_inc(v_theoryState_934_);
lean_inc(v_usedHyps_932_);
lean_inc(v_hypQueue_931_);
lean_inc(v_satExpr_930_);
lean_dec(v___x_929_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_946_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_940_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_941_ = l_Array_append___redArg(v_usedHyps_932_, v_hypQueue_931_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 2, v___x_941_);
lean_ctor_set(v___x_938_, 1, v___x_940_);
v___x_943_ = v___x_938_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_satExpr_930_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_theoryState_934_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_solverTimeBudgetMs_935_);
lean_ctor_set(v_reuseFailAlloc_945_, 5, v_roundBudget_936_);
lean_ctor_set_uint8(v_reuseFailAlloc_945_, sizeof(void*)*6, v_didChange_933_);
v___x_943_ = v_reuseFailAlloc_945_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = lean_st_ref_put(v_a_706_, v___x_943_);
v_hypQueue_743_ = v_hypQueue_931_;
v___y_744_ = v_a_705_;
v___y_745_ = v_a_706_;
v___y_746_ = v_a_707_;
v___y_747_ = v_a_708_;
v___y_748_ = v_a_709_;
v___y_749_ = v_a_710_;
v___y_750_ = v_a_711_;
v___y_751_ = v_a_712_;
v___y_752_ = v_a_713_;
v___y_753_ = v_a_714_;
v___y_754_ = v_a_715_;
v___y_755_ = v_a_716_;
v___y_756_ = v_a_717_;
v___y_757_ = v_a_718_;
goto v___jp_742_;
}
}
}
else
{
lean_object* v_inheritedTraceOptions_947_; lean_object* v___f_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v_a_956_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v_a_971_; lean_object* v___y_974_; lean_object* v___y_975_; uint8_t v_a_976_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v_a_982_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v_a_1003_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v_a_1015_; lean_object* v___y_1018_; lean_object* v___y_1019_; uint8_t v_a_1020_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v_a_1026_; 
v_inheritedTraceOptions_947_ = lean_ctor_get(v_toCold_926_, 11);
v___f_948_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__9));
v___x_949_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__13));
v___x_950_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__14));
v___x_951_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__17);
v___x_952_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_947_, v_options_927_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_1353_; uint8_t v___x_1354_; 
v___x_1353_ = l_Lean_trace_profiler;
v___x_1354_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_options_927_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v_satExpr_1356_; lean_object* v_hypQueue_1357_; lean_object* v_usedHyps_1358_; uint8_t v_didChange_1359_; lean_object* v_theoryState_1360_; lean_object* v_solverTimeBudgetMs_1361_; lean_object* v_roundBudget_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1372_; 
v___x_1355_ = lean_st_ref_take(v_a_706_);
v_satExpr_1356_ = lean_ctor_get(v___x_1355_, 0);
v_hypQueue_1357_ = lean_ctor_get(v___x_1355_, 1);
v_usedHyps_1358_ = lean_ctor_get(v___x_1355_, 2);
v_didChange_1359_ = lean_ctor_get_uint8(v___x_1355_, sizeof(void*)*6);
v_theoryState_1360_ = lean_ctor_get(v___x_1355_, 3);
v_solverTimeBudgetMs_1361_ = lean_ctor_get(v___x_1355_, 4);
v_roundBudget_1362_ = lean_ctor_get(v___x_1355_, 5);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1364_ = v___x_1355_;
v_isShared_1365_ = v_isSharedCheck_1372_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_roundBudget_1362_);
lean_inc(v_solverTimeBudgetMs_1361_);
lean_inc(v_theoryState_1360_);
lean_inc(v_usedHyps_1358_);
lean_inc(v_hypQueue_1357_);
lean_inc(v_satExpr_1356_);
lean_dec(v___x_1355_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1372_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1366_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1367_ = l_Array_append___redArg(v_usedHyps_1358_, v_hypQueue_1357_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 2, v___x_1367_);
lean_ctor_set(v___x_1364_, 1, v___x_1366_);
v___x_1369_ = v___x_1364_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_satExpr_1356_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v_theoryState_1360_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_solverTimeBudgetMs_1361_);
lean_ctor_set(v_reuseFailAlloc_1371_, 5, v_roundBudget_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*6, v_didChange_1359_);
v___x_1369_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_st_ref_put(v_a_706_, v___x_1369_);
v_hypQueue_743_ = v_hypQueue_1357_;
v___y_744_ = v_a_705_;
v___y_745_ = v_a_706_;
v___y_746_ = v_a_707_;
v___y_747_ = v_a_708_;
v___y_748_ = v_a_709_;
v___y_749_ = v_a_710_;
v___y_750_ = v_a_711_;
v___y_751_ = v_a_712_;
v___y_752_ = v_a_713_;
v___y_753_ = v_a_714_;
v___y_754_ = v_a_715_;
v___y_755_ = v_a_716_;
v___y_756_ = v_a_717_;
v___y_757_ = v_a_718_;
goto v___jp_742_;
}
}
}
else
{
goto v___jp_1044_;
}
}
else
{
goto v___jp_1044_;
}
v___jp_953_:
{
lean_object* v___x_957_; double v___x_958_; double v___x_959_; double v___x_960_; double v___x_961_; double v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_957_ = lean_io_mono_nanos_now();
v___x_958_ = lean_float_of_nat(v___y_954_);
v___x_959_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__18);
v___x_960_ = lean_float_div(v___x_958_, v___x_959_);
v___x_961_ = lean_float_of_nat(v___x_957_);
v___x_962_ = lean_float_div(v___x_961_, v___x_959_);
v___x_963_ = lean_box_float(v___x_960_);
v___x_964_ = lean_box_float(v___x_962_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v_a_956_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v___x_949_, v_hasTrace_928_, v___x_950_, v_options_927_, v___x_952_, v___y_955_, v___f_948_, v___x_966_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
return v___x_967_;
}
v___jp_968_:
{
lean_object* v___x_972_; 
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v_a_971_);
v___y_954_ = v___y_969_;
v___y_955_ = v___y_970_;
v_a_956_ = v___x_972_;
goto v___jp_953_;
}
v___jp_973_:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_box(v_a_976_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
v___y_954_ = v___y_974_;
v___y_955_ = v___y_975_;
v_a_956_ = v___x_978_;
goto v___jp_953_;
}
v___jp_979_:
{
lean_object* v___x_983_; lean_object* v_hypQueue_984_; lean_object* v_usedHyps_985_; uint8_t v_didChange_986_; lean_object* v_theoryState_987_; lean_object* v_solverTimeBudgetMs_988_; lean_object* v_roundBudget_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_998_; 
v___x_983_ = lean_st_ref_take(v_a_706_);
v_hypQueue_984_ = lean_ctor_get(v___x_983_, 1);
v_usedHyps_985_ = lean_ctor_get(v___x_983_, 2);
v_didChange_986_ = lean_ctor_get_uint8(v___x_983_, sizeof(void*)*6);
v_theoryState_987_ = lean_ctor_get(v___x_983_, 3);
v_solverTimeBudgetMs_988_ = lean_ctor_get(v___x_983_, 4);
v_roundBudget_989_ = lean_ctor_get(v___x_983_, 5);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v___x_983_, 0);
lean_dec(v_unused_999_);
v___x_991_ = v___x_983_;
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_roundBudget_989_);
lean_inc(v_solverTimeBudgetMs_988_);
lean_inc(v_theoryState_987_);
lean_inc(v_usedHyps_985_);
lean_inc(v_hypQueue_984_);
lean_dec(v___x_983_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_a_982_);
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_982_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_hypQueue_984_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_usedHyps_985_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_theoryState_987_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_solverTimeBudgetMs_988_);
lean_ctor_set(v_reuseFailAlloc_997_, 5, v_roundBudget_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*6, v_didChange_986_);
v___x_994_ = v_reuseFailAlloc_997_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = lean_st_ref_put(v_a_706_, v___x_994_);
v___x_996_ = 1;
v___y_974_ = v___y_980_;
v___y_975_ = v___y_981_;
v_a_976_ = v___x_996_;
goto v___jp_973_;
}
}
}
v___jp_1000_:
{
lean_object* v___x_1004_; double v___x_1005_; double v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1004_ = lean_io_get_num_heartbeats();
v___x_1005_ = lean_float_of_nat(v___y_1001_);
v___x_1006_ = lean_float_of_nat(v___x_1004_);
v___x_1007_ = lean_box_float(v___x_1005_);
v___x_1008_ = lean_box_float(v___x_1006_);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_a_1003_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6(v___x_949_, v_hasTrace_928_, v___x_950_, v_options_927_, v___x_952_, v___y_1002_, v___f_948_, v___x_1010_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
return v___x_1011_;
}
v___jp_1012_:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_a_1015_);
v___y_1001_ = v___y_1013_;
v___y_1002_ = v___y_1014_;
v_a_1003_ = v___x_1016_;
goto v___jp_1000_;
}
v___jp_1017_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_box(v_a_1020_);
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
v___y_1001_ = v___y_1018_;
v___y_1002_ = v___y_1019_;
v_a_1003_ = v___x_1022_;
goto v___jp_1000_;
}
v___jp_1023_:
{
lean_object* v___x_1027_; lean_object* v_hypQueue_1028_; lean_object* v_usedHyps_1029_; uint8_t v_didChange_1030_; lean_object* v_theoryState_1031_; lean_object* v_solverTimeBudgetMs_1032_; lean_object* v_roundBudget_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1042_; 
v___x_1027_ = lean_st_ref_take(v_a_706_);
v_hypQueue_1028_ = lean_ctor_get(v___x_1027_, 1);
v_usedHyps_1029_ = lean_ctor_get(v___x_1027_, 2);
v_didChange_1030_ = lean_ctor_get_uint8(v___x_1027_, sizeof(void*)*6);
v_theoryState_1031_ = lean_ctor_get(v___x_1027_, 3);
v_solverTimeBudgetMs_1032_ = lean_ctor_get(v___x_1027_, 4);
v_roundBudget_1033_ = lean_ctor_get(v___x_1027_, 5);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v___x_1027_, 0);
lean_dec(v_unused_1043_);
v___x_1035_ = v___x_1027_;
v_isShared_1036_ = v_isSharedCheck_1042_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_roundBudget_1033_);
lean_inc(v_solverTimeBudgetMs_1032_);
lean_inc(v_theoryState_1031_);
lean_inc(v_usedHyps_1029_);
lean_inc(v_hypQueue_1028_);
lean_dec(v___x_1027_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1042_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v_a_1026_);
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1026_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_hypQueue_1028_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_usedHyps_1029_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v_theoryState_1031_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v_solverTimeBudgetMs_1032_);
lean_ctor_set(v_reuseFailAlloc_1041_, 5, v_roundBudget_1033_);
lean_ctor_set_uint8(v_reuseFailAlloc_1041_, sizeof(void*)*6, v_didChange_1030_);
v___x_1038_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_st_ref_put(v_a_706_, v___x_1038_);
v___x_1040_ = 1;
v___y_1018_ = v___y_1024_;
v___y_1019_ = v___y_1025_;
v_a_1020_ = v___x_1040_;
goto v___jp_1017_;
}
}
}
v___jp_1044_:
{
lean_object* v___x_1045_; lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1352_; 
v___x_1045_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__4___redArg(v_a_718_);
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1352_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1352_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1051_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__5(v_options_927_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v_satExpr_1054_; lean_object* v_hypQueue_1055_; lean_object* v_usedHyps_1056_; uint8_t v_didChange_1057_; lean_object* v_theoryState_1058_; lean_object* v_solverTimeBudgetMs_1059_; lean_object* v_roundBudget_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1201_; 
v___x_1052_ = lean_io_mono_nanos_now();
v___x_1053_ = lean_st_ref_take(v_a_706_);
v_satExpr_1054_ = lean_ctor_get(v___x_1053_, 0);
v_hypQueue_1055_ = lean_ctor_get(v___x_1053_, 1);
v_usedHyps_1056_ = lean_ctor_get(v___x_1053_, 2);
v_didChange_1057_ = lean_ctor_get_uint8(v___x_1053_, sizeof(void*)*6);
v_theoryState_1058_ = lean_ctor_get(v___x_1053_, 3);
v_solverTimeBudgetMs_1059_ = lean_ctor_get(v___x_1053_, 4);
v_roundBudget_1060_ = lean_ctor_get(v___x_1053_, 5);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1062_ = v___x_1053_;
v_isShared_1063_ = v_isSharedCheck_1201_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_roundBudget_1060_);
lean_inc(v_solverTimeBudgetMs_1059_);
lean_inc(v_theoryState_1058_);
lean_inc(v_usedHyps_1056_);
lean_inc(v_hypQueue_1055_);
lean_inc(v_satExpr_1054_);
lean_dec(v___x_1053_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1201_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1066_ = l_Array_append___redArg(v_usedHyps_1056_, v_hypQueue_1055_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 2, v___x_1066_);
lean_ctor_set(v___x_1062_, 1, v___x_1065_);
v___x_1068_ = v___x_1062_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_satExpr_1054_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_theoryState_1058_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_solverTimeBudgetMs_1059_);
lean_ctor_set(v_reuseFailAlloc_1200_, 5, v_roundBudget_1060_);
lean_ctor_set_uint8(v_reuseFailAlloc_1200_, sizeof(void*)*6, v_didChange_1057_);
v___x_1068_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = lean_st_ref_put(v_a_706_, v___x_1068_);
v___x_1070_ = lean_array_get_size(v_hypQueue_1055_);
v___x_1071_ = lean_nat_dec_eq(v___x_1070_, v___x_1064_);
if (v___x_1071_ == 0)
{
lean_object* v_goal_1072_; lean_object* v_tacticContext_1073_; lean_object* v___x_1074_; lean_object* v_config_1075_; lean_object* v_mode_1076_; lean_object* v_timeout_1077_; uint8_t v_trimProofs_1078_; uint8_t v_binaryProofs_1079_; uint8_t v_acNf_1080_; uint8_t v_andFlattening_1081_; uint8_t v_embeddedConstraintSubst_1082_; uint8_t v_graphviz_1083_; lean_object* v_maxSteps_1084_; uint8_t v_solverMode_1085_; uint8_t v_uf_1086_; lean_object* v_cegarRounds_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1198_; 
v_goal_1072_ = lean_ctor_get(v_a_705_, 0);
v_tacticContext_1073_ = lean_ctor_get(v_a_705_, 2);
lean_inc_ref(v_tacticContext_1073_);
v___x_1074_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1073_);
v_config_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc_ref(v_config_1075_);
v_mode_1076_ = lean_ctor_get(v___x_1074_, 1);
lean_inc(v_mode_1076_);
lean_dec_ref(v___x_1074_);
v_timeout_1077_ = lean_ctor_get(v_config_1075_, 0);
v_trimProofs_1078_ = lean_ctor_get_uint8(v_config_1075_, sizeof(void*)*3);
v_binaryProofs_1079_ = lean_ctor_get_uint8(v_config_1075_, sizeof(void*)*3 + 1);
v_acNf_1080_ = lean_ctor_get_uint8(v_config_1075_, sizeof(void*)*3 + 2);
v_andFlattening_1081_ = lean_ctor_get_uint8(v_config_1075_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1082_ = lean_ctor_get_uint8(v_config_1075_, sizeof(void*)*3 + 4);
v_graphviz_1083_ = lean_ctor_get_uint8(v_config_1075_, sizeof(void*)*3 + 8);
v_maxSteps_1084_ = lean_ctor_get(v_config_1075_, 1);
v_solverMode_1085_ = lean_ctor_get_uint8(v_config_1075_, sizeof(void*)*3 + 10);
v_uf_1086_ = lean_ctor_get_uint8(v_config_1075_, sizeof(void*)*3 + 11);
v_cegarRounds_1087_ = lean_ctor_get(v_config_1075_, 2);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_config_1075_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1089_ = v_config_1075_;
v_isShared_1090_ = v_isSharedCheck_1198_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_cegarRounds_1087_);
lean_inc(v_maxSteps_1084_);
lean_inc(v_timeout_1077_);
lean_dec(v_config_1075_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1198_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
lean_inc(v_goal_1072_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_goal_1072_);
v___x_1092_ = v___x_1048_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_goal_1072_);
v___x_1092_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1094_; 
if (v_isShared_1090_ == 0)
{
v___x_1094_ = v___x_1089_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_timeout_1077_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_maxSteps_1084_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_cegarRounds_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*3, v_trimProofs_1078_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*3 + 1, v_binaryProofs_1079_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*3 + 2, v_acNf_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*3 + 3, v_andFlattening_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1082_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*3 + 8, v_graphviz_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*3 + 10, v_solverMode_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1196_, sizeof(void*)*3 + 11, v_uf_1086_);
v___x_1094_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_theoryState_1099_; lean_object* v_satExpr_1100_; lean_object* v_hypQueue_1101_; lean_object* v_usedHyps_1102_; uint8_t v_didChange_1103_; lean_object* v_solverTimeBudgetMs_1104_; lean_object* v_roundBudget_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1195_; 
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*3 + 5, v___x_1071_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*3 + 6, v___x_1071_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*3 + 7, v___x_1071_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*3 + 9, v___x_1071_);
v___x_1095_ = lean_box(v_hasTrace_928_);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
v___x_1097_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1076_, v___x_1094_, v___x_1096_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = lean_st_ref_take(v_a_706_);
v_theoryState_1099_ = lean_ctor_get(v___x_1098_, 3);
v_satExpr_1100_ = lean_ctor_get(v___x_1098_, 0);
v_hypQueue_1101_ = lean_ctor_get(v___x_1098_, 1);
v_usedHyps_1102_ = lean_ctor_get(v___x_1098_, 2);
v_didChange_1103_ = lean_ctor_get_uint8(v___x_1098_, sizeof(void*)*6);
v_solverTimeBudgetMs_1104_ = lean_ctor_get(v___x_1098_, 4);
v_roundBudget_1105_ = lean_ctor_get(v___x_1098_, 5);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1107_ = v___x_1098_;
v_isShared_1108_ = v_isSharedCheck_1195_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_roundBudget_1105_);
lean_inc(v_solverTimeBudgetMs_1104_);
lean_inc(v_theoryState_1099_);
lean_inc(v_usedHyps_1102_);
lean_inc(v_hypQueue_1101_);
lean_inc(v_satExpr_1100_);
lean_dec(v___x_1098_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1195_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v_funState_1109_; lean_object* v_bitvecState_1110_; lean_object* v_preprocessCaches_1111_; lean_object* v_satSolver_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1194_; 
v_funState_1109_ = lean_ctor_get(v_theoryState_1099_, 0);
v_bitvecState_1110_ = lean_ctor_get(v_theoryState_1099_, 1);
v_preprocessCaches_1111_ = lean_ctor_get(v_theoryState_1099_, 2);
v_satSolver_1112_ = lean_ctor_get(v_theoryState_1099_, 3);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_theoryState_1099_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1114_ = v_theoryState_1099_;
v_isShared_1115_ = v_isSharedCheck_1194_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_satSolver_1112_);
lean_inc(v_preprocessCaches_1111_);
lean_inc(v_bitvecState_1110_);
lean_inc(v_funState_1109_);
lean_dec(v_theoryState_1099_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1194_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 2, v___x_1116_);
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_funState_1109_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_bitvecState_1110_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_satSolver_1112_);
v___x_1118_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1120_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 3, v___x_1118_);
v___x_1120_ = v___x_1107_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_satExpr_1100_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_hypQueue_1101_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_usedHyps_1102_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v_solverTimeBudgetMs_1104_);
lean_ctor_set(v_reuseFailAlloc_1192_, 5, v_roundBudget_1105_);
lean_ctor_set_uint8(v_reuseFailAlloc_1192_, sizeof(void*)*6, v_didChange_1103_);
v___x_1120_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_typeAnalysis_1126_; lean_object* v_target_1127_; lean_object* v_hypotheses_1128_; uint8_t v_didChange_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1190_; 
v___x_1121_ = lean_st_ref_put(v_a_706_, v___x_1120_);
v___x_1122_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_1123_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1123_, 0, v___x_1116_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
lean_ctor_set(v___x_1123_, 2, v___x_1092_);
lean_ctor_set(v___x_1123_, 3, v___x_1065_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*4, v___x_1071_);
v___x_1124_ = lean_st_mk_ref(v___x_1123_);
v___x_1125_ = lean_st_ref_take(v___x_1124_);
v_typeAnalysis_1126_ = lean_ctor_get(v___x_1125_, 1);
v_target_1127_ = lean_ctor_get(v___x_1125_, 2);
v_hypotheses_1128_ = lean_ctor_get(v___x_1125_, 3);
v_didChange_1129_ = lean_ctor_get_uint8(v___x_1125_, sizeof(void*)*4);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; 
v_unused_1191_ = lean_ctor_get(v___x_1125_, 0);
lean_dec(v_unused_1191_);
v___x_1131_ = v___x_1125_;
v_isShared_1132_ = v_isSharedCheck_1190_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_hypotheses_1128_);
lean_inc(v_target_1127_);
lean_inc(v_typeAnalysis_1126_);
lean_dec(v___x_1125_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1190_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v_preprocessCaches_1111_);
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_preprocessCaches_1111_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_typeAnalysis_1126_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_target_1127_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_hypotheses_1128_);
lean_ctor_set_uint8(v_reuseFailAlloc_1189_, sizeof(void*)*4, v_didChange_1129_);
v___x_1134_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; size_t v_sz_1136_; size_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1135_ = lean_st_ref_put(v___x_1124_, v___x_1134_);
v_sz_1136_ = lean_array_size(v_hypQueue_1055_);
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_1136_, v___x_1137_, v_hypQueue_1055_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
v___x_1140_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1139_, v___x_1097_, v___x_1124_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec_ref(v___x_1097_);
lean_dec_ref_known(v___x_1139_, 1);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = lean_st_ref_get(v___x_1124_);
lean_dec(v___x_1124_);
v___x_1143_ = lean_unbox(v_a_1141_);
lean_dec(v_a_1141_);
if (v___x_1143_ == 0)
{
lean_object* v_caches_1144_; lean_object* v_hypotheses_1145_; lean_object* v___x_1146_; lean_object* v_theoryState_1147_; lean_object* v_satExpr_1148_; lean_object* v_hypQueue_1149_; lean_object* v_usedHyps_1150_; uint8_t v_didChange_1151_; lean_object* v_solverTimeBudgetMs_1152_; lean_object* v_roundBudget_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1186_; 
v_caches_1144_ = lean_ctor_get(v___x_1142_, 0);
lean_inc_ref(v_caches_1144_);
v_hypotheses_1145_ = lean_ctor_get(v___x_1142_, 3);
lean_inc_ref(v_hypotheses_1145_);
lean_dec(v___x_1142_);
v___x_1146_ = lean_st_ref_take(v_a_706_);
v_theoryState_1147_ = lean_ctor_get(v___x_1146_, 3);
v_satExpr_1148_ = lean_ctor_get(v___x_1146_, 0);
v_hypQueue_1149_ = lean_ctor_get(v___x_1146_, 1);
v_usedHyps_1150_ = lean_ctor_get(v___x_1146_, 2);
v_didChange_1151_ = lean_ctor_get_uint8(v___x_1146_, sizeof(void*)*6);
v_solverTimeBudgetMs_1152_ = lean_ctor_get(v___x_1146_, 4);
v_roundBudget_1153_ = lean_ctor_get(v___x_1146_, 5);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1155_ = v___x_1146_;
v_isShared_1156_ = v_isSharedCheck_1186_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_roundBudget_1153_);
lean_inc(v_solverTimeBudgetMs_1152_);
lean_inc(v_theoryState_1147_);
lean_inc(v_usedHyps_1150_);
lean_inc(v_hypQueue_1149_);
lean_inc(v_satExpr_1148_);
lean_dec(v___x_1146_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1186_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_funState_1157_; lean_object* v_bitvecState_1158_; lean_object* v_satSolver_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1184_; 
v_funState_1157_ = lean_ctor_get(v_theoryState_1147_, 0);
v_bitvecState_1158_ = lean_ctor_get(v_theoryState_1147_, 1);
v_satSolver_1159_ = lean_ctor_get(v_theoryState_1147_, 3);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_theoryState_1147_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v_theoryState_1147_, 2);
lean_dec(v_unused_1185_);
v___x_1161_ = v_theoryState_1147_;
v_isShared_1162_ = v_isSharedCheck_1184_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_satSolver_1159_);
lean_inc(v_bitvecState_1158_);
lean_inc(v_funState_1157_);
lean_dec(v_theoryState_1147_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1184_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 2, v_caches_1144_);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_funState_1157_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_bitvecState_1158_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_caches_1144_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_satSolver_1159_);
v___x_1164_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1166_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 3, v___x_1164_);
v___x_1166_ = v___x_1155_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_satExpr_1148_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_hypQueue_1149_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_usedHyps_1150_);
lean_ctor_set(v_reuseFailAlloc_1182_, 3, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1182_, 4, v_solverTimeBudgetMs_1152_);
lean_ctor_set(v_reuseFailAlloc_1182_, 5, v_roundBudget_1153_);
lean_ctor_set_uint8(v_reuseFailAlloc_1182_, sizeof(void*)*6, v_didChange_1151_);
v___x_1166_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; size_t v_sz_1168_; lean_object* v___x_1169_; 
v___x_1167_ = lean_st_ref_put(v_a_706_, v___x_1166_);
v_sz_1168_ = lean_array_size(v_hypotheses_1145_);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_1145_, v_sz_1168_, v___x_1137_, v___x_1065_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec_ref(v_hypotheses_1145_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = lean_array_get_size(v_a_1170_);
v___x_1172_ = lean_nat_dec_eq(v___x_1171_, v___x_1064_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v_satExpr_1174_; uint8_t v___x_1175_; 
v___x_1173_ = lean_st_ref_get(v_a_706_);
v_satExpr_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc_ref(v_satExpr_1174_);
lean_dec(v___x_1173_);
v___x_1175_ = lean_nat_dec_lt(v___x_1064_, v___x_1171_);
if (v___x_1175_ == 0)
{
lean_dec(v_a_1170_);
v___y_980_ = v___x_1052_;
v___y_981_ = v_a_1046_;
v_a_982_ = v_satExpr_1174_;
goto v___jp_979_;
}
else
{
size_t v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_usize_of_nat(v___x_1171_);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1170_, v___x_1137_, v___x_1176_, v_satExpr_1174_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_1170_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v___y_980_ = v___x_1052_;
v___y_981_ = v_a_1046_;
v_a_982_ = v_a_1178_;
goto v___jp_979_;
}
else
{
lean_object* v_a_1179_; 
v_a_1179_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1177_, 1);
v___y_969_ = v___x_1052_;
v___y_970_ = v_a_1046_;
v_a_971_ = v_a_1179_;
goto v___jp_968_;
}
}
}
else
{
uint8_t v___x_1180_; 
lean_dec(v_a_1170_);
v___x_1180_ = 2;
v___y_974_ = v___x_1052_;
v___y_975_ = v_a_1046_;
v_a_976_ = v___x_1180_;
goto v___jp_973_;
}
}
else
{
lean_object* v_a_1181_; 
v_a_1181_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1169_, 1);
v___y_969_ = v___x_1052_;
v___y_970_ = v_a_1046_;
v_a_971_ = v_a_1181_;
goto v___jp_968_;
}
}
}
}
}
}
else
{
uint8_t v___x_1187_; 
lean_dec(v___x_1142_);
v___x_1187_ = 0;
v___y_974_ = v___x_1052_;
v___y_975_ = v_a_1046_;
v_a_976_ = v___x_1187_;
goto v___jp_973_;
}
}
else
{
lean_object* v_a_1188_; 
lean_dec(v___x_1124_);
v_a_1188_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1140_, 1);
v___y_969_ = v___x_1052_;
v___y_970_ = v_a_1046_;
v_a_971_ = v_a_1188_;
goto v___jp_968_;
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
uint8_t v___x_1199_; 
lean_dec_ref(v_hypQueue_1055_);
lean_del_object(v___x_1048_);
v___x_1199_ = 2;
v___y_974_ = v___x_1052_;
v___y_975_ = v_a_1046_;
v_a_976_ = v___x_1199_;
goto v___jp_973_;
}
}
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_satExpr_1204_; lean_object* v_hypQueue_1205_; lean_object* v_usedHyps_1206_; uint8_t v_didChange_1207_; lean_object* v_theoryState_1208_; lean_object* v_solverTimeBudgetMs_1209_; lean_object* v_roundBudget_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1351_; 
v___x_1202_ = lean_io_get_num_heartbeats();
v___x_1203_ = lean_st_ref_take(v_a_706_);
v_satExpr_1204_ = lean_ctor_get(v___x_1203_, 0);
v_hypQueue_1205_ = lean_ctor_get(v___x_1203_, 1);
v_usedHyps_1206_ = lean_ctor_get(v___x_1203_, 2);
v_didChange_1207_ = lean_ctor_get_uint8(v___x_1203_, sizeof(void*)*6);
v_theoryState_1208_ = lean_ctor_get(v___x_1203_, 3);
v_solverTimeBudgetMs_1209_ = lean_ctor_get(v___x_1203_, 4);
v_roundBudget_1210_ = lean_ctor_get(v___x_1203_, 5);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1212_ = v___x_1203_;
v_isShared_1213_ = v_isSharedCheck_1351_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_roundBudget_1210_);
lean_inc(v_solverTimeBudgetMs_1209_);
lean_inc(v_theoryState_1208_);
lean_inc(v_usedHyps_1206_);
lean_inc(v_hypQueue_1205_);
lean_inc(v_satExpr_1204_);
lean_dec(v___x_1203_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1351_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__8));
v___x_1216_ = l_Array_append___redArg(v_usedHyps_1206_, v_hypQueue_1205_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 2, v___x_1216_);
lean_ctor_set(v___x_1212_, 1, v___x_1215_);
v___x_1218_ = v___x_1212_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_satExpr_1204_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_theoryState_1208_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_solverTimeBudgetMs_1209_);
lean_ctor_set(v_reuseFailAlloc_1350_, 5, v_roundBudget_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1350_, sizeof(void*)*6, v_didChange_1207_);
v___x_1218_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1219_ = lean_st_ref_put(v_a_706_, v___x_1218_);
v___x_1220_ = lean_array_get_size(v_hypQueue_1205_);
v___x_1221_ = lean_nat_dec_eq(v___x_1220_, v___x_1214_);
if (v___x_1221_ == 0)
{
lean_object* v_goal_1222_; lean_object* v_tacticContext_1223_; lean_object* v___x_1224_; lean_object* v_config_1225_; lean_object* v_mode_1226_; lean_object* v_timeout_1227_; uint8_t v_trimProofs_1228_; uint8_t v_binaryProofs_1229_; uint8_t v_acNf_1230_; uint8_t v_andFlattening_1231_; uint8_t v_embeddedConstraintSubst_1232_; uint8_t v_graphviz_1233_; lean_object* v_maxSteps_1234_; uint8_t v_solverMode_1235_; uint8_t v_uf_1236_; lean_object* v_cegarRounds_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1348_; 
v_goal_1222_ = lean_ctor_get(v_a_705_, 0);
v_tacticContext_1223_ = lean_ctor_get(v_a_705_, 2);
lean_inc_ref(v_tacticContext_1223_);
v___x_1224_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_1223_);
v_config_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc_ref(v_config_1225_);
v_mode_1226_ = lean_ctor_get(v___x_1224_, 1);
lean_inc(v_mode_1226_);
lean_dec_ref(v___x_1224_);
v_timeout_1227_ = lean_ctor_get(v_config_1225_, 0);
v_trimProofs_1228_ = lean_ctor_get_uint8(v_config_1225_, sizeof(void*)*3);
v_binaryProofs_1229_ = lean_ctor_get_uint8(v_config_1225_, sizeof(void*)*3 + 1);
v_acNf_1230_ = lean_ctor_get_uint8(v_config_1225_, sizeof(void*)*3 + 2);
v_andFlattening_1231_ = lean_ctor_get_uint8(v_config_1225_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_1232_ = lean_ctor_get_uint8(v_config_1225_, sizeof(void*)*3 + 4);
v_graphviz_1233_ = lean_ctor_get_uint8(v_config_1225_, sizeof(void*)*3 + 8);
v_maxSteps_1234_ = lean_ctor_get(v_config_1225_, 1);
v_solverMode_1235_ = lean_ctor_get_uint8(v_config_1225_, sizeof(void*)*3 + 10);
v_uf_1236_ = lean_ctor_get_uint8(v_config_1225_, sizeof(void*)*3 + 11);
v_cegarRounds_1237_ = lean_ctor_get(v_config_1225_, 2);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_config_1225_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1239_ = v_config_1225_;
v_isShared_1240_ = v_isSharedCheck_1348_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_cegarRounds_1237_);
lean_inc(v_maxSteps_1234_);
lean_inc(v_timeout_1227_);
lean_dec(v_config_1225_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1348_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
lean_inc(v_goal_1222_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_goal_1222_);
v___x_1242_ = v___x_1048_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_goal_1222_);
v___x_1242_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1244_; 
if (v_isShared_1240_ == 0)
{
v___x_1244_ = v___x_1239_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_timeout_1227_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_maxSteps_1234_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_cegarRounds_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3, v_trimProofs_1228_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3 + 1, v_binaryProofs_1229_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3 + 2, v_acNf_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3 + 3, v_andFlattening_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_1232_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3 + 8, v_graphviz_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3 + 10, v_solverMode_1235_);
lean_ctor_set_uint8(v_reuseFailAlloc_1346_, sizeof(void*)*3 + 11, v_uf_1236_);
v___x_1244_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_theoryState_1249_; lean_object* v_satExpr_1250_; lean_object* v_hypQueue_1251_; lean_object* v_usedHyps_1252_; uint8_t v_didChange_1253_; lean_object* v_solverTimeBudgetMs_1254_; lean_object* v_roundBudget_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1345_; 
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*3 + 5, v___x_1221_);
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*3 + 6, v___x_1221_);
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*3 + 7, v___x_1221_);
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*3 + 9, v___x_1221_);
v___x_1245_ = lean_box(v___x_1051_);
v___x_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
v___x_1247_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_1226_, v___x_1244_, v___x_1246_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = lean_st_ref_take(v_a_706_);
v_theoryState_1249_ = lean_ctor_get(v___x_1248_, 3);
v_satExpr_1250_ = lean_ctor_get(v___x_1248_, 0);
v_hypQueue_1251_ = lean_ctor_get(v___x_1248_, 1);
v_usedHyps_1252_ = lean_ctor_get(v___x_1248_, 2);
v_didChange_1253_ = lean_ctor_get_uint8(v___x_1248_, sizeof(void*)*6);
v_solverTimeBudgetMs_1254_ = lean_ctor_get(v___x_1248_, 4);
v_roundBudget_1255_ = lean_ctor_get(v___x_1248_, 5);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1257_ = v___x_1248_;
v_isShared_1258_ = v_isSharedCheck_1345_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_roundBudget_1255_);
lean_inc(v_solverTimeBudgetMs_1254_);
lean_inc(v_theoryState_1249_);
lean_inc(v_usedHyps_1252_);
lean_inc(v_hypQueue_1251_);
lean_inc(v_satExpr_1250_);
lean_dec(v___x_1248_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1345_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_funState_1259_; lean_object* v_bitvecState_1260_; lean_object* v_preprocessCaches_1261_; lean_object* v_satSolver_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1344_; 
v_funState_1259_ = lean_ctor_get(v_theoryState_1249_, 0);
v_bitvecState_1260_ = lean_ctor_get(v_theoryState_1249_, 1);
v_preprocessCaches_1261_ = lean_ctor_get(v_theoryState_1249_, 2);
v_satSolver_1262_ = lean_ctor_get(v_theoryState_1249_, 3);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_theoryState_1249_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1264_ = v_theoryState_1249_;
v_isShared_1265_ = v_isSharedCheck_1344_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_satSolver_1262_);
lean_inc(v_preprocessCaches_1261_);
lean_inc(v_bitvecState_1260_);
lean_inc(v_funState_1259_);
lean_dec(v_theoryState_1249_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1344_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1266_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 2, v___x_1266_);
v___x_1268_ = v___x_1264_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_funState_1259_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_bitvecState_1260_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_satSolver_1262_);
v___x_1268_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1270_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 3, v___x_1268_);
v___x_1270_ = v___x_1257_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_satExpr_1250_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_hypQueue_1251_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_usedHyps_1252_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_solverTimeBudgetMs_1254_);
lean_ctor_set(v_reuseFailAlloc_1342_, 5, v_roundBudget_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*6, v_didChange_1253_);
v___x_1270_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_typeAnalysis_1276_; lean_object* v_target_1277_; lean_object* v_hypotheses_1278_; uint8_t v_didChange_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1340_; 
v___x_1271_ = lean_st_ref_put(v_a_706_, v___x_1270_);
v___x_1272_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_1273_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1273_, 0, v___x_1266_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
lean_ctor_set(v___x_1273_, 2, v___x_1242_);
lean_ctor_set(v___x_1273_, 3, v___x_1215_);
lean_ctor_set_uint8(v___x_1273_, sizeof(void*)*4, v___x_1221_);
v___x_1274_ = lean_st_mk_ref(v___x_1273_);
v___x_1275_ = lean_st_ref_take(v___x_1274_);
v_typeAnalysis_1276_ = lean_ctor_get(v___x_1275_, 1);
v_target_1277_ = lean_ctor_get(v___x_1275_, 2);
v_hypotheses_1278_ = lean_ctor_get(v___x_1275_, 3);
v_didChange_1279_ = lean_ctor_get_uint8(v___x_1275_, sizeof(void*)*4);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v___x_1275_, 0);
lean_dec(v_unused_1341_);
v___x_1281_ = v___x_1275_;
v_isShared_1282_ = v_isSharedCheck_1340_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_hypotheses_1278_);
lean_inc(v_target_1277_);
lean_inc(v_typeAnalysis_1276_);
lean_dec(v___x_1275_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1340_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_preprocessCaches_1261_);
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_preprocessCaches_1261_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_typeAnalysis_1276_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_target_1277_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_hypotheses_1278_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*4, v_didChange_1279_);
v___x_1284_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; size_t v_sz_1286_; size_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1285_ = lean_st_ref_put(v___x_1274_, v___x_1284_);
v_sz_1286_ = lean_array_size(v_hypQueue_1205_);
v___x_1287_ = ((size_t)0ULL);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_1286_, v___x_1287_, v_hypQueue_1205_);
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
v___x_1290_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_1289_, v___x_1247_, v___x_1274_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec_ref(v___x_1247_);
lean_dec_ref_known(v___x_1289_, 1);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v___x_1292_ = lean_st_ref_get(v___x_1274_);
lean_dec(v___x_1274_);
v___x_1293_ = lean_unbox(v_a_1291_);
lean_dec(v_a_1291_);
if (v___x_1293_ == 0)
{
lean_object* v_caches_1294_; lean_object* v_hypotheses_1295_; lean_object* v___x_1296_; lean_object* v_theoryState_1297_; lean_object* v_satExpr_1298_; lean_object* v_hypQueue_1299_; lean_object* v_usedHyps_1300_; uint8_t v_didChange_1301_; lean_object* v_solverTimeBudgetMs_1302_; lean_object* v_roundBudget_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1336_; 
v_caches_1294_ = lean_ctor_get(v___x_1292_, 0);
lean_inc_ref(v_caches_1294_);
v_hypotheses_1295_ = lean_ctor_get(v___x_1292_, 3);
lean_inc_ref(v_hypotheses_1295_);
lean_dec(v___x_1292_);
v___x_1296_ = lean_st_ref_take(v_a_706_);
v_theoryState_1297_ = lean_ctor_get(v___x_1296_, 3);
v_satExpr_1298_ = lean_ctor_get(v___x_1296_, 0);
v_hypQueue_1299_ = lean_ctor_get(v___x_1296_, 1);
v_usedHyps_1300_ = lean_ctor_get(v___x_1296_, 2);
v_didChange_1301_ = lean_ctor_get_uint8(v___x_1296_, sizeof(void*)*6);
v_solverTimeBudgetMs_1302_ = lean_ctor_get(v___x_1296_, 4);
v_roundBudget_1303_ = lean_ctor_get(v___x_1296_, 5);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1305_ = v___x_1296_;
v_isShared_1306_ = v_isSharedCheck_1336_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_roundBudget_1303_);
lean_inc(v_solverTimeBudgetMs_1302_);
lean_inc(v_theoryState_1297_);
lean_inc(v_usedHyps_1300_);
lean_inc(v_hypQueue_1299_);
lean_inc(v_satExpr_1298_);
lean_dec(v___x_1296_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1336_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_funState_1307_; lean_object* v_bitvecState_1308_; lean_object* v_satSolver_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1334_; 
v_funState_1307_ = lean_ctor_get(v_theoryState_1297_, 0);
v_bitvecState_1308_ = lean_ctor_get(v_theoryState_1297_, 1);
v_satSolver_1309_ = lean_ctor_get(v_theoryState_1297_, 3);
v_isSharedCheck_1334_ = !lean_is_exclusive(v_theoryState_1297_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v_theoryState_1297_, 2);
lean_dec(v_unused_1335_);
v___x_1311_ = v_theoryState_1297_;
v_isShared_1312_ = v_isSharedCheck_1334_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_satSolver_1309_);
lean_inc(v_bitvecState_1308_);
lean_inc(v_funState_1307_);
lean_dec(v_theoryState_1297_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1334_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 2, v_caches_1294_);
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_funState_1307_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_bitvecState_1308_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_caches_1294_);
lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_satSolver_1309_);
v___x_1314_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1316_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 3, v___x_1314_);
v___x_1316_ = v___x_1305_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_satExpr_1298_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_hypQueue_1299_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_usedHyps_1300_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v_solverTimeBudgetMs_1302_);
lean_ctor_set(v_reuseFailAlloc_1332_, 5, v_roundBudget_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1332_, sizeof(void*)*6, v_didChange_1301_);
v___x_1316_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; size_t v_sz_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_st_ref_put(v_a_706_, v___x_1316_);
v_sz_1318_ = lean_array_size(v_hypotheses_1295_);
v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_1295_, v_sz_1318_, v___x_1287_, v___x_1215_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec_ref(v_hypotheses_1295_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1319_, 1);
v___x_1321_ = lean_array_get_size(v_a_1320_);
v___x_1322_ = lean_nat_dec_eq(v___x_1321_, v___x_1214_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v_satExpr_1324_; uint8_t v___x_1325_; 
v___x_1323_ = lean_st_ref_get(v_a_706_);
v_satExpr_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc_ref(v_satExpr_1324_);
lean_dec(v___x_1323_);
v___x_1325_ = lean_nat_dec_lt(v___x_1214_, v___x_1321_);
if (v___x_1325_ == 0)
{
lean_dec(v_a_1320_);
v___y_1024_ = v___x_1202_;
v___y_1025_ = v_a_1046_;
v_a_1026_ = v_satExpr_1324_;
goto v___jp_1023_;
}
else
{
size_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_usize_of_nat(v___x_1321_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_1320_, v___x_1287_, v___x_1326_, v_satExpr_1324_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_1320_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___y_1024_ = v___x_1202_;
v___y_1025_ = v_a_1046_;
v_a_1026_ = v_a_1328_;
goto v___jp_1023_;
}
else
{
lean_object* v_a_1329_; 
v_a_1329_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1327_, 1);
v___y_1013_ = v___x_1202_;
v___y_1014_ = v_a_1046_;
v_a_1015_ = v_a_1329_;
goto v___jp_1012_;
}
}
}
else
{
uint8_t v___x_1330_; 
lean_dec(v_a_1320_);
v___x_1330_ = 2;
v___y_1018_ = v___x_1202_;
v___y_1019_ = v_a_1046_;
v_a_1020_ = v___x_1330_;
goto v___jp_1017_;
}
}
else
{
lean_object* v_a_1331_; 
v_a_1331_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1319_, 1);
v___y_1013_ = v___x_1202_;
v___y_1014_ = v_a_1046_;
v_a_1015_ = v_a_1331_;
goto v___jp_1012_;
}
}
}
}
}
}
else
{
uint8_t v___x_1337_; 
lean_dec(v___x_1292_);
v___x_1337_ = 0;
v___y_1018_ = v___x_1202_;
v___y_1019_ = v_a_1046_;
v_a_1020_ = v___x_1337_;
goto v___jp_1017_;
}
}
else
{
lean_object* v_a_1338_; 
lean_dec(v___x_1274_);
v_a_1338_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1290_, 1);
v___y_1013_ = v___x_1202_;
v___y_1014_ = v_a_1046_;
v_a_1015_ = v_a_1338_;
goto v___jp_1012_;
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
uint8_t v___x_1349_; 
lean_dec_ref(v_hypQueue_1205_);
lean_del_object(v___x_1048_);
v___x_1349_ = 2;
v___y_1018_ = v___x_1202_;
v___y_1019_ = v_a_1046_;
v_a_1020_ = v___x_1349_;
goto v___jp_1017_;
}
}
}
}
}
}
}
v___jp_720_:
{
lean_object* v___x_723_; lean_object* v_hypQueue_724_; lean_object* v_usedHyps_725_; uint8_t v_didChange_726_; lean_object* v_theoryState_727_; lean_object* v_solverTimeBudgetMs_728_; lean_object* v_roundBudget_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_740_; 
v___x_723_ = lean_st_ref_take(v___y_721_);
v_hypQueue_724_ = lean_ctor_get(v___x_723_, 1);
v_usedHyps_725_ = lean_ctor_get(v___x_723_, 2);
v_didChange_726_ = lean_ctor_get_uint8(v___x_723_, sizeof(void*)*6);
v_theoryState_727_ = lean_ctor_get(v___x_723_, 3);
v_solverTimeBudgetMs_728_ = lean_ctor_get(v___x_723_, 4);
v_roundBudget_729_ = lean_ctor_get(v___x_723_, 5);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v___x_723_, 0);
lean_dec(v_unused_741_);
v___x_731_ = v___x_723_;
v_isShared_732_ = v_isSharedCheck_740_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_roundBudget_729_);
lean_inc(v_solverTimeBudgetMs_728_);
lean_inc(v_theoryState_727_);
lean_inc(v_usedHyps_725_);
lean_inc(v_hypQueue_724_);
lean_dec(v___x_723_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_740_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v_a_722_);
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_722_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_hypQueue_724_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_usedHyps_725_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_theoryState_727_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v_solverTimeBudgetMs_728_);
lean_ctor_set(v_reuseFailAlloc_739_, 5, v_roundBudget_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_739_, sizeof(void*)*6, v_didChange_726_);
v___x_734_ = v_reuseFailAlloc_739_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_735_ = lean_st_ref_put(v___y_721_, v___x_734_);
v___x_736_ = 1;
v___x_737_ = lean_box(v___x_736_);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
}
v___jp_742_:
{
lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_758_ = lean_array_get_size(v_hypQueue_743_);
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lean_nat_dec_eq(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v_goal_761_; lean_object* v_tacticContext_762_; lean_object* v___x_763_; lean_object* v_config_764_; lean_object* v_mode_765_; lean_object* v_timeout_766_; uint8_t v_trimProofs_767_; uint8_t v_binaryProofs_768_; uint8_t v_acNf_769_; uint8_t v_andFlattening_770_; uint8_t v_embeddedConstraintSubst_771_; uint8_t v_graphviz_772_; lean_object* v_maxSteps_773_; uint8_t v_solverMode_774_; uint8_t v_uf_775_; lean_object* v_cegarRounds_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_922_; 
v_goal_761_ = lean_ctor_get(v___y_744_, 0);
v_tacticContext_762_ = lean_ctor_get(v___y_744_, 2);
lean_inc_ref(v_tacticContext_762_);
v___x_763_ = l_Lean_Meta_Tactic_BVDecide_TacticContext_preProcessContext(v_tacticContext_762_);
v_config_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc_ref(v_config_764_);
v_mode_765_ = lean_ctor_get(v___x_763_, 1);
lean_inc(v_mode_765_);
lean_dec_ref(v___x_763_);
v_timeout_766_ = lean_ctor_get(v_config_764_, 0);
v_trimProofs_767_ = lean_ctor_get_uint8(v_config_764_, sizeof(void*)*3);
v_binaryProofs_768_ = lean_ctor_get_uint8(v_config_764_, sizeof(void*)*3 + 1);
v_acNf_769_ = lean_ctor_get_uint8(v_config_764_, sizeof(void*)*3 + 2);
v_andFlattening_770_ = lean_ctor_get_uint8(v_config_764_, sizeof(void*)*3 + 3);
v_embeddedConstraintSubst_771_ = lean_ctor_get_uint8(v_config_764_, sizeof(void*)*3 + 4);
v_graphviz_772_ = lean_ctor_get_uint8(v_config_764_, sizeof(void*)*3 + 8);
v_maxSteps_773_ = lean_ctor_get(v_config_764_, 1);
v_solverMode_774_ = lean_ctor_get_uint8(v_config_764_, sizeof(void*)*3 + 10);
v_uf_775_ = lean_ctor_get_uint8(v_config_764_, sizeof(void*)*3 + 11);
v_cegarRounds_776_ = lean_ctor_get(v_config_764_, 2);
v_isSharedCheck_922_ = !lean_is_exclusive(v_config_764_);
if (v_isSharedCheck_922_ == 0)
{
v___x_778_ = v_config_764_;
v_isShared_779_ = v_isSharedCheck_922_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_cegarRounds_776_);
lean_inc(v_maxSteps_773_);
lean_inc(v_timeout_766_);
lean_dec(v_config_764_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_922_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_inc(v_goal_761_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_goal_761_);
if (v_isShared_779_ == 0)
{
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 3, 12);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_timeout_766_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_maxSteps_773_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_cegarRounds_776_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*3, v_trimProofs_767_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*3 + 1, v_binaryProofs_768_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*3 + 2, v_acNf_769_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*3 + 3, v_andFlattening_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*3 + 4, v_embeddedConstraintSubst_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*3 + 8, v_graphviz_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*3 + 10, v_solverMode_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_921_, sizeof(void*)*3 + 11, v_uf_775_);
v___x_782_ = v_reuseFailAlloc_921_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_theoryState_786_; lean_object* v_satExpr_787_; lean_object* v_hypQueue_788_; lean_object* v_usedHyps_789_; uint8_t v_didChange_790_; lean_object* v_solverTimeBudgetMs_791_; lean_object* v_roundBudget_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_920_; 
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*3 + 5, v___x_760_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*3 + 6, v___x_760_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*3 + 7, v___x_760_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*3 + 9, v___x_760_);
v___x_783_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__0));
v___x_784_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessContext_new(v_mode_765_, v___x_782_, v___x_783_);
v___x_785_ = lean_st_ref_take(v___y_745_);
v_theoryState_786_ = lean_ctor_get(v___x_785_, 3);
v_satExpr_787_ = lean_ctor_get(v___x_785_, 0);
v_hypQueue_788_ = lean_ctor_get(v___x_785_, 1);
v_usedHyps_789_ = lean_ctor_get(v___x_785_, 2);
v_didChange_790_ = lean_ctor_get_uint8(v___x_785_, sizeof(void*)*6);
v_solverTimeBudgetMs_791_ = lean_ctor_get(v___x_785_, 4);
v_roundBudget_792_ = lean_ctor_get(v___x_785_, 5);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_920_ == 0)
{
v___x_794_ = v___x_785_;
v_isShared_795_ = v_isSharedCheck_920_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_roundBudget_792_);
lean_inc(v_solverTimeBudgetMs_791_);
lean_inc(v_theoryState_786_);
lean_inc(v_usedHyps_789_);
lean_inc(v_hypQueue_788_);
lean_inc(v_satExpr_787_);
lean_dec(v___x_785_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_920_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_funState_796_; lean_object* v_bitvecState_797_; lean_object* v_preprocessCaches_798_; lean_object* v_satSolver_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_919_; 
v_funState_796_ = lean_ctor_get(v_theoryState_786_, 0);
v_bitvecState_797_ = lean_ctor_get(v_theoryState_786_, 1);
v_preprocessCaches_798_ = lean_ctor_get(v_theoryState_786_, 2);
v_satSolver_799_ = lean_ctor_get(v_theoryState_786_, 3);
v_isSharedCheck_919_ = !lean_is_exclusive(v_theoryState_786_);
if (v_isSharedCheck_919_ == 0)
{
v___x_801_ = v_theoryState_786_;
v_isShared_802_ = v_isSharedCheck_919_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_satSolver_799_);
lean_inc(v_preprocessCaches_798_);
lean_inc(v_bitvecState_797_);
lean_inc(v_funState_796_);
lean_dec(v_theoryState_786_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_919_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__3);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 2, v___x_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_funState_796_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v_bitvecState_797_);
lean_ctor_set(v_reuseFailAlloc_918_, 2, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_918_, 3, v_satSolver_799_);
v___x_805_ = v_reuseFailAlloc_918_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 3, v___x_805_);
v___x_807_ = v___x_794_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_satExpr_787_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_hypQueue_788_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_usedHyps_789_);
lean_ctor_set(v_reuseFailAlloc_917_, 3, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_917_, 4, v_solverTimeBudgetMs_791_);
lean_ctor_set(v_reuseFailAlloc_917_, 5, v_roundBudget_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_917_, sizeof(void*)*6, v_didChange_790_);
v___x_807_ = v_reuseFailAlloc_917_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v_typeAnalysis_814_; lean_object* v_target_815_; lean_object* v_hypotheses_816_; uint8_t v_didChange_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_915_; 
v___x_808_ = lean_st_ref_put(v___y_745_, v___x_807_);
v___x_809_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6, &l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__6);
v___x_810_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___closed__7));
v___x_811_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_811_, 0, v___x_803_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
lean_ctor_set(v___x_811_, 2, v___x_780_);
lean_ctor_set(v___x_811_, 3, v___x_810_);
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*4, v___x_760_);
v___x_812_ = lean_st_mk_ref(v___x_811_);
v___x_813_ = lean_st_ref_take(v___x_812_);
v_typeAnalysis_814_ = lean_ctor_get(v___x_813_, 1);
v_target_815_ = lean_ctor_get(v___x_813_, 2);
v_hypotheses_816_ = lean_ctor_get(v___x_813_, 3);
v_didChange_817_ = lean_ctor_get_uint8(v___x_813_, sizeof(void*)*4);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v___x_813_, 0);
lean_dec(v_unused_916_);
v___x_819_ = v___x_813_;
v_isShared_820_ = v_isSharedCheck_915_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_hypotheses_816_);
lean_inc(v_target_815_);
lean_inc(v_typeAnalysis_814_);
lean_dec(v___x_813_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_915_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v_preprocessCaches_798_);
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_preprocessCaches_798_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_typeAnalysis_814_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_target_815_);
lean_ctor_set(v_reuseFailAlloc_914_, 3, v_hypotheses_816_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*4, v_didChange_817_);
v___x_822_ = v_reuseFailAlloc_914_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; size_t v_sz_824_; size_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_823_ = lean_st_ref_put(v___x_812_, v___x_822_);
v_sz_824_ = lean_array_size(v_hypQueue_743_);
v___x_825_ = ((size_t)0ULL);
v___x_826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__1(v_sz_824_, v___x_825_, v_hypQueue_743_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___x_828_ = l_Lean_Meta_Tactic_BVDecide_Normalize_bvNormalize(v___x_827_, v___x_784_, v___x_812_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec_ref(v___x_784_);
lean_dec_ref_known(v___x_827_, 1);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_905_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_905_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_905_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_905_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = lean_st_ref_get(v___x_812_);
lean_dec(v___x_812_);
v___x_834_ = lean_unbox(v_a_829_);
lean_dec(v_a_829_);
if (v___x_834_ == 0)
{
lean_object* v_caches_835_; lean_object* v_hypotheses_836_; lean_object* v___x_837_; lean_object* v_theoryState_838_; lean_object* v_satExpr_839_; lean_object* v_hypQueue_840_; lean_object* v_usedHyps_841_; uint8_t v_didChange_842_; lean_object* v_solverTimeBudgetMs_843_; lean_object* v_roundBudget_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_899_; 
lean_del_object(v___x_831_);
v_caches_835_ = lean_ctor_get(v___x_833_, 0);
lean_inc_ref(v_caches_835_);
v_hypotheses_836_ = lean_ctor_get(v___x_833_, 3);
lean_inc_ref(v_hypotheses_836_);
lean_dec(v___x_833_);
v___x_837_ = lean_st_ref_take(v___y_745_);
v_theoryState_838_ = lean_ctor_get(v___x_837_, 3);
v_satExpr_839_ = lean_ctor_get(v___x_837_, 0);
v_hypQueue_840_ = lean_ctor_get(v___x_837_, 1);
v_usedHyps_841_ = lean_ctor_get(v___x_837_, 2);
v_didChange_842_ = lean_ctor_get_uint8(v___x_837_, sizeof(void*)*6);
v_solverTimeBudgetMs_843_ = lean_ctor_get(v___x_837_, 4);
v_roundBudget_844_ = lean_ctor_get(v___x_837_, 5);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_899_ == 0)
{
v___x_846_ = v___x_837_;
v_isShared_847_ = v_isSharedCheck_899_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_roundBudget_844_);
lean_inc(v_solverTimeBudgetMs_843_);
lean_inc(v_theoryState_838_);
lean_inc(v_usedHyps_841_);
lean_inc(v_hypQueue_840_);
lean_inc(v_satExpr_839_);
lean_dec(v___x_837_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_899_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_funState_848_; lean_object* v_bitvecState_849_; lean_object* v_satSolver_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_897_; 
v_funState_848_ = lean_ctor_get(v_theoryState_838_, 0);
v_bitvecState_849_ = lean_ctor_get(v_theoryState_838_, 1);
v_satSolver_850_ = lean_ctor_get(v_theoryState_838_, 3);
v_isSharedCheck_897_ = !lean_is_exclusive(v_theoryState_838_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v_theoryState_838_, 2);
lean_dec(v_unused_898_);
v___x_852_ = v_theoryState_838_;
v_isShared_853_ = v_isSharedCheck_897_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_satSolver_850_);
lean_inc(v_bitvecState_849_);
lean_inc(v_funState_848_);
lean_dec(v_theoryState_838_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_897_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 2, v_caches_835_);
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_funState_848_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_bitvecState_849_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_caches_835_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v_satSolver_850_);
v___x_855_ = v_reuseFailAlloc_896_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 3, v___x_855_);
v___x_857_ = v___x_846_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_satExpr_839_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_hypQueue_840_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_usedHyps_841_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_solverTimeBudgetMs_843_);
lean_ctor_set(v_reuseFailAlloc_895_, 5, v_roundBudget_844_);
lean_ctor_set_uint8(v_reuseFailAlloc_895_, sizeof(void*)*6, v_didChange_842_);
v___x_857_ = v_reuseFailAlloc_895_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; size_t v_sz_859_; lean_object* v___x_860_; 
v___x_858_ = lean_st_ref_put(v___y_745_, v___x_857_);
v_sz_859_ = lean_array_size(v_hypotheses_836_);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__2(v_hypotheses_836_, v_sz_859_, v___x_825_, v___x_810_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec_ref(v_hypotheses_836_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_886_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_886_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_886_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_886_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = lean_array_get_size(v_a_861_);
v___x_866_ = lean_nat_dec_eq(v___x_865_, v___x_759_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v_satExpr_868_; uint8_t v___x_869_; 
lean_del_object(v___x_863_);
v___x_867_ = lean_st_ref_get(v___y_745_);
v_satExpr_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc_ref(v_satExpr_868_);
lean_dec(v___x_867_);
v___x_869_ = lean_nat_dec_lt(v___x_759_, v___x_865_);
if (v___x_869_ == 0)
{
lean_dec(v_a_861_);
v___y_721_ = v___y_745_;
v_a_722_ = v_satExpr_868_;
goto v___jp_720_;
}
else
{
size_t v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_usize_of_nat(v___x_865_);
v___x_871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_a_861_, v___x_825_, v___x_870_, v_satExpr_868_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v_a_861_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___y_721_ = v___y_745_;
v_a_722_ = v_a_872_;
goto v___jp_720_;
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_871_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
else
{
uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
lean_dec(v_a_861_);
v___x_881_ = 2;
v___x_882_ = lean_box(v___x_881_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_882_);
v___x_884_ = v___x_863_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_a_887_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_860_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_860_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
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
uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
lean_dec(v___x_833_);
v___x_900_ = 0;
v___x_901_ = lean_box(v___x_900_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_901_);
v___x_903_ = v___x_831_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec(v___x_812_);
v_a_906_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_828_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_828_);
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
}
}
}
}
}
}
}
else
{
uint8_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec_ref(v_hypQueue_743_);
v___x_923_ = 2;
v___x_924_ = lean_box(v___x_923_);
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
return v___x_925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps___boxed(lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps(v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
lean_dec(v_a_1386_);
lean_dec_ref(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec_ref(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
lean_dec(v_a_1378_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(lean_object* v_00_u03b1_1389_, lean_object* v_msg_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___redArg(v_msg_1390_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_1407_ = _args[0];
lean_object* v_msg_1408_ = _args[1];
lean_object* v___y_1409_ = _args[2];
lean_object* v___y_1410_ = _args[3];
lean_object* v___y_1411_ = _args[4];
lean_object* v___y_1412_ = _args[5];
lean_object* v___y_1413_ = _args[6];
lean_object* v___y_1414_ = _args[7];
lean_object* v___y_1415_ = _args[8];
lean_object* v___y_1416_ = _args[9];
lean_object* v___y_1417_ = _args[10];
lean_object* v___y_1418_ = _args[11];
lean_object* v___y_1419_ = _args[12];
lean_object* v___y_1420_ = _args[13];
lean_object* v___y_1421_ = _args[14];
lean_object* v___y_1422_ = _args[15];
lean_object* v___y_1423_ = _args[16];
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__0(v_00_u03b1_1407_, v_msg_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(lean_object* v_as_1425_, size_t v_i_1426_, size_t v_stop_1427_, lean_object* v_b_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___redArg(v_as_1425_, v_i_1426_, v_stop_1427_, v_b_1428_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3___boxed(lean_object** _args){
lean_object* v_as_1445_ = _args[0];
lean_object* v_i_1446_ = _args[1];
lean_object* v_stop_1447_ = _args[2];
lean_object* v_b_1448_ = _args[3];
lean_object* v___y_1449_ = _args[4];
lean_object* v___y_1450_ = _args[5];
lean_object* v___y_1451_ = _args[6];
lean_object* v___y_1452_ = _args[7];
lean_object* v___y_1453_ = _args[8];
lean_object* v___y_1454_ = _args[9];
lean_object* v___y_1455_ = _args[10];
lean_object* v___y_1456_ = _args[11];
lean_object* v___y_1457_ = _args[12];
lean_object* v___y_1458_ = _args[13];
lean_object* v___y_1459_ = _args[14];
lean_object* v___y_1460_ = _args[15];
lean_object* v___y_1461_ = _args[16];
lean_object* v___y_1462_ = _args[17];
lean_object* v___y_1463_ = _args[18];
_start:
{
size_t v_i_boxed_1464_; size_t v_stop_boxed_1465_; lean_object* v_res_1466_; 
v_i_boxed_1464_ = lean_unbox_usize(v_i_1446_);
lean_dec(v_i_1446_);
v_stop_boxed_1465_ = lean_unbox_usize(v_stop_1447_);
lean_dec(v_stop_1447_);
v_res_1466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__3(v_as_1445_, v_i_boxed_1464_, v_stop_boxed_1465_, v_b_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec_ref(v_as_1445_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(lean_object* v_00_u03b1_1467_, lean_object* v_x_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___redArg(v_x_1468_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_00_u03b1_1485_ = _args[0];
lean_object* v_x_1486_ = _args[1];
lean_object* v___y_1487_ = _args[2];
lean_object* v___y_1488_ = _args[3];
lean_object* v___y_1489_ = _args[4];
lean_object* v___y_1490_ = _args[5];
lean_object* v___y_1491_ = _args[6];
lean_object* v___y_1492_ = _args[7];
lean_object* v___y_1493_ = _args[8];
lean_object* v___y_1494_ = _args[9];
lean_object* v___y_1495_ = _args[10];
lean_object* v___y_1496_ = _args[11];
lean_object* v___y_1497_ = _args[12];
lean_object* v___y_1498_ = _args[13];
lean_object* v___y_1499_ = _args[14];
lean_object* v___y_1500_ = _args[15];
lean_object* v___y_1501_ = _args[16];
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__8(v_00_u03b1_1485_, v_x_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(lean_object* v_oldTraces_1503_, lean_object* v_data_1504_, lean_object* v_ref_1505_, lean_object* v_msg_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___redArg(v_oldTraces_1503_, v_data_1504_, v_ref_1505_, v_msg_1506_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7___boxed(lean_object** _args){
lean_object* v_oldTraces_1523_ = _args[0];
lean_object* v_data_1524_ = _args[1];
lean_object* v_ref_1525_ = _args[2];
lean_object* v_msg_1526_ = _args[3];
lean_object* v___y_1527_ = _args[4];
lean_object* v___y_1528_ = _args[5];
lean_object* v___y_1529_ = _args[6];
lean_object* v___y_1530_ = _args[7];
lean_object* v___y_1531_ = _args[8];
lean_object* v___y_1532_ = _args[9];
lean_object* v___y_1533_ = _args[10];
lean_object* v___y_1534_ = _args[11];
lean_object* v___y_1535_ = _args[12];
lean_object* v___y_1536_ = _args[13];
lean_object* v___y_1537_ = _args[14];
lean_object* v___y_1538_ = _args[15];
lean_object* v___y_1539_ = _args[16];
lean_object* v___y_1540_ = _args[17];
lean_object* v___y_1541_ = _args[18];
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Cegar_processNewHyps_spec__6_spec__7(v_oldTraces_1523_, v_data_1524_, v_ref_1525_, v_msg_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1542_;
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
